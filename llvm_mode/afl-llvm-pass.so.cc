/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS
#define DEBUG 1 
#include "../config.h"
#include "../debug.h"

#include <vector>
#include <map>
#include <set> 
#include <iostream> 
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <algorithm>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"

using namespace llvm;
using namespace std; 

vector<BasicBlock*> BBs, MultiBBs, SingleBBs; 
map<BasicBlock*, vector<BasicBlock*>> Preds; 
map<BasicBlock*, uint64_t> Keys; 

map<BasicBlock*, uint64_t> SingleHash; 
set<uint64_t> Hashes; 
map<BasicBlock*, array<uint64_t ,3>> Params; 
vector<BasicBlock*> Solv, UnSolv; 
map<pair<uint64_t, uint64_t>, uint64_t> HashMap; 
set<uint64_t> FreeHashes; 

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;
      void AssignUniqueRandomKeysToBBs(); 
      void CalcFmul(); 
      void CalcFhash();
      uint64_t RandomPopFreeHashes();  
      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;

void AFLCoverage::AssignUniqueRandomKeysToBBs() {
  uint64_t key = 0; 
  for(auto &BB: BBs) {
    Keys[&*BB] = key;  
    key += 1; 
  }
}

void AFLCoverage::CalcFmul() {
  for(uint64_t y = 1; y <= MAP_SIZE_POW2; y++) {
    Hashes.clear(); 
    Params.clear(); 
    Solv.clear(), UnSolv.clear(); 

    for(auto &bb_it: MultiBBs) {
      BasicBlock* BB= &*bb_it; 
      for(uint64_t x = 1; x <= MAP_SIZE_POW2; x++) {
        for(uint64_t z = 1; z <= MAP_SIZE_POW2; z++) {
          set<uint64_t> tmpHashSet; 
          uint64_t cur = Keys[BB]; 
          for(auto &p: Preds[BB]) {
            BasicBlock* predBB= &*p; 
            uint64_t edgeHash = (cur >> x) xor (Keys[predBB] >> y) + z; 
            tmpHashSet.insert(edgeHash);  
          }    

          set<uint64_t> interactionSet; 
          set_intersection(tmpHashSet.begin(), tmpHashSet.end(), Hashes.begin(), Hashes.end(), inserter(interactionSet, interactionSet.begin())); 
          if(tmpHashSet.size() == Preds[BB].size() && interactionSet.empty()) {
            Solv.push_back(BB); 
            Params[BB] = {x, y, z}; 
            Hashes.insert(tmpHashSet.begin(), tmpHashSet.end()); 
          }
        }
      }

      UnSolv.push_back(BB); 
    }

    if(UnSolv.empty() || (UnSolv.size()/BBs.size()) < 0.0001) {
      break; 
    }
  }
}

uint64_t AFLCoverage::RandomPopFreeHashes() {
  uint64_t randomHash = *FreeHashes.begin(); 
  FreeHashes.erase(randomHash); 
  return randomHash; 
}
void AFLCoverage::CalcFhash() {
  //create FreeHashes 
  for(uint64_t hash=1 ; hash < MAP_SIZE; hash++) {
    if(Hashes.count(hash) != 0) {
      continue ; 
    }
    FreeHashes.insert(hash); 
  }

#ifdef DEBUG 
  cout << "Hashes size: " << Hashes.size() << endl; 
  cout << "FreeHashes size: " << FreeHashes.size() << endl; 
#endif 

  for(auto &BB: UnSolv) {
    uint64_t cur = Keys[&*BB];  
    for(auto &P: Preds[&*BB]) {
      HashMap[make_pair(cur, Keys[&*P])] = RandomPopFreeHashes(); 
    }
  }
}


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  //step1 create BBs, SingleBBs, MultiBBs, Preds 
  int inst_blocks = 0;
 
  for (auto &F : M) {
    for(Function::iterator B = F.begin(), B_end = F.end(); B != B_end; B++) {
      BasicBlock* BB = &*B; 
      BBs.push_back(BB); 

      if(BB->hasNPredecessors(1)) {
        SingleBBs.push_back(BB);
      } else {
        MultiBBs.push_back(BB); 
      }

      for(auto it = pred_begin(BB), it_end = pred_end(BB); it != it_end; it ++) {
        Preds[BB].push_back(*it); 
      }
    }
  }
#ifdef DEBUG 
  cout << "BBs: "<< BBs.size() << endl; 
  cout << "SingleBBs: " << SingleBBs.size() << endl; 
  cout << "MultiBBs: " << MultiBBs.size() << endl; 
#endif

  //step2 create Keys 
  AssignUniqueRandomKeysToBBs(); 

  //step3 calc_fmul 
  CalcFmul(); 

  //step4 calc_Fhash 
  CalcFhash();

 //step5 InstrumentFmul 
  
  
#ifdef DEBUG
  for(auto &BB: MultiBBs) {
    printf("%lu %lu %lu\n", Params[&*BB][0], Params[&*BB][1], Params[&*BB][2]); 
  }
#endif

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
