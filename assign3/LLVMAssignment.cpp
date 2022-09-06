//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include <bits/stdc++.h>

#include "Liveness.h"

using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }

struct EnableFunctionOptPass : public FunctionPass {
  static char ID;
  EnableFunctionOptPass() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override {
    if (F.hasFnAttribute(Attribute::OptimizeNone)) {
      F.removeFnAttr(Attribute::OptimizeNone);
    }
    return true;
  }
};

char EnableFunctionOptPass::ID = 0;

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
std::map<unsigned, std::set<Function *>> pathInfo;

struct FuncPtrPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  FuncPtrPass() : ModulePass(ID) {}

  class FuncPtrInfo {
  public:
    std::map<Value *, std::set<Value *>> vmap;
    std::map<Value *, std::set<Value *>> mmap;
    std::pair<std::set<Value *>, std::map<Value *, std::set<Value *>>> *rptr;

    FuncPtrInfo() { rptr = nullptr; }

    bool operator==(const FuncPtrInfo &oth) const {
      return vmap == oth.vmap && mmap == oth.mmap;
    }
  };

  class FuncPtrVisitor : DataflowVisitor<FuncPtrInfo> {
  private:
    std::set<Value *> parseValue(Value *val, FuncPtrInfo *dfval) {
      std::set<Value *> result;
      if (val != nullptr) {
        if (Function *func = dyn_cast<Function>(val)) {
          result.insert(func);
        } else {
          result.insert(dfval->vmap[val].begin(), dfval->vmap[val].end());
        }
      }
      return result;
    }
    void visitAllocaInst(AllocaInst *inst, FuncPtrInfo *dfval) {
      dfval->vmap[inst].clear();
      dfval->vmap[inst].insert(inst);
    }
    void visitLoadInst(LoadInst *inst, FuncPtrInfo *dfval) {
      std::set<Value *> ptrSet = parseValue(inst->getPointerOperand(), dfval);
      dfval->vmap[inst].clear();
      for (auto ptr : ptrSet) {
        dfval->vmap[inst].insert(dfval->mmap[ptr].begin(),
                                 dfval->mmap[ptr].end());
      }
    }
    void visitStoreInst(StoreInst *inst, FuncPtrInfo *dfval) {
      std::set<Value *> valSet = parseValue(inst->getValueOperand(), dfval);
      std::set<Value *> ptrSet = parseValue(inst->getPointerOperand(), dfval);

      if (ptrSet.size() == 1) {
        Value *ptr = *ptrSet.begin();
        dfval->mmap[ptr].clear();
        dfval->mmap[ptr].insert(valSet.begin(), valSet.end());
      } else {
        for (auto ptr : ptrSet) {
          dfval->mmap[ptr].insert(valSet.begin(), valSet.end());
        }
      }
    }
    void visitMemCpyInst(MemCpyInst *inst, FuncPtrInfo *dfval) {
      BitCastInst *b0 = dyn_cast<BitCastInst>(inst->getArgOperand(0));
      BitCastInst *b1 = dyn_cast<BitCastInst>(inst->getArgOperand(1));
      if (b0 && b1) {
        std::set<Value *> destSet = parseValue(b0->getOperand(0), dfval);
        std::set<Value *> srcSet = parseValue(b1->getOperand(0), dfval);
        std::set<Value *> valSet;
        for (auto src : srcSet) {
          valSet.insert(dfval->mmap[src].begin(), dfval->mmap[src].end());
        }

        if (destSet.size() == 1) {
          Value *dest = *destSet.begin();
          dfval->mmap[dest].clear();
          dfval->mmap[dest].insert(valSet.begin(), valSet.end());
        } else {
          for (auto dest : destSet) {
            dfval->mmap[dest].insert(valSet.begin(), valSet.end());
          }
        }
      }
    }
    void visitPhiNode(PHINode *phi, FuncPtrInfo *dfval) {
      dfval->vmap[phi].clear();
      for (Value *val : phi->incoming_values()) {
        std::set<Value *> valSet = parseValue(val, dfval);
        dfval->vmap[phi].insert(valSet.begin(), valSet.end());
      }
    }
    void visitGepInst(GetElementPtrInst *inst, FuncPtrInfo *dfval) {
      std::set<Value *> ptrSet = parseValue(inst->getPointerOperand(), dfval);
      dfval->vmap[inst].clear();
      dfval->vmap[inst].insert(ptrSet.begin(), ptrSet.end());
    }
    void visitCallInst(CallInst *inst, FuncPtrInfo *dfval) {
      Value *val = inst->getCalledValue();
      std::set<Value *> calleeSet = parseValue(val, dfval);

      for (auto callee : calleeSet) {
        if (Function *func = dyn_cast<Function>(callee)) {
          if (func->isIntrinsic())
            continue;
          if (func->isDeclaration()) {
            dfval->vmap[inst].clear();
            dfval->vmap[inst].insert(inst);
          }
          pathInfo[inst->getDebugLoc().getLine()].insert(func);
        } else {
          errs() << "Error: callee is NOT a function!\n";
        }
      }
      std::vector<std::set<Value *>> calleeArgs;
      unsigned argNum = inst->getNumArgOperands();
      for (unsigned i = 0; i < argNum; i++) {
        Value *argi = inst->getArgOperand(i);
        calleeArgs.push_back(parseValue(argi, dfval));
      }

      std::map<Value *, std::set<Value *>> calleemmap;
      bool needUpdate = false;

      for (auto callee : calleeSet) {
        if (Function *func = dyn_cast<Function>(callee)) {
          if (func->isDeclaration())
            continue;

          FuncPtrVisitor visitor;
          DataflowResult<FuncPtrInfo>::Type result;
          FuncPtrInfo initval;
          std::pair<std::set<Value *>, std::map<Value *, std::set<Value *>>>
              rstate;
          initval.rptr = &rstate;

          for (auto entry : dfval->mmap) {
            initval.mmap[entry.first].insert(entry.second.begin(),
                                             entry.second.end());
          }
          for (unsigned i = 0; i < argNum; i++) {
            Argument *arg = func->getArg(i);
            initval.vmap[arg].insert(calleeArgs[i].begin(),
                                     calleeArgs[i].end());
          }

          visitor.forwardDataflow(func, &result, initval);
          dfval->vmap[inst].insert(rstate.first.begin(), rstate.first.end());

          for (auto entry : rstate.second) {
            calleemmap[entry.first].insert(entry.second.begin(),
                                           entry.second.end());
          }
          needUpdate = true;
        } else {
          errs() << "Error: callee is NOT a function!\n";
        }
      }

      if (needUpdate) {
        dfval->mmap.clear();
        for (auto entry : calleemmap) {
          dfval->mmap[entry.first].insert(entry.second.begin(),
                                          entry.second.end());
        }
      }
    }
    void visitReturnInst(ReturnInst *inst, FuncPtrInfo *dfval) {
      if (dfval->rptr) {
        std::set<Value *> valSet = parseValue(inst->getReturnValue(), dfval);
        dfval->rptr->first.insert(valSet.begin(), valSet.end());
        for (auto entry : dfval->mmap) {
          dfval->rptr->second[entry.first].insert(entry.second.begin(),
                                                  entry.second.end());
        }
      }
    }
    void visitBitCastInst(BitCastInst *inst, FuncPtrInfo *dfval) {
      std::set<Value *> ptrSet = parseValue(inst->getOperand(0), dfval);
      dfval->vmap[inst].clear();
      dfval->vmap[inst].insert(ptrSet.begin(), ptrSet.end());
    }

  public:
    void compDFVal(Instruction *inst, FuncPtrInfo *dfval) {
      if (dyn_cast<DbgInfoIntrinsic>(inst)) {
        return;
      }

      if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(inst)) {
        visitAllocaInst(allocaInst, dfval);
      } else if (LoadInst *ldInst = dyn_cast<LoadInst>(inst)) {
        visitLoadInst(ldInst, dfval);
      } else if (StoreInst *sdInst = dyn_cast<StoreInst>(inst)) {
        visitStoreInst(sdInst, dfval);
      } else if (MemCpyInst *mcInst = dyn_cast<MemCpyInst>(inst)) {
        visitMemCpyInst(mcInst, dfval);
      } else if (PHINode *phi = dyn_cast<PHINode>(inst)) {
        visitPhiNode(phi, dfval);
      } else if (GetElementPtrInst *gepInst =
                     dyn_cast<GetElementPtrInst>(inst)) {
        visitGepInst(gepInst, dfval);
      } else if (CallInst *callInst = dyn_cast<CallInst>(inst)) {
        visitCallInst(callInst, dfval);
      } else if (ReturnInst *retInst = dyn_cast<ReturnInst>(inst)) {
        visitReturnInst(retInst, dfval);
      } else if (BitCastInst *bcInst = dyn_cast<BitCastInst>(inst)) {
        visitBitCastInst(bcInst, dfval);
      }
    }
    void merge(FuncPtrInfo *dest, const FuncPtrInfo &src) {
      for (auto ii = src.vmap.begin(); ii != src.vmap.end(); ii++) {
        dest->vmap[ii->first].insert(ii->second.begin(), ii->second.end());
      }
      for (auto ii = src.mmap.begin(); ii != src.mmap.end(); ii++) {
        dest->mmap[ii->first].insert(ii->second.begin(), ii->second.end());
      }
    }

    void forwardDataflow(Function *fn,
                         typename DataflowResult<FuncPtrInfo>::Type *result,
                         const FuncPtrInfo &initval) {
      std::set<BasicBlock *> worklist;

      for (Function::iterator bi = fn->begin(); bi != fn->end(); ++bi) {
        BasicBlock *bb = &*bi;
        result->insert(std::make_pair(bb, std::make_pair(initval, initval)));
        worklist.insert(bb);
      }

      while (!worklist.empty()) {
        BasicBlock *bb = *worklist.begin();
        worklist.erase(worklist.begin());

        FuncPtrInfo bbentryval = (*result)[bb].first;
        for (auto pi = pred_begin(bb), pe = pred_end(bb); pi != pe; pi++) {
          BasicBlock *pred = *pi;
          merge(&bbentryval, (*result)[pred].second);
        }

        (*result)[bb].first = bbentryval;
        for (BasicBlock::iterator ii = bb->begin(), ie = bb->end(); ii != ie;
             ++ii) {
          Instruction *inst = &*ii;
          compDFVal(inst, &bbentryval);
        }

        if (bbentryval == (*result)[bb].second)
          continue;
        (*result)[bb].second = bbentryval;

        for (succ_iterator si = succ_begin(bb), se = succ_end(bb); si != se;
             si++) {
          worklist.insert(*si);
        }
      }
    }
  };

  bool runOnModule(Module &M) override {

    pathInfo.clear();
    for (auto it = M.begin(); it != M.end(); it++) {
      Function *F = &*it;
      if (F->isIntrinsic()) {
        continue;
      }

      FuncPtrVisitor visitor;
      DataflowResult<FuncPtrInfo>::Type result;
      FuncPtrInfo initval;

      visitor.forwardDataflow(F, &result, initval);
    }

    for (auto it = pathInfo.begin(); it != pathInfo.end(); it++) {
      unsigned line = it->first;
      std::set<Function *> &funcs = it->second;
      errs() << line << " : ";
      for (auto it = funcs.begin(); it != funcs.end(); it++) {
        if (it != funcs.begin()) {
          errs() << ", ";
        }
        errs() << (*it)->getName();
      }
      errs() << "\n";
    }
    return false;
  }
};

char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass",
                                   "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");

static cl::opt<std::string>
    InputFilename(cl::Positional, cl::desc("<filename>.bc"), cl::init(""));

int main(int argc, char **argv) {
  LLVMContext &Context = getGlobalContext();
  SMDiagnostic Err;
  // Parse the command line to read the Inputfilename
  cl::ParseCommandLineOptions(
      argc, argv, "FuncPtrPass \n My first LLVM too which does not do much.\n");

  // Load the input module
  std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }

  llvm::legacy::PassManager Passes;
#if LLVM_VERSION_MAJOR == 5
  Passes.add(new EnableFunctionOptPass());
#endif
  /// Transform it to SSA
  Passes.add(llvm::createPromoteMemoryToRegisterPass());

  /// Your pass to print Function and Call Instructions
  // Passes.add(new Liveness());
  Passes.add(new FuncPtrPass());
  Passes.run(*M.get());
}
