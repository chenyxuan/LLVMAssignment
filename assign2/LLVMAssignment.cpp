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

#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>

#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang
 * will have optnone attribute which would lead to some transform passes
 * disabled, like mem2reg.
 */
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

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 2
/// Updated 11/10/2017 by fargo: make all functions
/// processed by mem2reg before this pass.
struct FuncPtrPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  FuncPtrPass() : ModulePass(ID) {}
  std::set<Function *> func_set;
  std::map<unsigned, std::set<Function *>> path_info;

  bool runOnModule(Module &M) override {
    // errs() << "Hello: ";
    // errs().write_escaped(M.getName()) << '\n';
    // M.dump();
    // errs()<<"------------------------------\n";

    for (auto it = M.begin(); it != M.end(); it++) {
      if (it->isDeclaration()) {
        continue;
      }

      func_set.insert(&*it);
    }

    for (auto it = func_set.begin(); it != func_set.end(); it++) {
      Function *func = *it;
      ParseFunc(func, std::vector<std::set<Function *>>(func->arg_size()));
    }

    for (auto it = path_info.begin(); it != path_info.end(); it++) {
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

  std::set<Function *> ParseCallInst(std::set<BasicBlock *> &visited,
                                     CallInst *call_inst,
                                     std::vector<std::set<Function *>> args) {
    std::set<Function *> result_set;
    std::set<Function *> callee_set =
        ParseValue(visited, call_inst->getCalledValue(), args);
    std::vector<std::set<Function *>> callee_args;
    for (unsigned i = 0; i < call_inst->getNumArgOperands(); i++) {
      Value *argi = call_inst->getArgOperand(i);
      if (argi->getType()->isPointerTy() &&
          argi->getType()->getPointerElementType()->isFunctionTy()) {
        callee_args.push_back(ParseValue(visited, argi, args));
      } else {
        callee_args.push_back(std::set<Function *>());
      }
    }

    for (auto it = callee_set.begin(); it != callee_set.end(); ++it) {
      Function *callee = *it;
      unsigned line = call_inst->getDebugLoc().getLine();
      path_info[line].insert(callee);
      if (func_set.count(callee) && !visited.count(&callee->getEntryBlock())) {
        std::set<Function *> potential_set = ParseFunc(callee, callee_args);
        for (auto it = potential_set.begin(); it != potential_set.end(); it++) {
          result_set.insert(*it);
        }
      }
    }
    return result_set;
  }

  std::set<Function *> ParseValue(std::set<BasicBlock *> &visited, Value *val,
                                  std::vector<std::set<Function *>> &args) {
    std::set<Function *> result_set;
    if (PHINode *phi = dyn_cast<PHINode>(val)) {
      for (unsigned int i = 0; i < phi->getNumIncomingValues(); i++) {
        BasicBlock *block = phi->getIncomingBlock(i);
        if (visited.count(block)) {
          std::set<Function *> val_set =
              ParseValue(visited, phi->getIncomingValue(i), args);
          for (auto it = val_set.begin(); it != val_set.end(); it++) {
            result_set.insert(*it);
          }
        }
      }
    } else if (Function *func = dyn_cast<Function>(val)) {
      result_set.insert(func);
    } else if (Argument *arg = dyn_cast<Argument>(val)) {
      std::set<Function *> &argset = args[arg->getArgNo()];
      for (auto it = argset.begin(); it != argset.end(); it++) {
        result_set.insert(*it);
      }
    } else if (CallInst *call_inst = dyn_cast<CallInst>(val)) {
      return ParseCallInst(visited, call_inst, args);
    }
    return result_set;
  }
  void ParseBlock(BasicBlock *block, std::set<BasicBlock *> visited,
                  std::set<Function *> *ret_ptr,
                  std::vector<std::set<Function *>> &args) {
    visited.insert(block);

    for (auto it = block->begin(); it != block->end(); it++) {
      if (dyn_cast<DbgInfoIntrinsic>(&*it)) {
        continue;
      } else if (BranchInst *branch_inst = dyn_cast<BranchInst>(&*it)) {
        auto successors = branch_inst->successors();
        for (auto si = successors.begin(); si != successors.end(); si++) {
          if (!visited.count(*si)) {
            ParseBlock(*si, visited, ret_ptr, args);
          }
        }
      } else if (ReturnInst *return_inst = dyn_cast<ReturnInst>(&*it)) {
        if (ret_ptr) {
          std::set<Function *> ret_funcs =
              ParseValue(visited, return_inst->getReturnValue(), args);
          for (auto it = ret_funcs.begin(); it != ret_funcs.end(); it++) {
            ret_ptr->insert(*it);
          }
        }
      } else if (CallInst *call_inst = dyn_cast<CallInst>(&*it)) {
        ParseCallInst(visited, call_inst, args);
      }
    }
  }
  std::set<Function *> ParseFunc(Function *fun,
                                 std::vector<std::set<Function *>> args) {
    if (func_set.count(fun) == 0) {
      return std::set<Function *>();
    }

    std::set<Function *> ret, *ret_ptr = nullptr;
    if (fun->getReturnType()->isPointerTy() &&
        fun->getReturnType()->getPointerElementType()->isFunctionTy()) {
      ret_ptr = &ret;
    }

    ParseBlock(&fun->getEntryBlock(), std::set<BasicBlock *>(), ret_ptr, args);

    return ret;
  }
};

char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass",
                                   "Print function call instruction");

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

  /// Remove functions' optnone attribute in LLVM5.0
  Passes.add(new EnableFunctionOptPass());
  /// Transform it to SSA
  Passes.add(llvm::createPromoteMemoryToRegisterPass());

  /// Your pass to print Function and Call Instructions
  Passes.add(new FuncPtrPass());
  Passes.run(*M.get());
}

