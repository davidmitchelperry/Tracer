// Tracer.cpp - Instruments a program so that the order
// of functions and basic blocks executed are recorded

#define DEBUG_TYPE "hello"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include <llvm/IR/DerivedTypes.h>

#include <map>
#include <vector>
using namespace llvm;

Module *mod_ptr;

// Takes a string and inserts a corresponding constant value into
// the program. These constants will be the strings printed by
// the inserted printf statements
Constant *geti8StrVal(Module &M, char const *str, Twine const &name) {

  LLVMContext &ctx = M.getContext();
  Constant *strConstant = ConstantDataArray::getString(ctx, str);
  GlobalVariable *GVStr =
      new GlobalVariable(M, strConstant->getType(), true,
                         GlobalValue::InternalLinkage, strConstant, name);
  Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(ctx));
  Constant *indices[] = { zero, zero };
  Constant *strVal = ConstantExpr::getGetElementPtr(NULL, GVStr, indices, true);
  return strVal;
}

// Create the printf function prototype. Will be used as an argument
// when creating/inserting new printfs into the program
static Function *printf_prototype(LLVMContext &ctx, Module *mod) {

  FunctionType *printf_type =
      TypeBuilder<int(char *, ...), false>::get(mod->getContext());

  Function *func = cast<Function>(mod->getOrInsertFunction(
      "printf", printf_type,
      AttributeSet().addAttribute(mod->getContext(), 1U, Attribute::NoAlias)));

  return func;
}

// Function that renames each basic block is named in a consistant fashion
void rename_bbs() {

  for (auto func = mod_ptr->begin(), func_e = mod_ptr->end(); func != func_e;
       ++func) {
    if (func->isDeclaration() == false) {
      bool first = true;
      for (Function::iterator bb = func->begin(), bb_e = func->end();
           bb != bb_e; ++bb) {
        // Setting each basic blocks name
        if (first) {
          first = false;
          bb->setName(func->getName() + "_" + "entry");
        } else {
          bb->setName(func->getName() + "_" + "bb");
        }
      }
    }
  }
}

void findTraceLocations(Module *M, Instruction *trace_begins,
                        std::vector<Instruction *> *trace_ends,
                        std::vector<Instruction *> *trace_prints,
                        std::vector<Instruction *> *func_returns,
                        std::vector<Instruction *> *func_calls) {

  bool inserted_first = false;
  iplist<Function> &fl = M->getFunctionList();

  // Iterate through each function
  for (auto func_it = fl.begin(); func_it != fl.end(); func_it++) {
    iplist<BasicBlock> &bb = func_it->getBasicBlockList();
    // Iterate through each basic block
    for (auto bb_it = bb.begin(); bb_it != bb.end(); bb_it++) {
      iplist<Instruction> &inst = bb_it->getInstList();
      bool bb_trace_print = false;
      // Iterate through each instruction
      for (auto inst_it = inst.begin(); inst_it != inst.end(); inst_it++) {
        // Mark where the program execution begins
        if (inserted_first == false) {
          if (func_it->getName().str() == "main") {
            trace_begins = &(*inst_it);
            inserted_first = true;
          }
        }
        // Skip all the phinodes at the beggining of BB's.
        // LLVM requires that phinode's (instructios) must
        // come before all other instructions in a BB
        if (!isa<PHINode>(&(*inst_it))) {
          // Track the location of the first non-phinode
          // instruction in the BB
          if (bb_trace_print == false) {
            trace_prints->push_back(&(*inst_it));
            bb_trace_print = true;
          }
        }
        // Track the various return instructions in the
        // program
        if (ReturnInst *ri = dyn_cast<ReturnInst>(&(*inst_it))) {
          // If returning from main, record end of trace
          if (func_it->getName().str() == "main") {
            trace_ends->push_back(&(*inst_it));
          }
          // Otherwise just record it as a func return
          else {
            func_returns->push_back(&(*inst_it));
          }
        }
        // Track the various functions called during the program
        if (CallInst *ci = dyn_cast<CallInst>(&(*inst_it))) {
          // Retrieve the function that is being called
          Function *fun = ci->getCalledFunction();
          if (fun) {
            // If an exit is called, trace ends
            if (fun->getName().str() == "exit") {
              trace_ends->push_back(&(*inst_it));
            }
            // Otherise if the function is not just
            // a declaration (aka it is user defined)
            else if (!fun->isDeclaration()) {
              func_calls->push_back(&(*inst_it));
            }
          }
        }
      }
    }
  }
}

STATISTIC(HelloCounter, "Counts number of functions greeted");
namespace {
// Hello - The first implementation, without getAnalysisUsage.
struct Hello : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  Hello() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {

    // LLVMContext &ctx = getGlobalContext();
    LLVMContext &ctx = M.getContext();
    IRBuilder<> builder(ctx);
    Function *printf_func = printf_prototype(ctx, &M);
    mod_ptr = &M;

    Instruction *trace_begins;
    std::vector<Instruction *> trace_ends;
    std::vector<Instruction *> trace_prints;

    std::vector<Instruction *> func_returns;
    std::vector<Instruction *> func_calls;

    rename_bbs();
    findTraceLocations(&M, trace_begins, &trace_ends, &trace_prints,
                       &func_returns, &func_calls);

    // Insert call to printf at the start of the program
    builder.CreateCall(printf_func, geti8StrVal(M, "trace_start\n", "test"))
        ->insertBefore(trace_begins);

    // Insert call to print the currently being executed BB's
    // name at the start of its execution
    for (int i = 0; i < trace_prints.size(); i++) {
      char *bbNameString =
          new char[trace_prints[i]->getParent()->getName().str().length() + 8];
      strcpy(bbNameString, "\ntrace:");
      strcpy(&bbNameString[7],
             trace_prints[i]->getParent()->getName().str().c_str());
      strcpy(&bbNameString
                  [7 + trace_prints[i]->getParent()->getName().str().length()],
             "\n");
      builder.CreateCall(printf_func, geti8StrVal(M, bbNameString, "test"))
          ->insertBefore(trace_prints[i]);
    }
    // Insert a printf right before any non-main function returns
    for (auto ret = func_returns.begin(); ret != func_returns.end(); ++ret) {
      builder.CreateCall(printf_func,
                         geti8StrVal(M, "\ntrace:return\n", "return"))
          ->insertBefore(*ret);
    }
    // Insert a printf before every function call
    for (auto call = func_calls.begin(); call != func_calls.end(); ++call) {
      builder.CreateCall(printf_func, geti8StrVal(M, "\ntrace:call\n", "call"))
          ->insertBefore(*call);
    }
    // Insert a printf at every point where the program's execution
    // can end
    for (int i = 0; i < trace_ends.size(); i++) {
      builder.CreateCall(printf_func, geti8StrVal(M, "\ntrace_end\n", "test"))
          ->insertBefore(trace_ends[i]);
    }

    return false;
  }
};
}

char Hello::ID = 0;
static RegisterPass<Hello> X("TracerPass", "Hello World Pass");
