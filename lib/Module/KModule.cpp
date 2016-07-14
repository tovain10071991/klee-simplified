//===-- KModule.cpp -------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "KModule"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"

#include "Passes.h"

#include "klee/Config/Version.h"
#include "klee/Interpreter.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ModuleUtil.h"

#include "llvm/Bitcode/ReaderWriter.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/DataLayout.h"
#else
#include "llvm/Instructions.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/ValueSymbolTable.h"
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#else
#include "llvm/DataLayout.h"
#endif

#endif

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#include "llvm/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/Path.h"
#include "llvm/Transforms/Scalar.h"

#include <llvm/Transforms/Utils/Cloning.h>

#include <sstream>

using namespace llvm;
using namespace klee;

namespace {
  enum SwitchImplType {
    eSwitchTypeSimple,
    eSwitchTypeLLVM,
    eSwitchTypeInternal
  };
    
  cl::opt<bool>
  NoTruncateSourceLines("no-truncate-source-lines",
                        cl::desc("Don't truncate long lines in the output source"));

  cl::opt<bool>
  OutputSource("output-source",
               cl::desc("Write the assembly for the final transformed source"),
               cl::init(true));

  cl::opt<bool>
  OutputModule("output-module",
               cl::desc("Write the bitcode for the final transformed module"),
               cl::init(false));

  cl::opt<SwitchImplType>
  SwitchType("switch-type", cl::desc("Select the implementation of switch"),
             cl::values(clEnumValN(eSwitchTypeSimple, "simple", 
                                   "lower to ordered branches"),
                        clEnumValN(eSwitchTypeLLVM, "llvm", 
                                   "lower using LLVM"),
                        clEnumValN(eSwitchTypeInternal, "internal", 
                                   "execute switch internally"),
                        clEnumValEnd),
             cl::init(eSwitchTypeInternal));
  
  cl::opt<bool>
  DebugPrintEscapingFunctions("debug-print-escaping-functions", 
                              cl::desc("Print functions whose address is taken."));
}

namespace klee {
  std::map<uint64_t, KInstruction*> addr_inst_set;
  std::map<KInstruction*, uint64_t> inst_addr_set;
}

KModule::KModule(Module *_module) 
  : module(_module),
    targetData(new DataLayout(module)),
    constantTable(0) {
}

KModule::~KModule() {
  delete[] constantTable;

  for (std::map<llvm::Constant*, KConstant*>::iterator it=constantMap.begin(),
      itE=constantMap.end(); it!=itE;++it)
    delete it->second;

  delete targetData;
  delete module;
}

/***/

namespace llvm {
extern void Optimize(Module*);
}

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 3)
static void forceImport(Module *m, const char *name, LLVM_TYPE_Q Type *retType,
                        ...) {
  // If module lacks an externally visible symbol for the name then we
  // need to create one. We have to look in the symbol table because
  // we want to check everything (global variables, functions, and
  // aliases).

  Value *v = m->getValueSymbolTable().lookup(name);
  GlobalValue *gv = dyn_cast_or_null<GlobalValue>(v);

  if (!gv || gv->hasInternalLinkage()) {
    va_list ap;

    va_start(ap, retType);
    std::vector<LLVM_TYPE_Q Type *> argTypes;
    while (LLVM_TYPE_Q Type *t = va_arg(ap, LLVM_TYPE_Q Type*))
      argTypes.push_back(t);
    va_end(ap);

    m->getOrInsertFunction(name, FunctionType::get(retType, argTypes, false));
  }
}
#endif

void KModule::prepare(const Interpreter::ModuleOptions &opts,
                      InterpreterHandler *ih) {  
  for (Module::iterator it = module->begin(), ie = module->end();
       it != ie; ++it) {
    if (it->isDeclaration())
      continue;

    KFunction *kf = new KFunction(it, this);
    
    functionMap.insert(std::make_pair(it, kf));
  }
}

KConstant* KModule::getKConstant(Constant *c) {
  std::map<llvm::Constant*, KConstant*>::iterator it = constantMap.find(c);
  if (it != constantMap.end())
    return it->second;
  return NULL;
}

unsigned KModule::getConstantID(Constant *c, KInstruction* ki) {
  KConstant *kc = getKConstant(c);
  if (kc)
    return kc->id;  

  unsigned id = constants.size();
  kc = new KConstant(c, id, ki);
  constantMap.insert(std::make_pair(c, kc));
  constants.push_back(c);
  return id;
}

/***/

KConstant::KConstant(llvm::Constant* _ct, unsigned _id, KInstruction* _ki) {
  ct = _ct;
  id = _id;
  ki = _ki;
}

/***/

static int getOperandNum(Value *v,
                         std::map<Instruction*, unsigned> &registerMap,
                         KModule *km,
                         KInstruction *ki) {
  if (Instruction *inst = dyn_cast<Instruction>(v)) {
    return registerMap[inst];
  } else if (Argument *a = dyn_cast<Argument>(v)) {
    return a->getArgNo();
  } else if (isa<BasicBlock>(v) || isa<InlineAsm>(v) ||
             isa<MDNode>(v)) {
    return -1;
  } else {
    assert(isa<Constant>(v));
    Constant *c = cast<Constant>(v);
    return -(km->getConstantID(c, ki) + 2);
  }
}

uint64_t addr_count = 0;
uint64_t get_inst_addr(Instruction* inst)
{
  return addr_count++;
}

KFunction::KFunction(llvm::Function *_function,
                     KModule *km) 
  : function(_function),
    numArgs(function->arg_size()),
    numInstructions(0) {
  for (llvm::Function::iterator bbit = function->begin(), 
         bbie = function->end(); bbit != bbie; ++bbit) {
    BasicBlock *bb = bbit;
    basicBlockEntry[bb] = numInstructions;
    numInstructions += bb->size();
  }

  std::map<Instruction*, unsigned> registerMap;

  // The first arg_size() registers are reserved for formals.
  unsigned rnum = numArgs;
  for (llvm::Function::iterator bbit = function->begin(), 
         bbie = function->end(); bbit != bbie; ++bbit) {
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end();
         it != ie; ++it)
      registerMap[it] = rnum++;
  }
  numRegisters = rnum;
  
  unsigned i = 0;
  for (llvm::Function::iterator bbit = function->begin(), 
         bbie = function->end(); bbit != bbie; ++bbit) {
    for (llvm::BasicBlock::iterator it = bbit->begin(), ie = bbit->end();
         it != ie; ++it) {
      KInstruction *ki;

      switch(it->getOpcode()) {
      case Instruction::GetElementPtr:
      case Instruction::InsertValue:
      case Instruction::ExtractValue:
        ki = new KGEPInstruction(); break;
      default:
        ki = new KInstruction(); break;
      }

      ki->inst = it;      
      ki->dest = registerMap[it];

      if (isa<CallInst>(it) || isa<InvokeInst>(it)) {
        CallSite cs(it);
        unsigned numArgs = cs.arg_size();
        ki->operands = new int[numArgs+1];
        ki->operands[0] = getOperandNum(cs.getCalledValue(), registerMap, km,
                                        ki);
        for (unsigned j=0; j<numArgs; j++) {
          Value *v = cs.getArgument(j);
          ki->operands[j+1] = getOperandNum(v, registerMap, km, ki);
        }
      } else {
        unsigned numOperands = it->getNumOperands();
        ki->operands = new int[numOperands];
        for (unsigned j=0; j<numOperands; j++) {
          Value *v = it->getOperand(j);
          ki->operands[j] = getOperandNum(v, registerMap, km, ki);
        }
      }

      instructions.push_back(ki);
      uint64_t addr = get_inst_addr(ki->inst);
      inst_addr_set[ki] = addr;
      addr_inst_set[addr] = ki;
    }
  }
}

KFunction::~KFunction() {
  // for (unsigned i=0; i<numInstructions; ++i)
    // delete instructions[i];
  // delete[] instructions;
}
