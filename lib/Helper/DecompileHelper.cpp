#include "Helper/DecompileHelper.h"
#include "Helper/LLDBHelper.h"
#include "Helper/DebugHelper.h"

#include "CodeInv/Decompiler.h"
#include "CodeInv/Disassembler.h"
#include "CodeInv/MCDirector.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Host.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"
#include "llvm/Linker.h"

#include <map>
#include <string>
#include <err.h>

#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Module/KInstruction.h"

using namespace std;
using namespace fracture;
using namespace llvm;
using namespace klee;

static map<unsigned long, Disassembler*> disassemblers;
// static map<unsigned long, Decompiler*> decompilers;
static MCDirector* mcd;
Module* module;

class DecompileInited {
public:
  DecompileInited()
  {
    InitializeNativeTarget();
    InitializeNativeTargetDisassembler();
    InitializeNativeTargetAsmParser();
  
    string tripleName = sys::getDefaultTargetTriple();
  
    mcd = new MCDirector(tripleName, "generic", "", TargetOptions(), Reloc::DynamicNoPIC, CodeModel::Default, CodeGenOpt::Default, outs(), errs());
  }
};
static DecompileInited inited;

static void init_module()
{  
  const TargetMachine* TM = mcd->getTargetMachine();
  LLVMContext* context = mcd->getContext();
  
  module = new Module("tested_module", *context);
  module->setTargetTriple(TM->getTargetTriple());
  module->setDataLayout(TM->getDataLayout()->getStringRepresentation());

  const MCRegisterInfo* MRI = mcd->getMCRegisterInfo();
  for(unsigned i = 1; i < MRI->getNumRegs(); ++i)
  {
    MCSuperRegIterator super_reg_iter(i, MRI);
    if(!super_reg_iter.isValid())
    {
      new GlobalVariable(*module, Type::getIntNTy(*context, mcd->getRegType(i).getSizeInBits()), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::get(Type::getIntNTy(*context, mcd->getRegType(i).getSizeInBits()), 0), MRI->getName(i));
    }
  }

  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "OF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "SF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "ZF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "AF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "PF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "CF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "TF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "IF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "DF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "RF");
  new GlobalVariable(*module, Type::getInt1Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::getFalse(*context), "NT");
  new GlobalVariable(*module, Type::getInt64Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::get(Type::getInt64Ty(*context), 0), "FS_BASE");
  new GlobalVariable(*module, Type::getInt64Ty(*context), false, GlobalVariable::LinkageTypes::ExternalLinkage, ConstantInt::get(Type::getInt64Ty(*context), 0), "GS_BASE");
}

Module* get_module(string binary)
{
  // object::ObjectFile* obj = object::ObjectFile::createObjectFile(binary);
  // assert(obj->isObject() && obj->isELF() && "it is not object");

  create_debugger(binary);

  init_module();
  return module;
}

Decompiler* get_decompiler(unsigned long addr)
{
  unsigned long base = get_base(addr);
  if(disassemblers.find(base)==disassemblers.end())
  {
    object::ObjectFile* obj = get_object(addr);
    disassemblers[base] = new Disassembler(mcd, obj, NULL, outs(), outs());
  }
  Decompiler* decompiler = new Decompiler(disassemblers[base], module, nulls(), nulls());
  return decompiler;
}

static MachineFunction* MF;
static MachineBasicBlock* MBB;
static BasicBlock* BB;
static Function* F;

map<Instruction*, uint64_t> inst_addr_set;
map<uint64_t, Instruction*> addr_inst_set;
map<uint64_t, uint64_t> addr_idx_set;
map<uint64_t, KInstruction*> idx_inst_set;
map<KInstruction*, uint64_t> inst_idx_set;
uint64_t idx_count = 1;
map<uint64_t, uint64_t> addr_size_set;

void decompile_inst(uint64_t addr)
{
  Decompiler* decompiler = get_decompiler(addr);
  decompiler->getDisassembler()->decodeInstruction(get_unload_addr(addr),
  MBB);
  MachineInstr& I = MBB->back();
  decompiler->getEmitter()->EmitIR(BB, &I);
  
  Instruction* inst = module->begin()->begin()->getFirstNonPHI();
  if(idx_count!=1)
  {
    inst = idx_inst_set[idx_count-1]->inst;
    inst = inst->getNextNode();
  }
  Instruction& end_inst = module->begin()->begin()->back();
  addr_idx_set[decompiler->getDisassembler()->getDebugOffset(inst->getDebugLoc())] = idx_count;
  addr_size_set[addr] = I.getDesc().getSize();
  while(1) {
    inst_addr_set[inst] = addr;
    if(inst == &end_inst)
      break;
    inst = inst->getNextNode();
  }
}

Function* get_first_func(unsigned long addr)
{
  Decompiler* decompiler = get_decompiler(addr);
  Function* func = decompiler->decompileFunction(get_unload_addr(addr));
  assert(!func->empty());
  decompiler->getModule()->dump();
  if(func->getParent()!=module)
  {
    string error;
    if(Linker::LinkModules(module, decompiler->getModule(), Linker::LinkerMode::PreserveSource, &error))
      errx(-1, "link module failed: %s", error.c_str());
  }
  func = module->getFunction(func->getName());
  assert(func);
  return func;
}

Function* get_first_func(string func_name)
{
  Decompiler* decompiler = get_decompiler(get_addr(func_name));
  
  F = dyn_cast<Function>(module->getOrInsertFunction(func_name, FunctionType::get(Type::getVoidTy(*(mcd->getContext())), false)));
  
  unsigned func_unload_addr = (unsigned)get_unload_addr(get_addr(func_name));
  assert(func_unload_addr==get_unload_addr(get_addr(func_name)));
  MF = decompiler->getDisassembler()->getOrCreateFunction(func_unload_addr);
  
  std::stringstream MBBName;
  MBBName << "entry";

  // Dummy holds the name.
  BasicBlock *Dummy = BasicBlock::Create(*mcd->getContext(), MBBName.str());
  MBB = MF->CreateMachineBasicBlock(Dummy);
  MF->push_back(MBB);
  
  BB = decompiler->getOrCreateBasicBlock(MBB->getName(), F);
  
  decompile_inst(get_addr(func_name));
  
  return F;
}

Module* get_module_with_function(unsigned long addr)
{
  Decompiler* decompiler = get_decompiler(addr);
  Function* func = decompiler->decompileFunction(get_unload_addr(addr));
  assert(!func->empty());
  Module* mdl = decompiler->getModule();
  mdl->dump();
  return mdl;
}

Module* get_module_with_function(string func_name)
{
  unsigned long addr = get_addr(func_name);
  if(!addr)
    return NULL;
  return get_module_with_function(addr);
}