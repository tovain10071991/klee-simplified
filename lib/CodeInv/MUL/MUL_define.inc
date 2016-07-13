define_visit(IMUL32r)
{
  assert(I->getNumOperands()==5);
  MachineOperand& rhs_opr = I->getOperand(0);
  assert(rhs_opr.isReg());
  assert(I->getOperand(4).isReg() && I->getOperand(4).getReg()==X86::EAX);
  assert(I->getOperand(2).isReg() && I->getOperand(2).getReg()==X86::EDX);
  assert(I->getOperand(1).isReg() && I->getOperand(1).getReg()==X86::EAX);
  assert(I->getOperand(3).isReg() && I->getOperand(3).getReg()==X86::EFLAGS);

  IRB->SetInsertPoint(BB);
  LLVMContext* context = Dec->getContext();

  //read lhs
  Value* lhs_val = get_reg_val(X86::EAX);

  //read rhs
  Value* rhs_val = get_reg_val(rhs_opr.getReg());

  // compute
  Value* result = IRB->CreateMul(IRB->CreateSExt(lhs_val, Type::getInt64Ty(*context)), IRB->CreateSExt(rhs_val, Type::getInt64Ty(*context)));

  // writeback
    
  store_reg_val(X86::EAX, IRB->CreateTrunc(result, Type::getInt32Ty(*context)));
  store_reg_val(X86::EDX, IRB->CreateTrunc(IRB->CreateLShr(result, 32), Type::getInt32Ty(*context)));
  

  IRB->CreateStore(IRB->CreateTrunc(IRB->CreateLShr(result, 32), Type::getInt1Ty(*context)), Dec->getModule()->getGlobalVariable("SF"));

  Value* tmp_value = IRB->CreateICmpNE(IRB->CreateSExt(IRB->CreateTrunc(result, Type::getInt32Ty(*context)), Type::getInt64Ty(*context)), result);
  IRB->CreateStore(tmp_value, Dec->getModule()->getGlobalVariable("CF"));
  IRB->CreateStore(tmp_value, Dec->getModule()->getGlobalVariable("OF"));
}

define_visit(IMUL32rm)
{
  assert(I->getNumOperands()==8);
  MachineOperand& lhs_opr = I->getOperand(1);
  assert(lhs_opr.isReg());
  MachineOperand& base_opr = I->getOperand(2);
  assert(base_opr.isReg());
  MachineOperand& scale_opr = I->getOperand(3);
  assert(scale_opr.isImm());
  MachineOperand& idx_opr = I->getOperand(4);
  assert(idx_opr.isReg());
  MachineOperand& off_opr = I->getOperand(5);
  assert(off_opr.isImm());
  MachineOperand& seg_opr = I->getOperand(6);
  assert(seg_opr.isReg());
  assert(I->getOperand(0).isReg() && I->getOperand(0).getReg()==lhs_opr.getReg());
  assert(I->getOperand(7).isReg() && I->getOperand(7).getReg()==X86::EFLAGS);

  IRB->SetInsertPoint(BB);
  LLVMContext* context = Dec->getContext();

  //read lhs
  Value* lhs_val = get_reg_val(lhs_opr.getReg());

  //read rhs
  Value* rhs_val = get_mem_val(base_opr.getReg(), scale_opr.getImm(), idx_opr.getReg(), off_opr.getImm(), seg_opr.getReg(), 32);

  // compute
  Value* tmp_result = IRB->CreateMul(IRB->CreateSExt(lhs_val, Type::getInt64Ty(*context)), IRB->CreateSExt(rhs_val, Type::getInt64Ty(*context)));
  Value* result = IRB->CreateTrunc(tmp_result, Type::getInt32Ty(*context));

  // writeback
    
  store_reg_val(lhs_opr.getReg(), result);  

	store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);

  Value* tmp_value = IRB->CreateICmpNE(IRB->CreateSExt(result, Type::getInt64Ty(*context)), tmp_result);
  IRB->CreateStore(tmp_value, Dec->getModule()->getGlobalVariable("CF"));
  IRB->CreateStore(tmp_value, Dec->getModule()->getGlobalVariable("OF"));

}