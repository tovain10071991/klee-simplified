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