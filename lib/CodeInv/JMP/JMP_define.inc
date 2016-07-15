define_visit(JMP64r)
{
  assert(I->getNumOperands()==1);
  MachineOperand& target_opr = I->getOperand(0);
  assert(target_opr.isReg());

  IRB->SetInsertPoint(BB);

  // jmp target
  Value* target_val = get_reg_val(target_opr.getReg());
+  IRB->CreateCall(BB->getParent()->getParent()->getFunction("saib_branch"), std::vector<Value*>({target_val, get_imm_val(0, 64, 64), get_imm_val(1, 1, 1)}));
}

define_visit(JMP)
{
  assert(I->getNumOperands()==1);
  MachineOperand& off_opr = I->getOperand(0);
  assert(off_opr.isImm());

  IRB->SetInsertPoint(BB);

  int64_t off = off_opr.getImm();

  uint64_t target = Dec->getDisassembler()->getDebugOffset(I->getDebugLoc())+ I->getDesc().getSize() + off;
  Value* target_val = get_imm_val(target, 64, 64);
  IRB->CreateCall(BB->getParent()->getParent()->getFunction("saib_branch"), std::vector<Value*>({target_val, get_imm_val(0, 64, 64), get_imm_val(1, 1, 1)}));
}