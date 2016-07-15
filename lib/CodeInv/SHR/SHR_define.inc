void IREmitter::Shrri(BasicBlock *BB, MachineInstr* I, unsigned init_size, unsigned final_size)
{
  assert(I->getNumOperands() == 4);
  MachineOperand& des_opr = I->getOperand(0);
  assert(des_opr.isReg());
  MachineOperand& lhs_opr = I->getOperand(1);
  assert(lhs_opr.isReg() && des_opr.getReg() == lhs_opr.getReg());
  MachineOperand& rhs_opr = I->getOperand(2);
  assert(rhs_opr.isImm());
  assert(I->getOperand(3).isReg() && I->getOperand(3).getReg() == X86::EFLAGS);

  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_reg_val(lhs_opr.getReg());

  // read rhs
  Constant* rhs_val = get_imm_val(rhs_opr.getImm(), init_size, final_size);

  // compute
  Value* result = IRB->CreateLShr(lhs_val, rhs_val);

  // writeback
  store_reg_val(des_opr.getReg(), result);

  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

// define_visit(SHR16m1)
// {
// }

// define_visit(SHR16mCL)
// {
// }

// define_visit(SHR16mi)
// {
// }

// define_visit(SHR16r1)
// {
// }

// define_visit(SHR16rCL)
// {
// }

define_visit(SHR16ri)
{
	Shrri(BB, I, 16, 16);
}

// define_visit(SHR32m1)
// {
// }

// define_visit(SHR32mCL)
// {
// }

// define_visit(SHR32mi)
// {
// }

// define_visit(SHR32r1)
// {
// }

// define_visit(SHR32rCL)
// {
// }

define_visit(SHR32ri)
{
	Shrri(BB, I, 32, 32);
}

// define_visit(SHR8m1)
// {
// }

// define_visit(SHR8mCL)
// {
// }

// define_visit(SHR8mi)
// {
// }

// define_visit(SHR8r1)
// {
// }

// define_visit(SHR8rCL)
// {
// }

define_visit(SHR8ri)
{
	Shrri(BB, I, 8, 8);
}

define_visit(SHR64ri)
{
	Shrri(BB, I, 64, 64);
}