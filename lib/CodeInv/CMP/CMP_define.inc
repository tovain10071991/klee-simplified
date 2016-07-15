#define define_cmp(name) \
  void IREmitter::Cmp##name(BasicBlock *BB, MachineInstr* I, unsigned init_size, unsigned final_size)

define_cmp(r_)
{
  assert(I->getNumOperands()==3);
  MachineOperand& lhs_opr = I->getOperand(0);
  assert(lhs_opr.isReg());
  MachineOperand& rhs_opr = I->getOperand(1);
  assert(I->getOperand(2).isReg() && I->getOperand(2).getReg()==X86::EFLAGS);
  
  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_reg_val(lhs_opr.getReg());

  //read rhs
  Value* rhs_val;
  if(rhs_opr.isImm())
  {
    rhs_val = get_imm_val(rhs_opr.getImm(), init_size, final_size);
  }
  else
  {
    rhs_val = get_reg_val(rhs_opr.getReg());
  }

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_AF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

define_cmp(rm)
{
  assert(I->getNumOperands()==7);
  MachineOperand& lhs_opr = I->getOperand(0);
  assert(lhs_opr.isReg());
  MachineOperand& base_opr = I->getOperand(1);
  assert(base_opr.isReg());
  MachineOperand& scale_opr = I->getOperand(2);
  assert(scale_opr.isImm());
  MachineOperand& idx_opr = I->getOperand(3);
  assert(idx_opr.isReg());
  MachineOperand& off_opr = I->getOperand(4);
  assert(off_opr.isImm());
  MachineOperand& seg_opr = I->getOperand(5);
  assert(seg_opr.isReg());
  assert(I->getOperand(6).isReg() && I->getOperand(6).getReg()==X86::EFLAGS);

  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_reg_val(lhs_opr.getReg());

  //read rhs
  Value* rhs_val = get_mem_val(base_opr.getReg(), scale_opr.getImm(), idx_opr.getReg(), off_opr.getImm(), seg_opr.getReg(), final_size);

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_AF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

define_cmp(mi)
{
  assert(I->getNumOperands()==7);
  MachineOperand& base_opr = I->getOperand(0);
  assert(base_opr.isReg());
  MachineOperand& scale_opr = I->getOperand(1);
  assert(scale_opr.isImm());
  MachineOperand& idx_opr = I->getOperand(2);
  assert(idx_opr.isReg());
  MachineOperand& off_opr = I->getOperand(3);
  assert(off_opr.isImm());
  MachineOperand& seg_opr = I->getOperand(4);
  assert(seg_opr.isReg());
  MachineOperand& rhs_opr = I->getOperand(5);
  assert(rhs_opr.isImm());
  assert(I->getOperand(6).isReg() && I->getOperand(6).getReg()==X86::EFLAGS);

  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_mem_val(base_opr.getReg(), scale_opr.getImm(), idx_opr.getReg(), off_opr.getImm(), seg_opr.getReg(), final_size);

  //read rhs
  Value* rhs_val = get_imm_val(rhs_opr.getImm(), init_size, final_size);

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_AF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

define_visit(CMP8rr)
{
	Cmpr_(BB, I, 0, 0);
}

// define_visit(CMP8rr_REV)
// {
// }

define_visit(CMP16rr)
{
	Cmpr_(BB, I, 0, 0);
}

// define_visit(CMP16rr_REV)
// {
// }

// define_visit(CMP32rr_REV)
// {
// }

define_visit(CMP32rr)
{
	Cmpr_(BB, I, 0, 0);
}

define_visit(CMP64rr)
{
	Cmpr_(BB, I, 0, 0);
}

define_visit(CMP8ri)
{
	Cmpr_(BB, I, 8, 8);
}

// define_visit(CMP8i8)
// {
// }

define_visit(CMP16ri)
{
	Cmpr_(BB, I, 16, 16);
}

define_visit(CMP16ri8)
{
	Cmpr_(BB, I, 8, 16);
}

// define_visit(CMP16i16)
// {
// }

define_visit(CMP32i32)
{
  assert(I->getNumOperands()==4);
  MachineOperand& lhs_opr = I->getOperand(3);
  assert(lhs_opr.isReg());
  MachineOperand& rhs_opr = I->getOperand(0);
  assert(rhs_opr.isImm());
  assert(I->getOperand(1).isReg() && I->getOperand(1).getReg()==lhs_opr.getReg());
  assert(I->getOperand(2).isReg() && I->getOperand(2).getReg()==X86::EFLAGS);
  
  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_reg_val(lhs_opr.getReg());

  //read rhs
  Value* rhs_val;
  if(rhs_opr.isImm())
  {
    rhs_val = get_imm_val(rhs_opr.getImm(), 32, 32);
  }
  else
  {
    rhs_val = get_reg_val(rhs_opr.getReg());
  }

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_AF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

define_visit(CMP32ri)
{
	Cmpr_(BB, I, 32, 32);
}

define_visit(CMP32ri8)
{
	Cmpr_(BB, I, 8, 32);
}

define_visit(CMP64ri32)
{
	Cmpr_(BB, I, 32, 64);
}

define_visit(CMP64ri8)
{
	Cmpr_(BB, I, 8, 64);
}

define_visit(CMP64i32)
{
  assert(I->getNumOperands()==4);
  MachineOperand& lhs_opr = I->getOperand(3);
  assert(lhs_opr.isReg());
  assert(I->getOperand(1).isReg() && I->getOperand(1).getReg()==lhs_opr.getReg());  // is defed reg, why?
  MachineOperand& rhs_opr = I->getOperand(0);
  assert(rhs_opr.isImm());
  assert(I->getOperand(2).isReg() && I->getOperand(2).getReg()==X86::EFLAGS);
  
  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_reg_val(lhs_opr.getReg());

  //read rhs
  Value* rhs_val = get_imm_val(rhs_opr.getImm(), 32, 64);

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_AF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

define_visit(CMP32mi8)
{
	Cmpmi(BB, I, 8, 32);
}

define_visit(CMP8mi)
{
	Cmpmi(BB, I, 8, 8);
}

define_visit(CMP16mi)
{
	Cmpmi(BB, I, 16, 16);
}

define_visit(CMP32mi)
{
	Cmpmi(BB, I, 32, 32);
}

define_visit(CMP8rm)
{
	Cmprm(BB, I, 0, 8);
}

define_visit(CMP16rm)
{
	Cmprm(BB, I, 0, 16);
}

define_visit(CMP32rm)
{
	Cmprm(BB, I, 0, 32);
}

// define_visit(CMP8mr)
// {
// }

// define_visit(CMP16mr)
// {
// }

// define_visit(CMP32mr)
// {
// }

define_visit(CMP16mi8)
{
	Cmpmi(BB, I, 8, 16);
}

define_visit(CMP64mi8)
{
	Cmpmi(BB, I, 8, 64);
}

define_visit(CMP64mi32)
{
	Cmpmi(BB, I, 32, 64);
}

define_visit(CMP64rm)
{
	Cmprm(BB, I, 0, 64);
}

define_visit(CMP64mr)
{
  assert(I->getNumOperands()==7);
  MachineOperand& base_opr = I->getOperand(0);
  assert(base_opr.isReg());
  MachineOperand& scale_opr = I->getOperand(1);
  assert(scale_opr.isImm());
  MachineOperand& idx_opr = I->getOperand(2);
  assert(idx_opr.isReg());
  MachineOperand& off_opr = I->getOperand(3);
  assert(off_opr.isImm());
  MachineOperand& seg_opr = I->getOperand(4);
  assert(seg_opr.isReg());
  MachineOperand& rhs_opr = I->getOperand(5);
  assert(rhs_opr.isReg());
  assert(I->getOperand(6).isReg() && I->getOperand(6).getReg()==X86::EFLAGS);

  IRB->SetInsertPoint(BB);

  // read lhs
  Value* lhs_val = get_mem_val(base_opr.getReg(), scale_opr.getImm(), idx_opr.getReg(), off_opr.getImm(), seg_opr.getReg(), 64);

  //read rhs
  Value* rhs_val = get_reg_val(rhs_opr.getReg());

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_AF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_PF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_SF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_CF_val(I->getOpcode(), lhs_val, rhs_val, result);
  store_OF_val(I->getOpcode(), lhs_val, rhs_val, result);
}

define_visit(CMPXCHG32rm)
{
  assert(I->getNumOperands()==6);
  MachineOperand& base_opr = I->getOperand(0);
  assert(base_opr.isReg());
  MachineOperand& scale_opr = I->getOperand(1);
  assert(scale_opr.isImm());
  MachineOperand& idx_opr = I->getOperand(2);
  assert(idx_opr.isReg());
  MachineOperand& off_opr = I->getOperand(3);
  assert(off_opr.isImm());
  MachineOperand& seg_opr = I->getOperand(4);
  assert(seg_opr.isReg());
  MachineOperand& reg_opr = I->getOperand(5);
  assert(reg_opr.isReg());

  IRB->SetInsertPoint(BB);
  LLVMContext* context = Dec->getContext();
  
  // read lhs
  Value* lhs_val = get_mem_val(base_opr.getReg(), scale_opr.getImm(), idx_opr.getReg(), off_opr.getImm(), seg_opr.getReg(), 64);

  //read rhs
  Value* rhs_val = get_reg_val(X86::EAX);

  // compute
  Value* result = IRB->CreateSub(lhs_val, rhs_val);

  store_ZF_val(I->getOpcode(), lhs_val, rhs_val, result);
  
  Value* zf_val = get_ZF_val();

  Value* cond_val = IRB->CreateICmpEQ(zf_val, ConstantInt::getTrue(*context));
  
  std::stringstream true_bb_name;
  true_bb_name << "bb_" << (Dec->getDisassembler()->getDebugOffset(I->getDebugLoc())) << "_cmpxchg_true";
  BasicBlock* true_bb  = Dec->getOrCreateBasicBlock(true_bb_name.str(), BB->getParent());
  std::stringstream false_bb_name;
  false_bb_name << "bb_" << (Dec->getDisassembler()->getDebugOffset(I->getDebugLoc())) << "_cmpxchg_false";
  BasicBlock* false_bb  = Dec->getOrCreateBasicBlock(false_bb_name.str(), BB->getParent());

  std::stringstream next_bb_name;
  next_bb_name << "bb_" << (Dec->getDisassembler()->getDebugOffset(I->getDebugLoc()) + I->getDesc().getSize());
  BasicBlock* next_bb  = Dec->getOrCreateBasicBlock(next_bb_name.str(), BB->getParent());
  IRB->CreateCondBr(cond_val, true_bb, false_bb);
  
  IRB->SetInsertPoint(true_bb);
  Value* reg_val = get_reg_val(reg_opr.getReg());
  Value* true_result = reg_val;
  store_mem_val(base_opr.getReg(), scale_opr.getImm(), idx_opr.getReg(), off_opr.getImm(), seg_opr.getReg(), true_result);
  IRB->CreateBr(next_bb);
  
  IRB->SetInsertPoint(false_bb);
  Value* false_result = lhs_val;
  store_reg_val(X86::EAX, false_result);
  IRB->CreateBr(next_bb);
}