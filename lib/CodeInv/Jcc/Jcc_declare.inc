void Jcc(BasicBlock *BB, MachineInstr* I, Value* cond_val, int64_t off);
declare_visit(JA_1);
declare_visit(JAE_1);
declare_visit(JBE_1);
declare_visit(JB_1);
// declare_visit(JCXZ);
declare_visit(JE_1);
declare_visit(JG_1);
declare_visit(JGE_1);
declare_visit(JL_1);
declare_visit(JLE_1);
declare_visit(JNE_1);
declare_visit(JNO_1);
declare_visit(JNP_1);
declare_visit(JNS_1);
declare_visit(JO_1);
declare_visit(JP_1);
// declare_visit(JRCXZ);
declare_visit(JS_1);