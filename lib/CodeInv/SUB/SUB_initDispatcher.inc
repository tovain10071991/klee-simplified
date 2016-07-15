visitDispatchers[X86::SUB64i32] = &IREmitter::visitSUB64i32;
visitDispatchers[X86::SUB32i32] = &IREmitter::visitSUB32i32;
visitDispatchers[X86::SUB64ri32] = &IREmitter::visitSUB64ri32;
visitDispatchers[X86::SUB64ri8] = &IREmitter::visitSUB64ri8;
visitDispatchers[X86::SUB64rr] = &IREmitter::visitSUB64r;
visitDispatchers[X86::SUB32rr] = &IREmitter::visitSUB32r;