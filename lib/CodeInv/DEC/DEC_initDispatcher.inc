visitDispatchers[X86::DEC16r] = &IREmitter::visitDEC16r;
visitDispatchers[X86::DEC8r] = &IREmitter::visitDEC8r;
// visitDispatchers[X86::DEC16m] = &IREmitter::visitDEC16m;
// visitDispatchers[X86::DEC32m] = &IREmitter::visitDEC32m;
// visitDispatchers[X86::DEC8m] = &IREmitter::visitDEC8m;
visitDispatchers[X86::DEC32r] = &IREmitter::visitDEC32r;
// visitDispatchers[X86::DEC64_16r] = &IREmitter::visitDEC64_16r;
// visitDispatchers[X86::DEC64_32r] = &IREmitter::visitDEC64_32r;
visitDispatchers[X86::DEC64r] = &IREmitter::visitDEC64r;