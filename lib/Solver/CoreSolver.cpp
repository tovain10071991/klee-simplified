//===-- CoreSolver.cpp ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/CommandLine.h"
#include "klee/Solver.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

#ifdef ENABLE_METASMT

#include <metaSMT/DirectSolver_Context.hpp>
#include <metaSMT/backend/Z3_Backend.hpp>
#include <metaSMT/backend/Boolector.hpp>

#define Expr VCExpr
#define Type VCType
#define STP STP_Backend
#include <metaSMT/backend/STP.hpp>
#undef Expr
#undef Type
#undef STP

using namespace klee;
using namespace metaSMT;
using namespace metaSMT::solver;

static klee::Solver *handleMetaSMT() {
  Solver *coreSolver = NULL;
  std::string backend;
  switch (MetaSMTBackend) {
  case METASMT_BACKEND_STP:
    backend = "STP";
    coreSolver = new MetaSMTSolver<DirectSolver_Context<STP_Backend> >(
        UseForkedCoreSolver, CoreSolverOptimizeDivides);
    break;
  case METASMT_BACKEND_Z3:
    backend = "Z3";
    coreSolver = new MetaSMTSolver<DirectSolver_Context<Z3_Backend> >(
        UseForkedCoreSolver, CoreSolverOptimizeDivides);
    break;
  case METASMT_BACKEND_BOOLECTOR:
    backend = "Boolector";
    coreSolver = new MetaSMTSolver<DirectSolver_Context<Boolector> >(
        UseForkedCoreSolver, CoreSolverOptimizeDivides);
    break;
  default:
    llvm_unreachable("Unrecognised metasmt backend");
    break;
  };
  llvm::errs() << "Starting MetaSMTSolver(" << backend << ") ...\n";
  return coreSolver;
}
#endif /* ENABLE_METASMT */

namespace klee {

Solver *createCoreSolver(CoreSolverType cst) {
  assert(cst == STP_SOLVER);
  llvm::errs() << "Using STP solver backend\n";
  return new STPSolver(UseForkedCoreSolver, CoreSolverOptimizeDivides);
}
}
