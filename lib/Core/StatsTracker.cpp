//===-- StatsTracker.cpp --------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "StatsTracker.h"

#include "klee/ExecutionState.h"
#include "klee/Statistics.h"
#include "klee/Config/Version.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/MemoryUsage.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/SolverStats.h"

#include "CallPathManager.h"
#include "CoreStats.h"
#include "Executor.h"
#include "MemoryManager.h"
#include "UserSearcher.h"

#if LLVM_VERSION_CODE > LLVM_VERSION(3, 2)
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#else
#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/InlineAsm.h"
#include "llvm/Module.h"
#include "llvm/Type.h"
#endif
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/FileSystem.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#else
#include "llvm/IR/CallSite.h"
#include "llvm/IR/CFG.h"
#endif

#include <fstream>
#include <unistd.h>

using namespace klee;
using namespace llvm;

///

namespace {  
  cl::opt<bool>
  TrackInstructionTime("track-instruction-time",
                       cl::init(false),
		       cl::desc("Enable tracking of time for individual instructions (default=off)"));

  cl::opt<double>
  StatsWriteInterval("stats-write-interval",
                     cl::init(1.),
		     cl::desc("Approximate number of seconds between stats writes (default=1.0s)"));

  cl::opt<double>
  IStatsWriteInterval("istats-write-interval",
		      cl::init(10.),
                      cl::desc("Approximate number of seconds between istats writes (default: 10.0s)"));

  cl::opt<unsigned> IStatsWriteAfterInstructions(
      "istats-write-after-instructions", cl::init(0),
      cl::desc("Write istats after each n instructions, 0 to disable "
               "(default=0)"));

  // XXX I really would like to have dynamic rate control for something like this.
  cl::opt<double>
  UncoveredUpdateInterval("uncovered-update-interval",
                          cl::init(30.),
			  cl::desc("(default=30.0s)"));
}

///

bool StatsTracker::useStatistics() {
  return 1;
}

namespace klee {
  class WriteIStatsTimer : public Executor::Timer {
    StatsTracker *statsTracker;
    
  public:
    WriteIStatsTimer(StatsTracker *_statsTracker) : statsTracker(_statsTracker) {}
    ~WriteIStatsTimer() {}
    
    void run() { assert(0); }
  };
  
  class WriteStatsTimer : public Executor::Timer {
    StatsTracker *statsTracker;
    
  public:
    WriteStatsTimer(StatsTracker *_statsTracker) : statsTracker(_statsTracker) {}
    ~WriteStatsTimer() {}
    
    void run() { assert(0); }
  };

  class UpdateReachableTimer : public Executor::Timer {
    StatsTracker *statsTracker;
    
  public:
    UpdateReachableTimer(StatsTracker *_statsTracker) : statsTracker(_statsTracker) {}
    
    void run() { assert(0); }
  };
 
}

StatsTracker::StatsTracker(Executor &_executor, std::string _objectFilename,
                           bool _updateMinDistToUncovered)
  : executor(_executor),
    objectFilename(_objectFilename),
    startWallTime(util::getWallTime()),
    fullBranches(0),
    partialBranches(0) {
  if (!sys::path::is_absolute(objectFilename)) {
    SmallString<128> current(objectFilename);
    if(sys::fs::make_absolute(current)) {
      bool exists = false;

      error_code ec = sys::fs::exists(current.str(), exists);
      if (ec == errc::success && exists) {
        objectFilename = current.c_str();
      }
    }
  }
}

StatsTracker::~StatsTracker() {
}

void StatsTracker::done() {
}

void StatsTracker::stepInstruction(ExecutionState &es) {
}

double StatsTracker::elapsed() {
  return util::getWallTime() - startWallTime;
}