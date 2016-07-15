#ifndef _DECOMPILER_HELPER_H_
#define _DECOMPILER_HELPER_H_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include <string>

extern std::map<uint64_t, uint64_t> addr_idx_set;
extern uint64_t idx_count;
extern std::map<llvm::Instruction*, uint64_t> inst_addr_set;
extern std::map<uint64_t, uint64_t> addr_size_set;

llvm::Module* get_module(std::string binary);
llvm::Function* get_first_func(unsigned long addr);
llvm::Function* get_first_func(std::string func_name);
llvm::Module* get_module_with_function(std::string func_name);
llvm::Module* get_module_with_function(unsigned long addr);
void decompile_inst(uint64_t addr);

#endif