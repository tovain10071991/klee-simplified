LEVEL = ../..
LIBRARYNAME = SaibHelper
include $(LEVEL)/Makefile.common

ifdef DEC_TEST
CXX.Flags += -I/home/user/Documents/llvm-3.4/tools/lldb/include/ -I/home/user/Documents/llvm-3.4/tools/clang/include/ -I/home/sky/llvm-3.4/tools/lldb/include/ -I/home/sky/llvm-3.4/tools/clang/include/ -I/home/user/Documents/libelf-0.8.13-install/include/ -I/home/user/Documents/protobuf-2.5.0-install/include/
else
CXX.Flags += -I/home/user/Documents/llvm-3.4/tools/lldb/include/ -I/home/user/Documents/llvm-3.4/tools/clang/include/ -I/home/user/Documents/libelf-0.8.13-install/include/ -I/home/user/Documents/protobuf-2.5.0-install/include/ -frtti
endif