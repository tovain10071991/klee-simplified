#include "IndirectInfo.pb.h"

#include <iostream>
#include <fstream>
#include <map>
#include <set>

using namespace std;
using namespace saib;

extern std::map<uint64_t, std::set<uint64_t> > indirect_call_set;

void output_indirect()
{
  IndirectBrTargetSet indirect_br_target_set;
  for(auto iter = indirect_call_set.begin(); iter != indirect_call_set.end(); ++iter)
  {
    IndirectBrTarget* indirect_br_target = indirect_br_target_set.add_indirect_info();
    indirect_br_target->set_inst_addr(iter->first);
    for(auto target_iter = iter->second.begin(); target_iter != iter->second.end(); ++target_iter)
    {
      indirect_br_target->add_inst_target(*target_iter);      
    }
    assert(indirect_br_target->IsInitialized());
  }
  assert(indirect_br_target_set.IsInitialized());
  ofstream fout("/mnt/sdb/test/protobuf_test/output");
  assert(indirect_br_target_set.SerializeToOstream(&fout));
}