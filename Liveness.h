//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
#include <map>
#include <set>
#include <vector>
using namespace llvm;

//using FuntionSet = std::vector<Function *>;
using ValueSet = std::set<Value *>;
using LivenessToMap = std::map<Value *, ValueSet>;

struct LivenessInfo {
    LivenessToMap LiveVars_map;
    LivenessToMap LiveVars_feild_map;
    LivenessInfo() : LiveVars_map(),LiveVars_feild_map() {}
    LivenessInfo(const LivenessInfo &info) : LiveVars_map(info.LiveVars_map),LiveVars_feild_map(info.LiveVars_feild_map) {}
  
   bool operator == (const LivenessInfo & info) const {
       return LiveVars_map == info.LiveVars_map && LiveVars_feild_map==info.LiveVars_feild_map;
   }
};

inline raw_ostream &operator<<(raw_ostream &out, const LivenessToMap &v) {
    out << "{ ";
    for (auto i = v.begin(), e = v.end(); i != e; ++i)
    {
        out << i->first->getName() << " " << i->first << " -> ";
        for (auto ii = i->second.begin(), ie = i->second.end(); ii != ie; ++ii)
        {
            if (ii != i->second.begin())
            {
                errs() << ", ";
            }
            out << (*ii)->getName() << " " << (*ii);
        }
        out << " ; ";
    }
    out << "}";
    return out;
}

	
class LivenessVisitor : public DataflowVisitor<struct LivenessInfo> {
public:
   LivenessVisitor() {}
   void merge(LivenessInfo * dest, const LivenessInfo & src) override {
        for(auto ii = src.LiveVars_map.begin(),ie = src.LiveVars_map.end();ii!=ie;ii++){
            dest->LiveVars_map[ii->first].insert(ii->second.begin(),ii->second.end());
        }
        for(auto ii=src.LiveVars_feild_map.begin(),ie=src.LiveVars_feild_map.end();ii!=ie;ii++){
            dest->LiveVars_feild_map[ii->first].insert(ii->second.begin(),ii->second.end());
        }
   }

   void compDFVal(Instruction *inst, LivenessInfo * dfval) override{
       return;
   }
};


class Liveness : public FunctionPass {
public:

   static char ID;
   Liveness() : FunctionPass(ID) {} 

   bool runOnFunction(Function &F) override {
       F.dump();
       LivenessVisitor visitor;
       DataflowResult<LivenessInfo>::Type result;
       LivenessInfo initval;
/*
       compBackwardDataflow(&F, &visitor, &result, initval);
       printDataflowResult<LivenessInfo>(errs(), result);
*/       return false;
   }
};



