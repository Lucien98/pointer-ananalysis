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
    std::map<CallInst *, std::set<Function *>> call_func_result;
public:
   LivenessVisitor() : call_func_result() {}
   void merge(LivenessInfo * dest, const LivenessInfo & src) override {
        for(auto ii = src.LiveVars_map.begin(),ie = src.LiveVars_map.end();ii!=ie;ii++){
            dest->LiveVars_map[ii->first].insert(ii->second.begin(),ii->second.end());
        }
        for(auto ii=src.LiveVars_feild_map.begin(),ie=src.LiveVars_feild_map.end();ii!=ie;ii++){
            dest->LiveVars_feild_map[ii->first].insert(ii->second.begin(),ii->second.end());
        }
   }

    void HandlePHINode(PHINode *phiNode, DataflowResult<LivenessInfo>::Type *result)
    {
        LivenessInfo dfval = (*result)[phiNode].first;
        dfval.LiveVars_map[phiNode].clear();
        for (Value *value : phiNode->incoming_values())
        {
        }
    }

    void HandleCallInst(CallInst *callInst, DataflowResult<LivenessInfo>::Type *result)
    {
        LivenessInfo dfval = (*result)[callInst].first;
        std::set<Function *> callees;
    }

   void compDFVal(Instruction *inst, DataflowResult<LivenessInfo>::Type *result) override{
        if (isa<DbgInfoIntrinsic>(inst))
            return;
        if (auto phiNode = dyn_cast<PHINode>(inst))
        {
            errs() << "I am in PHINode"
                   << "\n";
            HandlePHINode(phiNode, result);
        }
        else if (auto callInst = dyn_cast<CallInst>(inst))
        {
            errs() << "I am in CallInst"
                   << "\n";
            HandleCallInst(callInst, result);
        }

       return;
   }
    void printCallFuncResult()
    {
        for (auto ii = call_func_result.begin(), ie = call_func_result.end(); ii != ie; ii++)
        {
            errs() << ii->first->getDebugLoc().getLine() << " : ";
            for (auto fi = ii->second.begin(), fe = ii->second.end(); fi != fe; fi++)
            {
                if(fi!=ii->second.begin()){
                    errs()<<", ";
                }
                errs()<<(*fi)->getName();
            }
            errs() << "\n";
        }
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



