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
#include <llvm/IR/InstIterator.h>

#include "Dataflow.h"
#include <map>
#include <set>
#include <vector>
using namespace llvm;
#define min(a,b) (((a)->first->getDebugLoc().getLine()<(b)->first->getDebugLoc().getLine())?(a):(b))

//using FuntionSet = std::vector<Function *>;
using ValueSet = std::set<Value *>;
using LivenessToMap = std::map<Value *, ValueSet>;
//bool debug=false;
struct LivenessInfo {
    LivenessToMap LiveVars_map;
    LivenessToMap LiveVars_feild_map;
    LivenessInfo() : LiveVars_map(),LiveVars_feild_map() {}
    LivenessInfo(const LivenessInfo &info) : LiveVars_map(info.LiveVars_map),LiveVars_feild_map(info.LiveVars_feild_map) {}
  
   bool operator == (const LivenessInfo & info) const {
       return LiveVars_map == info.LiveVars_map && LiveVars_feild_map==info.LiveVars_feild_map;
   }
   bool operator != (const LivenessInfo & info) const {
       return LiveVars_map != info.LiveVars_map || LiveVars_feild_map != info.LiveVars_feild_map;
   }
   LivenessInfo &operator=(const LivenessInfo &info)
   {
        LiveVars_map = info.LiveVars_map;
        LiveVars_feild_map = info.LiveVars_feild_map;
        return *this;
   }
};

inline raw_ostream &operator<<(raw_ostream &out, const LivenessToMap &v)
{
    out << "    { ";
    for (auto i = v.begin(), e = v.end(); i != e; ++i)
    {
        if (isa<Function> (i->first))
            out << "[value]" << i->first->getName() << " " << "----->";
        else
        out << "[value]" << *i->first << " " << " -----> ";
        for (auto ii = i->second.begin(), ie = i->second.end(); ii != ie; ++ii)
        {
            errs() << "[valueSet]"; 
            if (ii != i->second.begin())
            {
                errs() << ", ";
            }
            if (isa<Function>(*(ii)))
                out << (*ii)->getName() << " ";
            else
            out << *(*ii) << " " ;
        }
        out << "  \n\t\t  ";
    }
    out << "}\n";
    return out;
}
	
class LivenessVisitor : public DataflowVisitor<struct LivenessInfo> {
public:
    std::map<CallInst *, std::set<Function *>> call_func_result;
    std::set<Function *> fn_worklist;
   LivenessVisitor() : call_func_result(), fn_worklist() {}
   void merge(LivenessInfo * dest, const LivenessInfo & src) override {
        for(auto ii = src.LiveVars_map.begin(),ie = src.LiveVars_map.end();ii!=ie;ii++){
            dest->LiveVars_map[ii->first].insert(ii->second.begin(),ii->second.end());
        }
        for(auto ii=src.LiveVars_feild_map.begin(),ie=src.LiveVars_feild_map.end();ii!=ie;ii++){
            dest->LiveVars_feild_map[ii->first].insert(ii->second.begin(),ii->second.end());
        }
   }


    std::set<Function *> getCallees(Value *value, LivenessInfo *dfval)
    {
        std::set<Function *> result;
        if (auto *func = dyn_cast<Function>(value))
        {
            result.insert(func);
            return result;
        }

        ValueSet value_worklist;
        if (dfval->LiveVars_map.find(value) != dfval->LiveVars_map.end())
        {
            value_worklist.insert(dfval->LiveVars_map[value].begin(), dfval->LiveVars_map[value].end());
        }
        for (Value * v; !value_worklist.empty(); value_worklist.erase(v))
        {
            v = *value_worklist.begin();
            //errs() << dfval->LiveVars_map[v].size() << "\n";
            isa<Function>(*v) ? (void)result.insert((Function *)v) 
                : value_worklist.insert(dfval->LiveVars_map[v].begin(), dfval->LiveVars_map[v].end());
        }

        return result;
    }

    void HandleDataflow(std::map<Value *, Value *> ValueToArg_map, LivenessInfo &tmpdfval){
        for (auto bi = tmpdfval.LiveVars_map.begin(), be = tmpdfval.LiveVars_map.end(); bi != be; bi++)
        {
            for (auto argi = ValueToArg_map.begin(), arge = ValueToArg_map.end(); argi != arge; argi++)
            {
                if (bi->second.count(argi->first) && !isa<Function>(argi->first))
                {
                    // 函数
                    bi->second.erase(argi->first);
                    bi->second.insert(argi->second);
                }
            }
        }

        // replace LiveVars_feild_map
        for (auto bi = tmpdfval.LiveVars_feild_map.begin(), be = tmpdfval.LiveVars_feild_map.end(); bi != be; bi++)
        {
            for (auto argi = ValueToArg_map.begin(), arge = ValueToArg_map.end(); argi != arge; argi++)
            {
                if (bi->second.count(argi->first) && !isa<Function>(argi->first))
                {
                    bi->second.erase(argi->first);
                    bi->second.insert(argi->second);
                }
            }
        }

        for (auto argi = ValueToArg_map.begin(), arge = ValueToArg_map.end(); argi != arge; argi++)
        {
            if (tmpdfval.LiveVars_map.count(argi->first))
            {
                //errs() << "guess who i am ^_^\n\n\n\n\n\n";
                ValueSet values = tmpdfval.LiveVars_map[argi->first];
                tmpdfval.LiveVars_map.erase(argi->first);
                tmpdfval.LiveVars_map[argi->second].insert(values.begin(), values.end());
            }

            if (tmpdfval.LiveVars_feild_map.count(argi->first))
            {
                ValueSet values = tmpdfval.LiveVars_feild_map[argi->first];
                tmpdfval.LiveVars_feild_map.erase(argi->first);
                tmpdfval.LiveVars_feild_map[argi->second].insert(values.begin(), values.end());
            }
        }
    }

    void GetValueToArg_map(std::map<Value *, Value *> &ValueToArg_map, CallInst *callInst,
            Function * callee, bool reverse){
        for (int argi = 0, arge = callInst->getNumArgOperands(); argi < arge; argi++)
        {
            Value *caller_arg = callInst->getArgOperand(argi);
            if (caller_arg->getType()->isPointerTy())
            {
                // only consider pointer
                Argument *callee_arg = callee->arg_begin() + argi;
                reverse ? (void)ValueToArg_map.insert(std::make_pair(caller_arg, callee_arg))
                        : (void)ValueToArg_map.insert(std::make_pair(callee_arg, caller_arg));
            }
        }
    }

    void HandleCallInst(CallInst *callInst, DataflowResult<LivenessInfo>::Type *result)
    {
        //errs() << *callInst;
        LivenessInfo dfval = (*result)[callInst].first;
        std::set<Function *> callees;
        //callee被调用者，caller调用者
        callees = getCallees(callInst->getCalledValue(), &dfval);
        call_func_result[callInst].clear();
        call_func_result[callInst].insert(callees.begin(), callees.end());

        /// Return the function called, or null if this is an
        /// indirect function invocation.
        if (callInst->getCalledFunction() && callInst->getCalledFunction()->isDeclaration())
        {
            (*result)[callInst].second = (*result)[callInst].first;
            return;
        }
        for (auto calleei = callees.begin(), calleee = callees.end(); calleei != calleee; calleei++)
        {
            Function *callee = *calleei;
            // 声明不算
            if (callee->isDeclaration())
            {
                continue;
            }
            std::map<Value *, Value *> ValueToArg_map;

            GetValueToArg_map(ValueToArg_map, callInst, callee, true);
            if(ValueToArg_map.empty()){
                //errs() << callInst->getDebugLoc().getLine() << " ValueToArg_map is empty\n";
                LivenessInfo &tmpdfval = (*result)[callInst].second;
                merge(&tmpdfval, (*result)[callInst].first);
                continue;
            }

            // replace LiveVars_map
            LivenessInfo tmpfdval = (*result)[callInst].first;
            LivenessInfo &callee_dfval_in = (*result)[&*inst_begin(callee)].first;
            LivenessInfo old_callee_dfval_in = callee_dfval_in;

            HandleDataflow(ValueToArg_map, tmpfdval);
            merge(&callee_dfval_in, tmpfdval);
            if (old_callee_dfval_in.LiveVars_map != callee_dfval_in.LiveVars_map 
                    ||old_callee_dfval_in.LiveVars_feild_map != callee_dfval_in.LiveVars_feild_map)
            {
                //errs() << "call inst insert a function to fn_worklist: " << callee->getName() << "\n";
                fn_worklist.insert(callee);
            }
        }
    }

    void HandleLoadStoreInst(Instruction *inst, DataflowResult<LivenessInfo>::Type *result)
    {
        char type;
        type = isa<LoadInst>(inst) ? 'L' : 'S';
        LivenessInfo dfval = (*result)[inst].first;
        ValueSet values;

        switch (type)
        {
            case 'L':
                dfval.LiveVars_map[inst].clear();
                break;
            case 'S':
                if (dfval.LiveVars_map[((StoreInst *)inst)->getValueOperand()].empty())
                {
                    values.insert(((StoreInst *)inst)->getValueOperand());
                }
                else
                {
                    ValueSet &tmp = dfval.LiveVars_map[((StoreInst *)inst)->getValueOperand()];
                    values.insert(tmp.begin(), tmp.end());
                }
                break;
        }
        if (auto *getElementPtrInst = dyn_cast<GetElementPtrInst>(getLoadStorePointerOperand(inst)))
        {
            Value *pointerOperand = getElementPtrInst->getPointerOperand();
            if (dfval.LiveVars_map[pointerOperand].empty())
            {
                switch (type){
                    case 'S':
                        dfval.LiveVars_feild_map[pointerOperand].clear();
                        dfval.LiveVars_feild_map[pointerOperand].insert(values.begin(), values.end());
                        break;
                    case 'L':
                        ValueSet &tmp = dfval.LiveVars_feild_map[pointerOperand];
                        dfval.LiveVars_map[inst].insert(tmp.begin(), tmp.end());
                        break;
               }
            }
            else
            {
                ValueSet &tmp = dfval.LiveVars_map[pointerOperand];
                for (auto tmpi = tmp.begin(), tmpe = tmp.end(); tmpi != tmpe; tmpi++)
                {
                    Value *v = *tmpi;
                    switch (type){
                        case 'S' :
                            dfval.LiveVars_feild_map[v].clear();
                            dfval.LiveVars_feild_map[v].insert(values.begin(), values.end());
                            break;
                        case 'L' :
                            ValueSet &tmp = dfval.LiveVars_feild_map[v];
                            dfval.LiveVars_map[inst].insert(tmp.begin(), tmp.end());
                            break;
                    }
                }
            }
        }
        else
        {
            //ptr
            auto * pointerOperand = getLoadStorePointerOperand(inst);
            int flag = 0;
            Value * bitcastInst; 
            Value * loadInstPointerOperand;
            //errs() << "pointerOperand : " << *pointerOperand << "\n";
            switch (type){
                case 'S': 
                    dfval.LiveVars_map[pointerOperand].clear();
                    dfval.LiveVars_map[pointerOperand].insert(values.begin(), values.end());
                    flag = 0;
                    if (isa<LoadInst>(pointerOperand)){
                        loadInstPointerOperand = getLoadStorePointerOperand(pointerOperand);
                        //errs() << "loadInstPointerOperand : " << *loadInstPointerOperand << "\n";
                        //errs() << dfval.LiveVars_map;
                        if (isa<AllocaInst>(loadInstPointerOperand)){
                            //errs() << "li pu\n";
                            for (auto ii = dfval.LiveVars_map[loadInstPointerOperand].begin(),
                                    ie = dfval.LiveVars_map[loadInstPointerOperand].end();
                                    ii != ie;
                                    ii++){
                                //errs() << "this line must have been executed?\n ";
                                if (isa<BitCastInst> (*ii)){
                                    flag = 1;
                                    //errs() << "this line has not been executed?\n ";
                                    bitcastInst = *ii;
                                }
                            }
                        }
                    }
                    if (flag == 1){
                        dfval.LiveVars_feild_map[loadInstPointerOperand].clear();
                        dfval.LiveVars_feild_map[loadInstPointerOperand].insert(values.begin(), values.end());
                   }
                   break;
                case 'L':
                    ValueSet tmp = dfval.LiveVars_map[pointerOperand];
                    flag = 0;
                    if (isa<AllocaInst>(pointerOperand)){
                        for (auto ii = dfval.LiveVars_map[pointerOperand].begin(),
                                ie = dfval.LiveVars_map[pointerOperand].end();
                                ii != ie;
                                ii++){
                            if (isa<BitCastInst> (*ii)){
                                flag = 1;
                                bitcastInst = *ii;
                            }
                        }
                    }
                    tmp = dfval.LiveVars_feild_map[pointerOperand];
                    //size = dfval.LiveVars_map[pointerOperand].size();
                    if (flag == 1 && !tmp.empty()){
                        //if (size >= 3) dfval.LiveVars_map[pointerOperand].clear();
                        //errs() << "\nflag = 1 and tmp is not empty\n";
                        dfval.LiveVars_map[inst].insert(tmp.begin(), tmp.end());
                   }else
                   {
                       tmp = dfval.LiveVars_map[pointerOperand];
                       dfval.LiveVars_map[inst].insert(tmp.begin(), tmp.end());
                   }
                   //dfval.LiveVars_map[pointerOperand].insert(inst);
                   break;
            }
        }
        (*result)[inst].second = dfval;
    }

    void HandleReturnInst(ReturnInst *returnInst, DataflowResult<LivenessInfo>::Type *result)
    {
        LivenessInfo dfval = (*result)[returnInst].first;
        Function *callee = returnInst->getFunction();
        // 前向找到哪个函数调用了return的函数

        for (auto funci = call_func_result.begin(), funce = call_func_result.end(); funci != funce; funci++)
        {
            if (funci->second.count(callee))
            { //funci call callee
                Function *caller = funci->first->getFunction();
                std::map<Value *, Value *> ValueToArg_map;
                CallInst *callInst = funci->first;

                GetValueToArg_map(ValueToArg_map, callInst, callee, false);
                LivenessInfo tmpdfval = (*result)[returnInst].first;
                LivenessInfo &caller_dfval_out = (*result)[callInst].second;
                LivenessInfo old_caller_dfval_out = caller_dfval_out;

                if (returnInst->getReturnValue() &&
                    returnInst->getReturnValue()->getType()->isPointerTy())
                {
                    ValueSet values = tmpdfval.LiveVars_map[returnInst->getReturnValue()];
                    tmpdfval.LiveVars_map.erase(returnInst->getReturnValue());
                    tmpdfval.LiveVars_map[callInst].insert(values.begin(), values.end());
                }
                HandleDataflow(ValueToArg_map, tmpdfval);

                merge(&caller_dfval_out, tmpdfval);
                (*result)[callInst].second = caller_dfval_out;
                if (caller_dfval_out != old_caller_dfval_out)
                {
                    fn_worklist.insert(caller);
                }
            }
        }
        (*result)[returnInst].second = dfval;
    }

    void compDFVal(Instruction *inst, DataflowResult<LivenessInfo>::Type *result) override{
        if (debug){
            errs() << *inst << "\n\n";
            errs() << "\t\tdfval_In: " << (*result)[inst].first.LiveVars_map;
        }
        if (isa<IntrinsicInst>(inst))
        {
            (*result)[inst].second = (*result)[inst].first;
            return;
        }
        if (auto callInst = dyn_cast<CallInst>(inst))
        {
            HandleCallInst(callInst, result);
        }
        else if (isa<StoreInst>(inst) || isa<LoadInst>(inst))
        {
            HandleLoadStoreInst(inst, result);
        }
        else if (auto returnInst = dyn_cast<ReturnInst>(inst))
        {
            HandleReturnInst(returnInst, result);
        }
        else
        {
            // out equal in
            (*result)[inst].second = (*result)[inst].first;
        }
        if (debug){
            errs() << "\t\tdfval_Out: " << (*result)[inst].second.LiveVars_map << "\n";
        }
       return;
   }
    void printCallFuncResult()
    {
        while(!call_func_result.empty())
        {   
            auto begin = call_func_result.begin(), end = call_func_result.end(), ii = begin;
            while (begin != end)
            {
                ii = ii->first->getDebugLoc().getLine()
                    < begin->first->getDebugLoc().getLine() 
                    ? ii 
                    : begin; //min(ii, begin);
                begin++;            
            }
            errs() << ii->first->getDebugLoc().getLine() << " : ";
            for (auto fi = ii->second.begin(), fe = ii->second.end(); fi != fe; fi++)
            {
                if(fi!=ii->second.begin()){
                    errs()<<", ";
                }
                errs()<<(*fi)->getName();
            }
            errs() << "\n";
            call_func_result.erase(ii);
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



