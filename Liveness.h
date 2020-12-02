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

using ValueSet = std::set<Value *>;
using LivenessToMap = std::map<Value *, ValueSet>;
struct LivenessInfo {
    LivenessToMap LiveVars_Map[2]; //0 for average variable; 1 for structure variable
    LivenessInfo() : LiveVars_Map{} {}
    LivenessInfo(const LivenessInfo &info) : LiveVars_Map{info.LiveVars_Map[0], info.LiveVars_Map[1]}{}
  
   bool operator == (const LivenessInfo & info) const {
       for (int i = 0; i < 2; i++){
           if (LiveVars_Map[i] != info.LiveVars_Map[i])
               return false;
       }
       return true;
   }
   bool operator != (const LivenessInfo & info) const {
       for (int i = 0; i < 2; i++){
           if (LiveVars_Map[i] != info.LiveVars_Map[i])
               return true;
       }
       return false;
  }
   LivenessInfo &operator=(const LivenessInfo &info)
   {
        LiveVars_Map[0] = info.LiveVars_Map[0];
        LiveVars_Map[1] = info.LiveVars_Map[1];
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
        out << "[value]" << *i->first << " (" << i->first <<")" << " -----> ";
        for (auto ii = i->second.begin(), ie = i->second.end(); ii != ie; ++ii)
        {
            if (ii != i->second.begin())
            {
                errs() << ", ";
            }
            errs() << "[valueSet]"; 
            if (isa<Function>(*(ii)))
                out << (*ii)->getName() << " ";
            else
            out << *(*ii) << " (" <<  *ii << ") " ;
        }
        out << "  \n\t\t  ";
    }
    out << "}\n";
    return out;
}
	
class LivenessVisitor : public DataflowVisitor<struct LivenessInfo> {
public:
    std::map<CallInst *, std::set<Function *>> call_func_result;
   LivenessVisitor() : call_func_result() {}
   void merge(LivenessInfo * dest, const LivenessInfo & src) override {
       for (int i = 0; i < 2; i++)
        for(auto ii = src.LiveVars_Map[i].begin(),ie = src.LiveVars_Map[i].end();ii!=ie;ii++){
            dest->LiveVars_Map[i][ii->first].insert(ii->second.begin(),ii->second.end());
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
        if (dfval->LiveVars_Map[0].find(value) != dfval->LiveVars_Map[0].end())
        {
            value_worklist.insert(dfval->LiveVars_Map[0][value].begin(), dfval->LiveVars_Map[0][value].end());
        }
        for (Value * v; !value_worklist.empty(); value_worklist.erase(v))
        {
            v = *value_worklist.begin();
            isa<Function>(*v) ? (void)result.insert((Function *)v) 
                : value_worklist.insert(dfval->LiveVars_Map[0][v].begin(), dfval->LiveVars_Map[0][v].end());
        }

        return result;
    }

    void HandleDataflow(std::map<Value *, Value *> ValueToArg_map, LivenessInfo &tmpdfval){
        for (auto bi = tmpdfval.LiveVars_Map[0].begin(), be = tmpdfval.LiveVars_Map[0].end(); bi != be; bi++)
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

        // replace LiveVars_Map[1]
        for (auto bi = tmpdfval.LiveVars_Map[1].begin(), be = tmpdfval.LiveVars_Map[1].end(); bi != be; bi++)
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
            if (tmpdfval.LiveVars_Map[0].count(argi->first))
            {
                ValueSet values = tmpdfval.LiveVars_Map[0][argi->first];
                tmpdfval.LiveVars_Map[0].erase(argi->first);
                tmpdfval.LiveVars_Map[0][argi->second].insert(values.begin(), values.end());
            }

            if (tmpdfval.LiveVars_Map[1].count(argi->first))
            {
                ValueSet values = tmpdfval.LiveVars_Map[1][argi->first];
                tmpdfval.LiveVars_Map[1].erase(argi->first);
                tmpdfval.LiveVars_Map[1][argi->second].insert(values.begin(), values.end());
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
                LivenessInfo &tmpdfval = (*result)[callInst].second;
                merge(&tmpdfval, (*result)[callInst].first);
                continue;
            }

            // replace LiveVars_Map[0]
            LivenessInfo tmpfdval = (*result)[callInst].first;
            LivenessInfo &callee_dfval_in = (*result)[&*inst_begin(callee)].first;
            LivenessInfo old_callee_dfval_in = callee_dfval_in;

            HandleDataflow(ValueToArg_map, tmpfdval);
            merge(&callee_dfval_in, tmpfdval);
            if (old_callee_dfval_in.LiveVars_Map[0] != callee_dfval_in.LiveVars_Map[0] 
                    ||old_callee_dfval_in.LiveVars_Map[1] != callee_dfval_in.LiveVars_Map[1])
            {
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
                dfval.LiveVars_Map[0][inst].clear();
                break;
            case 'S':
                if (dfval.LiveVars_Map[0][((StoreInst *)inst)->getValueOperand()].empty())
                {
                    values.insert(((StoreInst *)inst)->getValueOperand());
                }
                else
                {
                    ValueSet &tmp = dfval.LiveVars_Map[0][((StoreInst *)inst)->getValueOperand()];
                    values.insert(tmp.begin(), tmp.end());
                }
                break;
        }
        if (auto *getElementPtrInst = dyn_cast<GetElementPtrInst>(getLoadStorePointerOperand(inst)))
        {
            Value *pointerOperand = getElementPtrInst->getPointerOperand();
            if (dfval.LiveVars_Map[0][pointerOperand].empty())
            {
                switch (type){
                    case 'S':
                        dfval.LiveVars_Map[1][pointerOperand].clear();
                        dfval.LiveVars_Map[1][pointerOperand].insert(values.begin(), values.end());
                        break;
                    case 'L':
                        ValueSet &tmp = dfval.LiveVars_Map[1][pointerOperand];
                        dfval.LiveVars_Map[0][inst].insert(tmp.begin(), tmp.end());
                        break;
               }
            }
            else
            {
                ValueSet &tmp = dfval.LiveVars_Map[0][pointerOperand];
                for (auto tmpi = tmp.begin(), tmpe = tmp.end(); tmpi != tmpe; tmpi++)
                {
                    Value *v = *tmpi;
                    switch (type){
                        case 'S' :
                            dfval.LiveVars_Map[1][v].clear();
                            dfval.LiveVars_Map[1][v].insert(values.begin(), values.end());
                            break;
                        case 'L' :
                            ValueSet &tmp = dfval.LiveVars_Map[1][v];
                            dfval.LiveVars_Map[0][inst].insert(tmp.begin(), tmp.end());
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
            switch (type){
                case 'S': 
                    dfval.LiveVars_Map[0][pointerOperand].clear();
                    dfval.LiveVars_Map[0][pointerOperand].insert(values.begin(), values.end());
                    flag = 0;
                    if (isa<LoadInst>(pointerOperand)){
                        loadInstPointerOperand = getLoadStorePointerOperand(pointerOperand);
                        if (isa<AllocaInst>(loadInstPointerOperand)){
                            for (auto ii = dfval.LiveVars_Map[0][loadInstPointerOperand].begin(),
                                    ie = dfval.LiveVars_Map[0][loadInstPointerOperand].end();
                                    ii != ie;
                                    ii++){
                                if (isa<BitCastInst> (*ii) || isa<Argument> (*ii)){
                                    flag = 1;
                                    bitcastInst = *ii;
                                }
                            }
                        }
                    }
                    /*  %9 = load i32 (i32, i32)**, i32 (i32, i32)*** %3, align 8, !dbg !26
                     *  store i32 (i32, i32)* @plus, i32 (i32, i32)** %9, align 8, !dbg !28
                     *  %10 = load i32 (i32, i32)**, i32 (i32, i32)*** %3, align 8, !dbg !29
                     *  %11 = load i32 (i32, i32)*, i32 (i32, i32)** %10, align 8, !dbg !30
                     *  handle the alias of %3: %9, %10 is the alias of %3, when store plus to %9 
                     *  (actually it stores plus to %3), we store it to the LiveVars_field_map[%3]; 
                     *  when we want to load the value of %3 to %10 , we go to the LiveVars_field_map
                     *  to get the value of %3
                     * */
                    if (flag == 1){
                        dfval.LiveVars_Map[1][loadInstPointerOperand].clear();
                        dfval.LiveVars_Map[1][loadInstPointerOperand].insert(values.begin(), values.end());
                   }
                   break;
                case 'L':
                    ValueSet tmp = dfval.LiveVars_Map[0][pointerOperand];
                    flag = 0;
                    if (isa<AllocaInst>(pointerOperand)){
                        for (auto ii = dfval.LiveVars_Map[0][pointerOperand].begin(),
                                ie = dfval.LiveVars_Map[0][pointerOperand].end();
                                ii != ie;
                                ii++){
                            if (isa<BitCastInst> (*ii)|| isa<Argument> (*ii)){
                                flag = 1;
                                bitcastInst = *ii;
                            }
                        }
                    }
                    tmp = dfval.LiveVars_Map[1][pointerOperand];
                    if (flag == 1 && !tmp.empty()){
                        dfval.LiveVars_Map[0][inst].insert(tmp.begin(), tmp.end());
                   }else
                   {
                       tmp = dfval.LiveVars_Map[0][pointerOperand];
                       dfval.LiveVars_Map[0][inst].insert(tmp.begin(), tmp.end());
                   }
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
                    ValueSet values = tmpdfval.LiveVars_Map[0][returnInst->getReturnValue()];
                    tmpdfval.LiveVars_Map[0].erase(returnInst->getReturnValue());
                    tmpdfval.LiveVars_Map[0][callInst].insert(values.begin(), values.end());
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

    void HandleGetElementPtrInst(GetElementPtrInst *getElementPtrInst, DataflowResult<LivenessInfo>::Type *result)
    {
        LivenessInfo dfval = (*result)[getElementPtrInst].first;

        dfval.LiveVars_Map[0][getElementPtrInst].clear();

        Value *pointerOperand = getElementPtrInst->getPointerOperand();
        dfval.LiveVars_Map[0][pointerOperand].empty()
            ? (void) dfval.LiveVars_Map[0][getElementPtrInst].insert(pointerOperand)
            : (void) dfval.LiveVars_Map[0][getElementPtrInst].insert(dfval.LiveVars_Map[0][pointerOperand].begin(), dfval.LiveVars_Map[0][pointerOperand].end());

        (*result)[getElementPtrInst].second = dfval;
    }

    void compDFVal(Instruction *inst, DataflowResult<LivenessInfo>::Type *result) override{
        if (isa<IntrinsicInst>(inst))
        {
            (*result)[inst].second = (*result)[inst].first;
            //return;
        }
        else if (auto callInst = dyn_cast<CallInst>(inst))
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
        else if (auto getElementPtrInst = dyn_cast<GetElementPtrInst>(inst))
        {
            HandleGetElementPtrInst(getElementPtrInst, result);
        }
        else
        {
            // out equal in
            (*result)[inst].second = (*result)[inst].first;
        }
        if (Instruction *next_inst = inst->getNextNode()){
            (*result)[next_inst].first = (*result)[inst].second;
        }
        if (debug){
            errs() << *inst << "\n\n";
            errs() << "\t\tdfval_In: " << (*result)[inst].first.LiveVars_Map[0];
        }

        if (debug){
            errs() << "\t\tdfval_Out: " << (*result)[inst].second.LiveVars_Map[0] << "\n";
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
       return false;
   }
};



