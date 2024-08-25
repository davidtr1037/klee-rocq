#ifndef KLEE_TRANSLATION_H
#define KLEE_TRANSLATION_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include "klee/Coq/CoqLanguage.h"

namespace klee {

class ModuleTranslator {

public:

    llvm::Module &m;

    ModuleTranslator(llvm::Module &m);

    ref<CoqExpr> translateModule();

    ref<CoqExpr> translateFunction(llvm::Function &f);

    ref<CoqExpr> translateDecl(llvm::Function &f);

    ref<CoqExpr> createFunctionType(llvm::Function &f);

    ref<CoqExpr> createParamAttrs(llvm::Function &f);

    ref<CoqExpr> createAttrs(llvm::Function &f);

    ref<CoqExpr> createAnnotations(llvm::Function &f);

    ref<CoqExpr> createArgs(llvm::Function &f);

    ref<CoqExpr> createCFG(llvm::Function &f);

    ref<CoqExpr> translateBasicBlock(llvm::BasicBlock &bb);

    ref<CoqExpr> translateInst(llvm::Instruction &inst);

    ref<CoqExpr> translateBinaryOperator(llvm::Instruction &inst);

    ref<CoqExpr> createBinOp(ref<CoqExpr> target,
                             ref<CoqExpr> ibinop,
                             ref<CoqExpr> arg_type,
                             ref<CoqExpr> arg1,
                             ref<CoqExpr> arg2);

    ref<CoqExpr> translateCmpInst(llvm::CmpInst *inst);

    ref<CoqExpr> createCmpOp(ref<CoqExpr> target,
                             ref<CoqExpr> icmp,
                             ref<CoqExpr> arg_type,
                             ref<CoqExpr> arg1,
                             ref<CoqExpr> arg2);

    ref<CoqExpr> translateBranchInst(llvm::BranchInst *inst);

    ref<CoqExpr> translatePHINode(llvm::PHINode *inst);

    ref<CoqExpr> translateCallInst(llvm::CallInst *inst);

    ref<CoqExpr> translateReturnInst(llvm::ReturnInst *inst);

    ref<CoqExpr> createCMDInst(unsigned id, ref<CoqExpr> e);

    ref<CoqExpr> createCMDTerm(unsigned id, ref<CoqExpr> e);

    ref<CoqExpr> createCMDPhi(unsigned id, ref<CoqExpr> e);

    ref<CoqExpr> translateValue(llvm::Value *v);

    ref<CoqExpr> translateType(llvm::Type *t);

    ref<CoqExpr> createLocalID(const std::string &name);

    ref<CoqExpr> createGlobalID(const std::string &name);

    ref<CoqExpr> createName(const std::string &name);

    ~ModuleTranslator();
};

}

#endif
