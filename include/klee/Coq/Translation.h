#ifndef KLEE_TRANSLATION_H
#define KLEE_TRANSLATION_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include "klee/Coq/CoqLanguage.h"

namespace klee {

class ModuleTranslator {

public:

    llvm::Module &m;

    ModuleTranslator(llvm::Module &m);

    ref<CoqExpr> translate();

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

    ref<CoqExpr> translateType(llvm::Type *t);

    ref<CoqExpr> createName(const std::string &name);

    ~ModuleTranslator();
};

}

#endif
