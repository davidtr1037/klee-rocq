#ifndef KLEE_TRANSLATION_H
#define KLEE_TRANSLATION_H

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include "klee/Coq/CoqLanguage.h"

#include <map>

namespace klee {

class ModuleTranslator {

private:

  std::map<llvm::Instruction*, uint64_t> instIDs;

public:

  llvm::Module &m;

  std::map<llvm::Instruction*, ref<CoqExpr>> instCache;

  std::vector<ref<CoqExpr>> instDefs;

  std::map<llvm::BasicBlock*, ref<CoqExpr>> bbCache;

  std::vector<ref<CoqExpr>> bbDefs;

  std::map<llvm::Function*, ref<CoqExpr>> declCache;

  std::vector<ref<CoqExpr>> declDefs;

  std::map<llvm::Function*, ref<CoqExpr>> functionCache;

  std::vector<ref<CoqExpr>> functionDefs;

  ModuleTranslator(llvm::Module &m);

  ref<CoqExpr> translateModule();

  ref<CoqExpr> translateFunctionCached(llvm::Function &f);

  ref<CoqExpr> translateFunction(llvm::Function &f);

  ref<CoqExpr> translateDeclCached(llvm::Function &f);

  ref<CoqExpr> translateDecl(llvm::Function &f);

  ref<CoqExpr> createFunctionType(llvm::Function &f);

  ref<CoqExpr> createParamAttrs(llvm::Function &f);

  ref<CoqExpr> createAttrs(llvm::Function &f);

  ref<CoqExpr> createAnnotations(llvm::Function &f);

  ref<CoqExpr> createArgs(llvm::Function &f);

  ref<CoqExpr> createCFG(llvm::Function &f);

  ref<CoqExpr> translateBasicBlockCached(llvm::BasicBlock &bb);

  ref<CoqExpr> translateBasicBlock(llvm::BasicBlock &bb);

  ref<CoqExpr> translateInstCached(llvm::Instruction &inst);

  ref<CoqExpr> translateInst(llvm::Instruction &inst);

  ref<CoqExpr> translateBinaryOperator(llvm::BinaryOperator *inst);

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

  bool shouldIgnoreCall(llvm::CallInst *inst);

  std::vector<ref<CoqExpr>> translateArgs(llvm::CallInst *inst);

  ref<CoqExpr> translateReturnInst(llvm::ReturnInst *inst);

  ref<CoqExpr> translateUnreachableInst(llvm::UnreachableInst *inst);

  ref<CoqExpr> createCMDInst(uint64_t id, ref<CoqExpr> e);

  ref<CoqExpr> createCMDTerm(uint64_t id, ref<CoqExpr> e);

  ref<CoqExpr> createCMDPhi(uint64_t id, ref<CoqExpr> e);

  ref<CoqExpr> translateValue(llvm::Value *v);

  ref<CoqExpr> translateType(llvm::Type *t);

  ref<CoqExpr> createLocalID(const std::string &name);

  ref<CoqExpr> createGlobalID(const std::string &name);

  ref<CoqExpr> createName(const std::string &name);

  bool isSupportedFunction(llvm::Function *f);

  bool isSupportedInst(llvm::Instruction &inst);

  bool isSupportedType(llvm::Type *t);

  uint64_t getInstID(llvm::Instruction *inst);

  ~ModuleTranslator();
};

}

#endif
