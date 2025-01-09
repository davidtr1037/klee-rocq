#ifndef KLEE_MODULETRANSLATION_H
#define KLEE_MODULETRANSLATION_H

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

  std::map<std::string, ref<CoqExpr>> nameCache;

  std::vector<ref<CoqExpr>> nameDefs;

  std::map<llvm::Instruction*, uint64_t> instIds;

  std::map<llvm::Instruction*, ref<CoqExpr>> instCache;

  std::vector<ref<CoqExpr>> instDefs;

  std::map<llvm::BasicBlock*, uint64_t> bbIds;

  std::map<llvm::BasicBlock*, ref<CoqExpr>> bbCache;

  std::vector<ref<CoqExpr>> bbDefs;

  std::map<llvm::Function*, ref<CoqExpr>> declCache;

  std::vector<ref<CoqExpr>> declDefs;

  std::map<llvm::Function*, ref<CoqExpr>> functionCache;

  std::vector<ref<CoqExpr>> functionDefs;

  ref<CoqExpr> moduleAlias;

  ref<CoqExpr> moduleDef;

  ModuleTranslator(llvm::Module &m);

  ref<CoqExpr> translateModuleCached();

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

  uint64_t getBasicBlockID(llvm::BasicBlock &inst);

  ref<CoqExpr> translateBasicBlock(llvm::BasicBlock &bb);

  ref<CoqExpr> translateInstCached(llvm::Instruction &inst);

  uint64_t getInstID(llvm::Instruction &inst);

  ref<CoqExpr> translateInst(llvm::Instruction &inst);

  ref<CoqExpr> translateBinaryOperator(llvm::BinaryOperator *inst);

  ref<CoqExpr> translateBinaryOperatorName(llvm::BinaryOperator *inst);

  ref<CoqExpr> translateBinaryOperatorOpcode(llvm::BinaryOperator *inst);

  ref<CoqExpr> translateBinaryOperatorExpr(llvm::BinaryOperator *inst);

  ref<CoqExpr> translateCmpInst(llvm::CmpInst *inst);

  ref<CoqExpr> translateCmpInstName(llvm::CmpInst *inst);

  ref<CoqExpr> translateCmpInstPredicate(llvm::CmpInst *inst);

  ref<CoqExpr> translateCmpInstExpr(llvm::CmpInst *inst);

  ref<CoqExpr> translateCastInst(llvm::CastInst *inst);

  ref<CoqExpr> translateCastInstName(llvm::CastInst *inst);

  ref<CoqExpr> translateCastInstOpcode(llvm::CastInst *inst);

  ref<CoqExpr> translateCastInstExpr(llvm::CastInst *inst);

  ref<CoqExpr> translateSelectInst(llvm::SelectInst *inst);

  ref<CoqExpr> translateSelectInstName(llvm::SelectInst *inst);

  ref<CoqExpr> translateSelectInstExpr(llvm::SelectInst *inst);

  ref<CoqExpr> translateBranchInst(llvm::BranchInst *inst);

  ref<CoqExpr> translateBranchInstExpr(llvm::BranchInst *inst);

  ref<CoqExpr> translateBranchInstBid(llvm::BranchInst *inst, unsigned i);

  ref<CoqExpr> translatePHINode(llvm::PHINode *inst);

  ref<CoqExpr> translatePHINodeName(llvm::PHINode *inst);

  ref<CoqExpr> translatePHINodeType(llvm::PHINode *inst);

  ref<CoqExpr> translatePHINodeArgs(llvm::PHINode *inst);

  ref<CoqExpr> translateCallInst(llvm::CallInst *inst);

  bool shouldIgnoreCall(llvm::CallInst *inst);

  std::vector<ref<CoqExpr>> translateArgs(llvm::CallInst *inst);

  ref<CoqExpr> translateReturnInst(llvm::ReturnInst *inst);

  ref<CoqExpr> translateReturnInstType(llvm::ReturnInst *inst);

  ref<CoqExpr> translateReturnInstExpr(llvm::ReturnInst *inst);

  ref<CoqExpr> translateUnreachableInst(llvm::UnreachableInst *inst);

  ref<CoqExpr> createCMDInst(uint64_t id, ref<CoqExpr> e);

  ref<CoqExpr> createCMDTerm(uint64_t id, ref<CoqExpr> e);

  ref<CoqExpr> createCMDPhi(uint64_t id, ref<CoqExpr> e);

  ref<CoqExpr> createInstrOp(ref<CoqExpr> target, ref<CoqExpr> expr);

  ref<CoqExpr> translateValue(llvm::Value *v);

  ref<CoqExpr> translateType(llvm::Type *t);

  ref<CoqExpr> createTypeI(uint64_t width);

  ref<CoqExpr> createLocalID(const std::string &name);

  ref<CoqExpr> createGlobalID(const std::string &name);

  ref<CoqExpr> createName(const std::string &name);

  bool isSupportedFunction(llvm::Function &f);

  bool isSupportedInst(llvm::Instruction &inst);

  bool isSupportedType(llvm::Type *t);

  uint64_t getInstID(llvm::Instruction *inst);

  bool isAssignment(llvm::Instruction &inst);

  ~ModuleTranslator();

  static bool isMakeSymbolicInt32(llvm::Instruction *inst);

  static bool isAssumeBool(llvm::Instruction *inst);
};

}

#endif
