#ifndef KLEE_OPTIMIZED_PROOF_GENERATOR_H
#define KLEE_OPTIMIZED_PROOF_GENERATOR_H

#include "ExecutionState.h"
#include "ProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Coq/ModuleAssumptions.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <string>

namespace klee {

class OptimizedProofGenerator : public ProofGenerator {

private:

  std::map<llvm::Function *, std::string> functionLemmas;

  std::map<llvm::BasicBlock *, std::string> bbLemmas;

  std::map<llvm::BasicBlock *, std::string> bbEntryLemmas;

  std::map<llvm::BasicBlock *, std::string> bbDecompositionLemmas;

public:

  OptimizedProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  void generate();

  void generateModuleLemmas();

  ref<CoqLemma> getFunctionLemma(llvm::Function &f);

  std::string getFunctionLemmaName(llvm::Function &f);

  ref<CoqLemma> getBasicBlockLemma(llvm::BasicBlock &bb);

  std::string getBasicBlockLemmaName(llvm::BasicBlock &bb);

  ref<CoqLemma> getBasicBlockEntryLemma(llvm::BasicBlock &bb);

  std::string getBasicBlockEntryLemmaName(llvm::BasicBlock &bb);

  ref<CoqLemma> getBasicBlockDecompositionLemma(llvm::BasicBlock &bb);

  std::string getBasicBlockDecompositionLemmaName(llvm::BasicBlock &bb);

  void decomposeBasicBlock(llvm::BasicBlock &bb,
                           ref<CoqExpr> &head,
                           std::vector<ref<CoqExpr>> &tail);

  void decomposeBasicBlockFrom(llvm::BasicBlock &bb,
                               llvm::Instruction &from,
                               ref<CoqExpr> &head,
                               std::vector<ref<CoqExpr>> &tail);

  ref<CoqLemma> createLemmaForSubtree(StateInfo &si,
                                      ExecutionState &successor);

  ref<CoqTactic> getTacticForSubtree(StateInfo &si,
                                     ExecutionState &successor);

  ref<CoqTactic> getTacticForSubtreeAssignment(StateInfo &si,
                                               ExecutionState &successor);

  ref<CoqTactic> getTacticForSubtreePHI(StateInfo &si,
                                        ExecutionState &successor);

  ref<CoqTactic> getTacticForSubtreeBranch(StateInfo &si,
                                           ExecutionState &successor);

  ref<CoqTactic> getTacticForSubtreeCall(StateInfo &si,
                                         ExecutionState &successor);

  ref<CoqTactic> getTacticForSubtreeReturn(StateInfo &si,
                                           ExecutionState &successor);

  ref<CoqLemma> createLemmaForSubtree(StateInfo &stateInfo,
                                      SuccessorInfo &successor1,
                                      SuccessorInfo &successor2);

  ref<CoqTactic> getTacticForSubtree(StateInfo &stateInfo,
                                     SuccessorInfo &successor1,
                                     SuccessorInfo &successor2);

};

}

#endif
