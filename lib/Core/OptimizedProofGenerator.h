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

  ref<CoqLemma> getBasicBlockLemma(llvm::BasicBlock &bb);

  ref<CoqLemma> getBasicBlockEntryLemma(llvm::BasicBlock &bb);

  ref<CoqLemma> getBasicBlockDecompositionLemma(llvm::BasicBlock &bb);

  void decomposeBasicBlock(llvm::BasicBlock &bb,
                           ref<CoqExpr> &head,
                           std::vector<ref<CoqExpr>> &tail);

  ref<CoqTactic> getTacticForEquivAssignment(StateInfo &si,
                                             ExecutionState &successor);

  ref<CoqTactic> getTacticForEquivPHI(StateInfo &si,
                                      ExecutionState &successor);

  ref<CoqTactic> getTacticForEquivBranch(StateInfo &si,
                                         ExecutionState &successor,
                                         ProofHint *hint);

  ref<CoqTactic> getTacticForEquivSimpleCall(StateInfo &si,
                                             ExecutionState &successor);

  ref<CoqTactic> getTacticForEquivReturn(StateInfo &si,
                                         ExecutionState &successor);


  ref<CoqTactic> getTacticForStep(StateInfo &stateInfo,
                                  SuccessorInfo &si1,
                                  SuccessorInfo &si2);

  ref<CoqTactic> getTacticForUnsat(ref<CoqExpr> pc, uint64_t axiomID);

};

}

#endif
