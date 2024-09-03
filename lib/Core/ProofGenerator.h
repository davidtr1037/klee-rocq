#ifndef KLEE_PROOF_GENERATOR_H
#define KLEE_PROOF_GENERATOR_H

#include "ExecutionState.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <vector>

namespace klee {

struct StateInfo {
  uint64_t stepID;
  llvm::Instruction *inst;

  StateInfo() :
    stepID(0), inst(nullptr) {}

  StateInfo(uint64_t stepID, llvm::Instruction *inst)
      : stepID(stepID), inst(inst) {}
};

class ProofGenerator {

private:

    ref<CoqExpr> coqModuleAlias;

    ref<CoqExpr> coqGlobalStoreAlias;

public:

  llvm::Module &m;

  llvm::raw_ostream &output;

  ModuleTranslator *moduleTranslator;

  ExprTranslator *exprTranslator;

  std::list<ref<CoqExpr>> treeDefs;

  std::list<ref<CoqExpr>> lemmaDefs;

  ProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  void generate();

  void generateGlobalDefs();

  void generateModule();

  void generateState(ExecutionState &es);

  ref<CoqExpr> translateState(ExecutionState &es);

  ref<CoqExpr> createInstCounter(ExecutionState &es);

  ref<CoqExpr> createInstCounter(llvm::Instruction *inst);

  ref<CoqExpr> createCommand(ExecutionState &es);

  ref<CoqExpr> createTrailingCommands(ExecutionState &es);

  ref<CoqExpr> createPrevBID(ExecutionState &es);

  ref<CoqExpr> createPrevBID(StackFrame &sf);

  ref<CoqExpr> createLocalStore(ExecutionState &es);

  ref<CoqExpr> translateRegisterUpdates(ExecutionState &es,
                                        std::list<RegisterUpdate> &updates);

  ref<CoqExpr> createStack(ExecutionState &es);

  ref<CoqExpr> createGlobalStore(ExecutionState &es);

  ref<CoqExpr> createSymbolics(ExecutionState &es);

  ref<CoqExpr> getSymbolicName(unsigned index);

  ref<CoqExpr> getSymbolicNames(unsigned index);

  ref<CoqExpr> createPC(ExecutionState &es);

  ref<CoqExpr> createModule();

  void generateImports();

  std::vector<ref<CoqExpr>> getImports();

  void handleStep(const StateInfo &si, ExecutionState &successor);

  void handleTerminatedState(ExecutionState &state);

  ref<CoqExpr> createLemmaForLeaf(ExecutionState &state);

  ref<CoqTactic> getTacticForLeaf(ExecutionState &state);

  ref<CoqExpr> createLemma(ExecutionState &state, ref<CoqTactic> tactic);

  void generateTreeDefs();

  void generateLemmaDefs();
};

}

#endif
