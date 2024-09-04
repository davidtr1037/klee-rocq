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
  bool wasRegisterUpdated;

  StateInfo() :
    stepID(0), inst(nullptr), wasRegisterUpdated(false) {}

  StateInfo(uint64_t stepID,
            llvm::Instruction *inst,
            bool wasRegisterUpdated) :
    stepID(stepID),
    inst(inst),
    wasRegisterUpdated(wasRegisterUpdated) {}
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

  void handleTerminatedState(ExecutionState &state);

  ref<CoqExpr> createLemmaForLeaf(ExecutionState &state);

  ref<CoqTactic> getTacticForLeaf(ExecutionState &state);

  void handleStep(StateInfo &si, ExecutionState &successor);

  ref<CoqExpr> createLemmaForSubtree(StateInfo &si,
                                     ExecutionState &successor);

  ref<CoqTactic> getTacticForSafety(StateInfo &si);

  ref<CoqTactic> getTacticForStep(StateInfo &si,
                                  ExecutionState &successor);

  ref<CoqTactic> getTacticForSat(StateInfo &si,
                                 ExecutionState &successor);

  ref<CoqTactic> getEquivTactic(StateInfo &si,
                                ExecutionState &successor);

  void handleStep(StateInfo &si,
                  ExecutionState *successor1,
                  ExecutionState *successor2);

  ref<CoqExpr> createLemmaForSubtree(StateInfo &si,
                                     ExecutionState *successor1,
                                     ExecutionState *successor2);

  ref<CoqTactic> getTacticForStep(StateInfo &si,
                                  ExecutionState *successor1,
                                  ExecutionState *successor2);

  ref<CoqTactic> getTacticForSubtree(ref<CoqTactic> safetyTactic,
                                     ref<CoqTactic> stepTactic);

  ref<CoqExpr> createLemma(uint64_t stepID, ref<CoqTactic> tactic, bool isAdmitted = false);

  void generateTreeDefs();

  void generateLemmaDefs();

  void generateTheorem();

  ref<CoqExpr> getTheorem();

};

}

#endif
