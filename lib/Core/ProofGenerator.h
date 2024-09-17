#ifndef KLEE_PROOF_GENERATOR_H
#define KLEE_PROOF_GENERATOR_H

#include "ExecutionState.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Coq/ModuleAssumptions.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <list>
#include <string>
#include <vector>

namespace klee {

struct StateInfo {

  uint64_t stepID;
  llvm::Instruction *inst;
  bool wasRegisterUpdated;
  std::list<RegisterUpdate> suffix;
  ref<Expr> branchCondition;

  StateInfo() :
    stepID(0), inst(nullptr), wasRegisterUpdated(false), branchCondition(nullptr)  {}

};

struct SuccessorInfo {

  bool isSat;
  ExecutionState *state;
  ref<Expr> unsatPC;

  SuccessorInfo(ExecutionState *state) :
    isSat(true), state(state), unsatPC(nullptr) {}

  SuccessorInfo(ref<Expr> unsatPC) :
    isSat(false), state(nullptr), unsatPC(unsatPC) {}

};

class ProofHint {

public:

  ref<CoqExpr> unsatPC;
  uint64_t unsatAxiomID;
  bool isTrueBranch;

  ProofHint(ref<CoqExpr> unsatPC, uint64_t unsatAxiomID, bool isTrueBranch) :
    unsatPC(unsatPC), unsatAxiomID(unsatAxiomID), isTrueBranch(isTrueBranch) {}

};

class ProofGenerator {

private:

    ref<CoqExpr> coqGlobalStoreAlias;

public:

  llvm::Module &m;

  llvm::raw_ostream &output;

  ModuleTranslator *moduleTranslator;

  ModuleSupport *moduleSupport;

  ExprTranslator *exprTranslator;

  std::list<ref<CoqExpr>> treeDefs;

  std::list<ref<CoqExpr>> unsatAxioms;

  std::list<ref<CoqExpr>> lemmaDefs;

  ProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  virtual void generate();

  void generateGlobalDefs();

  void generateModule();

  void generateModuleAssumptionsProof();

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
                                 ExecutionState &successor,
                                 unsigned index,
                                 ProofHint *hint = nullptr);

  ref<CoqTactic> getTacticForEquiv(StateInfo &si,
                                   ExecutionState &successor,
                                   ProofHint *hint);

  virtual ref<CoqTactic> getTacticForEquivAssignment(StateInfo &si,
                                                     ExecutionState &successor);

  virtual ref<CoqTactic> getTacticForEquivPHI(StateInfo &si,
                                              ExecutionState &successor);

  virtual ref<CoqTactic> getTacticForEquivBranch(StateInfo &si,
                                                 ExecutionState &successor,
                                                 ProofHint *hint);

  virtual ref<CoqTactic> getTacticForEquivCall(StateInfo &si,
                                               ExecutionState &successor);

  virtual ref<CoqTactic> getTacticForEquivMakeSymbolic(StateInfo &si,
                                                       ExecutionState &successor);

  virtual ref<CoqTactic> getTacticForEquivAssumeBool(StateInfo &si,
                                                     ExecutionState &successor);

  virtual ref<CoqTactic> getTacticForEquivSimpleCall(StateInfo &si,
                                                     ExecutionState &successor);

  virtual ref<CoqTactic> getTacticForEquivReturn(StateInfo &si,
                                                 ExecutionState &successor);

  void handleStep(StateInfo &stateInfo,
                  SuccessorInfo &successor1,
                  SuccessorInfo &successor2);

  ref<CoqExpr> createLemmaForSubtree(StateInfo &stateInfo,
                                     SuccessorInfo &successor1,
                                     SuccessorInfo &successor2);

  virtual ref<CoqTactic> getTacticForStep(StateInfo &stateInfo,
                                          SuccessorInfo &successor1,
                                          SuccessorInfo &successor2);

  void getTacticsForBranches(StateInfo &stateInfo,
                             SuccessorInfo &si1,
                             SuccessorInfo &si2,
                             ref<CoqTactic> &tactic1,
                             ref<CoqTactic> &tactic2);

  virtual ref<CoqTactic> getTacticForUnsat(ref<CoqExpr> pc, uint64_t axiomID);

  ref<CoqExpr> getUnsatAxiom(ref<CoqExpr> pc, uint64_t axiomID);

  ref<CoqTactic> getTacticForSubtree(ref<CoqTactic> safetyTactic,
                                     ref<CoqTactic> stepTactic);

  ref<CoqExpr> createLemma(uint64_t stepID, ref<CoqTactic> tactic, bool isAdmitted = false);

  ref<CoqTactic> getTacticForList(StateInfo &si, unsigned index);

  ref<CoqList> createSuffixUpdates(std::list<RegisterUpdate> &updates);

  uint64_t allocateAxiomID();

  void generateTreeDefs();

  void generateUnsatAxioms();

  void generateLemmaDefs();

  void generateTheorem();

  ref<CoqExpr> getTheorem();

  /* TODO: move from here */
  bool isMakeSymbolicInt32(llvm::Instruction *inst);

  /* TODO: move from here */
  bool isAssumeBool(llvm::Instruction *inst);
};

}

#endif
