#ifndef KLEE_PROOF_GENERATOR_H
#define KLEE_PROOF_GENERATOR_H

#include "ExecutionState.h"
#include "StateTranslation.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ModuleTranslation.h"
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

/* TODO: rename */
struct ProofGenerationOutput {

  std::string unsatAxiomName;

  ProofGenerationOutput() = default;

  ProofGenerationOutput(std::string unsatAxiomName) :
    unsatAxiomName(unsatAxiomName) {

  }

};

/* TODO: rename */
class ExternalProofHint {

public:

  std::string lastUnsatAxiomName;

  ExternalProofHint(std::string lastUnsatAxiomName) :
    lastUnsatAxiomName(lastUnsatAxiomName) {

  }

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

  StateTranslator *stateTranslator;

  std::list<ref<CoqExpr>> treeDefs;

  std::list<ref<CoqLemma>> unsatAxioms;

  std::list<ref<CoqLemma>> lemmaDefs;

  ProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  virtual void generateStaticDefs();

  void generateGlobalDefs();

  void generateModule();

  void generateModuleAssumptionsProof();

  void generateState(ExecutionState &es);

  void generateImports();

  std::vector<ref<CoqExpr>> getImports();

  void handleTerminatedState(ExecutionState &state);

  ref<CoqLemma> createLemmaForLeaf(ExecutionState &state);

  ref<CoqTactic> getTacticForLeaf(ExecutionState &state);

  void handleStep(StateInfo &si,
                  ExecutionState &successor,
                  const ExternalProofHint &hint);

  virtual ref<CoqLemma> createLemmaForSubtree(StateInfo &si,
                                              ExecutionState &successor,
                                              const ExternalProofHint &hint);

  ref<CoqTactic> getTacticForSafety(StateInfo &si, const ExternalProofHint *hint);

  ref<CoqTactic> getTacticForSDivSafety(StateInfo &si, const ExternalProofHint *hint);

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
                  SuccessorInfo &successor2,
                  ProofGenerationOutput &output);

  virtual ref<CoqLemma> createLemmaForSubtree(StateInfo &stateInfo,
                                              SuccessorInfo &successor1,
                                              SuccessorInfo &successor2,
                                              ProofGenerationOutput &output);

  virtual ref<CoqTactic> getTacticForStep(StateInfo &stateInfo,
                                          SuccessorInfo &successor1,
                                          SuccessorInfo &successor2,
                                          ProofGenerationOutput &output);

  void getTacticsForBranches(StateInfo &stateInfo,
                             SuccessorInfo &si1,
                             SuccessorInfo &si2,
                             ref<CoqTactic> &tactic1,
                             ref<CoqTactic> &tactic2,
                             ProofGenerationOutput &output);

  virtual ref<CoqTactic> getTacticForUnsat(ref<CoqExpr> pc, uint64_t axiomID);

  ref<CoqLemma> getUnsatAxiom(ref<CoqExpr> pc, uint64_t axiomID);

  std::string createUnsatAxiomName(uint64_t axiomID);

  ref<CoqTactic> getTacticForSubtree(ref<CoqTactic> safetyTactic,
                                     ref<CoqTactic> stepTactic);

  ref<CoqLemma> createLemma(uint64_t stepID, ref<CoqTactic> tactic, bool isAdmitted = false);

  std::string createLemmaName(uint64_t stepID);

  ref<CoqTactic> getTacticForList(StateInfo &si, unsigned index);

  ref<CoqList> createSuffixUpdates(std::list<RegisterUpdate> &updates);

  uint64_t allocateAxiomID();

  std::string getStateAliasName(uint64_t stepID);

  ref<CoqVariable> getStateAlias(uint64_t stepID);

  std::string getTreeAliasName(uint64_t stepID);

  ref<CoqVariable> getTreeAlias(uint64_t stepID);

  ref<CoqExpr> getEvaluatedSMTExpr(StateInfo &stateInfo, llvm::Value *v);

  void generateTreeDefs();

  void generateUnsatAxioms();

  void generateLemmaDefs();

  void generateTheorem();

  ref<CoqExpr> getTheorem();

  void generateDebugScript(llvm::raw_ostream &output);

  bool isInstrumented(llvm::Instruction *inst);
};

}

#endif
