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

#include <string>
#include <vector>

namespace klee {

class OptimizedProofGenerator : public ProofGenerator {

public:

  OptimizedProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  ref<CoqTactic> getTacticForEquivAssignment(StateInfo &si,
                                             ExecutionState &successor);

  ref<CoqTactic> getTacticForEquivPHI(StateInfo &si,
                                      ExecutionState &successor);

  ref<CoqTactic> getTacticForEquivBranch(StateInfo &si,
                                         ExecutionState &successor,
                                         ProofHint *hint);

  ref<CoqTactic> getTacticForEquivCall(StateInfo &si,
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
