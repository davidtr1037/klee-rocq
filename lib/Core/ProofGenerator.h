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

class ProofGenerator {

private:

    ref<CoqExpr> coqModuleAlias;

    ref<CoqExpr> coqGlobalStoreAlias;

public:

  llvm::Module &m;

  llvm::raw_ostream &output;

  ModuleTranslator *moduleTranslator;

  ExprTranslator *exprTranslator;

  ProofGenerator(llvm::Module &m, llvm::raw_ostream &output);

  void generate();

  void translateModule();

  ref<CoqExpr> translateState(ExecutionState &es);

  ref<CoqExpr> createInstCounter(ExecutionState &es);

  ref<CoqExpr> createCommand(ExecutionState &es);

  ref<CoqExpr> createTrailingCommands(ExecutionState &es);

  ref<CoqExpr> createPrevBID(ExecutionState &es);

  ref<CoqExpr> createLocalStore(ExecutionState &es);

  ref<CoqExpr> translateRegisterUpdates(std::list<RegisterUpdate> &updates);

  ref<CoqExpr> createStack(ExecutionState &es);

  ref<CoqExpr> createGlobalStore(ExecutionState &es);

  ref<CoqExpr> createSymbolics(ExecutionState &es);

  ref<CoqExpr> createPC(ExecutionState &es);

  ref<CoqExpr> createModule();

  std::vector<ref<CoqExpr>> generateImports();

};

}

#endif
