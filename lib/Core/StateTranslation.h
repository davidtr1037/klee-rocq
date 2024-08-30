#ifndef KLEE_STATE_TRANSLATION_H
#define KLEE_STATE_TRANSLATION_H

#include "ExecutionState.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

#include <map>

namespace klee {

class StateTranslator {

private:

  ModuleTranslator &mt;

  ref<CoqExpr> coqGlobalStore;

public:

  StateTranslator(ModuleTranslator &mt);

  ref<CoqExpr> translate(ExecutionState &es);

  ref<CoqExpr> createInstCounter(ExecutionState &es);

  ref<CoqExpr> createCommand(ExecutionState &es);

  ref<CoqExpr> createTrailingCommands(ExecutionState &es);

  ref<CoqExpr> createPrevBID(ExecutionState &es);

  ref<CoqExpr> createLocalStore(ExecutionState &es);

  ref<CoqExpr> createStack(ExecutionState &es);

  ref<CoqExpr> createGlobalStore(ExecutionState &es);

  ref<CoqExpr> createSymbolics(ExecutionState &es);

  ref<CoqExpr> createPC(ExecutionState &es);

  ref<CoqExpr> createModule();

  ~StateTranslator();
};

}

#endif
