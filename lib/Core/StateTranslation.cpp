#include "StateTranslation.h"
#include "ExecutionState.h"

#include "klee/Module/KInstruction.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace klee;

StateTranslator::StateTranslator(ModuleTranslator &mt) : mt(mt) {
  /* TODO: add shared definitions (global store, etc.) */
  coqGlobalStore = new CoqVariable("gs");
}

ref<CoqExpr> StateTranslator::translate(ExecutionState &es) {
  return new CoqApplication(
    new CoqVariable("mk_sym_state"),
    {
      createInstCounter(es),
      createCommand(es),
      createTrailingCommands(es),
      createPrevBID(es),
      createLocalStore(es),
      createStack(es),
      createGlobalStore(es),
      createSymbolics(es),
      createPC(es),
      createModule(),
    }
  );
}

ref<CoqExpr> StateTranslator::createInstCounter(ExecutionState &es) {
  Instruction *inst = es.prevPC->inst;
  BasicBlock *bb = inst->getParent();
  Function *f = bb->getParent();

  return new CoqApplication(
    new CoqVariable("mk_inst_counter"),
    {
      mt.createName(f->getName().str()),
      mt.createName(bb->getName().str()),
      new CoqInteger(mt.getInstID(inst)),
    }
  );
}

ref<CoqExpr> StateTranslator::createCommand(ExecutionState &es) {
  return mt.translateInstCached(*es.prevPC->inst);
}

ref<CoqExpr> StateTranslator::createTrailingCommands(ExecutionState &es) {
  BasicBlock *bb = es.prevPC->inst->getParent();

  std::vector<ref<CoqExpr>> coq_insts;

  /* TODO: use the pc/prevPC iterators */
  bool found = false;
  for (Instruction &inst : *bb) {
    if (found && mt.isSupportedInst(inst)) {
      ref<CoqExpr> e = mt.translateInstCached(inst);
      coq_insts.push_back(e);
    }
    if (&inst == es.prevPC->inst) {
      found = true;
    }
  }

  return new CoqList(coq_insts);
}

ref<CoqExpr> StateTranslator::createPrevBID(ExecutionState &es) {
  return new CoqVariable("None");
}

ref<CoqExpr> StateTranslator::createLocalStore(ExecutionState &es) {
  return new CoqVariable("None");
}

ref<CoqExpr> StateTranslator::createStack(ExecutionState &es) {
  return new CoqList({});
}

ref<CoqExpr> StateTranslator::createGlobalStore(ExecutionState &es) {
  return coqGlobalStore;
}

ref<CoqExpr> StateTranslator::createSymbolics(ExecutionState &es) {
  return new CoqList({});
}

ref<CoqExpr> StateTranslator::createPC(ExecutionState &es) {
  return new CoqVariable("SMT_True");
}

ref<CoqExpr> StateTranslator::createModule() {
  /* TODO: add as a global definition */
  return new CoqVariable("mdl");
}

StateTranslator::~StateTranslator() {

}
