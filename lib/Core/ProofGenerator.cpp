#include "ProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Module/KModule.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/Cell.h"

#include <string>
#include <sstream>

using namespace std;
using namespace llvm;
using namespace klee;

ProofGenerator::ProofGenerator(Module &m, raw_ostream &output) : m(m), output(output) {
  moduleTranslator = new ModuleTranslator(m);
  exprTranslator = new ExprTranslator();

  /* TODO: add shared definitions (global store, etc.) */
  coqModuleAlias = nullptr;
  coqGlobalStoreAlias = nullptr;
}

/* TODO: rename */
void ProofGenerator::generate() {
  generateImports();
  generateGlobalDefs();
  generateModule();
}

void ProofGenerator::generateGlobalDefs() {
  vector<ref<CoqExpr>> requiredDefs;

  /* TODO: add a general mechanism for aliasing */
  string globalStoreAlias = "gs";
  ref<CoqExpr> coqGlobalStoreDef = new CoqDefinition(
    globalStoreAlias,
    "smt_store",
    {new CoqVariable("empty_smt_store")}
  );
  requiredDefs.push_back(coqGlobalStoreDef);
  coqGlobalStoreAlias = new CoqVariable(globalStoreAlias);

  for (ref<CoqExpr> def : requiredDefs) {
    output << def->dump() << "\n";
  }
}

void ProofGenerator::generateModule() {
  vector<ref<CoqExpr>> requiredDefs;

  ref<CoqExpr> coqModule = moduleTranslator->translateModule();

  for (ref<CoqExpr> def : moduleTranslator->instDefs) {
    requiredDefs.push_back(def);
  }

  for (ref<CoqExpr> def : moduleTranslator->bbDefs) {
    requiredDefs.push_back(def);
  }

  for (ref<CoqExpr> def : moduleTranslator->declDefs) {
    requiredDefs.push_back(def);
  }

  for (ref<CoqExpr> def : moduleTranslator->functionDefs) {
    requiredDefs.push_back(def);
  }

  string alias = "mdl";
  ref<CoqExpr> coqModuleDef = new CoqDefinition(
    alias,
    "llvm_module",
     coqModule
  );
  requiredDefs.push_back(coqModuleDef);

  for (ref<CoqExpr> def : requiredDefs) {
    output << def->dump() << "\n";
  }

  /* set aliases */
  coqModuleAlias = new CoqVariable(alias);
}

void ProofGenerator::generateState(ExecutionState &es) {
  ref<CoqExpr> coqState = translateState(es);
  ref<CoqExpr> coqStateDef = new CoqDefinition(
    "s_" + to_string(es.stepID),
    "sym_state",
    coqState
  );

  output << coqStateDef->dump() << "\n";
}

klee::ref<CoqExpr> ProofGenerator::translateState(ExecutionState &es) {
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

klee::ref<CoqExpr> ProofGenerator::createInstCounter(ExecutionState &es) {
  return createInstCounter(es.prevPC->inst);
}

klee::ref<CoqExpr> ProofGenerator::createInstCounter(Instruction *inst) {
  BasicBlock *bb = inst->getParent();
  Function *f = bb->getParent();

  return new CoqApplication(
    new CoqVariable("mk_inst_counter"),
    {
      moduleTranslator->createName(f->getName().str()),
      moduleTranslator->createName(bb->getName().str()),
      new CoqInteger(moduleTranslator->getInstID(inst)),
    }
  );
}

klee::ref<CoqExpr> ProofGenerator::createCommand(ExecutionState &es) {
  return moduleTranslator->translateInstCached(*es.prevPC->inst);
}

klee::ref<CoqExpr> ProofGenerator::createTrailingCommands(ExecutionState &es) {
  BasicBlock *bb = es.prevPC->inst->getParent();

  std::vector<ref<CoqExpr>> coq_insts;

  /* TODO: use the pc/prevPC iterators */
  bool found = false;
  for (Instruction &inst : *bb) {
    if (found && moduleTranslator->isSupportedInst(inst)) {
      ref<CoqExpr> e = moduleTranslator->translateInstCached(inst);
      coq_insts.push_back(e);
    }
    if (&inst == es.prevPC->inst) {
      found = true;
    }
  }

  return new CoqList(coq_insts);
}

klee::ref<CoqExpr> ProofGenerator::createPrevBID(ExecutionState &es) {
  return createPrevBID(es.stack.back());
}

klee::ref<CoqExpr> ProofGenerator::createPrevBID(StackFrame &sf) {
  if (sf.incomingBB) {
    return createSome(moduleTranslator->createName(sf.incomingBB->getName().str()));
  } else {
    return createNone();
  }
}

klee::ref<CoqExpr> ProofGenerator::createLocalStore(ExecutionState &es) {
  return translateRegisterUpdates(es, es.stack.back().updates);
}

klee::ref<CoqExpr> ProofGenerator::translateRegisterUpdates(ExecutionState &es,
                                                            list<RegisterUpdate> &updates) {
  ostringstream output;

  output << "(";
  for (auto i = updates.rbegin(); i != updates.rend(); i++) {
    RegisterUpdate &ru = *i;
    if (ru.value.isNull()) {
      continue;
    }

    ref<CoqExpr> coq_name = moduleTranslator->createName(ru.name);
    ref<CoqExpr> coq_expr = exprTranslator->translate(ru.value, &es.arrayTranslation);
    output << coq_name->dump() << " !-> " << "Some (" << coq_expr->dump() << "); ";
  }

  output << "empty_smt_store)";
  return new CoqVariable(output.str());
}

klee::ref<CoqExpr> ProofGenerator::createStack(ExecutionState &es) {
  vector<ref<CoqExpr>> frames;

  for (unsigned i = 0; i < es.stack.size() - 1; i++) {
    StackFrame &sf = es.stack[i];
    StackFrame &next_sf = es.stack[i + 1];

    KInstruction *ki = next_sf.caller;
    assert(ki);
    CallInst *callInst = dyn_cast<CallInst>(ki->inst);
    assert(callInst);
    ref<CoqExpr> v;
    if (callInst->getFunctionType()->getReturnType()->isVoidTy()) {
      v = createNone();
    } else {
      v = createSome(moduleTranslator->createName(callInst->getName().str()));
    }

    Instruction *next = callInst->getNextNode();
    assert(next);

    ref<CoqExpr> e = new CoqApplication(
      new CoqVariable("Sym_Frame"),
      {
        translateRegisterUpdates(es, sf.updates),
        createInstCounter(next),
        createPrevBID(sf),
        v,
      }
    );
    frames.push_back(e);
  }
  return new CoqList(frames);
}

klee::ref<CoqExpr> ProofGenerator::createGlobalStore(ExecutionState &es) {
  return coqGlobalStoreAlias;
}

klee::ref<CoqExpr> ProofGenerator::createSymbolics(ExecutionState &es) {
  if (es.symbolics.empty()) {
    return createEmptyList();
  } else {
    return getSymbolicNames(es.symbolics.size() - 1);
  }
}

/* TODO: rename to createSymbolicName */
/* TODO: add an alias */
klee::ref<CoqExpr> ProofGenerator::getSymbolicName(unsigned index) {
  ref<CoqExpr> arg;
  if (index == 0) {
    arg = createEmptyList();
  } else {
    arg = getSymbolicNames(index - 1);
  }
  return new CoqApplication(
    new CoqVariable("fresh_name"),
    {arg}
  );
}

/* TODO: rename to createSymbolicNames */
/* TODO: add an alias */
klee::ref<CoqExpr> ProofGenerator::getSymbolicNames(unsigned index) {
  ref<CoqExpr> arg;
  if (index == 0) {
    arg = createEmptyList();
  } else {
    arg = getSymbolicNames(index - 1);
  }
  return new CoqApplication(
    new CoqVariable("extend_names"),
    {arg}
  );
}

klee::ref<CoqExpr> ProofGenerator::createPC(ExecutionState &es) {
  ref<Expr> pc = ConstantExpr::create(1, Expr::Bool);
  for (ref<Expr> e : es.constraints) {
    pc = AndExpr::create(pc, e);
  }
  return exprTranslator->translate(pc, &es.arrayTranslation);
}

klee::ref<CoqExpr> ProofGenerator::createModule() {
  return coqModuleAlias;
}

void ProofGenerator::generateImports() {
  for (ref<CoqExpr> import : getImports()) {
    output << import->dump() << "\n";
  }
}

vector<klee::ref<CoqExpr>> ProofGenerator::getImports() {
  return {
    new CoqRequire("Coq", "ZArith"),
    new CoqRequire("Coq", "Strings.String"),
    new CoqRequire("Coq", "List"),
    new CoqImport("ListNotations"),
    new CoqRequire("SE", "BitVectors"),
    new CoqRequire("SE", "CFG"),
    new CoqRequire("SE", "ChoiceAxiom"),
    new CoqRequire("SE", "Concrete"),
    new CoqRequire("SE", "DynamicValue"),
    new CoqRequire("SE", "ExecutionTreeOpt"),
    new CoqRequire("SE", "IDMap"),
    new CoqRequire("SE", "LLVMAst"),
    new CoqRequire("SE", "Symbolic"),
    new CoqRequire("SE", "ProofGeneration"),
    new CoqRequire("SE.SMT", "Expr"),
    new CoqRequire("SE.SMT", "Model"),
  };
}

void ProofGenerator::handleTerminatedState(ExecutionState &state) {
  ref<CoqExpr> def = new CoqDefinition(
    "t_" + to_string(state.stepID),
    "execution_tree",
    new CoqApplication(
      new CoqVariable("t_leaf"),
      {new CoqVariable("s_" + to_string(state.stepID))}
    )
  );
  treeDefs.push_front(def);

  ref<CoqExpr> lemma = createLemmaForLeaf(state);
  lemmaDefs.push_front(lemma);
}

klee::ref<CoqExpr> ProofGenerator::createLemmaForLeaf(ExecutionState &state) {
  ref<CoqTactic> tactic = getTacticForLeaf(state);
  return createLemma(state, tactic);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForLeaf(ExecutionState &state) {
  return new Apply("Safe_Leaf_Ret");
}

klee::ref<CoqExpr> ProofGenerator::createLemma(ExecutionState &state, ref<CoqTactic> tactic) {
  return new CoqLemma(
    "L_" + to_string(state.stepID),
    new CoqApplication(
      new CoqVariable("safe_et_opt"),
      {new CoqVariable("t_" + to_string(state.stepID))}
    ),
    tactic,
    false
  );
  return nullptr;
}

void ProofGenerator::handleStep(const StateInfo &si, ExecutionState &successor) {
  ref<CoqExpr> def = new CoqDefinition(
    "t_" + to_string(si.stepID),
    "execution_tree",
    new CoqApplication(
      new CoqVariable("t_subtree"),
      {
        new CoqVariable("s_" + to_string(si.stepID)),
        new CoqList(
          {new CoqVariable("t_" + to_string(successor.stepID))}
        )
      }
    )
  );
  treeDefs.push_front(def);
}

void ProofGenerator::generateTreeDefs() {
  for (ref<CoqExpr> def : treeDefs) {
    output << def->dump() << "\n";
  }
}

void ProofGenerator::generateLemmaDefs() {
  for (ref<CoqExpr> def : lemmaDefs) {
    output << def->dump() << "\n";
  }
}
