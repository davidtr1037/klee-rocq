#include "ProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Coq/ModuleAssumptions.h"
#include "klee/Module/KModule.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/Cell.h"

#include <string>
#include <sstream>

using namespace std;
using namespace llvm;
using namespace klee;

cl::opt<bool> DecomposeState(
  "decompose-state",
  cl::init(false),
  cl::desc("")
);

cl::opt<bool> CacheCoqExpr(
  "cache-coq-expr",
  cl::init(false),
  cl::desc("")
);

/* TODO: decide how to handle assertions */
/* TODO: add a function for generating names of axioms and lemmas (L_, UNSAT_, etc.) */

ProofGenerator::ProofGenerator(Module &m, raw_ostream &output) : m(m), output(output) {
  moduleTranslator = new ModuleTranslator(m);
  moduleSupport = new ModuleSupport(m, *moduleTranslator);
  exprTranslator = new ExprTranslator();

  /* TODO: add shared definitions (global store, etc.) */
  coqGlobalStoreAlias = nullptr;
}

/* TODO: rename */
void ProofGenerator::generate() {
  generateImports();
  generateGlobalDefs();
  generateModule();
  generateModuleAssumptionsProof();
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

  moduleTranslator->translateModuleCached();

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

  requiredDefs.push_back(moduleTranslator->moduleDef);

  for (ref<CoqExpr> def : requiredDefs) {
    output << def->dump() << "\n";
  }
}

void ProofGenerator::generateModuleAssumptionsProof() {
  ref<CoqLemma> lemma = moduleSupport->generateProof();

  for (ref<CoqLemma> lemma : moduleSupport->instLemmas) {
    output << lemma->dump() << "\n";
  }

  for (ref<CoqLemma> lemma : moduleSupport->bbLemmas) {
    output << lemma->dump() << "\n";
  }

  for (ref<CoqLemma> lemma : moduleSupport->functionLemmas) {
    output << lemma->dump() << "\n";
  }

  output << lemma->dump() << "\n";
}

void ProofGenerator::generateState(ExecutionState &es) {
  vector<ref<CoqExpr>> defs;
  ref<CoqExpr> coqState = translateState(es, defs);
  ref<CoqExpr> coqStateDef = new CoqDefinition(
    getStateAliasName(es.stepID),
    "sym_state",
    coqState
  );

  for (ref<CoqExpr> def : defs) {
    output << def->dump() << "\n";
  }
  output << coqStateDef->dump() << "\n";
}

klee::ref<CoqExpr> ProofGenerator::translateState(ExecutionState &es,
                                                  vector<ref<CoqExpr>> &defs) {
  if (!DecomposeState) {
    return new CoqApplication(
      new CoqVariable("mk_sym_state"),
      {
        createInstCounter(es),
        createCommand(es),
        createTrailingCommands(es),
        createPrevBID(es),
        createLocalStore(es),
        createStack(es),
        createGlobalStore(),
        createSymbolics(es),
        createPC(es, defs),
        createModule(),
      }
    );
  }

  defs.push_back(
    new CoqDefinition(
      getICAliasName(es.stepID),
      "inst_counter",
      createInstCounter(es)
   )
  );
  defs.push_back(
    new CoqDefinition(
      getCommandAliasName(es.stepID),
      "llvm_cmd",
      createCommand(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getCommandsAliasName(es.stepID),
      "list llvm_cmd",
      createTrailingCommands(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getPrevBIDAliasName(es.stepID),
      "option block_id",
      createPrevBID(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getLocalStoreAliasName(es.stepID),
      "smt_store",
      createLocalStore(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getStackAliasName(es.stepID),
      "list sym_frame",
      createStack(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getSymbolicsAliasName(es.stepID),
      "list string",
      createSymbolics(es)
    )
  );
  defs.push_back(
    new CoqDefinition(
      getPCAliasName(es.stepID),
      "smt_ast_bool",
      createPC(es, defs)
    )
  );

  return new CoqApplication(
    new CoqVariable("mk_sym_state"),
    {
      getICAlias(es.stepID),
      getCommandAlias(es.stepID),
      getCommandsAlias(es.stepID),
      getPrevBIDAlias(es.stepID),
      getLocalStoreAlias(es.stepID),
      getStackAlias(es.stepID),
      createGlobalStore(),
      getSymbolicsAlias(es.stepID),
      getPCAlias(es.stepID),
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

  vector<ref<CoqExpr>> coqInsts;

  /* TODO: use the pc/prevPC iterators */
  bool found = false;
  for (Instruction &inst : *bb) {
    if (found && moduleTranslator->isSupportedInst(inst)) {
      ref<CoqExpr> e = moduleTranslator->translateInstCached(inst);
      coqInsts.push_back(e);
    }
    if (&inst == es.prevPC->inst) {
      found = true;
    }
  }

  return new CoqList(coqInsts);
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

    ref<CoqExpr> coqName = moduleTranslator->createName(ru.name);
    ref<CoqExpr> coqExpr = exprTranslator->translateAsSMTExpr(ru.value, &es.arrayTranslation);
    assert(coqName && coqExpr);
    output << coqName->dump() << " !-> " << "Some (" << coqExpr->dump() << "); ";
  }

  output << "empty_smt_store)";
  return new CoqVariable(output.str());
}

/* TODO: CoqList should receive a list of CoqExpr */
/* TODO: avoid reversed iteration */
klee::ref<CoqExpr> ProofGenerator::createStack(ExecutionState &es) {
  vector<ref<CoqExpr>> frames;

  for (int i = es.stack.size() - 2; i >= 0; i--) {
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

/* TODO: check if was set? */
klee::ref<CoqExpr> ProofGenerator::createGlobalStore() {
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

klee::ref<CoqExpr> ProofGenerator::createPC(ExecutionState &es, vector<ref<CoqExpr>> &defs) {
  /* TODO: add a method to ExecutionState */
  ref<Expr> pc = ConstantExpr::create(1, Expr::Bool);
  for (ref<Expr> e : es.constraints) {
    pc = AndExpr::create(pc, e);
  }
  if (CacheCoqExpr) {
    return exprTranslator->translateCached(pc, &es.arrayTranslation, defs);
  } else {
    return exprTranslator->translate(pc, &es.arrayTranslation);
  }
}

klee::ref<CoqExpr> ProofGenerator::createModule() {
  return moduleTranslator->translateModuleCached();
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
    new CoqRequire("SE", "ModuleAssumptions"),
    new CoqRequire("SE", "Symbolic"),
    new CoqRequire("SE", "ProofGeneration"),
    new CoqRequire("SE.SMT", "Expr"),
    new CoqRequire("SE.SMT", "Model"),
    new CoqRequire("SE.Utils", "Util"),
  };
}

void ProofGenerator::handleTerminatedState(ExecutionState &state) {
  ref<CoqExpr> def = new CoqDefinition(
    getTreeAliasName(state.stepID),
    "execution_tree",
    new CoqApplication(
      new CoqVariable("t_leaf"),
      {getStateAlias(state.stepID)}
    )
  );
  treeDefs.push_front(def);

  ref<CoqLemma> lemma = createLemmaForLeaf(state);
  lemmaDefs.push_front(lemma);
}

klee::ref<CoqLemma> ProofGenerator::createLemmaForLeaf(ExecutionState &state) {
  ref<CoqTactic> tactic = getTacticForLeaf(state);
  return createLemma(state.stepID, tactic);
}

/* TODO: check the instruction type */
klee::ref<CoqTactic> ProofGenerator::getTacticForLeaf(ExecutionState &state) {
  if (!DecomposeState) {
    return new Apply("Safe_Leaf_Ret");
  }

  return new Apply(
    "Safe_Leaf_Ret",
    {
      getICAlias(state.stepID),
      createPlaceHolder(),
      createPlaceHolder(),
      createPlaceHolder(),
      getPrevBIDAlias(state.stepID),
      getLocalStoreAlias(state.stepID),
      createGlobalStore(),
      getSymbolicsAlias(state.stepID),
      getPCAlias(state.stepID),
      createModule(),
    }
  );
}

void ProofGenerator::handleStep(StateInfo &si, ExecutionState &successor) {
  ref<CoqExpr> def = new CoqDefinition(
    getTreeAliasName(si.stepID),
    "execution_tree",
    new CoqApplication(
      new CoqVariable("t_subtree"),
      {
        getStateAlias(si.stepID),
        new CoqList(
          {getTreeAlias(successor.stepID)}
        )
      }
    )
  );
  treeDefs.push_front(def);

  ref<CoqLemma> lemma = createLemmaForSubtree(si, successor);
  lemmaDefs.push_front(lemma);
}

klee::ref<CoqLemma> ProofGenerator::createLemmaForSubtree(StateInfo &si,
                                                          ExecutionState &successor) {
  ref<CoqTactic> safetyTactic = getTacticForSafety(si);
  ref<CoqTactic> stepTactic = getTacticForStep(si, successor);
  ref<CoqTactic> tactic = getTacticForSubtree(safetyTactic, stepTactic);
  return createLemma(si.stepID, tactic);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForSafety(StateInfo &si) {
  if (isa<BinaryOperator>(si.inst) || isa<CmpInst>(si.inst)) {
    return new Block(
      {new Apply("not_error_instr_op")}
    );
  }

  if (isa<BranchInst>(si.inst)) {
    BranchInst *bi = cast<BranchInst>(si.inst);
    if (bi->isConditional()) {
      return new Block(
        {new Apply("not_error_br")}
      );
    } else {
      return new Block(
        {new Apply("not_error_unconditional_br")}
      );
    }
  }

  if (isa<PHINode>(si.inst)) {
    return new Block(
      {new Apply("not_error_phi")}
    );
  }

  if (isa<CallInst>(si.inst)) {
    CallInst *callInst = dyn_cast<CallInst>(si.inst);
    if (callInst->getFunctionType()->getReturnType()->isVoidTy()) {
      return new Block(
        {
          new Apply("not_error_void_call"),
          new Intros({"H"}),
          new Inversion("H"),
        }
      );
    } else {
      return new Block(
        {new Apply("not_error_call")}
      );
    }
  }

  if (isa<ReturnInst>(si.inst)) {
    ReturnInst *returnInst = dyn_cast<ReturnInst>(si.inst);
    if (returnInst->getReturnValue()) {
      return new Block(
        {new Apply("not_error_ret")}
      );
    } else {
      return new Block(
        {new Apply("not_error_ret_void")}
      );
    }
  }

  assert(false);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForStep(StateInfo &si,
                                                      ExecutionState &successor) {
  ref<CoqTactic> tactic = getTacticForSat(si, successor, 0);
  if (isMakeSymbolicInt32(si.inst)) {
    return new Block(
      {
        new Intros({"s", "Hstep"}),
        new Inversion("Hstep"),
        new Block(
          {
            new Inversion("H16"),
          }
        ),
        tactic,
      }
    );
  } else if (isAssumeBool(si.inst)) {
    return new Block(
      {
        new Intros({"s", "Hstep"}),
        new Inversion("Hstep"),
        new Block(
          {
            new Inversion("H14"),
          }
        ),
        tactic,
      }
    );
  } else {
    return new Block(
      {
        new Intros({"s", "Hstep"}),
        tactic,
      }
    );
  }
}

klee::ref<CoqTactic> ProofGenerator::getTacticForSat(StateInfo &si,
                                                     ExecutionState &successor,
                                                     unsigned index,
                                                     ProofHint *hint) {
  ref<CoqTactic> eqTactic = getTacticForEquiv(si, successor, hint);
  return new Block(
    {
      new Left(),
      new Exists(getTreeAlias(successor.stepID)),
      new Split(
        getTacticForList(si, index),
        new Block(
          {
            new Split(
              new Block({new Apply("L_" + to_string(successor.stepID))}),
              eqTactic
            )
          }
        )
      ),
    }
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquiv(StateInfo &si,
                                                       ExecutionState &successor,
                                                       ProofHint *hint) {
  if (isa<BinaryOperator>(si.inst) || isa<CmpInst>(si.inst)) {
    return getTacticForEquivAssignment(si, successor);
  }

  if (isa<PHINode>(si.inst)) {
    return getTacticForEquivPHI(si, successor);
  }

  if (isa<BranchInst>(si.inst)) {
    return getTacticForEquivBranch(si, successor, hint);
  }

  if (isa<CallInst>(si.inst)) {
    return getTacticForEquivCall(si, successor);
  }

  if (isa<ReturnInst>(si.inst)) {
    return getTacticForEquivReturn(si, successor);
  }

  assert(false);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivAssignment(StateInfo &si,
                                                                 ExecutionState &successor) {
  ref<CoqTactic> t;
  if (si.wasRegisterUpdated) {
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_optimized_update",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createSuffixUpdates(si.suffix),
          }
        ),
        new Inversion("H13"),
        new Subst(),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  } else {
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_update_via_some",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqVariable("H13"),
          }
        ),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }
  return new Block(
    {
      new Inversion("Hstep"),
      new Subst(),
      new Apply("EquivSymState"),
      t,
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_smt_expr_refl")}),
    }
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivPHI(StateInfo &si,
                                                          ExecutionState &successor) {
  ref<CoqTactic> t;
  if (si.wasRegisterUpdated) {
    t = new Block(
      {
        /* TODO: can use a more simple lemma? */
        new Apply(
          "equiv_smt_store_on_optimized_update",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createSuffixUpdates(si.suffix),
          }
        ),
        new Inversion("H14"),
        new Subst(),
        new Apply("equiv_smt_expr_refl"),
      }
    );
  } else {
    t = new Block(
      {
        new Inversion("H14"),
        new Subst(),
        new Apply("equiv_smt_store_refl"),
      }
    );
  }
  return new Block(
    {
      new Inversion("Hstep"),
      new Subst(),
      new Apply("EquivSymState"),
      t,
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_smt_expr_refl")}),
    }
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivBranch(StateInfo &si,
                                                             ExecutionState &successor,
                                                             ProofHint *hint) {
  BranchInst *bi = cast<BranchInst>(si.inst);
  if (bi->isConditional()) {
    assert(si.branchCondition);
    ref<CoqTactic> t;
    if (hint && !isa<ConstantExpr>(si.branchCondition)) {
      t = new Block(
        {
          new Apply(
            hint->isTrueBranch ? "implied_condition" : "implied_negated_condition",
            {
              createPlaceHolder(),
              createPlaceHolder(),
              hint->unsatPC,
            }
          ),
          new Block(
            {
              new Apply("injection_some", "H12"),
              new Apply("injection_expr", "H12"),
              new Subst(),
              new Apply("equiv_smt_expr_normalize_simplify"),
            }
          ),
          new Block(
            {new Apply("UNSAT_" + to_string(hint->unsatAxiomID))}
          ),
        }
      );
    } else {
      t = new Block(
        {
          new Apply("injection_some", "H12"),
          new Apply("injection_expr", "H12"),
          new Subst(),
          new Apply("equiv_smt_expr_normalize_simplify"),
        }
      );
    }

    return new Block(
      {
        new Inversion("H13"),
        new Subst(),
        new Inversion("H14"),
        new Subst(),
        new Inversion("H15"),
        new Subst(),
        new Apply("EquivSymState"),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_sym_stack_refl")}),
        new Block({new Apply("equiv_smt_store_refl")}),
        t,
      }
    );
  } else {
    return new Block(
      {
        new Inversion("Hstep"),
        new Subst(),
        new Inversion("H10"),
        new Subst(),
        new Inversion("H11"),
        new Subst(),
        new Inversion("H12"),
        new Subst(),
        new Apply("equiv_sym_state_refl"),
      }
    );
  }
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivCall(StateInfo &si,
                                                           ExecutionState &successor) {
  if (isMakeSymbolicInt32(si.inst)) {
    return getTacticForEquivMakeSymbolic(si, successor);
  } else if (isAssumeBool(si.inst)) {
    return getTacticForEquivAssumeBool(si, successor);
  } else {
    return getTacticForEquivSimpleCall(si, successor);
  }
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivMakeSymbolic(StateInfo &si,
                                                                   ExecutionState &successor) {
  return new Block(
    {new Apply("equiv_sym_state_refl")}
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivAssumeBool(StateInfo &si,
                                                                 ExecutionState &successor) {
  return new Block(
    {
      new Inversion("H16"),
      new Subst(),
      new Apply("EquivSymState"),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block(
        {
          new Apply("injection_some", "H16"),
          new Apply("injection_expr", "H16"),
          new Subst(),
          new Apply("equiv_smt_expr_normalize_simplify"),
        }
      ),
    }
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivSimpleCall(StateInfo &si,
                                                                 ExecutionState &successor) {
  CallInst *callInst = dyn_cast<CallInst>(si.inst);
  if (callInst->getFunctionType()->getReturnType()->isVoidTy()) {
    return new Block(
      {
        new Inversion("Hstep"),
        new Subst(),
        new Inversion("H14"),
        new Subst(),
        new Inversion("H16"),
        new Subst(),
        new Inversion("H17"),
        new Subst(),
        new Inversion("H18"),
        new Subst(),
        new Apply("EquivSymState"),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_sym_stack_refl")}),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_smt_expr_refl")}),
      }
    );
  } else {
    return new Block(
      {
        new Inversion("Hstep"),
        new Subst(),
        new Inversion("H16"),
        new Subst(),
        new Inversion("H18"),
        new Subst(),
        new Inversion("H19"),
        new Subst(),
        new Apply("EquivSymState"),
        new Block(
          {
            new Inversion("H20"),
            new Apply("equiv_smt_store_refl"),
          }
        ),
        new Block({new Apply("equiv_sym_stack_refl")}),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_smt_expr_refl")}),
      }
    );
  }
}

klee::ref<CoqTactic> ProofGenerator::getTacticForEquivReturn(StateInfo &si,
                                                             ExecutionState &successor) {
  ReturnInst *returnInst = dyn_cast<ReturnInst>(si.inst);
  if (returnInst->getReturnValue()) {
    /* TODO: avoid code duplication */
    ref<CoqTactic> t;
    if (si.wasRegisterUpdated) {
      t = new Block(
        {
          new Apply(
            "equiv_smt_store_on_optimized_update",
            {
              createPlaceHolder(),
              createPlaceHolder(),
              createPlaceHolder(),
              createPlaceHolder(),
              createPlaceHolder(),
              createSuffixUpdates(si.suffix),
            }
          ),
          new Inversion("H15"),
          new Apply("equiv_smt_expr_refl"),
        }
      );
    } else {
      t = new Block(
        {
          new Inversion("H15"),
          new Apply("equiv_smt_store_refl"),
        }
      );
    }

    return new Block(
      {
        new Inversion("Hstep"),
        new Subst(),
        new Inversion("H16"),
        new Subst(),
        new Inversion("H17"),
        new Subst(),
        new Apply("EquivSymState"),
        t,
        new Block({new Apply("equiv_sym_stack_refl")}),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_smt_expr_refl")}),
      }
    );
  } else {
    return new Block(
      {
        new Inversion("Hstep"),
        new Subst(),
        new Inversion("H12"),
        new Subst(),
        new Inversion("H13"),
        new Subst(),
        new Apply("EquivSymState"),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_sym_stack_refl")}),
        new Block({new Apply("equiv_smt_store_refl")}),
        new Block({new Apply("equiv_smt_expr_refl")}),
      }
    );
  }
}

void ProofGenerator::handleStep(StateInfo &stateInfo,
                                SuccessorInfo &si1,
                                SuccessorInfo &si2) {
  vector<ref<CoqExpr>> satSuccessors;
  if (si1.isSat) {
    satSuccessors.push_back(getTreeAlias(si1.state->stepID));
  }
  if (si2.isSat) {
    satSuccessors.push_back(getTreeAlias(si2.state->stepID));
  }

  ref<CoqExpr> def = new CoqDefinition(
    getTreeAliasName(stateInfo.stepID),
    "execution_tree",
    new CoqApplication(
      new CoqVariable("t_subtree"),
      {
        getStateAlias(stateInfo.stepID),
        new CoqList(satSuccessors),
      }
    )
  );
  treeDefs.push_front(def);

  ref<CoqLemma> lemma = createLemmaForSubtree(stateInfo, si1, si2);
  lemmaDefs.push_front(lemma);
}

klee::ref<CoqLemma> ProofGenerator::createLemmaForSubtree(StateInfo &stateInfo,
                                                          SuccessorInfo &si1,
                                                          SuccessorInfo &si2) {
  ref<CoqTactic> safetyTactic = getTacticForSafety(stateInfo);
  ref<CoqTactic> stepTactic = getTacticForStep(stateInfo, si1, si2);
  ref<CoqTactic> tactic = getTacticForSubtree(safetyTactic, stepTactic);
  return createLemma(stateInfo.stepID, tactic);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForStep(StateInfo &stateInfo,
                                                      SuccessorInfo &si1,
                                                      SuccessorInfo &si2) {
  ref<CoqTactic> tactic1, tactic2;
  getTacticsForBranches(stateInfo, si1, si2, tactic1, tactic2);
  return new Block(
    {
      new Intros({"s", "Hstep"}),
      new Inversion("Hstep"),
      new Subst(),
      tactic1,
      tactic2,
    }
  );
}

void ProofGenerator::getTacticsForBranches(StateInfo &stateInfo,
                                           SuccessorInfo &si1,
                                           SuccessorInfo &si2,
                                           ref<CoqTactic> &tactic1,
                                           ref<CoqTactic> &tactic2) {
  assert(si1.isSat || si2.isSat);

  if (!si1.isSat || !si2.isSat) {
    uint64_t axiomID = allocateAxiomID();
    if (!si1.isSat) {
      ref<CoqExpr> e = exprTranslator->translate(si1.unsatPC, &si2.state->arrayTranslation);
      ref<CoqLemma> lemma = getUnsatAxiom(e, axiomID);
      unsatAxioms.push_front(lemma);

      ProofHint hint(e, axiomID, false);
      tactic1 = getTacticForUnsat(e, axiomID);
      tactic2 = getTacticForSat(stateInfo, *si2.state, 0, &hint);
    }
    if (!si2.isSat) {
      ref<CoqExpr> e = exprTranslator->translate(si2.unsatPC, &si1.state->arrayTranslation);
      ref<CoqLemma> lemma = getUnsatAxiom(e, axiomID);
      unsatAxioms.push_front(lemma);

      ProofHint hint(e, axiomID, true);
      tactic1 = getTacticForSat(stateInfo, *si1.state, 0, &hint);
      tactic2 = getTacticForUnsat(e, axiomID);
    }
  } else {
    tactic1 = getTacticForSat(stateInfo, *si1.state, 0);
    tactic2 = getTacticForSat(stateInfo, *si2.state, 1);
  }
}

klee::ref<CoqTactic> ProofGenerator::getTacticForUnsat(ref<CoqExpr> pc, uint64_t axiomID) {
  return new Block(
    {
      new Right(),
      new Apply("Unsat_State"),
      new Apply(
        "equiv_smt_expr_unsat",
        {
          pc,
          createPlaceHolder(),
        }
      ),
      new Block(
        {
          new Apply("equiv_smt_expr_symmetry"),
          new Apply("injection_some", "H12"),
          new Apply("injection_expr", "H12"),
          new Subst(),
          new Apply("equiv_smt_expr_normalize_simplify"),
        }
      ),
      new Block(
        {
          new Apply("UNSAT_" + to_string(axiomID)),
        }
      ),
    }
  );
}

klee::ref<CoqLemma> ProofGenerator::getUnsatAxiom(ref<CoqExpr> pc, uint64_t axiomID) {
  return new CoqLemma(
    "UNSAT_" + to_string(axiomID),
    new CoqApplication(
      new CoqVariable("unsat"),
      {pc}
    ),
    nullptr,
    true
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForSubtree(ref<CoqTactic> safetyTactic,
                                                         ref<CoqTactic> stepTactic) {
  return new Block(
    {
      new Apply("Safe_Subtree"),
      safetyTactic,
      stepTactic,
    }
  );
}

klee::ref<CoqLemma> ProofGenerator::createLemma(uint64_t stepID,
                                                ref<CoqTactic> tactic,
                                                bool isAdmitted) {
  return new CoqLemma(
    "L_" + to_string(stepID),
    new CoqApplication(
      new CoqVariable("safe_et_opt"),
      {getTreeAlias(stepID)}
    ),
    tactic,
    isAdmitted
  );
  return nullptr;
}

klee::ref<CoqTactic> ProofGenerator::getTacticForList(StateInfo &si,
                                                      unsigned index) {
  if (index == 0) {
    return new Block({new Apply("in_list_0")});
  }
  if (index == 1) {
    return new Block({new Apply("in_list_1")});
  }

  assert(false);
}

klee::ref<CoqList> ProofGenerator::createSuffixUpdates(list<RegisterUpdate> &updates) {
  std::vector<ref<CoqExpr>> pairs;
  for (RegisterUpdate &ru : updates) {
    ref<CoqExpr> pair = new CoqPair(
      moduleTranslator->createName(ru.name),
      createPlaceHolder()
    );
    pairs.push_back(pair);
  }

  return new CoqList(pairs);
}

uint64_t ProofGenerator::allocateAxiomID() {
  static uint64_t globalAxiomID = 0;
  return globalAxiomID++;
}

string ProofGenerator::getStateAliasName(uint64_t stepID) {
  return "s_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getStateAlias(uint64_t stepID) {
  return new CoqVariable(getStateAliasName(stepID));
}

string ProofGenerator::getICAliasName(uint64_t stepID) {
  return "s_ic_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getICAlias(uint64_t stepID) {
  return new CoqVariable(getICAliasName(stepID));
}

string ProofGenerator::getCommandAliasName(uint64_t stepID) {
  return "s_cmd_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getCommandAlias(uint64_t stepID) {
  return new CoqVariable(getCommandAliasName(stepID));
}

string ProofGenerator::getCommandsAliasName(uint64_t stepID) {
  return "s_cmds_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getCommandsAlias(uint64_t stepID) {
  return new CoqVariable(getCommandsAliasName(stepID));
}

string ProofGenerator::getPrevBIDAliasName(uint64_t stepID) {
  return "s_prev_bid_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getPrevBIDAlias(uint64_t stepID) {
  return new CoqVariable(getPrevBIDAliasName(stepID));
}

string ProofGenerator::getLocalStoreAliasName(uint64_t stepID) {
  return "s_local_store_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getLocalStoreAlias(uint64_t stepID) {
  return new CoqVariable(getLocalStoreAliasName(stepID));
}

string ProofGenerator::getStackAliasName(uint64_t stepID) {
  return "s_stack_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getStackAlias(uint64_t stepID) {
  return new CoqVariable(getStackAliasName(stepID));
}

string ProofGenerator::getSymbolicsAliasName(uint64_t stepID) {
  return "s_symbolics_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getSymbolicsAlias(uint64_t stepID) {
  return new CoqVariable(getSymbolicsAliasName(stepID));
}

string ProofGenerator::getPCAliasName(uint64_t stepID) {
  return "s_pc_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getPCAlias(uint64_t stepID) {
  return new CoqVariable(getPCAliasName(stepID));
}

string ProofGenerator::getTreeAliasName(uint64_t stepID) {
  return "t_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getTreeAlias(uint64_t stepID) {
  return new CoqVariable(getTreeAliasName(stepID));
}

void ProofGenerator::generateTreeDefs() {
  for (ref<CoqExpr> def : treeDefs) {
    output << def->dump() << "\n";
  }
}

void ProofGenerator::generateUnsatAxioms() {
  for (ref<CoqExpr> axiom : unsatAxioms) {
    output << axiom->dump() << "\n";
  }
}

void ProofGenerator::generateLemmaDefs() {
  for (ref<CoqExpr> def : lemmaDefs) {
    output << def->dump() << "\n";
  }
}

void ProofGenerator::generateTheorem() {
  output << getTheorem()->dump() << "\n";
}

klee::ref<CoqExpr> ProofGenerator::getTheorem() {
  ref<CoqTactic> tactic = new Block(
    {
      new Destruct("t_0", {{"r"}, {"r", "l"}}, "E"),
      new Block({new Discriminate("E")}),
      new Block(
        {
          new Apply(
            "completeness_via_et",
            {
              moduleTranslator->translateModuleCached(),
              moduleTranslator->createName("main"),
              new CoqVariable("s_0"),
              new CoqVariable("l"),
            }
          ),
          new Block({new Apply("is_supported_mdl")}),
          new Block({new Reflexivity()}),
          new Block(
            {
              new Inversion("E"),
              new Subst(),
              new Rewrite("E", false),
              new Apply("L_0"),
            }
          ),
        }
      ),
    }
  );

  return new CoqLemma(
    "program_safety",
    new CoqApplication(
      new CoqVariable("is_safe_program"),
      {
        moduleTranslator->translateModuleCached(),
        moduleTranslator->createName("main"),
      }
    ),
    tactic
  );
}

/* TODO: check funcion type */
bool ProofGenerator::isMakeSymbolicInt32(Instruction *inst) {
  if (isa<CallInst>(inst)) {
    CallInst *callInst = dyn_cast<CallInst>(inst);
    Function *f = dyn_cast<Function>(callInst->getCalledOperand());
    if (f && f->isDeclaration()) {
      return f->getName().equals("klee_make_symbolic_int32");
    }
  }

  return false;
}

/* TODO: check funcion type */
bool ProofGenerator::isAssumeBool(Instruction *inst) {
  if (isa<CallInst>(inst)) {
    CallInst *callInst = dyn_cast<CallInst>(inst);
    Function *f = dyn_cast<Function>(callInst->getCalledOperand());
    if (f && f->isDeclaration()) {
      return f->getName().equals("klee_assume_bool");
    }
  }

  return false;
}

void ProofGenerator::generateDebugScript(llvm::raw_ostream &output) {
  vector<ref<CoqExpr>> imports = getImports();
  imports.push_back(new CoqRequire("SE", "out"));

  for (ref<CoqExpr> import : imports) {
    output << import->dump() << "\n";
  }

  for (ref<CoqLemma> lemma : lemmaDefs) {
    output << "Print " << lemma->name << ".\n";
  }
}
