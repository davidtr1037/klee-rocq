#include "ProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ModuleTranslation.h"
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

cl::opt<bool> TraceLemmas("trace-lemmas", cl::desc(""), cl::init(false));

/* TODO: decide how to handle assertions */

ProofGenerator::ProofGenerator(Module &m, raw_ostream &output) : m(m), output(output) {
  moduleTranslator = new ModuleTranslator(m);
  moduleSupport = new ModuleSupport(m, *moduleTranslator);
  exprTranslator = new ExprTranslator();
  stateTranslator = new StateTranslator(m, moduleTranslator, exprTranslator);

  /* TODO: add shared definitions (global store, etc.) */
  coqGlobalStoreAlias = nullptr;
}

void ProofGenerator::generateStaticDefs() {
  generateImports();
  generateGlobalDefs();
  generateModule();
  generateModuleAssumptionsProof();
}

void ProofGenerator::generateGlobalDefs() {
  vector<ref<CoqExpr>> requiredDefs;

  stateTranslator->generateGlobalDefs(requiredDefs);

  for (ref<CoqExpr> def : requiredDefs) {
    output << def->dump() << "\n";
  }
}

void ProofGenerator::generateModule() {
  vector<ref<CoqExpr>> requiredDefs;

  moduleTranslator->translateModuleCached();

  for (ref<CoqExpr> def : moduleTranslator->nameDefs) {
    requiredDefs.push_back(def);
  }

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

  for (ref<CoqLemma> lemma : moduleSupport->exprLemmas) {
    output << lemma->dump() << "\n";
  }

  for (ref<CoqLemma> lemma : moduleSupport->valueLemmas) {
    output << lemma->dump() << "\n";
  }

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
  ref<CoqExpr> coqState = stateTranslator->translateState(es, defs);
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

void ProofGenerator::generateImports() {
  for (ref<CoqExpr> import : getImports()) {
    output << import->dump() << "\n";
  }
}

vector<klee::ref<CoqExpr>> ProofGenerator::getImports() {
  return {
    new CoqRequire("Coq", "ZArith"),
    new CoqRequire("Coq", "Strings.String"),
    new CoqRequire("Coq", "Lia"),
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
    new CoqRequire("SE.Numeric", "Integers"),
    new CoqRequire("SE.SMT", "Expr"),
    new CoqRequire("SE.SMT", "Model"),
    new CoqRequire("SE.SMT", "Simplification"),
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
  return new Apply(
    "Safe_Leaf_Ret",
    {
      stateTranslator->getICAlias(state.stepID),
      createPlaceHolder(),
      createPlaceHolder(),
      createPlaceHolder(),
      stateTranslator->getPrevBIDAlias(state.stepID),
      stateTranslator->getLocalStoreAlias(state.stepID),
      stateTranslator->createGlobalStore(),
      stateTranslator->getSymbolicsAlias(state.stepID),
      stateTranslator->getPCAlias(state.stepID),
      stateTranslator->createModule(),
    }
  );
}

void ProofGenerator::handleStep(StateInfo &si,
                                ExecutionState &successor,
                                const ExternalProofHint &hint) {
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

  ref<CoqLemma> lemma = createLemmaForSubtree(si, successor, hint);
  lemmaDefs.push_front(lemma);
}

klee::ref<CoqLemma> ProofGenerator::createLemmaForSubtree(StateInfo &si,
                                                          ExecutionState &successor,
                                                          const ExternalProofHint &hint) {
  ref<CoqTactic> safetyTactic = getTacticForSafety(si, &hint);
  ref<CoqTactic> stepTactic = getTacticForStep(si, successor);
  ref<CoqTactic> tactic = getTacticForSubtree(safetyTactic, stepTactic);
  return createLemma(si.stepID, tactic);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForSafety(StateInfo &si,
                                                        const ExternalProofHint *hint) {
  if (moduleTranslator->isAssignment(*si.inst)) {
    if (moduleSupport->isUnsafeInstruction(*si.inst)) {
      BinaryOperator *bo = cast<BinaryOperator>(si.inst);

      if (bo->getOpcode() == Instruction::SDiv) {
        return getTacticForSDivSafety(si, hint);
      }

      bool isDivision;
      std::string lemmaName;
      switch (bo->getOpcode()) {
      case Instruction::UDiv:
      case Instruction::URem:
      case Instruction::SRem:
        lemmaName = "unsat_sym_division_error_condition";
        isDivision = true;
        break;

      case Instruction::Shl:
      case Instruction::LShr:
      case Instruction::AShr:
        lemmaName = "unsat_sym_shift_error_condition";
        isDivision = false;
        break;

      default:
        assert(false);
      }

      ref<CoqTactic> unsatTactic = nullptr;
      if (isInstrumented(si.inst)) {
        assert(hint && !hint->lastUnsatAxiomName.empty());
        unsatTactic = new Block(
          {
            new EApply(lemmaName),
            new Block({new EApply("equiv_smt_expr_normalize_simplify")}),
            new Block({new Apply(hint->lastUnsatAxiomName)}),
          }
        );
      } else {
        unsatTactic = new Block(
          {
            new Apply("unsat_and_right"),
            new Apply("unsat_false"),
          }
        );
      }

      ref<CoqTactic> t1 = new Block(
        {
          new Subst(),
          new Inversion("H15"),
          new Subst(),
          new EApply("sat_unsat_contradiction"),
          new Block({new EAssumption()}),
          unsatTactic,
        }
      );
      ref<CoqTactic> t2 = new Block(
        {
          new Subst(),
          new Inversion("H2"),
        }
      );

      return new Block(
        {
          new Intros({"Herr"}),
          new Inversion("Herr"),
          isDivision ? t1 : t2,
          isDivision ? t2 : t1,
        }
      );
    } else {
      return new Block(
        {
          new Apply("not_error_instr_op"),
          moduleSupport->getTacticForAssignmentExprCached(*si.inst),
        }
      );
    }
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

klee::ref<CoqTactic> ProofGenerator::getTacticForSDivSafety(StateInfo &si,
                                                            const ExternalProofHint *hint) {
  ref<CoqTactic> unsatDivisionTactic = nullptr;
  if (isInstrumented(si.inst)) {
    assert(hint && !hint->lastUnsatAxiomName.empty());
    unsatDivisionTactic = new Block({new Apply(hint->lastUnsatAxiomName)});
  } else {
    unsatDivisionTactic = new Block({new Apply("unsat_false")});
  }

  Value *dividend = si.inst->getOperand(0);
  ref<CoqExpr> ast1 = getEvaluatedSMTExpr(si, dividend);

  ref<CoqTactic> divisionTactic = new Block(
    {
      new Subst(),
      new Inversion("H15"),
      new Subst(),
      new EApply("sat_unsat_contradiction"),
      new Block({new EAssumption()}),
      new Block(
        {
          new EApply(
            "unsat_sym_sdiv_division_error_condition",
            {
              createPlaceHolder(),
              ast1,
              createPlaceHolder(),
              createPlaceHolder(),
            }
          ),
          new Block({new EApply("equiv_smt_expr_normalize_simplify")}),
          unsatDivisionTactic,
        }
      ),
    }
  );

  ref<CoqTactic> unsatDivisionOverflowTactic;
  if (isInstrumented(si.inst)) {
    assert(hint && !hint->lastUnsatAxiomName.empty());
    unsatDivisionOverflowTactic = new Block({new Apply(hint->lastUnsatAxiomName)});
  } else {
    unsatDivisionOverflowTactic = new Block({new Apply("unsat_false")});
  }

  ref<CoqTactic> divisionOverflowTactic = new Block(
    {
      new Subst(),
      new Inversion("H2"),
      new Subst(),
      new Inversion("H15"),
      new Subst(),
      new EApply("sat_unsat_contradiction"),
      new Block({new EAssumption()}),
      new Block(
        {
          new EApply("unsat_sym_sdiv_overflow_error_condition"),
          new Block({new EApply("equiv_smt_expr_normalize_simplify")}),
          unsatDivisionOverflowTactic,
        }
      ),
    }
  );

  ref<CoqTactic> shiftTactic = new Block(
    {
      new Subst(),
      new Inversion("H2"),
    }
  );

  return new Block(
    {
      new Intros({"Herr"}),
      new Inversion("Herr"),
      divisionTactic,
      divisionOverflowTactic,
      shiftTactic,
    }
  );
}

klee::ref<CoqTactic> ProofGenerator::getTacticForStep(StateInfo &si,
                                                      ExecutionState &successor) {
  ref<CoqTactic> tactic = getTacticForSat(si, successor, 0);
  if (ModuleTranslator::isMakeSymbolicInt32(si.inst)) {
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
  } else if (ModuleTranslator::isAssumeBool(si.inst)) {
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
              new Block({new Apply(createLemmaName(successor.stepID))}),
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
  if (moduleTranslator->isAssignment(*si.inst)) {
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
            {new Apply(createUnsatAxiomName(hint->unsatAxiomID))}
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
  if (ModuleTranslator::isMakeSymbolicInt32(si.inst)) {
    return getTacticForEquivMakeSymbolic(si, successor);
  } else if (ModuleTranslator::isAssumeBool(si.inst)) {
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
    /* TODO: avoid code duplication? */
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

/* TODO: pass an external proof hint? */
void ProofGenerator::handleStep(StateInfo &stateInfo,
                                SuccessorInfo &si1,
                                SuccessorInfo &si2,
                                ProofGenerationOutput &output) {
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

  ref<CoqLemma> lemma = createLemmaForSubtree(stateInfo, si1, si2, output);
  lemmaDefs.push_front(lemma);
}

klee::ref<CoqLemma> ProofGenerator::createLemmaForSubtree(StateInfo &stateInfo,
                                                          SuccessorInfo &si1,
                                                          SuccessorInfo &si2,
                                                          ProofGenerationOutput &output) {
  ref<CoqTactic> safetyTactic = getTacticForSafety(stateInfo, nullptr);
  ref<CoqTactic> stepTactic = getTacticForStep(stateInfo, si1, si2, output);
  ref<CoqTactic> tactic = getTacticForSubtree(safetyTactic, stepTactic);
  return createLemma(stateInfo.stepID, tactic);
}

klee::ref<CoqTactic> ProofGenerator::getTacticForStep(StateInfo &stateInfo,
                                                      SuccessorInfo &si1,
                                                      SuccessorInfo &si2,
                                                      ProofGenerationOutput &output) {
  ref<CoqTactic> tactic1, tactic2;
  getTacticsForBranches(stateInfo, si1, si2, tactic1, tactic2, output);
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
                                           ref<CoqTactic> &tactic2,
                                           ProofGenerationOutput &output) {
  assert(si1.isSat || si2.isSat);

  if (!si1.isSat || !si2.isSat) {
    uint64_t axiomID = allocateAxiomID();
    if (!si1.isSat) {
      ref<CoqExpr> e = exprTranslator->translate(si1.unsatPC, &si2.state->arrayTranslation, true);
      ref<CoqLemma> lemma = getUnsatAxiom(e, axiomID);
      unsatAxioms.push_front(lemma);
      output.unsatAxiomName = lemma->name;

      ProofHint hint(e, axiomID, false);
      tactic1 = getTacticForUnsat(e, axiomID);
      tactic2 = getTacticForSat(stateInfo, *si2.state, 0, &hint);
    }
    if (!si2.isSat) {
      ref<CoqExpr> e = exprTranslator->translate(si2.unsatPC, &si1.state->arrayTranslation, true);
      ref<CoqLemma> lemma = getUnsatAxiom(e, axiomID);
      unsatAxioms.push_front(lemma);
      output.unsatAxiomName = lemma->name;

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
          new Apply(createUnsatAxiomName(axiomID)),
        }
      ),
    }
  );
}

klee::ref<CoqLemma> ProofGenerator::getUnsatAxiom(ref<CoqExpr> pc, uint64_t axiomID) {
  return new CoqLemma(
    createUnsatAxiomName(axiomID),
    new CoqApplication(
      new CoqVariable("unsat"),
      {pc}
    ),
    nullptr,
    true
  );
}

string ProofGenerator::createUnsatAxiomName(uint64_t axiomID) {
  return "UNSAT_" + to_string(axiomID);
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
  if (TraceLemmas) {
    tactic = new Block(
      {
        new Idtac(createLemmaName(stepID)),
        tactic,
      }
    );
  }

  return new CoqLemma(
    createLemmaName(stepID),
    new CoqApplication(
      new CoqVariable("safe_et_opt"),
      {getTreeAlias(stepID)}
    ),
    tactic,
    isAdmitted
  );
  return nullptr;
}

string ProofGenerator::createLemmaName(uint64_t stepID) {
  return "L_" + to_string(stepID);
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
      /* TODO: pass an argument (cached?) */
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

string ProofGenerator::getTreeAliasName(uint64_t stepID) {
  return "t_" + to_string(stepID);
}

klee::ref<CoqVariable> ProofGenerator::getTreeAlias(uint64_t stepID) {
  return new CoqVariable(getTreeAliasName(stepID));
}

klee::ref<CoqExpr> ProofGenerator::getEvaluatedAST(StateInfo &stateInfo,
                                                   Value *v) {
  return new CoqApplication(
    new CoqVariable("extract_ast"),
    {
      new CoqApplication(
        new CoqVariable("sym_eval_exp"),
        {
          stateTranslator->getLocalStoreAlias(stateInfo.stepID),
          stateTranslator->createGlobalStore(),
          createSome(moduleTranslator->translateType(v->getType())),
          moduleTranslator->translateValue(v),
        }
      ),
    }
  );
}

klee::ref<CoqExpr> ProofGenerator::getEvaluatedSMTExpr(StateInfo &stateInfo,
                                                       Value *v) {
  return new CoqApplication(
    new CoqVariable("extract_smt_expr"),
    {
      new CoqApplication(
        new CoqVariable("sym_eval_exp"),
        {
          stateTranslator->getLocalStoreAlias(stateInfo.stepID),
          stateTranslator->createGlobalStore(),
          createSome(moduleTranslator->translateType(v->getType())),
          moduleTranslator->translateValue(v),
        }
      ),
    }
  );
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
            "program_safety_via_et",
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
              new Apply(createLemmaName(0)),
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
        new CoqVariable("step"),
        moduleTranslator->translateModuleCached(),
        moduleTranslator->createName("main"),
      }
    ),
    tactic
  );
}

void ProofGenerator::generateDebugScript(llvm::raw_ostream &output) {
  vector<ref<CoqExpr>> imports = getImports();
  imports.push_back(new CoqRequire("AutoGen", "proof"));

  for (ref<CoqExpr> import : imports) {
    output << import->dump() << "\n";
  }

  for (ref<CoqLemma> lemma : lemmaDefs) {
    output << "Print " << lemma->name << ".\n";
  }
}

bool ProofGenerator::isInstrumented(Instruction *inst) {
  static set<string> functions = {
    "klee_div_zero_check",
    "klee_sdiv_check_32",
    "klee_sdiv_check_64",
    "klee_overshift_check",
  };

  Instruction *prevInst = inst->getPrevNode();
  if (prevInst && isa<CallInst>(prevInst)) {
    CallInst *callInst = cast<CallInst>(prevInst);
    Function *f = callInst->getCalledFunction();
    if (f && functions.find(f->getName().str()) != functions.end()) {
      return true;
    }
  }

  return false;
}
