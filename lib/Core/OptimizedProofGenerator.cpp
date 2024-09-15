#include "OptimizedProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Module/KInstruction.h"

#include <string>

using namespace std;
using namespace llvm;
using namespace klee;

OptimizedProofGenerator::OptimizedProofGenerator(Module &m, raw_ostream &output)
  : ProofGenerator(m, output) {

}

void OptimizedProofGenerator::generate() {
  generateImports();
  generateGlobalDefs();
  generateModule();
  generateModuleAssumptionsProof();
  generateModuleLemmas();
}

void OptimizedProofGenerator::generateModuleLemmas() {
  for (Function &f : m) {
    if (moduleTranslator->isSupportedFunction(f)) {
      if (f.isDeclaration()) {
        continue;
      }

      ref<CoqLemma> lemma = getFunctionLemma(f);
      lemmas.push_back(lemma);

      //for (BasicBlock &bb : f) {
      //  ref<CoqLemma> lemma = getBasicBlockLemma(bb);
      //  lemmas.push_back(lemma);
      //}
    }
  }

  for (ref<CoqLemma> lemma : lemmas) {
    output << lemma->dump() << "\n";
  }
}

klee::ref<CoqLemma> OptimizedProofGenerator::getFunctionLemma(Function &f) {
  ref<CoqExpr> body = new CoqImply(
    new CoqEq(
      new CoqApplication(
        new CoqVariable("find_function"),
        {
          new CoqVariable("mdl"),
          moduleTranslator->createName(f.getName().str()),
        }
      ),
      createSome(new CoqVariable("d"))
    ),
    new CoqEq(
      new CoqVariable("d"),
      moduleTranslator->translateFunctionCached(f)
    )
  );

  ref<CoqTactic> proof = new Block(
    {
      new Intros({"d", "H"}),
      new Inversion("H"),
      new Subst(),
      new Reflexivity(),
    }
  );

  return new CoqLemma(
    "L_" + f.getName().str(),
    {"d"},
    body,
    proof
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivAssignment(StateInfo &si,
                                                                          ExecutionState &successor) {
  ref<CoqTactic> t;
  if (si.wasRegisterUpdated) {
    vector<ref<CoqExpr>> pairs;
    for (RegisterUpdate &ru : si.suffix) {
      ref<CoqExpr> pair = new CoqPair(
        moduleTranslator->createName(ru.name),
        createPlaceHolder()
      );
      pairs.push_back(pair);
    }
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
            new CoqList(pairs),
          }
        ),
        new Apply(
          "equiv_smt_expr_1",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqVariable("Heval"),
          }
        ),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  } else {
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_update",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqVariable("Heval"),
          }
        ),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }

  return new Block(
    {
      new Apply("inversion_instr_op", "Hstep"),
      new Destruct("Hstep", {{"se", "Hstep"}}),
      new Destruct("Hstep", {{"Heval", "Heq"}}),
      new Rewrite("Heq"),
      new Apply("EquivSymState"),
      t,
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_smt_expr_refl")}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivPHI(StateInfo &si,
                                                                   ExecutionState &successor) {
  ref<CoqTactic> t;
  if (si.wasRegisterUpdated) {
    vector<ref<CoqExpr>> pairs;
    for (RegisterUpdate &ru : si.suffix) {
      ref<CoqExpr> pair = new CoqPair(
        moduleTranslator->createName(ru.name),
        createPlaceHolder()
      );
      pairs.push_back(pair);
    }
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
            new CoqList(pairs),
          }
        ),
        new Apply(
          "equiv_smt_expr_1",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqVariable("Heval"),
          }
        ),
        new Apply("equiv_smt_expr_refl"),
      }
    );
  } else {
    t = new Block(
      {
        new Apply(
          "equiv_smt_store_on_update_same",
          {
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            new CoqVariable("Heval"),
          }
        ),
      }
    );
  }
  return new Block(
    {
      new Apply("inversion_phi", "Hstep"),
      new Destruct("Hstep", {{"se", "Hstep"}}),
      new Destruct("Hstep", {{"Heval", "Heq"}}),
      new Rewrite("Heq"),
      new Apply("EquivSymState"),
      t,
      new Block({new Apply("equiv_sym_stack_refl")}),
      new Block({new Apply("equiv_smt_store_refl")}),
      new Block({new Apply("equiv_smt_expr_refl")}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivBranch(StateInfo &si,
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
              new Apply("injection_some", "Heval"),
              new Apply("injection_expr", "Heval"),
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
          new Apply("injection_some", "Heval"),
          new Apply("injection_expr", "Heval"),
          new Subst(),
          new Apply("equiv_smt_expr_normalize_simplify"),
        }
      );
    }

    return new Block(
      {
        new Inversion("Hd"),
        new Subst(),
        new Inversion("Hb"),
        new Subst(),
        new Inversion("Hcs"),
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
        new Apply("inversion_unconditional_br", "Hstep"),
        new Destruct("Hstep", {{"d", "Hstep"}}),
        new Destruct("Hstep", {{"b", "Hstep"}}),
        new Destruct("Hstep", {{"c", "Hstep"}}),
        new Destruct("Hstep", {{"cs", "Hstep"}}),
        new Destruct("Hstep", {{"Hd", "Hb"}}),
        new Destruct("Hb", {{"Hb", "Hcs"}}),
        new Destruct("Hcs", {{"Hcs", "Heq"}}),
        new Inversion("Hd"),
        new Subst(),
        new Inversion("Hb"),
        new Subst(),
        new Inversion("Hcs"),
        new Subst(),
        new Apply("equiv_sym_state_refl"),
      }
    );
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivCall(StateInfo &si,
                                                                    ExecutionState &successor) {
  return ProofGenerator::getTacticForEquivCall(si, successor);
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivReturn(StateInfo &si,
                                                                      ExecutionState &successor) {
  return ProofGenerator::getTacticForEquivReturn(si, successor);
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForStep(StateInfo &stateInfo,
                                                               SuccessorInfo &si1,
                                                               SuccessorInfo &si2) {
  ref<CoqTactic> tactic1, tactic2;
  getTacticsForBranches(stateInfo, si1, si2, tactic1, tactic2);
  return new Block(
    {
      new Intros({"s", "Hstep"}),
      new Apply("inversion_br", "Hstep"),
      new Destruct("Hstep", {{"cond", "Hstep"}}),
      new Destruct("Hstep", {{"d", "Hstep"}}),
      new Destruct("Hstep", {{"b", "Hstep"}}),
      new Destruct("Hstep", {{"c", "Hstep"}}),
      new Destruct("Hstep", {{"cs", "Hstep"}}),
      new Destruct("Hstep", {{"Heval", "Hstep"}}),
      new Destruct("Hstep", {{"Hd", "Hstep"}}),
      new Concat(
        {
          new Destruct("Hstep", {{"Hstep"}, {"Hstep"}}),
          new Destruct("Hstep", {{"Hb", "Hcs"}}),
          new Destruct("Hcs", {{"Hcs", "Heq"}}),
          new Rewrite("Heq"),
        }
      ),
      tactic1,
      tactic2,
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForUnsat(ref<CoqExpr> pc,
                                                                uint64_t axiomID) {
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
          new Apply("injection_some", "Heval"),
          new Apply("injection_expr", "Heval"),
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
