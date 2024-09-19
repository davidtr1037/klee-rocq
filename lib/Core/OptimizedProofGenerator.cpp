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
  vector<ref<CoqLemma>> lemmas;

  for (Function &f : m) {
    if (moduleTranslator->isSupportedFunction(f)) {
      if (f.isDeclaration()) {
        continue;
      }

      ref<CoqLemma> lemma = getFunctionLemma(f);
      lemmas.push_back(lemma);
      functionLemmas.insert(std::make_pair(&f, lemma->name));

      /* TODO: add docs */
      BasicBlock &entry = f.getEntryBlock();
      ref<CoqLemma> bbEntryLemma = getBasicBlockEntryLemma(entry);
      lemmas.push_back(bbEntryLemma);
      bbEntryLemmas.insert(std::make_pair(&entry, bbEntryLemma->name));

      for (BasicBlock &bb : f) {
        /* TODO: add docs */
        ref<CoqLemma> lemma = getBasicBlockLemma(bb);
        lemmas.push_back(lemma);
        bbLemmas.insert(std::make_pair(&bb, lemma->name));
        /* TODO: add docs */
        ref<CoqLemma> decompositionLemma = getBasicBlockDecompositionLemma(bb);
        lemmas.push_back(decompositionLemma);
        bbDecompositionLemmas.insert(std::make_pair(&bb, decompositionLemma->name));
      }
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

klee::ref<CoqLemma> OptimizedProofGenerator::getBasicBlockLemma(BasicBlock &bb) {
  ref<CoqExpr> body = new CoqImply(
    new CoqEq(
      new CoqApplication(
        new CoqVariable("fetch_block"),
        {
          moduleTranslator->translateFunctionCached(*bb.getParent()),
          moduleTranslator->createName(bb.getName().str()),
        }
      ),
      createSome(new CoqVariable("b"))
    ),
    new CoqEq(
      new CoqVariable("b"),
      moduleTranslator->translateBasicBlockCached(bb)
    )
  );

  ref<CoqTactic> proof = new Block(
    {
      new Intros({"b", "H"}),
      new Inversion("H"),
      new Subst(),
      new Reflexivity(),
    }
  );

  return new CoqLemma(
    "L_bb_" + to_string(moduleTranslator->getBasicBlockID(bb)),
    {"b"},
    body,
    proof
  );
}

klee::ref<CoqLemma> OptimizedProofGenerator::getBasicBlockEntryLemma(BasicBlock &bb) {
  ref<CoqExpr> body = new CoqImply(
    new CoqEq(
      new CoqApplication(
        new CoqVariable("entry_block"),
        {moduleTranslator->translateFunctionCached(*bb.getParent())}
      ),
      createSome(new CoqVariable("b"))
    ),
    new CoqEq(
      new CoqVariable("b"),
      moduleTranslator->translateBasicBlockCached(bb)
    )
  );

  ref<CoqTactic> proof = new Block(
    {
      new Intros({"b", "H"}),
      new Inversion("H"),
      new Subst(),
      new Reflexivity(),
    }
  );

  return new CoqLemma(
    "L_entry_bb_" + to_string(moduleTranslator->getBasicBlockID(bb)),
    {"b"},
    body,
    proof
  );
}

klee::ref<CoqLemma> OptimizedProofGenerator::getBasicBlockDecompositionLemma(BasicBlock &bb) {
  ref<CoqExpr> head = nullptr;
  std::vector<ref<CoqExpr>> tail;

  for (Instruction &inst : bb) {
    if (!head) {
      head = moduleTranslator->translateInstCached(inst);
    } else {
      ref<CoqExpr> coqInst = moduleTranslator->translateInstCached(inst);
      if (coqInst) {
        tail.push_back(coqInst);
      } else {
        assert(false);
      }
    }
  }

  ref<CoqExpr> body = new CoqImply(
    new CoqEq(
      new CoqApplication(
        new CoqVariable("blk_cmds"),
        {moduleTranslator->translateBasicBlockCached(bb)}
      ),
      /* TODO: ... */
      new CoqVariable("c :: cs")
    ),
    new CoqAnd(
      new CoqEq(new CoqVariable("c"), head),
      new CoqEq(new CoqVariable("cs"), new CoqList(tail))
    )
  );

  ref<CoqTactic> proof = new Block(
    {
      new Intros({"c", "cs", "H"}),
      new Inversion("H"),
      new Subst(),
      new Split(
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()})
      ),
    }
  );

  return new CoqLemma(
    "L_decompose_bb_" + to_string(moduleTranslator->getBasicBlockID(bb)),
    {"c", "cs"},
    body,
    proof
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivAssignment(StateInfo &si,
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

  /* TODO: add an option to decompose these (and define once) */
  ref<CoqExpr> var = nullptr;
  ref<CoqExpr> expr = nullptr;
  if (isa<BinaryOperator>(si.inst)) {
    BinaryOperator *bo = cast<BinaryOperator>(si.inst);
    var = moduleTranslator->translateBinaryOperatorName(bo);
    expr = moduleTranslator->translateBinaryOperatorExpr(bo);
  }

  if (isa<CmpInst>(si.inst)) {
    CmpInst *ci = cast<CmpInst>(si.inst);
    var = moduleTranslator->translateCmpInstName(ci);
    expr = moduleTranslator->translateCmpInstExpr(ci);
  }

  assert(var && expr);

  return new Block(
    {
      new Apply(
        "equiv_sym_state_instr_op",
        {
          getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(*si.inst)),
          var,
          expr,
          getCommandAlias(successor.stepID),
          getCommandsAlias(successor.stepID),
          getPrevBIDAlias(si.stepID),
          getLocalStoreAlias(si.stepID),
          getStackAlias(si.stepID),
          createPlaceHolder(), // createGlobalStore(),
          getSymbolicsAlias(si.stepID),
          getPCAlias(si.stepID),
          createModule(),
          getLocalStoreAlias(successor.stepID),
          new CoqVariable("s"),
        }
      ),
      t,
      new Block({new Assumption()}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivPHI(StateInfo &si,
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
  /* target instruction */
  Instruction *inst = successor.pc->inst;
  BasicBlock *bb = inst->getParent();
  Function *f = bb->getParent();

  assert(bbLemmas.find(bb) != bbLemmas.end());
  string bbLemma = bbLemmas[bb];

  assert(bbDecompositionLemmas.find(bb) != bbDecompositionLemmas.end());
  string bbDecompositionLemma = bbDecompositionLemmas[bb];

  assert(functionLemmas.find(f) != functionLemmas.end());
  string functionLemma = functionLemmas[f];

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
        new Apply(functionLemma, "Hd"),
        new Subst(),
        new Apply(bbLemma, "Hb"),
        new Subst(),
        new Apply(bbDecompositionLemma, "Hcs"),
        new Destruct("Hcs", {{"Hc", "Hcs"}}),
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
        new Apply(functionLemma, "Hd"),
        new Subst(),
        new Apply(bbLemma, "Hb"),
        new Subst(),
        new Apply(bbDecompositionLemma, "Hcs"),
        new Destruct("Hcs", {{"Hc", "Hcs"}}),
        new Subst(),
        new Apply("equiv_sym_state_refl"),
      }
    );
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivSimpleCall(StateInfo &si,
                                                                          ExecutionState &successor) {
  CallInst *callInst = dyn_cast<CallInst>(si.inst);
  Function *f = callInst->getCalledFunction();
  assert(f);

  /* target basic block */
  BasicBlock *bb = &f->getEntryBlock();

  assert(bbEntryLemmas.find(bb) != bbEntryLemmas.end());
  string bbEntryLemma = bbLemmas[bb];

  assert(bbDecompositionLemmas.find(bb) != bbDecompositionLemmas.end());
  string bbDecompositionLemma = bbDecompositionLemmas[bb];

  /* arguments for inversion_call */
  map<string, ref<CoqExpr>> kwargs;
  kwargs["d"] = moduleTranslator->translateFunctionCached(*f);

  if (callInst->getFunctionType()->getReturnType()->isVoidTy()) {
    return new Block(
      {
        new Apply("inversion_void_call", kwargs, "Hstep"),
        new Block(
          {
            new Destruct("Hstep", {{"b", "Hstep"}}),
            new Destruct("Hstep", {{"c'", "Hstep"}}),
            new Destruct("Hstep", {{"cs'", "Hstep"}}),
            new Destruct("Hstep", {{"ls'", "Hstep"}}),
            new Destruct("Hstep", {{"Hdc", "Hb"}}),
            new Destruct("Hb", {{"Hb", "Hcs"}}),
            new Destruct("Hcs", {{"Hcs", "Hls"}}),
            new Destruct("Hls", {{"Hls", "Heq"}}),
            new Apply(bbEntryLemma, "Hb"),
            new Subst(),
            new Apply(bbDecompositionLemma, "Hcs"),
            new Destruct("Hcs", {{"Hc", "Hcs"}}),
            new Apply("injection_some", "Hls"),
            new Subst(),
            new Apply("equiv_sym_state_refl"),
          }
        ),
        new Block({new Reflexivity()}),
      }
    );
  } else {
    return new Block(
      {
        new Apply("inversion_call", kwargs, "Hstep"),
        new Block(
          {
            new Destruct("Hstep", {{"b", "Hstep"}}),
            new Destruct("Hstep", {{"c'", "Hstep"}}),
            new Destruct("Hstep", {{"cs'", "Hstep"}}),
            new Destruct("Hstep", {{"ls'", "Hstep"}}),
            new Destruct("Hstep", {{"Hdc", "Hb"}}),
            new Destruct("Hb", {{"Hb", "Hcs"}}),
            new Destruct("Hcs", {{"Hcs", "Hls"}}),
            new Destruct("Hls", {{"Hls", "Heq"}}),
            new Apply(bbEntryLemma, "Hb"),
            new Subst(),
            new Apply(bbDecompositionLemma, "Hcs"),
            new Destruct("Hcs", {{"Hc", "Hcs"}}),
            new Subst(),
            new Apply("EquivSymState"),
            new Block(
              {
                new Apply(
                  "equiv_smt_store_via_some_injection",
                  {
                    createPlaceHolder(),
                    createPlaceHolder(),
                    createPlaceHolder(),
                    new CoqVariable("Hls"),
                  }
                ),
                new Apply("equiv_smt_store_refl"),
              }
            ),
            new Block({new Apply("equiv_sym_stack_refl")}),
            new Block({new Apply("equiv_smt_store_refl")}),
            new Block({new Apply("equiv_smt_expr_refl")}),
          }
        ),
        new Block({new Reflexivity()}),
      }
    );
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivReturn(StateInfo &si,
                                                                      ExecutionState &successor) {
  ReturnInst *returnInst = dyn_cast<ReturnInst>(si.inst);

  /* target instruction */
  Instruction *inst = successor.pc->inst;
  Function *f = inst->getParent()->getParent();

  assert(functionLemmas.find(f) != functionLemmas.end());
  string functionLemma = functionLemmas[f];

  if (returnInst->getReturnValue()) {
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
          new Apply(
            "equiv_smt_expr_via_some_injection",
            {
              createPlaceHolder(),
              createPlaceHolder(),
              new CoqVariable("Heval"),
            }
          ),
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
          new Apply("equiv_smt_expr_refl"),
        }
      );
    }
    return new Block(
      {
        new Apply("inversion_ret", "Hstep"),
        new Destruct("Hstep", {{"se", "Hstep"}}),
        new Destruct("Hstep", {{"d", "Hstep"}}),
        new Destruct("Hstep", {{"c'", "Hstep"}}),
        new Destruct("Hstep", {{"cs'", "Hstep"}}),
        new Destruct("Hstep", {{"Heval", "Hd"}}),
        new Destruct("Hd", {{"Hd", "Htrail"}}),
        new Destruct("Htrail", {{"Htrail", "Heq"}}),
        new Apply(functionLemma, "Hd"),
        new Subst(),
        /* TODO: add a lemma lazily to avoid this inversion */
        new Inversion("Htrail"),
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
        new Apply("inversion_ret_void", "Hstep"),
        new Destruct("Hstep", {{"d", "Hstep"}}),
        new Destruct("Hstep", {{"c'", "Hstep"}}),
        new Destruct("Hstep", {{"cs'", "Hstep"}}),
        new Destruct("Hstep", {{"Hd", "Htrail"}}),
        new Destruct("Htrail", {{"Htrail", "Heq"}}),
        new Apply(functionLemma, "Hd"),
        new Subst(),
        /* TODO: add a lemma lazily to avoid this inversion */
        new Inversion("Htrail"),
        new Subst(),
        new Apply("equiv_sym_state_refl"),
      }
    );
  }
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
