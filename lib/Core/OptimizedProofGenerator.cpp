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
  decomposeBasicBlock(bb, head, tail);

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

void OptimizedProofGenerator::decomposeBasicBlock(BasicBlock &bb,
                                                  ref<CoqExpr> &head,
                                                  std::vector<ref<CoqExpr>> &tail) {
  head = nullptr;

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
}

void OptimizedProofGenerator::decomposeBasicBlockFrom(BasicBlock &bb,
                                                      Instruction &from,
                                                      ref<CoqExpr> &head,
                                                      std::vector<ref<CoqExpr>> &tail) {
  head = nullptr;

  for (Instruction &inst : bb) {
    if (&inst == &from) {
      head = moduleTranslator->translateInstCached(inst);
    } else {
      if (head) {
        ref<CoqExpr> coqInst = moduleTranslator->translateInstCached(inst);
        if (coqInst) {
          tail.push_back(coqInst);
        } else {
          assert(false);
        }
      }
    }
  }
}

klee::ref<CoqLemma> OptimizedProofGenerator::createLemmaForSubtree(StateInfo &si,
                                                                   ExecutionState &successor) {
  ref<CoqTactic> t = getTacticForSubtree(si, successor);
  if (t) {
    return createLemma(si.stepID, t);
  }

  return ProofGenerator::createLemmaForSubtree(si, successor);
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtree(StateInfo &si,
                                                                  ExecutionState &successor) {
  if (isa<BinaryOperator>(si.inst) || isa<CmpInst>(si.inst)) {
    return getTacticForSubtreeAssignment(si, successor);
  }

  if (isa<PHINode>(si.inst)) {
    return getTacticForSubtreePHI(si, successor);
  }

  if (isa<BranchInst>(si.inst)) {
    return getTacticForSubtreeBranch(si, successor);
  }

  if (isa<CallInst>(si.inst)) {
    if (isMakeSymbolicInt32(si.inst)) {
      return nullptr;
    }
    if (isAssumeBool(si.inst)) {
      return nullptr;
    }
    return getTacticForSubtreeCall(si, successor);
  }

  if (isa<ReturnInst>(si.inst)) {
    return getTacticForSubtreeReturn(si, successor);
  }

  return nullptr;
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtreeAssignment(StateInfo &si,
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
        new Apply("equiv_smt_store_on_update"),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }

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
        "safe_subtree_instr_op",
        {
          getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(si.inst)),
          var,
          expr,
          createPlaceHolder(),
          createPlaceHolder(),
          getPrevBIDAlias(si.stepID),
          getLocalStoreAlias(si.stepID),
          getStackAlias(si.stepID),
          createGlobalStore(),
          getSymbolicsAlias(si.stepID),
          getPCAlias(si.stepID),
          createModule(),
          getLocalStoreAlias(successor.stepID),
          getTreeAlias(successor.stepID),
        }
      ),
      t,
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(successor.stepID))}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtreePHI(StateInfo &si,
                                                                     ExecutionState &successor) {
  PHINode *phi = dyn_cast<PHINode>(si.inst);
  assert(phi);

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
        new Apply("equiv_smt_store_on_update"),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }

  return new Block(
    {
      new Apply(
        "safe_subtree_phi",
        {
          getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(phi)),
          moduleTranslator->translatePHINodeName(phi),
          moduleTranslator->translatePHINodeType(phi),
          moduleTranslator->translatePHINodeArgs(phi),
          createPlaceHolder(),
          createPlaceHolder(),
          createPlaceHolder(), /* TODO: pass argument */
          getLocalStoreAlias(si.stepID),
          getStackAlias(si.stepID),
          createGlobalStore(),
          getSymbolicsAlias(si.stepID),
          getPCAlias(si.stepID),
          createModule(),
          getLocalStoreAlias(successor.stepID),
          getTreeAlias(successor.stepID),
        }
      ),
      t,
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(successor.stepID))}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtreeBranch(StateInfo &si,
                                                                        ExecutionState &successor) {
  BranchInst *bi = cast<BranchInst>(si.inst);
  assert(bi && !bi->isConditional());
  BasicBlock *bb = bi->getParent();
  Function *f = bb->getParent();
  BasicBlock *targetBB = bi->getSuccessor(0);

  return new Block(
    {
      new Apply(
        "safe_subtree_unconditional_br",
        {
          getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(bi)),
          moduleTranslator->translateBranchInstBid(bi, 0),
          getPrevBIDAlias(si.stepID),
          getLocalStoreAlias(si.stepID),
          getStackAlias(si.stepID),
          createGlobalStore(),
          getSymbolicsAlias(si.stepID),
          getPCAlias(si.stepID),
          createModule(),
          moduleTranslator->translateFunctionCached(*f),
          moduleTranslator->translateBasicBlockCached(*targetBB),
          getCommandAlias(successor.stepID),
          getCommandsAlias(successor.stepID),
          getTreeAlias(successor.stepID),
        }
      ),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(successor.stepID))}),
    }
  );
}

/* TODO: pass arguments */
klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtreeCall(StateInfo &si,
                                                                      ExecutionState &successor) {
  CallInst *callInst = dyn_cast<CallInst>(si.inst);
  assert(callInst);

  Function *f = callInst->getCalledFunction();
  assert(f);

  /* entry basic block */
  BasicBlock *bb = &f->getEntryBlock();

  /* decompose */
  ref<CoqExpr> head = nullptr;
  std::vector<ref<CoqExpr>> tail;
  decomposeBasicBlock(*bb, head, tail);

  if (callInst->getFunctionType()->getReturnType()->isVoidTy()) {
    return new Block(
      {
        new Apply(
          "safe_subtree_void_call",
          {
            getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(callInst)),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            getPrevBIDAlias(si.stepID),
            getLocalStoreAlias(si.stepID),
            getStackAlias(si.stepID),
            createGlobalStore(),
            getSymbolicsAlias(si.stepID),
            getPCAlias(si.stepID),
            createModule(),
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*bb),
            head,
            new CoqList(tail),
            getLocalStoreAlias(successor.stepID),
            getTreeAlias(successor.stepID),
          }
        ),
        new Block(
          {
            new Intros({"H"}),
            new Discriminate("H"),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(successor.stepID))}),
      }
    );
  } else {
    return new Block(
      {
        new Apply(
          "safe_subtree_call",
          {
            getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(callInst)),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            getPrevBIDAlias(si.stepID),
            getLocalStoreAlias(si.stepID),
            getStackAlias(si.stepID),
            createGlobalStore(),
            getSymbolicsAlias(si.stepID),
            getPCAlias(si.stepID),
            createModule(),
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*bb),
            head,
            new CoqList(tail),
            getLocalStoreAlias(successor.stepID),
            getTreeAlias(successor.stepID),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(successor.stepID))}),
      }
    );
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtreeReturn(StateInfo &si,
                                                                        ExecutionState &successor) {
  ReturnInst *returnInst = dyn_cast<ReturnInst>(si.inst);
  assert(returnInst);

  /* target instruction */
  Instruction *inst = successor.pc->inst;
  BasicBlock *bb = inst->getParent();
  Function *f = inst->getParent()->getParent();

  ref<CoqExpr> head = nullptr;
  vector<ref<CoqExpr>> tail;
  decomposeBasicBlockFrom(*bb, *inst, head, tail);

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
          new Apply("equiv_smt_expr_refl"),
        }
      );
    } else {
      t = new Block({new Apply("equiv_smt_store_refl")});
    }

    return new Block(
      {
        new Apply(
          "safe_subtree_ret",
          {
            getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(returnInst)),
            moduleTranslator->translateReturnInstType(returnInst),
            moduleTranslator->translateReturnInstExpr(returnInst),
            getPrevBIDAlias(si.stepID),
            getLocalStoreAlias(si.stepID),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(), /* TODO: pass stack */
            createGlobalStore(),
            getSymbolicsAlias(si.stepID),
            getPCAlias(si.stepID),
            createModule(),
            moduleTranslator->translateFunctionCached(*f),
            head,
            new CoqList(tail),
            getLocalStoreAlias(successor.stepID),
            getTreeAlias(successor.stepID),
          }
        ),
        t,
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(successor.stepID))}),
      }
    );
  } else {
    return new Block(
      {
        new Apply(
          "safe_subtree_ret_void",
          {
            getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(returnInst)),
            getPrevBIDAlias(si.stepID),
            getLocalStoreAlias(si.stepID),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(), /* TODO: pass stack */
            createGlobalStore(),
            getSymbolicsAlias(si.stepID),
            getPCAlias(si.stepID),
            createModule(),
            moduleTranslator->translateFunctionCached(*f),
            head,
            new CoqList(tail),
            getTreeAlias(successor.stepID),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(successor.stepID))}),
      }
    );
  }
}

klee::ref<CoqLemma> OptimizedProofGenerator::createLemmaForSubtree(StateInfo &stateInfo,
                                                                   SuccessorInfo &si1,
                                                                   SuccessorInfo &si2) {
  ref<CoqTactic> t = getTacticForSubtree(stateInfo, si1, si2);
  if (t) {
    return createLemma(stateInfo.stepID, t);
  } else {
    return ProofGenerator::createLemmaForSubtree(stateInfo, si1, si2);
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtree(StateInfo &stateInfo,
                                                                  SuccessorInfo &si1,
                                                                  SuccessorInfo &si2) {
  BranchInst *bi = dyn_cast<BranchInst>(stateInfo.inst);
  assert(bi && bi->isConditional());

  BasicBlock *bb = bi->getParent();
  Function *f = bb->getParent();

  ref<CoqExpr> cond = new CoqApplication(
    new CoqVariable("extract_ast"),
    {
      new CoqApplication(
        new CoqVariable("sym_eval_exp"),
        {
          getLocalStoreAlias(stateInfo.stepID),
          createGlobalStore(),
          createSome(moduleTranslator->createTypeI(1)),
          moduleTranslator->translateBranchInstExpr(bi),
        }
      ),
    }
  );

  if (si1.isSat && !si2.isSat) {
    ref<CoqExpr> satPC = exprTranslator->translate(si1.satPC,
                                                   &si1.state->arrayTranslation);
    ref<CoqExpr> unsatPC = exprTranslator->translate(si2.unsatPC,
                                                     &si1.state->arrayTranslation);
    uint64_t axiomID = allocateAxiomID();
    ref<CoqLemma> lemma = getUnsatAxiom(unsatPC, axiomID);
    unsatAxioms.push_front(lemma);

    Instruction *targetInst = si1.state->pc->inst;
    BasicBlock *targetBB = targetInst->getParent();

    ref<CoqTactic> t;
    if (!isa<ConstantExpr>(stateInfo.branchCondition)) {
      t = new Block(
        {
          new Apply(
            "implied_condition",
            {
              createPlaceHolder(),
              createPlaceHolder(),
              unsatPC,
            }
          ),
          new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
          new Block({new Apply("UNSAT_" + to_string(axiomID))}),
        }
      );
    } else {
      t = new Block({new Apply("equiv_smt_expr_normalize_simplify")});
    }

    return new Block(
      {
        new Apply(
          "safe_subtree_br_sat_unsat",
          {
            getICAlias(stateInfo.stepID),
            createNat(moduleTranslator->getInstID(bi)),
            moduleTranslator->translateBranchInstExpr(bi),
            moduleTranslator->translateBranchInstBid(bi, 0),
            moduleTranslator->translateBranchInstBid(bi, 1),
            getPrevBIDAlias(stateInfo.stepID),
            getLocalStoreAlias(stateInfo.stepID),
            getStackAlias(stateInfo.stepID),
            createGlobalStore(),
            getSymbolicsAlias(stateInfo.stepID),
            getPCAlias(stateInfo.stepID),
            createModule(),
            cond,
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*targetBB),
            getCommandAlias(si1.state->stepID),
            getCommandsAlias(si1.state->stepID),
            getPCAlias(si1.state->stepID),
            unsatPC,
            getTreeAlias(si1.state->stepID),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(si1.state->stepID))}),
        t,
        new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
        new Block({new Apply("UNSAT_" + to_string(axiomID))}),
      }
    );
  }

  if (!si1.isSat && si2.isSat) {
    ref<CoqExpr> satPC = exprTranslator->translate(si2.satPC,
                                                   &si2.state->arrayTranslation);
    ref<CoqExpr> unsatPC = exprTranslator->translate(si1.unsatPC,
                                                     &si2.state->arrayTranslation);
    uint64_t axiomID = allocateAxiomID();
    ref<CoqLemma> lemma = getUnsatAxiom(unsatPC, axiomID);
    unsatAxioms.push_front(lemma);

    Instruction *targetInst = si2.state->pc->inst;
    BasicBlock *targetBB = targetInst->getParent();

    ref<CoqTactic> t;
    if (!isa<ConstantExpr>(stateInfo.branchCondition)) {
      t = new Block(
        {
          new Apply(
            "implied_negated_condition",
            {
              createPlaceHolder(),
              createPlaceHolder(),
              unsatPC,
            }
          ),
          new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
          new Block({new Apply("UNSAT_" + to_string(axiomID))}),
        }
      );
    } else {
      t = new Block({new Apply("equiv_smt_expr_normalize_simplify")});
    }

    return new Block(
      {
        new Apply(
          "safe_subtree_br_unsat_sat",
          {
            getICAlias(stateInfo.stepID),
            createNat(moduleTranslator->getInstID(bi)),
            moduleTranslator->translateBranchInstExpr(bi),
            moduleTranslator->translateBranchInstBid(bi, 0),
            moduleTranslator->translateBranchInstBid(bi, 1),
            getPrevBIDAlias(stateInfo.stepID),
            getLocalStoreAlias(stateInfo.stepID),
            getStackAlias(stateInfo.stepID),
            createGlobalStore(),
            getSymbolicsAlias(stateInfo.stepID),
            getPCAlias(stateInfo.stepID),
            createModule(),
            cond,
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*targetBB),
            getCommandAlias(si2.state->stepID),
            getCommandsAlias(si2.state->stepID),
            getPCAlias(si2.state->stepID),
            unsatPC,
            getTreeAlias(si2.state->stepID),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(si2.state->stepID))}),
        t,
        new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
        new Block({new Apply("UNSAT_" + to_string(axiomID))}),
      }
    );
  }

  Instruction *inst1 = si1.state->pc->inst;
  BasicBlock *bb1 = inst1->getParent();
  Instruction *inst2 = si2.state->pc->inst;
  BasicBlock *bb2 = inst2->getParent();

  return new Block(
    {
      new Apply(
        "safe_subtree_br_fork",
        {
          getICAlias(stateInfo.stepID),
          createNat(moduleTranslator->getInstID(bi)),
          moduleTranslator->translateBranchInstExpr(bi),
          moduleTranslator->translateBranchInstBid(bi, 0),
          moduleTranslator->translateBranchInstBid(bi, 1),
          getPrevBIDAlias(stateInfo.stepID),
          getLocalStoreAlias(stateInfo.stepID),
          getStackAlias(stateInfo.stepID),
          createGlobalStore(),
          getSymbolicsAlias(stateInfo.stepID),
          getPCAlias(stateInfo.stepID),
          createModule(),
          cond,
          moduleTranslator->translateFunctionCached(*f),
          moduleTranslator->translateBasicBlockCached(*bb1),
          getCommandAlias(si1.state->stepID),
          getCommandsAlias(si1.state->stepID),
          getPCAlias(si1.state->stepID),
          moduleTranslator->translateBasicBlockCached(*bb2),
          getCommandAlias(si2.state->stepID),
          getCommandsAlias(si2.state->stepID),
          getPCAlias(si2.state->stepID),
          getTreeAlias(si1.state->stepID),
          getTreeAlias(si2.state->stepID),
        }
      ),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(si1.state->stepID))}),
      new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(si2.state->stepID))}),
      new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
    }
  );
}
