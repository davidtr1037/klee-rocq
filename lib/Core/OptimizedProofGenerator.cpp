#include "OptimizedProofGenerator.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ModuleTranslation.h"
#include "klee/Coq/ExprTranslation.h"
#include "klee/Module/KInstruction.h"

#include <string>

using namespace std;
using namespace llvm;
using namespace klee;

OptimizedProofGenerator::OptimizedProofGenerator(Module &m, raw_ostream &output)
  : ProofGenerator(m, output) {

}

void OptimizedProofGenerator::generateStaticDefs() {
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
  ref<CoqExpr> body = new CoqEq(
    new CoqApplication(
      new CoqVariable("find_function"),
      {
        new CoqVariable("mdl"),
        moduleTranslator->createName(f.getName().str()),
      }
    ),
    createSome(moduleTranslator->translateFunctionCached(f))
  );

  ref<CoqTactic> proof = new Block(
    {
      new Reflexivity(),
    }
  );

  return new CoqLemma(
    "L_" + f.getName().str(),
    body,
    proof
  );
}

string OptimizedProofGenerator::getFunctionLemmaName(Function &f) {
  auto i = functionLemmas.find(&f);
  assert(i != functionLemmas.end());
  return i->second;
}

klee::ref<CoqLemma> OptimizedProofGenerator::getBasicBlockLemma(BasicBlock &bb) {
  ref<CoqExpr> body = new CoqEq(
    new CoqApplication(
      new CoqVariable("fetch_block"),
      {
        moduleTranslator->translateFunctionCached(*bb.getParent()),
        moduleTranslator->createName(bb.getName().str()),
      }
    ),
    createSome(moduleTranslator->translateBasicBlockCached(bb))
  );

  ref<CoqTactic> proof = new Block(
    {
      new Reflexivity(),
    }
  );

  return new CoqLemma(
    "L_bb_" + to_string(moduleTranslator->getBasicBlockID(bb)),
    body,
    proof
  );
}

string OptimizedProofGenerator::getBasicBlockLemmaName(BasicBlock &bb) {
  auto i = bbLemmas.find(&bb);
  assert(i != bbLemmas.end());
  return i->second;
}

klee::ref<CoqLemma> OptimizedProofGenerator::getBasicBlockEntryLemma(BasicBlock &bb) {
  ref<CoqExpr> body = new CoqEq(
    new CoqApplication(
      new CoqVariable("entry_block"),
      {moduleTranslator->translateFunctionCached(*bb.getParent())}
    ),
    createSome(moduleTranslator->translateBasicBlockCached(bb))
  );

  ref<CoqTactic> proof = new Block(
    {
      new Reflexivity(),
    }
  );

  return new CoqLemma(
    "L_entry_bb_" + to_string(moduleTranslator->getBasicBlockID(bb)),
    body,
    proof
  );
}

string OptimizedProofGenerator::getBasicBlockEntryLemmaName(BasicBlock &bb) {
  auto i = bbEntryLemmas.find(&bb);
  assert(i != bbEntryLemmas.end());
  return i->second;
}

klee::ref<CoqLemma> OptimizedProofGenerator::getBasicBlockDecompositionLemma(BasicBlock &bb) {
  ref<CoqExpr> head = nullptr;
  std::vector<ref<CoqExpr>> tail;
  decomposeBasicBlock(bb, head, tail);

  ref<CoqExpr> body = new CoqEq(
    new CoqApplication(
      new CoqVariable("blk_cmds"),
      {moduleTranslator->translateBasicBlockCached(bb)}
    ),
    new CoqListCons(head, new CoqList(tail))
  );

  ref<CoqTactic> proof = new Block(
    {
      new Block({new Reflexivity()}),
    }
  );

  return new CoqLemma(
    "L_decompose_bb_" + to_string(moduleTranslator->getBasicBlockID(bb)),
    body,
    proof
  );
}

string OptimizedProofGenerator::getBasicBlockDecompositionLemmaName(BasicBlock &bb) {
  auto i = bbDecompositionLemmas.find(&bb);
  assert(i != bbDecompositionLemmas.end());
  return i->second;
}

void OptimizedProofGenerator::decomposeBasicBlock(BasicBlock &bb,
                                                  ref<CoqExpr> &head,
                                                  std::vector<ref<CoqExpr>> &tail) {
  head = nullptr;

  for (Instruction &inst : bb) {
    if (!moduleTranslator->isSupportedInst(inst)) {
      continue;
    }

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
    if (!moduleTranslator->isSupportedInst(inst)) {
      continue;
    }

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
                                                                   ExecutionState &successor,
                                                                   const ExternalProofHint &hint) {
  ref<CoqTactic> t = getTacticForSubtree(si, successor, hint);
  if (t) {
    return createLemma(si.stepID, t);
  }

  return ProofGenerator::createLemmaForSubtree(si, successor, hint);
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtree(StateInfo &si,
                                                                  ExecutionState &successor,
                                                                  const ExternalProofHint &hint) {
  if (moduleTranslator->isAssignment(*si.inst)) {
    return getTacticForSubtreeAssignment(si, successor, hint);
  }

  if (isa<PHINode>(si.inst)) {
    return getTacticForSubtreePHI(si, successor);
  }

  if (isa<BranchInst>(si.inst)) {
    return getTacticForSubtreeBranch(si, successor);
  }

  if (isa<CallInst>(si.inst)) {
    if (ModuleTranslator::isMakeSymbolicInt32(si.inst)) {
      return nullptr;
    }
    if (ModuleTranslator::isAssumeBool(si.inst)) {
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
                                                                            ExecutionState &successor,
                                                                            const ExternalProofHint &hint) {
  if (moduleSupport->isUnsafeInstruction(*si.inst)) {
    return getTacticForUnsafeOperation(si, successor, hint);
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

  if (isa<CastInst>(si.inst)) {
    CastInst *ci = cast<CastInst>(si.inst);
    var = moduleTranslator->translateCastInstName(ci);
    expr = moduleTranslator->translateCastInstExpr(ci);
  }

  ref<CoqTactic> exprTactic = moduleSupport->getTacticForAssignmentExprCached(*si.inst);
  assert(!exprTactic.isNull());

  assert(var && expr);
  return new Block(
    {
      new Apply(
        "safe_subtree_instr_op",
        {
          stateTranslator->getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(si.inst)),
          var,
          expr,
          createPlaceHolder(),
          createPlaceHolder(),
          stateTranslator->getPrevBIDAlias(si.stepID),
          stateTranslator->getLocalStoreAlias(si.stepID),
          stateTranslator->getStackAlias(si.stepID),
          stateTranslator->createGlobalStore(),
          stateTranslator->getSymbolicsAlias(si.stepID),
          stateTranslator->getPCAlias(si.stepID),
          stateTranslator->createModule(),
          stateTranslator->getLocalStoreAlias(successor.stepID),
          getTreeAlias(successor.stepID),
        }
      ),
      exprTactic, /* is_supported_exp */
      getTacticForEquivStore(si),
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(successor.stepID))}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForUnsafeOperation(StateInfo &si,
                                                                          ExecutionState &successor,
                                                                          const ExternalProofHint &hint) {
  BinaryOperator *bo = cast<BinaryOperator>(si.inst);
  Value *v1 = bo->getOperand(0);
  Value *v2 = bo->getOperand(1);

  ref<CoqTactic> t1 = moduleSupport->getTacticForValueCached(v1);
  ref<CoqTactic> t2 = moduleSupport->getTacticForValueCached(v2);

  ref<CoqTactic> unsatTactic = getTacticForErrorCondition(si, successor, hint);
  assert(!unsatTactic.isNull());

  ref<CoqExpr> ast2 = new CoqApplication(
    new CoqVariable("extract_smt_expr"),
    {
      new CoqApplication(
        new CoqVariable("sym_eval_exp"),
        {
          stateTranslator->getLocalStoreAlias(si.stepID),
          stateTranslator->createGlobalStore(),
          createSome(moduleTranslator->translateType(v2->getType())),
          moduleTranslator->translateValue(v2),
        }
      ),
    }
  );

  if (bo->getOpcode() == Instruction::SDiv) {
    ref<CoqExpr> ast1 = new CoqApplication(
      new CoqVariable("extract_smt_expr"),
      {
        new CoqApplication(
          new CoqVariable("sym_eval_exp"),
          {
            stateTranslator->getLocalStoreAlias(si.stepID),
            stateTranslator->createGlobalStore(),
            createSome(moduleTranslator->translateType(v2->getType())),
            moduleTranslator->translateValue(v1),
          }
        ),
      }
    );

    return new Block(
      {
        new Apply(
          "safe_subtree_instr_op_sdiv",
          {
            stateTranslator->getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(si.inst)),
            createPlaceHolder(), /* var */
            createPlaceHolder(), /* optional type */
            createPlaceHolder(), /* e1 */
            createPlaceHolder(), /* e2 */
            createPlaceHolder(),
            createPlaceHolder(),
            stateTranslator->getPrevBIDAlias(si.stepID),
            stateTranslator->getLocalStoreAlias(si.stepID),
            stateTranslator->getStackAlias(si.stepID),
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(si.stepID),
            stateTranslator->getPCAlias(si.stepID),
            stateTranslator->createModule(),
            stateTranslator->getLocalStoreAlias(successor.stepID),
            ast1,
            ast2,
            getTreeAlias(successor.stepID),
          }
        ),
        t1, /* is_supported_exp e1 */
        t2, /* is_supported_exp e2 */
        getTacticForEquivStore(si),
        new Block({new Reflexivity()}),
        new Block({new Reflexivity()}),
        unsatTactic, /* unsat */
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(successor.stepID))}),
      }
    );
  }

  std::string lemmaName;
  switch (bo->getOpcode()) {
  case Instruction::UDiv:
    lemmaName = "safe_subtree_instr_op_udiv";
    break;

  case Instruction::URem:
    lemmaName = "safe_subtree_instr_op_urem";
    break;

  case Instruction::SRem:
    lemmaName = "safe_subtree_instr_op_srem";
    break;

  case Instruction::Shl:
    lemmaName = "safe_subtree_instr_op_shl";
    break;

  case Instruction::LShr:
    lemmaName = "safe_subtree_instr_op_lshr";
    break;

  case Instruction::AShr:
    lemmaName = "safe_subtree_instr_op_ashr";
    break;

  default:
    assert(false);
  }

  return new Block(
    {
      new Apply(
        lemmaName,
        {
          stateTranslator->getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(si.inst)),
          createPlaceHolder(), /* var */
          createPlaceHolder(), /* optional type */
          createPlaceHolder(), /* e1 */
          createPlaceHolder(), /* e2 */
          createPlaceHolder(),
          createPlaceHolder(),
          stateTranslator->getPrevBIDAlias(si.stepID),
          stateTranslator->getLocalStoreAlias(si.stepID),
          stateTranslator->getStackAlias(si.stepID),
          stateTranslator->createGlobalStore(),
          stateTranslator->getSymbolicsAlias(si.stepID),
          stateTranslator->getPCAlias(si.stepID),
          stateTranslator->createModule(),
          stateTranslator->getLocalStoreAlias(successor.stepID),
          ast2,
          getTreeAlias(successor.stepID),
        }
      ),
      t1, /* is_supported_exp e1 */
      t2, /* is_supported_exp e2 */
      getTacticForEquivStore(si),
      new Block({new Reflexivity()}),
      unsatTactic, /* unsat */
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(successor.stepID))}),
    }
  );
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForErrorCondition(StateInfo &si,
                                                                         ExecutionState &successor,
                                                                         const ExternalProofHint &hint) {
  BinaryOperator *bo = cast<BinaryOperator>(si.inst);
  Value *v2 = bo->getOperand(1);

  if (bo->getOpcode() == Instruction::SDiv) {
    return new Block({new Admit()});
  }

  std::string lemmaName;
  switch (bo->getOpcode()) {
  case Instruction::UDiv:
  case Instruction::URem:
  case Instruction::SRem:
    lemmaName = "unsat_div_condition_bv32";
    break;

  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
    lemmaName = "unsat_shift_condition_bv32";
    break;

  default:
    assert(false);
  }

  if (isa<ConstantInt>(v2)) {
    return new Block(
      {
        new Apply("unsat_and_right"),
        new Apply("unsat_false"),
      }
    );
  } else {
    /* in this case, we are supposed to pass through klee_div_zero_check */
    assert(!hint.lastUnsatAxiomName.empty());
    return new Block(
      {
        new Concat(
          {
            /* this block should come first, otherwise the failing tactic is slow... */
            new Try(
              {
                new Apply(lemmaName),
                new Apply(hint.lastUnsatAxiomName),
              }
            ),
            new Try(
              {
                new Apply("unsat_and_right"),
                new Apply("unsat_false"),
              }
            ),
          }
        )
      }
    );
  }
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
        new Apply(
          "equiv_smt_store_on_update",
          {
            stateTranslator->getLocalStoreAlias(si.stepID),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
          }
        ),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }

  return new Block(
    {
      new Apply(
        "safe_subtree_phi",
        {
          stateTranslator->getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(phi)),
          moduleTranslator->translatePHINodeName(phi),
          moduleTranslator->translatePHINodeType(phi),
          moduleTranslator->translatePHINodeArgs(phi),
          createPlaceHolder(),
          createPlaceHolder(),
          createPlaceHolder(), /* TODO: pass argument */
          stateTranslator->getLocalStoreAlias(si.stepID),
          stateTranslator->getStackAlias(si.stepID),
          stateTranslator->createGlobalStore(),
          stateTranslator->getSymbolicsAlias(si.stepID),
          stateTranslator->getPCAlias(si.stepID),
          stateTranslator->createModule(),
          stateTranslator->getLocalStoreAlias(successor.stepID),
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
          stateTranslator->getICAlias(si.stepID),
          createNat(moduleTranslator->getInstID(bi)),
          moduleTranslator->translateBranchInstBid(bi, 0),
          stateTranslator->getPrevBIDAlias(si.stepID),
          stateTranslator->getLocalStoreAlias(si.stepID),
          stateTranslator->getStackAlias(si.stepID),
          stateTranslator->createGlobalStore(),
          stateTranslator->getSymbolicsAlias(si.stepID),
          stateTranslator->getPCAlias(si.stepID),
          stateTranslator->createModule(),
          moduleTranslator->translateFunctionCached(*f),
          moduleTranslator->translateBasicBlockCached(*targetBB),
          stateTranslator->getCommandAlias(successor.stepID),
          stateTranslator->getCommandsAlias(successor.stepID),
          getTreeAlias(successor.stepID),
        }
      ),
      new Block({new Apply(getFunctionLemmaName(*f))}),
      new Block({new Apply(getBasicBlockLemmaName(*targetBB))}),
      new Block({new Apply(getBasicBlockDecompositionLemmaName(*targetBB))}),
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
            stateTranslator->getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(callInst)),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            stateTranslator->getPrevBIDAlias(si.stepID),
            stateTranslator->getLocalStoreAlias(si.stepID),
            stateTranslator->getStackAlias(si.stepID),
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(si.stepID),
            stateTranslator->getPCAlias(si.stepID),
            stateTranslator->createModule(),
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*bb),
            head,
            new CoqList(tail),
            stateTranslator->getLocalStoreAlias(successor.stepID),
            getTreeAlias(successor.stepID),
          }
        ),
        new Block(
          {
            new Intros({"H"}),
            new Discriminate("H"),
          }
        ),
        new Block({new Apply(getFunctionLemmaName(*f))}),
        new Block({new Reflexivity()}), /* TODO: optimize? */
        new Block({new Apply(getBasicBlockEntryLemmaName(*bb))}),
        new Block({new Apply(getBasicBlockDecompositionLemmaName(*bb))}),
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
            stateTranslator->getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(callInst)),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            stateTranslator->getPrevBIDAlias(si.stepID),
            stateTranslator->getLocalStoreAlias(si.stepID),
            stateTranslator->getStackAlias(si.stepID),
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(si.stepID),
            stateTranslator->getPCAlias(si.stepID),
            stateTranslator->createModule(),
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*bb),
            head,
            new CoqList(tail),
            stateTranslator->getLocalStoreAlias(successor.stepID),
            getTreeAlias(successor.stepID),
          }
        ),
        new Block({new Apply(getFunctionLemmaName(*f))}),
        new Block({new Reflexivity()}), /* TODO: optimize? */
        new Block({new Apply(getBasicBlockEntryLemmaName(*bb))}),
        new Block({new Apply(getBasicBlockDecompositionLemmaName(*bb))}),
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
            stateTranslator->getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(returnInst)),
            moduleTranslator->translateReturnInstType(returnInst),
            moduleTranslator->translateReturnInstExpr(returnInst),
            stateTranslator->getPrevBIDAlias(si.stepID),
            stateTranslator->getLocalStoreAlias(si.stepID),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(), /* TODO: pass stack */
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(si.stepID),
            stateTranslator->getPCAlias(si.stepID),
            stateTranslator->createModule(),
            moduleTranslator->translateFunctionCached(*f),
            head,
            new CoqList(tail),
            stateTranslator->getLocalStoreAlias(successor.stepID),
            getTreeAlias(successor.stepID),
          }
        ),
        t,
        new Block({new Apply(getFunctionLemmaName(*f))}),
        new Block({new Reflexivity()}), /* TODO: define lemma */
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
            stateTranslator->getICAlias(si.stepID),
            createNat(moduleTranslator->getInstID(returnInst)),
            stateTranslator->getPrevBIDAlias(si.stepID),
            stateTranslator->getLocalStoreAlias(si.stepID),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(), /* TODO: pass stack */
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(si.stepID),
            stateTranslator->getPCAlias(si.stepID),
            stateTranslator->createModule(),
            moduleTranslator->translateFunctionCached(*f),
            head,
            new CoqList(tail),
            getTreeAlias(successor.stepID),
          }
        ),
        new Block({new Apply(getFunctionLemmaName(*f))}),
        new Block({new Reflexivity()}), /* TODO: define lemma */
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(successor.stepID))}),
      }
    );
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForEquivStore(StateInfo &si) {
  if (si.wasRegisterUpdated) {
    return new Block(
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
    return new Block(
      {
        new Apply(
          "equiv_smt_store_on_update",
          {
            stateTranslator->getLocalStoreAlias(si.stepID),
            createPlaceHolder(),
            createPlaceHolder(),
            createPlaceHolder(),
          }
        ),
        new Apply("equiv_smt_expr_normalize_simplify"),
      }
    );
  }
}

klee::ref<CoqLemma> OptimizedProofGenerator::createLemmaForSubtree(StateInfo &stateInfo,
                                                                   SuccessorInfo &si1,
                                                                   SuccessorInfo &si2,
                                                                   ProofGenerationOutput &output) {
  ref<CoqTactic> t = getTacticForSubtree(stateInfo, si1, si2, output);
  if (t) {
    return createLemma(stateInfo.stepID, t);
  } else {
    return ProofGenerator::createLemmaForSubtree(stateInfo, si1, si2, output);
  }
}

klee::ref<CoqTactic> OptimizedProofGenerator::getTacticForSubtree(StateInfo &stateInfo,
                                                                  SuccessorInfo &si1,
                                                                  SuccessorInfo &si2,
                                                                  ProofGenerationOutput &output) {
  BranchInst *bi = dyn_cast<BranchInst>(stateInfo.inst);
  assert(bi && bi->isConditional());

  BasicBlock *bb = bi->getParent();
  Function *f = bb->getParent();

  assert(functionLemmas.find(f) != functionLemmas.end());
  string functionLemma = functionLemmas[f];

  ref<CoqExpr> cond = new CoqApplication(
    new CoqVariable("extract_ast"),
    {
      new CoqApplication(
        new CoqVariable("sym_eval_exp"),
        {
          stateTranslator->getLocalStoreAlias(stateInfo.stepID),
          stateTranslator->createGlobalStore(),
          createSome(moduleTranslator->createTypeI(1)),
          moduleTranslator->translateBranchInstExpr(bi),
        }
      ),
    }
  );

  if (si1.isSat && !si2.isSat) {
    ref<CoqExpr> unsatPC = exprTranslator->translate(si2.unsatPC,
                                                     &si1.state->arrayTranslation,
                                                     true);
    uint64_t axiomID = allocateAxiomID();
    ref<CoqLemma> lemma = getUnsatAxiom(unsatPC, axiomID);
    unsatAxioms.push_front(lemma);
    output.unsatAxiomName = lemma->name;

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
          new Block({new Apply(createUnsatAxiomName(axiomID))}),
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
            stateTranslator->getICAlias(stateInfo.stepID),
            createNat(moduleTranslator->getInstID(bi)),
            moduleTranslator->translateBranchInstExpr(bi),
            moduleTranslator->translateBranchInstBid(bi, 0),
            moduleTranslator->translateBranchInstBid(bi, 1),
            stateTranslator->getPrevBIDAlias(stateInfo.stepID),
            stateTranslator->getLocalStoreAlias(stateInfo.stepID),
            stateTranslator->getStackAlias(stateInfo.stepID),
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(stateInfo.stepID),
            stateTranslator->getPCAlias(stateInfo.stepID),
            stateTranslator->createModule(),
            cond,
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*targetBB),
            stateTranslator->getCommandAlias(si1.state->stepID),
            stateTranslator->getCommandsAlias(si1.state->stepID),
            stateTranslator->getPCAlias(si1.state->stepID),
            unsatPC,
            getTreeAlias(si1.state->stepID),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Apply(getFunctionLemmaName(*f))}),
        new Block({new Apply(getBasicBlockLemmaName(*targetBB))}),
        new Block({new Apply(getBasicBlockDecompositionLemmaName(*targetBB))}),
        new Block({new Reflexivity()}),
        new Block({new Apply("L_" + to_string(si1.state->stepID))}),
        t,
        new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
        new Block({new Apply(createUnsatAxiomName(axiomID))}),
      }
    );
  }

  if (!si1.isSat && si2.isSat) {
    ref<CoqExpr> unsatPC = exprTranslator->translate(si1.unsatPC,
                                                     &si2.state->arrayTranslation,
                                                     true);
    uint64_t axiomID = allocateAxiomID();
    ref<CoqLemma> lemma = getUnsatAxiom(unsatPC, axiomID);
    unsatAxioms.push_front(lemma);
    output.unsatAxiomName = lemma->name;

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
          new Block({new Apply(createUnsatAxiomName(axiomID))}),
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
            stateTranslator->getICAlias(stateInfo.stepID),
            createNat(moduleTranslator->getInstID(bi)),
            moduleTranslator->translateBranchInstExpr(bi),
            moduleTranslator->translateBranchInstBid(bi, 0),
            moduleTranslator->translateBranchInstBid(bi, 1),
            stateTranslator->getPrevBIDAlias(stateInfo.stepID),
            stateTranslator->getLocalStoreAlias(stateInfo.stepID),
            stateTranslator->getStackAlias(stateInfo.stepID),
            stateTranslator->createGlobalStore(),
            stateTranslator->getSymbolicsAlias(stateInfo.stepID),
            stateTranslator->getPCAlias(stateInfo.stepID),
            stateTranslator->createModule(),
            cond,
            moduleTranslator->translateFunctionCached(*f),
            moduleTranslator->translateBasicBlockCached(*targetBB),
            stateTranslator->getCommandAlias(si2.state->stepID),
            stateTranslator->getCommandsAlias(si2.state->stepID),
            stateTranslator->getPCAlias(si2.state->stepID),
            unsatPC,
            getTreeAlias(si2.state->stepID),
          }
        ),
        new Block({new Reflexivity()}),
        new Block({new Apply(getFunctionLemmaName(*f))}),
        new Block({new Apply(getBasicBlockLemmaName(*targetBB))}),
        new Block({new Apply(getBasicBlockDecompositionLemmaName(*targetBB))}),
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
          stateTranslator->getICAlias(stateInfo.stepID),
          createNat(moduleTranslator->getInstID(bi)),
          moduleTranslator->translateBranchInstExpr(bi),
          moduleTranslator->translateBranchInstBid(bi, 0),
          moduleTranslator->translateBranchInstBid(bi, 1),
          stateTranslator->getPrevBIDAlias(stateInfo.stepID),
          stateTranslator->getLocalStoreAlias(stateInfo.stepID),
          stateTranslator->getStackAlias(stateInfo.stepID),
          stateTranslator->createGlobalStore(),
          stateTranslator->getSymbolicsAlias(stateInfo.stepID),
          stateTranslator->getPCAlias(stateInfo.stepID),
          stateTranslator->createModule(),
          cond,
          moduleTranslator->translateFunctionCached(*f),
          moduleTranslator->translateBasicBlockCached(*bb1),
          stateTranslator->getCommandAlias(si1.state->stepID),
          stateTranslator->getCommandsAlias(si1.state->stepID),
          stateTranslator->getPCAlias(si1.state->stepID),
          moduleTranslator->translateBasicBlockCached(*bb2),
          stateTranslator->getCommandAlias(si2.state->stepID),
          stateTranslator->getCommandsAlias(si2.state->stepID),
          stateTranslator->getPCAlias(si2.state->stepID),
          getTreeAlias(si1.state->stepID),
          getTreeAlias(si2.state->stepID),
        }
      ),
      new Block({new Reflexivity()}),
      new Block({new Apply(getFunctionLemmaName(*f))}),
      new Block({new Apply(getBasicBlockLemmaName(*bb1))}),
      new Block({new Apply(getBasicBlockDecompositionLemmaName(*bb1))}),
      new Block({new Apply(getBasicBlockLemmaName(*bb2))}),
      new Block({new Apply(getBasicBlockDecompositionLemmaName(*bb2))}),
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(si1.state->stepID))}),
      new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
      new Block({new Reflexivity()}),
      new Block({new Apply("L_" + to_string(si2.state->stepID))}),
      new Block({new Apply("equiv_smt_expr_normalize_simplify")}),
    }
  );
}
