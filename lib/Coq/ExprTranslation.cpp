#include "klee/Support/ErrorHandling.h"
#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/ExprTranslation.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace klee;

ExprTranslator::ExprTranslator() {

}

ref<CoqExpr> ExprTranslator::translateAsSMTExprCached(ref<Expr> e,
                                                      ArrayTranslation *m) {
  ref<CoqExpr> coqAST = translateCached(e, m);
  if (coqAST.isNull()) {
    return nullptr;
  }

  /* TODO: create a method */
  return new CoqApplication(
    new CoqVariable("Expr"),
    {
      createBVSort(e->getWidth()),
      coqAST,
    }
  );
}

ref<CoqExpr> ExprTranslator::translateAsSMTExpr(ref<Expr> e,
                                                ArrayTranslation *m) {
  ref<CoqExpr> coqAST = translate(e, m);
  if (coqAST.isNull()) {
    return nullptr;
  }

  /* TODO: create a method */
  return new CoqApplication(
    new CoqVariable("Expr"),
    {
      createBVSort(e->getWidth()),
      coqAST,
    }
  );
}

ref<CoqExpr> ExprTranslator::translateCached(ref<Expr> e,
                                             ArrayTranslation *m,
                                             std::vector<ref<CoqExpr>> &defs) {
  auto i = exprCache.find(e);
  if (i != exprCache.end()) {
    return i->second;
  }

  ref<CoqExpr> coqExpr = translate(e, m);
  std::string aliasName = allocateAliasName();
  ref<CoqExpr> def = new CoqDefinition(aliasName, coqExpr);
  defs.push_back(def);
  ref<CoqExpr> alias = new CoqVariable(aliasName);
  exprCache.insert(std::make_pair(e, alias));

  return alias;
}

ref<CoqExpr> ExprTranslator::translateCached(ref<Expr> e,
                                             ArrayTranslation *m) {
  auto i = exprCache.find(e);
  if (i != exprCache.end()) {
    return i->second;
  }

  return translate(e, m);
}

ref<CoqExpr> ExprTranslator::translate(ref<Expr> e,
                                       ArrayTranslation *m) {
  if (isa<ConstantExpr>(e)) {
    return translateConstantExpr(dyn_cast<ConstantExpr>(e));
  }

  if (isa<CmpExpr>(e)) {
    return translateCmpExpr(dyn_cast<CmpExpr>(e), m);
  }

  if (isa<BinaryExpr>(e)) {
    ref<BinaryExpr> be = dyn_cast<BinaryExpr>(e);
    ref<Expr> left = be->left;
    ref<Expr> right = be->right;
    if (isa<AddExpr>(e)) {
      return createSMTBinOp("SMT_Add", left, right, m);
    }
    if (isa<SubExpr>(e)) {
      return createSMTBinOp("SMT_Sub", left, right, m);
    }
    if (isa<MulExpr>(e)) {
      return createSMTBinOp("SMT_Mul", left, right, m);
    }
    if (isa<AndExpr>(e)) {
      return createSMTBinOp("SMT_And", left, right, m);
    }
  }

  if (isa<ConcatExpr>(e)) {
    return translateConcatExpr(dyn_cast<ConcatExpr>(e), m);
  }

  return nullptr;
}

ref<CoqExpr> ExprTranslator::translateConstantExpr(ref<ConstantExpr> e) {
  std::string repr;

  switch (e->getWidth()) {
  case Expr::Bool:
    repr = "Int1.repr";
    break;

  case Expr::Int8:
    repr = "Int8.repr";
    break;

  case Expr::Int16:
    repr = "Int16.repr";
    break;

  case Expr::Int32:
    repr = "Int32.repr";
    break;

  case Expr::Int64:
    repr = "Int64.repr";
    break;

  default:
    return nullptr;
  }

  return new CoqApplication(
    new CoqVariable("AST_Const"),
    {
      createBVSort(e->getWidth()),
      new CoqApplication(
        new CoqVariable(repr),
        {new CoqVariable(std::to_string(e->getZExtValue()))}
      ),
    }
  );
}

ref<CoqExpr> ExprTranslator::createSMTBinOp(std::string op,
                                            ref<Expr> left,
                                            ref<Expr> right,
                                            ArrayTranslation *m) {
  ref<CoqExpr> coqLeft = translate(left, m);
  if (!coqLeft) {
    return nullptr;
  }

  ref<CoqExpr> coqRight = translate(right, m);
  if (!coqRight) {
    return nullptr;
  }

  return new CoqApplication(
    new CoqVariable("AST_BinOp"),
    {
      createBVSort(left->getWidth()),
      new CoqVariable(op),
      coqLeft,
      coqRight,
    }
  );
}

ref<CoqExpr> ExprTranslator::translateCmpExpr(ref<CmpExpr> e,
                                              ArrayTranslation *m) {
  std::string op;

  switch (e->getKind()) {
  case Expr::Eq:
    op = "SMT_Eq";
    break;

  case Expr::Ne:
    op = "SMT_Ne";
    break;

  case Expr::Ult:
    op = "SMT_Ult";
    break;

  case Expr::Ule:
    op = "SMT_Ule";
    break;

  case Expr::Ugt:
    op = "SMT_Ugt";
    break;

  case Expr::Uge:
    op = "SMT_Uge";
    break;

  case Expr::Slt:
    op = "SMT_Slt";
    break;

  case Expr::Sle:
    op = "SMT_Sle";
    break;

  case Expr::Sgt:
    op = "SMT_Sgt";
    break;

  case Expr::Sge:
    op = "SMT_Sge";
    break;

  default:
    return nullptr;
  }

  ref<CoqExpr> coqLeft = translate(e->left, m);
  if (coqLeft.isNull()) {
    return nullptr;
  }

  ref<CoqExpr> coqRight = translate(e->right, m);
  if (coqRight.isNull()) {
    return nullptr;
  }

  return new CoqApplication(
    new CoqVariable("AST_CmpOp"),
    {
      createBVSort(e->left->getWidth()),
      new CoqVariable(op),
      coqLeft,
      coqRight,
    }
  );
}

ref<CoqExpr> ExprTranslator::translateConcatExpr(ref<ConcatExpr> e,
                                                 ArrayTranslation *m) {
  if (!m) {
    /* must provide an array translation map */
    return nullptr;
  }

  if (isa<ReadExpr>(e->getLeft())) {
    ReadExpr *re = dyn_cast<ReadExpr>(e->getLeft());
    const Array *array = re->updates.root;
    if (array && array->isSymbolicArray()) {
      auto i = m->find(array);
      if (i != m->end()) {
        return i->second;
      }
    }
  }

  return nullptr;
}

ref<CoqExpr> ExprTranslator::createSMTVar(unsigned width,
                                          ref<CoqExpr> name) {
  std::string constructor;
  switch (width) {
  case 1:
    constructor = "SMT_Var_I1";
    break;

  case 8:
    constructor = "SMT_Var_I8";
    break;

  case 16:
    constructor = "SMT_Var_I16";
    break;

  case 32:
    constructor = "SMT_Var_I32";
    break;

  case 64:
    constructor = "SMT_Var_I64";
    break;

  default:
    assert(false);
  }

  return new CoqApplication(
    new CoqVariable("AST_Var"),
    {
      createBVSort(width),
      name
    }
  );
}

ref<CoqExpr> ExprTranslator::createBVSort(Expr::Width w) {
  static ref<CoqExpr> coqBVSort1 = nullptr;
  static ref<CoqExpr> coqBVSort8 = nullptr;
  static ref<CoqExpr> coqBVSort16 = nullptr;
  static ref<CoqExpr> coqBVSort32 = nullptr;
  static ref<CoqExpr> coqBVSort64 = nullptr;

  switch (w) {
  case Expr::Bool:
   if (coqBVSort1.isNull()) {
     coqBVSort1 = new CoqVariable("Sort_BV1");
   }
   return coqBVSort1;

  case Expr::Int8:
    if (coqBVSort8.isNull()) {
      coqBVSort8 = new CoqVariable("Sort_BV8");
    }
    return coqBVSort8;

  case Expr::Int16:
    if (coqBVSort16.isNull()) {
      coqBVSort16 = new CoqVariable("Sort_BV16");
    }
    return coqBVSort16;

  case Expr::Int32:
    if (coqBVSort32.isNull()) {
      coqBVSort32 = new CoqVariable("Sort_BV32");
    }
    return coqBVSort32;

  case Expr::Int64:
    if (coqBVSort64.isNull()) {
      coqBVSort64 = new CoqVariable("Sort_BV64");
    }
    return coqBVSort64;

  default:
    break;
  }

  assert(false);
}

static uint64_t exprID;

std::string ExprTranslator::allocateAliasName() {
  return "expr_" + std::to_string(exprID++);
}

ExprTranslator::~ExprTranslator() {

}
