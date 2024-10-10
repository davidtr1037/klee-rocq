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
                                                      ArrayTranslation *m,
                                                      bool useCache,
                                                      std::vector<ref<CoqExpr>> &defs) {
  ref<CoqExpr> coqAST = translateCached(e, m, useCache, defs);
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
                                             bool useCache,
                                             std::vector<ref<CoqExpr>> &defs) {
  auto i = exprCache.find(e);
  if (i != exprCache.end()) {
    return i->second;
  }

  ref<CoqExpr> coqExpr = translate(e, m, useCache);
  std::string aliasName = allocateAliasName();
  ref<CoqExpr> def = new CoqDefinition(aliasName, coqExpr);
  defs.push_back(def);
  ref<CoqExpr> alias = new CoqVariable(aliasName);
  exprCache.insert(std::make_pair(e, alias));

  return alias;
}

ref<CoqExpr> ExprTranslator::translate(ref<Expr> e,
                                       ArrayTranslation *m,
                                       bool useCache) {
  if (useCache) {
    auto i = exprCache.find(e);
    if (i != exprCache.end()) {
      return i->second;
    }
  }

  if (isa<ConstantExpr>(e)) {
    return translateConstantExpr(dyn_cast<ConstantExpr>(e));
  }

  if (isa<CmpExpr>(e)) {
    return translateCmpExpr(dyn_cast<CmpExpr>(e), m);
  }

  if (isa<CastExpr>(e)) {
    return translateCastExpr(dyn_cast<CastExpr>(e), m);
  }

  if (isa<ExtractExpr>(e)) {
    return translateExtractExpr(dyn_cast<ExtractExpr>(e), m);
  }

  if (isa<BinaryExpr>(e)) {
    return translateBinaryExpr(dyn_cast<BinaryExpr>(e), m, useCache);
  }

  if (isa<ConcatExpr>(e)) {
    return translateConcatExpr(dyn_cast<ConcatExpr>(e), m);
  }

  assert(false);
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
    assert(false);
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
                                            ArrayTranslation *m,
                                            bool useCache) {
  ref<CoqExpr> coqLeft = translate(left, m, useCache);
  if (!coqLeft) {
    return nullptr;
  }

  ref<CoqExpr> coqRight = translate(right, m, useCache);
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
    assert(false);
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

ref<CoqExpr> ExprTranslator::translateCastExpr(ref<CastExpr> e,
                                               ArrayTranslation *m) {
  std::string constructor;
  switch (e->getKind()) {
  case Expr::ZExt:
    constructor = "AST_ZExt";
    break;

  case Expr::SExt:
    constructor = "AST_SExt";
    break;

  default:
    assert(false);
  }

  return new CoqApplication(
    new CoqVariable(constructor),
    {
      createBVSort(e->src->getWidth()),
      translate(e->src, m),
      createBVSort(e->getWidth()),
    }
  );
}

ref<CoqExpr> ExprTranslator::translateExtractExpr(ref<ExtractExpr> e,
                                                  ArrayTranslation *m) {
  return new CoqApplication(
    new CoqVariable("AST_Extract"),
    {
      createBVSort(e->expr->getWidth()),
      translate(e->expr, m),
      createBVSort(e->getWidth()),
    }
  );
}

ref<CoqExpr> ExprTranslator::translateBinaryExpr(ref<BinaryExpr> e,
                                                 ArrayTranslation *m,
                                                 bool useCache) {
  ref<Expr> left = e->left;
  ref<Expr> right = e->right;

  std::string op;
  switch (e->getKind()) {
  case Expr::Add:
    op = "SMT_Add";
    break;

  case Expr::Sub:
    op = "SMT_Sub";
    break;

  case Expr::Mul:
    op = "SMT_Mul";
    break;

  case Expr::URem:
    op = "SMT_URem";
    break;

  case Expr::SRem:
    op = "SMT_SRem";
    break;

  case Expr::And:
    op = "SMT_And";
    break;

  case Expr::Xor:
    op = "SMT_Xor";
    break;

  case Expr::Shl:
    op = "SMT_Shl";
    break;

  case Expr::LShr:
    op = "SMT_LShr";
    break;

  default:
    assert(false);
  }

  return createSMTBinOp(op, left, right, m, useCache);
}

ref<CoqExpr> ExprTranslator::translateConcatExpr(ref<ConcatExpr> e,
                                                 ArrayTranslation *m) {
  if (!m) {
    /* must provide an array translation map */
    return nullptr;
  }

  if (isa<ReadExpr>(e->getLeft())) {
    return translateReadExpr(dyn_cast<ReadExpr>(e->getLeft()), m);
  }

  assert(false);
}

ref<CoqExpr> ExprTranslator::translateReadExpr(ref<ReadExpr> e,
                                               ArrayTranslation *m) {
  if (!m) {
    /* must provide an array translation map */
    return nullptr;
  }

  const Array *array = e->updates.root;
  if (array && array->isSymbolicArray()) {
    auto i = m->find(array);
    if (i != m->end()) {
      return i->second;
    }
  }

  assert(false);
}

ref<CoqExpr> ExprTranslator::createSMTVar(unsigned width,
                                          ref<CoqExpr> name) {
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
