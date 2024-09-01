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

/* TODO: return nullptr instead of assertions */
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
    if (isa<AndExpr>(e)) {
      return createSMTBinOp("SMT_And", left, right, m);
    }
  }

  if (isa<ConcatExpr>(e)) {
    return translateConcatExpr(dyn_cast<ConcatExpr>(e), m);
  }

  assert(false);
  return nullptr;
}

ref<CoqExpr> ExprTranslator::translateConstantExpr(ref<ConstantExpr> e) {
  std::string smt_constructor;
  std::string repr;

  switch (e->getWidth()) {
  case Expr::Bool:
    smt_constructor = "SMT_Const_I1";
    repr = "Int1.repr";
    break;

  case Expr::Int8:
    smt_constructor = "SMT_Const_I8";
    repr = "Int8.repr";
    break;

  case Expr::Int16:
    smt_constructor = "SMT_Const_I16";
    repr = "Int16.repr";
    break;

  case Expr::Int32:
    smt_constructor = "SMT_Const_I32";
    repr = "Int32.repr";
    break;

  case Expr::Int64:
    smt_constructor = "SMT_Const_I64";
    repr = "Int64.repr";
    break;

  default:
    return nullptr;
  }

  return new CoqApplication(
    new CoqVariable(smt_constructor),
    {
      new CoqApplication(
        new CoqVariable(repr),
        {new CoqVariable(std::to_string(e->getZExtValue()))}
      )
    }
  );
}

ref<CoqExpr> ExprTranslator::createSMTBinOp(std::string op,
                                            ref<Expr> left,
                                            ref<Expr> right,
                                            ArrayTranslation *m) {
  return new CoqApplication(
    new CoqVariable("SMT_BinOp"),
    {
      new CoqVariable(op),
      translate(left, m),
      translate(right, m),
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

  return new CoqApplication(
    new CoqVariable("SMT_CmpOp"),
    {
      new CoqVariable(op),
      translate(e->left, m),
      translate(e->right, m),
    }
  );
}

ref<CoqExpr> ExprTranslator::translateConcatExpr(ref<ConcatExpr> e,
                                                 ArrayTranslation *m) {
  if (!m) {
    /* TODO: must provide an array translation map */
    assert(false);
  }

  if (isa<ReadExpr>(e->getLeft())) {
    ReadExpr *re = dyn_cast<ReadExpr>(e->getLeft());
    const Array *array = re->updates.root;
    if (array && array->isSymbolicArray()) {
      auto i = m->find(array);
      if (i == m->end()) {
        assert(false);
      } else {
        return i->second;
      }
    }
  }

  assert(false);
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
    new CoqVariable(constructor),
    {name}
  );
}

ExprTranslator::~ExprTranslator() {

}
