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

ref<CoqExpr> ExprTranslator::translate(ref<Expr> e) {
  if (isa<ConstantExpr>(e)) {
    return translateConstantExpr(dyn_cast<ConstantExpr>(e));
  }

  if (isa<CmpExpr>(e)) {
    return translateCmpExpr(dyn_cast<CmpExpr>(e));
  }

  if (isa<BinaryExpr>(e)) {
    ref<BinaryExpr> be = dyn_cast<BinaryExpr>(e);
    ref<Expr> left = be->left;
    ref<Expr> right = be->right;
    if (isa<AddExpr>(e)) {
      return createSMTBinOp("SMT_Add", left, right);
    }
    if (isa<AndExpr>(e)) {
      return createSMTBinOp("SMT_And", left, right);
    }
  }

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
                                            ref<Expr> right) {
  return new CoqApplication(
    new CoqVariable("SMT_BinOp"),
    {
      new CoqVariable(op),
      translate(left),
      translate(right),
    }
  );
}

ref<CoqExpr> ExprTranslator::translateCmpExpr(ref<CmpExpr> e) {
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
      translate(e->left),
      translate(e->right),
    }
  );
}

ExprTranslator::~ExprTranslator() {

}
