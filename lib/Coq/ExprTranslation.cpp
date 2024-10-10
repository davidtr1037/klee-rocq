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
    createExpr(),
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
    createExpr(),
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

  return new CoqApplication(
    createASTConst(),
    {
      createBVSort(e->getWidth()),
      new CoqApplication(
        createRepr(e->getWidth()),
        {new CoqVariable(std::to_string(e->getZExtValue()))}
      ),
    }
  );
}

ref<CoqExpr> ExprTranslator::createSMTBinOp(ref<CoqExpr> op,
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
    createASTBinOp(),
    {
      createBVSort(left->getWidth()),
      op,
      coqLeft,
      coqRight,
    }
  );
}

ref<CoqExpr> ExprTranslator::translateCmpExpr(ref<CmpExpr> e,
                                              ArrayTranslation *m) {
  ref<CoqExpr> op;

  switch (e->getKind()) {
  case Expr::Eq:
    op = createSMTEq();
    break;

  case Expr::Ne:
    op = createSMTNe();
    break;

  case Expr::Ult:
    op = createSMTUlt();
    break;

  case Expr::Ule:
    op = createSMTUle();
    break;

  case Expr::Ugt:
    op = createSMTUgt();
    break;

  case Expr::Uge:
    op = createSMTUge();
    break;

  case Expr::Slt:
    op = createSMTSlt();
    break;

  case Expr::Sle:
    op = createSMTSle();
    break;

  case Expr::Sgt:
    op = createSMTSgt();
    break;

  case Expr::Sge:
    op = createSMTSge();
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
    createASTCmpOp(),
    {
      createBVSort(e->left->getWidth()),
      op,
      coqLeft,
      coqRight,
    }
  );
}

ref<CoqExpr> ExprTranslator::translateCastExpr(ref<CastExpr> e,
                                               ArrayTranslation *m) {
  ref<CoqExpr> constructor;
  switch (e->getKind()) {
  case Expr::ZExt:
    constructor = createASTZExt();
    break;

  case Expr::SExt:
    constructor = createASTSExt();
    break;

  default:
    assert(false);
  }

  return new CoqApplication(
    constructor,
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
    createASTExtract(),
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

  ref<CoqExpr> op;
  switch (e->getKind()) {
  case Expr::Add:
    op = createSMTAdd();
    break;

  case Expr::Sub:
    op = createSMTSub();
    break;

  case Expr::Mul:
    op = createSMTMul();
    break;

  case Expr::URem:
    op = createSMTURem();
    break;

  case Expr::SRem:
    op = createSMTSRem();
    break;

  case Expr::And:
    op = createSMTAnd();
    break;

  case Expr::Xor:
    op = createSMTXor();
    break;

  case Expr::Shl:
    op = createSMTShl();
    break;

  case Expr::LShr:
    op = createSMTLShr();
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
    createASTVar(),
    {
      createBVSort(width),
      name
    }
  );
}

ref<CoqExpr> ExprTranslator::createASTVar() {
  static ref<CoqExpr> coqASTVar = nullptr;
  if (coqASTVar.isNull()) {
    coqASTVar = new CoqVariable("AST_Var");
  }
  return coqASTVar;
}

ref<CoqExpr> ExprTranslator::createExpr() {
  static ref<CoqExpr> coqExpr = nullptr;
  if (coqExpr.isNull()) {
    coqExpr = new CoqVariable("Expr");
  }
  return coqExpr;
}

ref<CoqExpr> ExprTranslator::createASTConst() {
  static ref<CoqExpr> coqASTConst = nullptr;
  if (coqASTConst.isNull()) {
    coqASTConst = new CoqVariable("AST_Const");
  }
  return coqASTConst;
}

ref<CoqExpr> ExprTranslator::createSMTEq() {
  static ref<CoqExpr> coqSMTEq = nullptr;
  if (coqSMTEq.isNull()) {
    coqSMTEq = new CoqVariable("SMT_Eq");
  }
  return coqSMTEq;
}

ref<CoqExpr> ExprTranslator::createSMTNe() {
  static ref<CoqExpr> coqSMTNe = nullptr;
  if (coqSMTNe.isNull()) {
    coqSMTNe = new CoqVariable("SMT_Ne");
  }
  return coqSMTNe;
}

ref<CoqExpr> ExprTranslator::createSMTUlt() {
  static ref<CoqExpr> coqSMTUlt = nullptr;
  if (coqSMTUlt.isNull()) {
    coqSMTUlt = new CoqVariable("SMT_Ult");
  }
  return coqSMTUlt;
}

ref<CoqExpr> ExprTranslator::createSMTUle() {
  static ref<CoqExpr> coqSMTUle = nullptr;
  if (coqSMTUle.isNull()) {
    coqSMTUle = new CoqVariable("SMT_Ule");
  }
  return coqSMTUle;
}

ref<CoqExpr> ExprTranslator::createSMTUgt() {
  static ref<CoqExpr> coqSMTUgt = nullptr;
  if (coqSMTUgt.isNull()) {
    coqSMTUgt = new CoqVariable("SMT_Ugt");
  }
  return coqSMTUgt;
}

ref<CoqExpr> ExprTranslator::createSMTUge() {
  static ref<CoqExpr> coqSMTUge = nullptr;
  if (coqSMTUge.isNull()) {
    coqSMTUge = new CoqVariable("SMT_Uge");
  }
  return coqSMTUge;
}

ref<CoqExpr> ExprTranslator::createSMTSlt() {
  static ref<CoqExpr> coqSMTSlt = nullptr;
  if (coqSMTSlt.isNull()) {
    coqSMTSlt = new CoqVariable("SMT_Slt");
  }
  return coqSMTSlt;
}

ref<CoqExpr> ExprTranslator::createSMTSle() {
  static ref<CoqExpr> coqSMTSle = nullptr;
  if (coqSMTSle.isNull()) {
    coqSMTSle = new CoqVariable("SMT_Sle");
  }
  return coqSMTSle;
}

ref<CoqExpr> ExprTranslator::createSMTSgt() {
  static ref<CoqExpr> coqSMTSgt = nullptr;
  if (coqSMTSgt.isNull()) {
    coqSMTSgt = new CoqVariable("SMT_Sgt");
  }
  return coqSMTSgt;
}

ref<CoqExpr> ExprTranslator::createSMTSge() {
  static ref<CoqExpr> coqSMTSge = nullptr;
  if (coqSMTSge.isNull()) {
    coqSMTSge = new CoqVariable("SMT_Sge");
  }
  return coqSMTSge;
}

ref<CoqExpr> ExprTranslator::createASTCmpOp() {
  static ref<CoqExpr> coqASTCmpOp = nullptr;
  if (coqASTCmpOp.isNull()) {
    coqASTCmpOp = new CoqVariable("AST_CmpOp");
  }
  return coqASTCmpOp;
}

ref<CoqExpr> ExprTranslator::createASTZExt() {
  static ref<CoqExpr> coqASTZExt = nullptr;
  if (coqASTZExt.isNull()) {
    coqASTZExt = new CoqVariable("AST_ZExt");
  }
  return coqASTZExt;
}

ref<CoqExpr> ExprTranslator::createASTSExt() {
  static ref<CoqExpr> coqASTSExt = nullptr;
  if (coqASTSExt.isNull()) {
    coqASTSExt = new CoqVariable("AST_SExt");
  }
  return coqASTSExt;
}

ref<CoqExpr> ExprTranslator::createASTExtract() {
  static ref<CoqExpr> coqASTExtract = nullptr;
  if (coqASTExtract.isNull()) {
    coqASTExtract = new CoqVariable("AST_Extract");
  }
  return coqASTExtract;
}

ref<CoqExpr> ExprTranslator::createSMTAdd() {
  static ref<CoqExpr> coqSMTAdd = nullptr;
  if (coqSMTAdd.isNull()) {
    coqSMTAdd = new CoqVariable("SMT_Add");
  }
  return coqSMTAdd;
}

ref<CoqExpr> ExprTranslator::createSMTSub() {
  static ref<CoqExpr> coqSMTSub = nullptr;
  if (coqSMTSub.isNull()) {
    coqSMTSub = new CoqVariable("SMT_Sub");
  }
  return coqSMTSub;
}

ref<CoqExpr> ExprTranslator::createSMTMul() {
  static ref<CoqExpr> coqSMTMul = nullptr;
  if (coqSMTMul.isNull()) {
    coqSMTMul = new CoqVariable("SMT_Mul");
  }
  return coqSMTMul;
}

ref<CoqExpr> ExprTranslator::createSMTURem() {
  static ref<CoqExpr> coqSMTURem = nullptr;
  if (coqSMTURem.isNull()) {
    coqSMTURem = new CoqVariable("SMT_URem");
  }
  return coqSMTURem;
}

ref<CoqExpr> ExprTranslator::createSMTSRem() {
  static ref<CoqExpr> coqSMTSRem = nullptr;
  if (coqSMTSRem.isNull()) {
    coqSMTSRem = new CoqVariable("SMT_SRem");
  }
  return coqSMTSRem;
}

ref<CoqExpr> ExprTranslator::createSMTAnd() {
  static ref<CoqExpr> coqSMTAnd = nullptr;
  if (coqSMTAnd.isNull()) {
    coqSMTAnd = new CoqVariable("SMT_And");
  }
  return coqSMTAnd;
}

ref<CoqExpr> ExprTranslator::createSMTXor() {
  static ref<CoqExpr> coqSMTXor = nullptr;
  if (coqSMTXor.isNull()) {
    coqSMTXor = new CoqVariable("SMT_Xor");
  }
  return coqSMTXor;
}

ref<CoqExpr> ExprTranslator::createSMTShl() {
  static ref<CoqExpr> coqSMTShl = nullptr;
  if (coqSMTShl.isNull()) {
    coqSMTShl = new CoqVariable("SMT_Shl");
  }
  return coqSMTShl;
}

ref<CoqExpr> ExprTranslator::createSMTLShr() {
  static ref<CoqExpr> coqSMTLShr = nullptr;
  if (coqSMTLShr.isNull()) {
    coqSMTLShr = new CoqVariable("SMT_LShr");
  }
  return coqSMTLShr;
}

ref<CoqExpr> ExprTranslator::createASTBinOp() {
  static ref<CoqExpr> coqASTBinOp = nullptr;
  if (coqASTBinOp.isNull()) {
    coqASTBinOp = new CoqVariable("AST_BinOp");
  }
  return coqASTBinOp;
}

ref<CoqExpr> ExprTranslator::createRepr(Expr::Width w) {
  static ref<CoqExpr> coqReprInt1 = nullptr;
  static ref<CoqExpr> coqReprInt8 = nullptr;
  static ref<CoqExpr> coqReprInt16 = nullptr;
  static ref<CoqExpr> coqReprInt32 = nullptr;
  static ref<CoqExpr> coqReprInt64 = nullptr;

  switch (w) {
  case Expr::Bool:
   if (coqReprInt1.isNull()) {
     coqReprInt1 = new CoqVariable("Int1.repr");
   }
   return coqReprInt1;

  case Expr::Int8:
    if (coqReprInt8.isNull()) {
      coqReprInt8 = new CoqVariable("Int8.repr");
    }
    return coqReprInt8;

  case Expr::Int16:
    if (coqReprInt16.isNull()) {
      coqReprInt16 = new CoqVariable("Int16.repr");
    }
    return coqReprInt16;

  case Expr::Int32:
    if (coqReprInt32.isNull()) {
      coqReprInt32 = new CoqVariable("Int32.repr");
    }
    return coqReprInt32;

  case Expr::Int64:
    if (coqReprInt64.isNull()) {
      coqReprInt64 = new CoqVariable("Int64.repr");
    }
    return coqReprInt64;

  default:
    break;
  }

  assert(false);
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
