#ifndef KLEE_EXPRTRANSLATION_H
#define KLEE_EXPRTRANSLATION_H

#include "klee/Expr/Expr.h"

#include "klee/Coq/CoqLanguage.h"

#include <map>
#include <vector>

namespace klee {

typedef std::map<const Array *, ref<CoqExpr>> ArrayTranslation;

typedef std::map<ref<Expr>, ref<CoqExpr>> ExprCache;

class ExprTranslator {

public:

  ExprCache exprCache;

  ExprTranslator();

  ref<CoqExpr> translateAsSMTExprCached(ref<Expr> e,
                                        ArrayTranslation *m,
                                        bool useCache,
                                        std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateAsSMTExpr(ref<Expr> e,
                                  ArrayTranslation *m);

  ref<CoqExpr> translateCached(ref<Expr> e,
                               ArrayTranslation *m,
                               bool useCache,
                               std::vector<ref<CoqExpr>> &defs);

  /* TODO: is the default argument necessary? */
  ref<CoqExpr> translate(ref<Expr> e,
                         ArrayTranslation *m,
                         bool useCache = false);

  ref<CoqExpr> translateConstantExpr(ref<ConstantExpr> e);

  ref<CoqExpr> createSMTBinOp(std::string constructor,
                              ref<Expr> left,
                              ref<Expr> right,
                              ArrayTranslation *m,
                              bool useCache);

  ref<CoqExpr> translateCmpExpr(ref<CmpExpr> e,
                                ArrayTranslation *m);

  ref<CoqExpr> translateCastExpr(ref<CastExpr> e,
                                 ArrayTranslation *m);

  ref<CoqExpr> translateExtractExpr(ref<ExtractExpr> e,
                                    ArrayTranslation *m);

  ref<CoqExpr> translateBinaryExpr(ref<BinaryExpr> e,
                                   ArrayTranslation *m,
                                   bool useCache);

  ref<CoqExpr> translateConcatExpr(ref<ConcatExpr> e,
                                   ArrayTranslation *m);

  ref<CoqExpr> translateReadExpr(ref<ReadExpr> e,
                                 ArrayTranslation *m);

  ref<CoqExpr> createSMTVar(unsigned width,
                            ref<CoqExpr> name);

  ref<CoqExpr> createBVSort(Expr::Width w);

  std::string allocateAliasName();

  ~ExprTranslator();
};

}

#endif
