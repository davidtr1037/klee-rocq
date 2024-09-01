#ifndef KLEE_EXPRTRANSLATION_H
#define KLEE_EXPRTRANSLATION_H

#include "klee/Expr/Expr.h"

#include "klee/Coq/CoqLanguage.h"

#include <map>

namespace klee {

typedef std::map<const Array *, ref<CoqExpr>> ArrayTranslation;

class ExprTranslator {

public:

  ExprTranslator();

  ref<CoqExpr> translate(ref<Expr> e,
                         ArrayTranslation *m = nullptr);

  ref<CoqExpr> translateConstantExpr(ref<ConstantExpr> e);

  ref<CoqExpr> createSMTBinOp(std::string constructor,
                              ref<Expr> left,
                              ref<Expr> right,
                              ArrayTranslation *m);

  ref<CoqExpr> translateCmpExpr(ref<CmpExpr> e,
                                ArrayTranslation *m);

  ref<CoqExpr> translateConcatExpr(ref<ConcatExpr> e,
                                   ArrayTranslation *m);

  ref<CoqExpr> createSMTVar(unsigned width,
                            ref<CoqExpr> name);

  ~ExprTranslator();
};

}

#endif
