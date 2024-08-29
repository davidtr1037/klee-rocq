#ifndef KLEE_EXPRTRANSLATION_H
#define KLEE_EXPRTRANSLATION_H

#include "klee/Expr/Expr.h"

#include "klee/Coq/CoqLanguage.h"

#include <map>

namespace klee {

class ExprTranslator {

public:

  ExprTranslator();

  ref<CoqExpr> translate(ref<Expr> e);

  ref<CoqExpr> translateConstantExpr(ref<ConstantExpr> e);

  ref<CoqExpr> translateCmpExpr(ref<CmpExpr> e);

  ~ExprTranslator();
};

}

#endif
