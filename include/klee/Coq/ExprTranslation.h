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

  ref<CoqExpr> translateAsSMTExpr(ref<Expr> e,
                                  ArrayTranslation *m,
                                  bool useCache = false);

  ref<CoqExpr> translateAsSMTExpr(ref<Expr> e,
                                  ArrayTranslation *m,
                                  bool useCache,
                                  bool updateCache,
                                  std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translate(ref<Expr> e,
                         ArrayTranslation *m,
                         bool useCache = false);

  ref<CoqExpr> translate(ref<Expr> e,
                         ArrayTranslation *m,
                         bool useCache,
                         bool updateCache,
                         std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateConstantExpr(ref<ConstantExpr> e);

  ref<CoqExpr> translateCmpExpr(ref<CmpExpr> e,
                                ArrayTranslation *m,
                                bool useCache,
                                bool updateCache,
                                std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateCastExpr(ref<CastExpr> e,
                                 ArrayTranslation *m,
                                 bool useCache,
                                 bool updateCache,
                                 std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateExtractExpr(ref<ExtractExpr> e,
                                    ArrayTranslation *m,
                                    bool useCache,
                                    bool updateCache,
                                    std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateBinaryExpr(ref<BinaryExpr> e,
                                   ArrayTranslation *m,
                                   bool useCache,
                                   bool updateCache,
                                   std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> createSMTBinOp(ref<CoqExpr> op,
                              ref<Expr> left,
                              ref<Expr> right,
                              ArrayTranslation *m,
                              bool useCache,
                              bool updateCache,
                              std::vector<ref<CoqExpr>> &defs);

  ref<CoqExpr> translateConcatExpr(ref<ConcatExpr> e,
                                   ArrayTranslation *m);

  ref<CoqExpr> translateReadExpr(ref<ReadExpr> e,
                                 ArrayTranslation *m);

  ref<CoqExpr> createSMTVar(unsigned width,
                            ref<CoqExpr> name);

  ref<CoqExpr> createExpr();

  ref<CoqExpr> createASTConst();

  ref<CoqExpr> createSMTEq();

  ref<CoqExpr> createSMTNe();

  ref<CoqExpr> createSMTUlt();

  ref<CoqExpr> createSMTUle();

  ref<CoqExpr> createSMTUgt();

  ref<CoqExpr> createSMTUge();

  ref<CoqExpr> createSMTSlt();

  ref<CoqExpr> createSMTSle();

  ref<CoqExpr> createSMTSgt();

  ref<CoqExpr> createSMTSge();

  ref<CoqExpr> createASTCmpOp();

  ref<CoqExpr> createASTZExt();

  ref<CoqExpr> createASTSExt();

  ref<CoqExpr> createASTExtract();

  ref<CoqExpr> createSMTAdd();

  ref<CoqExpr> createSMTSub();

  ref<CoqExpr> createSMTMul();

  ref<CoqExpr> createSMTUDiv();

  ref<CoqExpr> createSMTSDiv();

  ref<CoqExpr> createSMTURem();

  ref<CoqExpr> createSMTSRem();

  ref<CoqExpr> createSMTAnd();

  ref<CoqExpr> createSMTOr();

  ref<CoqExpr> createSMTXor();

  ref<CoqExpr> createSMTShl();

  ref<CoqExpr> createSMTLShr();

  ref<CoqExpr> createSMTAShr();

  ref<CoqExpr> createASTBinOp();

  ref<CoqExpr> createASTVar();

  ref<CoqExpr> createRepr(Expr::Width w);

  ref<CoqExpr> createBVSort(Expr::Width w);

  std::string allocateAliasName();

  ~ExprTranslator();
};

}

#endif
