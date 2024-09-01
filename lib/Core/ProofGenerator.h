#ifndef KLEE_PROOF_GENERATOR_H
#define KLEE_PROOF_GENERATOR_H

#include "llvm/IR/Module.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

#include <string>

namespace klee {

class ProofGenerator {

public:

  llvm::Module &m;

  ProofGenerator(llvm::Module &m);

  std::string generate();

  std::vector<ref<CoqExpr>> generateImports();

};

}

#endif
