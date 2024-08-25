#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Proof.h"

#include <string>
#include <sstream>

using namespace std;
using namespace llvm;
using namespace klee;

ProofGenerator::ProofGenerator(Module &m) : m(m) {

}

string ProofGenerator::generate() {
  ostringstream output;

  for (ref<CoqExpr> import : generateImports()) {
    output << import->dump() << "\n";
  }

  ModuleTranslator t(m);
  output << t.translateModule()->dump() << "\n";

  return output.str();
}

vector<klee::ref<CoqExpr>> ProofGenerator::generateImports() {
  return {
    new CoqRequire("Coq", "ZArith"),
    new CoqRequire("Coq", "Strings.String"),
    new CoqRequire("Coq", "List"),
    new CoqImport("ListNotations"),
    new CoqRequire("SE", "BitVectors"),
    new CoqRequire("SE", "CFG"),
    new CoqRequire("SE", "Concrete"),
    new CoqRequire("SE", "DynamicValue"),
    new CoqRequire("SE", "IDMap"),
    new CoqRequire("SE", "LLVMAst"),
  };
}
