#include "klee/Coq/CoqLanguage.h"
#include "ProofGenerator.h"

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
  ref<CoqExpr> coqModule = t.translateModule();

  for (ref<CoqExpr> def : t.instDefs) {
    output << def->dump() << "\n";
  }

  for (ref<CoqExpr> def : t.bbDefs) {
    output << def->dump() << "\n";
  }

  for (ref<CoqExpr> def : t.declDefs) {
    output << def->dump() << "\n";
  }

  for (ref<CoqExpr> def : t.functionDefs) {
    output << def->dump() << "\n";
  }

  ref<CoqExpr> moduleDef = new CoqDefinition(
    "mdl",
    "llvm_module",
     coqModule
  );

  output << moduleDef->dump() << "\n";

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
    new CoqRequire("SE", "ChoiceAxiom"),
    new CoqRequire("SE", "Concrete"),
    new CoqRequire("SE", "DynamicValue"),
    new CoqRequire("SE", "ExecutionTreeOpt"),
    new CoqRequire("SE", "IDMap"),
    new CoqRequire("SE", "LLVMAst"),
    new CoqRequire("SE", "Symbolic"),
    new CoqRequire("SE", "ProofGeneration"),
    new CoqRequire("SE.SMT", "Expr"),
    new CoqRequire("SE.SMT", "Model"),
  };
}
