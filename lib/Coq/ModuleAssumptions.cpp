#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Constants.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"
#include "klee/Coq/ModuleAssumptions.h"

#include <map>
#include <string>

using namespace llvm;
using namespace klee;

ModuleSupport::ModuleSupport(Module &m, ModuleTranslator &moduleTranslator) :
  m(m), moduleTranslator(moduleTranslator) {

}

ref<CoqExpr> ModuleSupport::generateProof() {
  return getLemmaForModule();
}

ref<CoqExpr> ModuleSupport::getLemmaForModule() {
  /* TODO: use aliases */
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_module"),
    {moduleTranslator.translateModule()}
  );

  ref<CoqTactic> proof = getTacticForModule();

  return new CoqLemma(
    "is_supported_?",
    body,
    proof,
    true
  );
}

ref<CoqTactic> ModuleSupport::getTacticForModule() {
  return new Block({new Admit()});
}

ref<CoqExpr> ModuleSupport::getLemmaForFunction(Function &f) {
  /* TODO: use aliases */
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_definition"),
    {moduleTranslator.translateFunction(f)}
  );

  ref<CoqTactic> proof = getTacticForFunction(f);

  return new CoqLemma(
    "is_supported_?",
    body,
    proof,
    true
  );
}

ref<CoqTactic> ModuleSupport::getTacticForFunction(Function &f) {
  return new Block({new Admit()});
}

ref<CoqExpr> ModuleSupport::getLemmaForBasicBlock(BasicBlock &bb) {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_block"),
    {moduleTranslator.translateBasicBlock(bb)}
  );

  ref<CoqTactic> proof = getTacticForBasicBlock(bb);

  return new CoqLemma(
    "is_supported_?",
    body,
    proof,
    true
  );
}

ref<CoqTactic> ModuleSupport::getTacticForBasicBlock(BasicBlock &bb) {
  return new Block({new Admit()});
}

ref<CoqExpr> ModuleSupport::getLemmaForInst(Instruction &inst) {
  /* TODO: use aliases */
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_cmd"),
    {moduleTranslator.translateInst(inst)}
  );

  ref<CoqTactic> proof = getTacticForInst(inst);

  return new CoqLemma(
    "is_supported_?",
    body,
    proof,
    true
  );
}

ref<CoqTactic> ModuleSupport::getTacticForInst(Instruction &inst) {
  return new Block({new Admit()});
}

ModuleSupport::~ModuleSupport() {

}
