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
#include <vector>

using namespace llvm;
using namespace klee;

ModuleSupport::ModuleSupport(Module &m, ModuleTranslator &moduleTranslator) :
  m(m), moduleTranslator(moduleTranslator) {

}

ref<CoqExpr> ModuleSupport::generateProof() {
  return getLemmaForModule();
}

ref<CoqExpr> ModuleSupport::getLemmaForModule() {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_module"),
    {moduleTranslator.translateModuleCached()}
  );

  ref<CoqTactic> proof = getTacticForModule();

  return new CoqLemma(
    "is_supported_mdl",
    body,
    proof,
    true
  );
}

ref<CoqTactic> ModuleSupport::getTacticForModule() {
  std::vector<ref<CoqTactic>> tactics;

  tactics.push_back(new Intros({"d", "Hin"}));

  for (Function &f : m) {
    if (moduleTranslator.isSupportedFunction(f)) {
      if (!f.isDeclaration()) {
        tactics.push_back(
          new Destruct("Hin", {{"Hin"}, {"Hin"}})
        );
        ref<CoqLemma> lemma = getLemmaForFunction(f);
        functionLemmas.push_back(lemma);
        tactics.push_back(
          new Block(
            {
              new Subst(),
              new Apply(lemma->name),
            }
          )
        );
      }
    }
  }

  tactics.push_back(
    new Block({new Destruct("Hin")})
  );

  return new Block(
    {
      new Apply("IS_Module"),
      /* globals */
      new Block(
        {
          new Intros({"g", "H"}),
          new Destruct("H"),
        }
      ),
      /* definitions */
      new Block(tactics),
    }
  );
}

ref<CoqLemma> ModuleSupport::getLemmaForFunction(Function &f) {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_definition"),
    {moduleTranslator.translateFunctionCached(f)}
  );

  ref<CoqTactic> proof = getTacticForFunction(f);

  return new CoqLemma(
    "is_supported_def_" + f.getName().str(),
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
    "is_supported_bb_" + std::to_string(moduleTranslator.getBasicBlockID(bb)),
    body,
    proof,
    true
  );
}

ref<CoqTactic> ModuleSupport::getTacticForBasicBlock(BasicBlock &bb) {
  return new Block({new Admit()});
}

ref<CoqExpr> ModuleSupport::getLemmaForInst(Instruction &inst) {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_cmd"),
    {moduleTranslator.translateInstCached(inst)}
  );

  ref<CoqTactic> proof = getTacticForInst(inst);

  return new CoqLemma(
    "is_supported_inst_" + std::to_string(moduleTranslator.getInstID(inst)),
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
