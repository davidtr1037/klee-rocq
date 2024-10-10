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

ref<CoqLemma> ModuleSupport::generateProof() {
  return getLemmaForModule();
}

ref<CoqLemma> ModuleSupport::getLemmaForModule() {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_module"),
    {moduleTranslator.translateModuleCached()}
  );

  ref<CoqTactic> proof = getTacticForModule();

  return new CoqLemma(
    "is_supported_mdl",
    body,
    proof
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
    proof
  );
}

ref<CoqTactic> ModuleSupport::getTacticForFunction(Function &f) {
  std::vector<ref<CoqTactic>> tactics;

  tactics.push_back(new Apply("IS_Definition"));
  tactics.push_back(new Intros({"b", "Hin"}));

  for (BasicBlock &bb : f) {
    tactics.push_back(
      new Destruct("Hin", {{"Hin"}, {"Hin"}})
    );
    ref<CoqLemma> lemma = getLemmaForBasicBlock(bb);
    bbLemmas.push_back(lemma);
    tactics.push_back(
      new Block(
        {
          new Subst(),
          new Apply(lemma->name),
        }
      )
    );
  }

  tactics.push_back(
    new Block({new Destruct("Hin")})
  );

  return new Block(tactics);
}

ref<CoqLemma> ModuleSupport::getLemmaForBasicBlock(BasicBlock &bb) {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_block"),
    {moduleTranslator.translateBasicBlock(bb)}
  );

  ref<CoqTactic> proof = getTacticForBasicBlock(bb);

  return new CoqLemma(
    "is_supported_bb_" + std::to_string(moduleTranslator.getBasicBlockID(bb)),
    body,
    proof
  );
}

ref<CoqTactic> ModuleSupport::getTacticForBasicBlock(BasicBlock &bb) {
  std::vector<ref<CoqTactic>> tactics;

  tactics.push_back(new Apply("IS_Block"));
  tactics.push_back(new Apply("IS_CmdList"));
  tactics.push_back(new Intros({"c", "Hin"}));

  for (Instruction &inst : bb) {
    if (!moduleTranslator.isSupportedInst(inst)) {
      continue;
    }

    tactics.push_back(
      new Destruct("Hin", {{"Hin"}, {"Hin"}})
    );
    ref<CoqLemma> lemma = getLemmaForInst(inst);
    instLemmas.push_back(lemma);
    tactics.push_back(
      new Block(
        {
          new Subst(),
          new Apply(lemma->name),
        }
      )
    );
  }

  tactics.push_back(
    new Block({new Destruct("Hin")})
  );

  return new Block(tactics);
}

ref<CoqLemma> ModuleSupport::getLemmaForInst(Instruction &inst) {
  ref<CoqExpr> body = new CoqApplication(
    new CoqVariable("is_supported_cmd"),
    {moduleTranslator.translateInstCached(inst)}
  );

  ref<CoqTactic> proof = getTacticForInst(inst);

  return new CoqLemma(
    "is_supported_inst_" + std::to_string(moduleTranslator.getInstID(inst)),
    body,
    proof
  );
}

ref<CoqTactic> ModuleSupport::getTacticForInst(Instruction &inst) {
  if (isa<BinaryOperator>(&inst)) {
    return getTacticForBinaryOperator(dyn_cast<BinaryOperator>(&inst));
  }

  if (isa<CmpInst>(&inst)) {
    return getTacticForCmpInst(dyn_cast<CmpInst>(&inst));
  }

  if (isa<CastInst>(&inst)) {
    return getTacticForCastInst(dyn_cast<CastInst>(&inst));
  }

  if (isa<BranchInst>(&inst)) {
    return getTacticForBranchInst(dyn_cast<BranchInst>(&inst));
  }

  if (isa<PHINode>(&inst)) {
    return getTacticForPHINode(dyn_cast<PHINode>(&inst));
  }

  if (isa<CallInst>(&inst)) {
    return getTacticForCallInst(dyn_cast<CallInst>(&inst));
  }

  if (isa<ReturnInst>(&inst)) {
    return getTacticForReturnInst(dyn_cast<ReturnInst>(&inst));
  }

  if (isa<UnreachableInst>(&inst)) {
    return getTacticForUnreachableInst(dyn_cast<UnreachableInst>(&inst));
  }

  assert(false);
}

ref<CoqTactic> ModuleSupport::getTacticForBinaryOperator(BinaryOperator *inst) {
  if (isShitOperator(inst)) {
    return getTacticForShiftOperator(inst);
  }

  std::string constructor;
  switch (inst->getOpcode()) {
  case Instruction::Add:
    constructor = "IS_Add";
    break;

  case Instruction::Sub:
    constructor = "IS_Sub";
    break;

  case Instruction::Mul:
    constructor = "IS_Mul";
    break;

  case Instruction::URem:
    constructor = "IS_URem";
    break;

  case Instruction::SRem:
    constructor = "IS_SRem";
    break;

  case Instruction::And:
    constructor = "IS_And";
    break;

  case Instruction::Or:
    constructor = "IS_Or";
    break;

  case Instruction::Xor:
    constructor = "IS_Xor";
    break;

  default:
      assert(false);
  }

  ref<CoqTactic> opTactic = new Block({new Apply(constructor)});
  return new Block(
    {
      new Apply("IS_INSTR_Op"),
      new Apply("IS_OP_IBinop"),
      getTacticForValue(inst->getOperand(0)),
      getTacticForValue(inst->getOperand(1)),
      opTactic,
    }
  );
}

ref<CoqTactic> ModuleSupport::getTacticForShiftOperator(BinaryOperator *inst) {
  std::string constructor;
  switch (inst->getOpcode()) {
  case Instruction::Shl:
    constructor = "IS_Shl";
    break;

  case Instruction::LShr:
    constructor = "IS_LShr";
    break;

  default:
    assert(false);
  }

  ref<CoqTactic> opTactic = new Block({new Apply(constructor)});
  return new Block(
    {
      new Apply("IS_INSTR_Op"),
      new Apply("IS_OP_Shift"),
      opTactic,
      getTacticForValue(inst->getOperand(0)),
      new Block({new LIA()}),
      new Block({new LIA()}),
    }
  );
}

ref<CoqTactic> ModuleSupport::getTacticForCmpInst(CmpInst *inst) {
  return new Block(
    {
      new Apply("IS_INSTR_Op"),
      new Apply("IS_OP_ICmp"),
      getTacticForValue(inst->getOperand(0)),
      getTacticForValue(inst->getOperand(1)),
    }
  );
}

ref<CoqTactic> ModuleSupport::getTacticForCastInst(CastInst *inst) {
  std::string constructor;
  switch (inst->getOpcode()) {
    case Instruction::ZExt:
    constructor = "IS_ZExt";
    break;

  case Instruction::SExt:
    constructor = "IS_SExt";
    break;

  case Instruction::Trunc:
    constructor = "IS_Trunc";
    break;

  case Instruction::BitCast:
    constructor = "IS_Bitcast";
    break;

  default:
      assert(false);
  }

  ref<CoqTactic> opTactic = new Block({new Apply(constructor)});
  return new Block(
    {
      new Apply("IS_INSTR_Op"),
      new Apply("IS_OP_Conversion"),
      opTactic,
      getTacticForValue(inst->getOperand(0)),
    }
  );
}

ref<CoqTactic> ModuleSupport::getTacticForBranchInst(BranchInst *inst) {
  if (inst->isConditional()) {
    return new Block(
      {
        new Apply("IS_Term_Br"),
        getTacticForValue(inst->getCondition()),
      }
    );
  } else {
    return new Block(
      {new Apply("IS_Term_UnconditionalBr")}
    );
  }
}

ref<CoqTactic> ModuleSupport::getTacticForPHINode(PHINode *inst) {
  std::vector<ref<CoqTactic>> tactics;

  tactics.push_back(new Apply("IS_Phi"));
  tactics.push_back(new Intros({"bid", "e", "Hin"}));
  for (unsigned i = 0; i < inst->getNumIncomingValues(); i++) {
    tactics.push_back(new Destruct("Hin", {{"Hin"}, {"Hin"}}));
    tactics.push_back(
      new Block(
        {
          new Inversion("Hin"),
          new Subst(),
          getTacticForValue(inst->getIncomingValue(i)),
        }
      )
    );
  }

  tactics.push_back(new Destruct("Hin"));

  return new Block(tactics);
}

ref<CoqTactic> ModuleSupport::getTacticForCallInst(CallInst *inst) {
  std::vector<ref<CoqTactic>> tactics;

  Function *f = dyn_cast<Function>(inst->getCalledOperand());
  assert(f);

  Type *returnType = f->getFunctionType()->getReturnType();
  if (returnType->isVoidTy()) {
    tactics.push_back(new Apply("IS_INSTR_VoidCall"));
  } else {
    tactics.push_back(new Apply("IS_INSTR_Call"));
  }

  tactics.push_back(new Intros({"arg", "Hin"}));
  for (unsigned i = 0; i < inst->getNumArgOperands(); i++) {
    tactics.push_back(new Destruct("Hin", {{"Hin"}, {"Hin"}}));
    tactics.push_back(
      new Block(
        {
          new Inversion("Hin"),
          new Subst(),
          new Apply("IS_FunctionArg"),
          getTacticForValue(inst->getArgOperand(i)),
        }
      )
    );
  }

  tactics.push_back(new Destruct("Hin"));

  return new Block(tactics);
}

ref<CoqTactic> ModuleSupport::getTacticForReturnInst(ReturnInst *inst) {
  Value *v = inst->getReturnValue();
  if (v) {
    return new Block(
      {
        new Apply("IS_Term_Ret"),
        getTacticForValue(v),
      }
    );
  } else {
    return new Block(
      {new Apply("IS_Term_RetVoid")}
    );
  }
}

ref<CoqTactic> ModuleSupport::getTacticForUnreachableInst(UnreachableInst *inst) {
  return new Block(
    {new Apply("IS_Term_Unreachable")}
  );
}

ref<CoqTactic> ModuleSupport::getTacticForValue(Value *value) {
  if (isa<llvm::Argument>(value)) {
    return new Block(
      {new Apply("IS_EXP_Ident")}
    );
  } else if (isa<llvm::User>(value)) {
    if (isa<llvm::Constant>(value)) {
      if (isa<llvm::ConstantInt>(value)) {
        return new Block(
          {new Apply("IS_EXP_Integer")}
        );
      }
    } else if (isa<llvm::Instruction>(value)) {
      return new Block(
        {new Apply("IS_EXP_Ident")}
      );
    }
  }

  assert(false);
}

bool ModuleSupport::isShitOperator(BinaryOperator *inst) {
  switch (inst->getOpcode()) {
  case Instruction::Shl:
  case Instruction::LShr:
  case Instruction::AShr:
    return true;

  default:
    return false;
  }
}

ModuleSupport::~ModuleSupport() {

}
