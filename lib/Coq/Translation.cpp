#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Constants.h"

#include "klee/Support/ErrorHandling.h"
#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

#include <string>
#include <set>
#include <vector>

using namespace llvm;
using namespace klee;

/* TODO: handle constants: true, false, null */

ModuleTranslator::ModuleTranslator(Module &m) :
  m(m), moduleAlias(nullptr), moduleDef(nullptr) {

}

ref<CoqExpr> ModuleTranslator::translateModuleCached() {
  if (moduleAlias.isNull()) {
    ref<CoqExpr> coqModule = translateModule();
    std::string varName = "mdl";
    moduleAlias = new CoqVariable(varName);
    moduleDef = new CoqDefinition(varName, "llvm_module", coqModule);
  }

  return moduleAlias;
}

ref<CoqExpr> ModuleTranslator::translateModule() {
  std::vector<ref<CoqExpr>> coq_decls;
  std::vector<ref<CoqExpr>> coq_defs;

  for (Function &f : m) {
    if (isSupportedFunction(f)) {
      if (f.isDeclaration()) {
        ref<CoqExpr> coq_decl = translateDeclCached(f);
        coq_decls.push_back(coq_decl);
      } else {
        ref<CoqExpr> coq_f = translateFunctionCached(f);
        coq_defs.push_back(coq_f);
      }
    } else {
      //klee_warning("Ignoring unsupported function: %s", f.getName().str().c_str());
    }
  }

  ref<CoqExpr> coq_module = new CoqApplication(
    new CoqVariable("mk_module"),
    {
      new CoqVariable("None"),
      new CoqVariable("None"),
      new CoqVariable("None"),
      new CoqList({}),
      new CoqList({}),
      new CoqList(coq_decls),
      new CoqList(coq_defs),
    }
  );

  return coq_module;
}

ref<CoqExpr> ModuleTranslator::translateFunctionCached(Function &f) {
  auto i = functionCache.find(&f);
  if (i != functionCache.end()) {
    return i->second;
  }

  ref<CoqExpr> expr = translateFunction(f);
  std::string varName = "def_" + f.getName().str();
  ref<CoqExpr> alias = new CoqVariable(varName);
  functionCache.insert(std::make_pair(&f, alias));
  ref<CoqExpr> def = new CoqDefinition(varName, "llvm_definition", expr);
  functionDefs.push_back(def);

  return alias;
}

ref<CoqExpr> ModuleTranslator::translateFunction(Function &f) {
  ref<CoqExpr> coq_f = new CoqApplication(
    new CoqVariable("mk_definition"),
    {
      new CoqVariable("_"),
      translateDeclCached(f),
      createArgs(f),
      createCFG(f),
    }
  );

  return coq_f;
}

ref<CoqExpr> ModuleTranslator::translateDeclCached(Function &f) {
  auto i = declCache.find(&f);
  if (i != declCache.end()) {
    return i->second;
  }

  ref<CoqExpr> expr = translateDecl(f);
  std::string varName = "decl_" + f.getName().str();
  ref<CoqExpr> alias = new CoqVariable(varName);
  declCache.insert(std::make_pair(&f, alias));
  ref<CoqExpr> def = new CoqDefinition(varName, "llvm_declaration", expr);
  declDefs.push_back(def);

  return alias;
}

ref<CoqExpr> ModuleTranslator::translateDecl(Function &f) {
  return new CoqApplication(
    new CoqVariable("mk_declaration"),
    {
      createName(f.getName().str()),
      createFunctionType(f),
      createParamAttrs(f),
      createAttrs(f),
      createAnnotations(f),
    }
  );
}

ref<CoqExpr> ModuleTranslator::createFunctionType(Function &f) {
  FunctionType *ft = f.getFunctionType();
  assert(!ft->isVarArg());

  std::vector<ref<CoqExpr>> arg_types;
  for (Type *t : ft->params()) {
    arg_types.push_back(translateType(t));
  }

  return new CoqApplication(
    new CoqVariable("TYPE_Function"),
    {
      translateType(ft->getReturnType()),
      new CoqList(arg_types),
      new CoqVariable("false"),
    }
  );
}

/* TODO: ... */
ref<CoqExpr> ModuleTranslator::createParamAttrs(Function &f) {
  return new CoqPair(
    new CoqList({}),
    new CoqList({new CoqList({}), new CoqList({})})
  );
}

/* TODO: ... */
ref<CoqExpr> ModuleTranslator::createAttrs(Function &f) {
  return new CoqList({});
}

/* TODO: ... */
ref<CoqExpr> ModuleTranslator::createAnnotations(Function &f) {
  return new CoqList({});
}

ref<CoqExpr> ModuleTranslator::createArgs(Function &f) {
  std::vector<ref<CoqExpr>> coq_args;

  for (Argument &arg : f.args()) {
    coq_args.push_back(createName(arg.getName().str()));
  }

  return new CoqList(coq_args);
}

ref<CoqExpr> ModuleTranslator::createCFG(Function &f) {
  std::vector<ref<CoqExpr>> coq_bbs;
  BasicBlock &entry = f.getEntryBlock();

  for (BasicBlock &bb : f) {
    coq_bbs.push_back(translateBasicBlockCached(bb));
  }

  return new CoqApplication(
    new CoqVariable("mk_cfg"),
    {
      createName(entry.getName().str()),
      new CoqList(coq_bbs),
    }
  );
}

ref<CoqExpr> ModuleTranslator::translateBasicBlockCached(BasicBlock &bb) {
  auto i = bbCache.find(&bb);
  if (i != bbCache.end()) {
    return i->second;
  }

  uint64_t bbId = getBasicBlockID(bb);
  std::string varName = "bb_" + std::to_string(bbId);

  ref<CoqExpr> expr = translateBasicBlock(bb);
  ref<CoqExpr> alias = new CoqVariable(varName);

  bbCache.insert(std::make_pair(&bb, alias));
  ref<CoqExpr> def = new CoqDefinition(varName, "llvm_block", expr);
  bbDefs.push_back(def);

  return alias;
}

uint64_t ModuleTranslator::getBasicBlockID(BasicBlock &bb) {
  uint64_t id;
  auto i = bbIds.find(&bb);
  if (i == bbIds.end()) {
    id = bbIds.size();
    bbIds.insert(std::make_pair(&bb, id));
  } else {
    id = i->second;
  }

  return id;
}

ref<CoqExpr> ModuleTranslator::translateBasicBlock(BasicBlock &bb) {
  std::vector<ref<CoqExpr>> coq_insts;

  for (Instruction &inst : bb) {
    ref<CoqExpr> coq_inst = translateInstCached(inst);
    /* TODO: add ignore predicate? */
    if (!coq_inst.isNull()) {
      coq_insts.push_back(coq_inst);
    }
  }

  return new CoqApplication(
    new CoqVariable("mk_block"),
      {
        createName(bb.getName().str()),
        new CoqList(coq_insts),
        new CoqVariable("None"),
      }
  );
}

ref<CoqExpr> ModuleTranslator::translateInstCached(Instruction &inst) {
  auto i = instCache.find(&inst);
  if (i != instCache.end()) {
    return i->second;
  }

  uint64_t instId = getInstID(inst);
  std::string varName = "inst_" + std::to_string(instId);

  ref<CoqExpr> expr = translateInst(inst);
  if (expr.isNull()) {
    /* TODO: ... */
    return nullptr;
  }

  ref<CoqExpr> alias = new CoqVariable(varName);

  instCache.insert(std::make_pair(&inst, alias));
  ref<CoqExpr> def = new CoqDefinition(varName, "llvm_cmd", expr);
  instDefs.push_back(def);

  return alias;
}

uint64_t ModuleTranslator::getInstID(Instruction &inst) {
  uint64_t id;
  auto i = instIDs.find(&inst);
  if (i == instIDs.end()) {
    id = instIDs.size();
    instIDs.insert(std::make_pair(&inst, id));
  } else {
    id = i->second;
  }

  return id;
}

ref<CoqExpr> ModuleTranslator::translateInst(Instruction &inst) {
  ref<CoqExpr> coq_inst = nullptr;

  if (isa<BinaryOperator>(&inst)) {
    return translateBinaryOperator(dyn_cast<BinaryOperator>(&inst));
  }

  if (isa<CmpInst>(&inst)) {
    return translateCmpInst(dyn_cast<CmpInst>(&inst));
  }

  if (isa<BranchInst>(&inst)) {
    return translateBranchInst(dyn_cast<BranchInst>(&inst));
  }

  if (isa<PHINode>(&inst)) {
    return translatePHINode(dyn_cast<PHINode>(&inst));
  }

  if (isa<CallInst>(&inst)) {
    return translateCallInst(dyn_cast<CallInst>(&inst));
  }

  if (isa<ReturnInst>(&inst)) {
    return translateReturnInst(dyn_cast<ReturnInst>(&inst));
  }

  if (isa<UnreachableInst>(&inst)) {
    return translateUnreachableInst(dyn_cast<UnreachableInst>(&inst));
  }

  assert(false);
}

ref<CoqExpr> ModuleTranslator::translateBinaryOperator(BinaryOperator *inst) {
  Value *v1 = inst->getOperand(0);
  Value *v2 = inst->getOperand(1);

  assert(v1->getType() == v2->getType());
  Type *operandType = v1->getType();

  if (inst->getOpcode() == Instruction::Add) {
    return createCMDInst(
      getInstID(inst),
      createBinOp(
        createName(inst->getName().str()),
        new CoqApplication(
          new CoqVariable("LLVMAst.Add"),
          {new CoqVariable("false"), new CoqVariable("false"), }
        ),
        translateType(operandType),
        translateValue(v1),
        translateValue(v2)
      )
    );
  }

  assert(false);
}

ref<CoqExpr> ModuleTranslator::createBinOp(ref<CoqExpr> target,
                                           ref<CoqExpr> ibinop,
                                           ref<CoqExpr> arg_type,
                                           ref<CoqExpr> arg1,
                                           ref<CoqExpr> arg2) {
  return new CoqApplication(
    new CoqVariable("INSTR_Op"),
    {
      target,
      new CoqApplication(
        new CoqVariable("OP_IBinop"),
        {
          ibinop,
          arg_type,
          arg1,
          arg2,
        }
      ),
    }
  );
}

ref<CoqExpr> ModuleTranslator::translateCmpInst(CmpInst *inst) {
  Value *v1 = inst->getOperand(0);
  Value *v2 = inst->getOperand(1);

  assert(v1->getType() == v2->getType());
  Type *operandType = v1->getType();

  std::string op;
  switch (inst->getPredicate()) {
  case ICmpInst::ICMP_EQ:
    op = "Eq";
    break;

  case ICmpInst::ICMP_NE:
    op = "Ne";
    break;

  case ICmpInst::ICMP_UGT:
    op = "Ugt";
    break;

  case ICmpInst::ICMP_UGE:
    op = "Uge";
    break;

  case ICmpInst::ICMP_ULT:
    op = "Ult";
    break;

  case ICmpInst::ICMP_ULE:
    op = "Ule";
    break;

  case ICmpInst::ICMP_SGT:
    op = "Sgt";
    break;

  case ICmpInst::ICMP_SGE:
    op = "Sge";
    break;

  case ICmpInst::ICMP_SLT:
    op = "Slt";
    break;

  case ICmpInst::ICMP_SLE:
    op = "Sle";
    break;

  default:
    assert(false);
  }

  return createCMDInst(
    getInstID(inst),
    createCmpOp(
      createName(inst->getName().str()),
      new CoqVariable(op),
      translateType(operandType),
      translateValue(v1),
      translateValue(v2)
    )
  );
}


ref<CoqExpr> ModuleTranslator::createCmpOp(ref<CoqExpr> target,
                                           ref<CoqExpr> icmp,
                                           ref<CoqExpr> arg_type,
                                           ref<CoqExpr> arg1,
                                           ref<CoqExpr> arg2) {
  return new CoqApplication(
    new CoqVariable("INSTR_Op"),
    {
      target,
      new CoqApplication(
        new CoqVariable("OP_ICmp"),
        {
          icmp,
          arg_type,
          arg1,
          arg2,
        }
      ),
    }
  );
}

ref<CoqExpr> ModuleTranslator::translateBranchInst(BranchInst *inst) {
  if (inst->isUnconditional()) {
    BasicBlock *bb = inst->getSuccessor(0);
    return createCMDTerm(
      getInstID(inst),
      new CoqApplication(
        new CoqVariable("TERM_UnconditionalBr"),
        { createName(bb->getName().str()), }
      )
    );
  }

  if (inst->isConditional()) {
    assert(inst->getNumSuccessors() == 2);
    std::vector<ref<CoqExpr>> bb_ids;
    for (unsigned i = 0; i < inst->getNumSuccessors(); i++) {
      BasicBlock *bb = inst->getSuccessor(i);
      bb_ids.push_back(createName(bb->getName().str()));
    }

    return createCMDTerm(
      getInstID(inst),
      new CoqApplication(
        new CoqVariable("TERM_Br"),
        {
          new CoqPair(
            translateType(inst->getCondition()->getType()),
            translateValue(inst->getCondition())
          ),
          bb_ids[0],
          bb_ids[1],
        }
      )
    );
  }

  assert(false);
}

ref<CoqExpr> ModuleTranslator::translatePHINode(PHINode *inst) {
  std::vector<ref<CoqExpr>> incoming;

  assert(inst->getNumIncomingValues() > 0);
  for (unsigned i = 0; i < inst->getNumIncomingValues(); i++) {
    BasicBlock *bb = inst->getIncomingBlock(i);
    Value *v = inst->getIncomingValue(i);

    ref<CoqExpr> node = new CoqPair(
      createName(bb->getName().str()),
      translateValue(v)
    );

    incoming.push_back(node);
  }

  return createCMDPhi(
    getInstID(inst),
    new CoqApplication(
      new CoqVariable("Phi"),
      {
        createName(inst->getName().str()),
        translateType(inst->getType()),
        new CoqList(incoming),
      }
    )
  );
}

ref<CoqExpr> ModuleTranslator::translateCallInst(CallInst *inst) {
  if (shouldIgnoreCall(inst)) {
    return nullptr;
  }

  Function *f = dyn_cast<Function>(inst->getCalledOperand());
  assert(f);

  FunctionType *ft = f->getFunctionType();
  Type *returnType = ft->getReturnType();

  std::vector<ref<CoqExpr>> coq_args = translateArgs(inst);

  if (returnType->isVoidTy()) {
    return createCMDInst(
      getInstID(inst),
      new CoqApplication(
        new CoqVariable("INSTR_VoidCall"),
        {
          new CoqPair(
            translateType(returnType),
            createGlobalID(f->getName().str())
          ),
          new CoqList(coq_args),
          new CoqList({}),
        }
      )
    );
  } else {
    return createCMDInst(
      getInstID(inst),
      new CoqApplication(
        new CoqVariable("INSTR_Call"),
        {
          createName(inst->getName().str()),
          new CoqPair(
            translateType(inst->getType()),
            createGlobalID(f->getName().str())
          ),
          new CoqList(coq_args),
          new CoqList({}),
        }
      )
    );
  }
}

static std::set<std::string> functions_to_ignore = {
    "__assert_fail",
};

bool ModuleTranslator::shouldIgnoreCall(CallInst *inst) {
  Function *f = dyn_cast<Function>(inst->getCalledOperand());
  assert(f);

  if (f->isIntrinsic()) {
    return true;
  }

  if (functions_to_ignore.find(f->getName().str()) != functions_to_ignore.end()) {
    return true;
  }

  return false;
}

std::vector<ref<CoqExpr>> ModuleTranslator::translateArgs(CallInst *inst) {
  std::vector<ref<CoqExpr>> coq_args;
  for (unsigned i = 0; i < inst->getNumArgOperands(); i++) {
    Value *arg = inst->getArgOperand(i);
    ref<CoqExpr> coq_arg = new CoqPair(
      new CoqPair(
        translateType(arg->getType()),
        translateValue(arg)
      ),
      new CoqList({})
    );
    coq_args.push_back(coq_arg);
  }

  return coq_args;
}

ref<CoqExpr> ModuleTranslator::translateReturnInst(ReturnInst *inst) {
  Value *v = inst->getReturnValue();
  if (v) {
    Type *returnType = v->getType();
    return createCMDTerm(
      getInstID(inst),
      new CoqApplication(
        new CoqVariable("TERM_Ret"),
        {
          new CoqPair(
            translateType(returnType),
            translateValue(v)
          )
        }
      )
    );
  } else {
    return createCMDTerm(
      getInstID(inst),
      new CoqVariable("TERM_RetVoid")
    );
  }
}

ref<CoqExpr> ModuleTranslator::translateUnreachableInst(UnreachableInst *inst) {
  return createCMDTerm(
    getInstID(inst),
    new CoqVariable("TERM_Unreachable")
  );
}

/* TODO: manage command id's */
/* TODO: pass the name of the constructor? */
ref<CoqExpr> ModuleTranslator::createCMDInst(uint64_t id, ref<CoqExpr> e) {
  return new CoqApplication(
    new CoqVariable("CMD_Inst"),
    {
      new CoqVariable(std::to_string(id)),
      e,
    }
  );
}

ref<CoqExpr> ModuleTranslator::createCMDTerm(uint64_t id, ref<CoqExpr> e) {
  return new CoqApplication(
    new CoqVariable("CMD_Term"),
    {
      new CoqVariable(std::to_string(id)),
      e,
    }
  );
}

ref<CoqExpr> ModuleTranslator::createCMDPhi(uint64_t id, ref<CoqExpr> e) {
  return new CoqApplication(
    new CoqVariable("CMD_Phi"),
    {
      new CoqVariable(std::to_string(id)),
      e,
    }
  );
}

ref<CoqExpr> ModuleTranslator::translateValue(Value *value) {
  if (isa<llvm::Argument>(value)) {
    return createLocalID(value->getName().str());
  } else if (isa<llvm::User>(value)) {
    if (isa<llvm::Constant>(value)) {
      if (isa<llvm::ConstantInt>(value)) {
        return new CoqApplication(
          new CoqVariable("EXP_Integer"),
          { createZ(cast<ConstantInt>(value)->getZExtValue()), }
        );
      } else if (isa<llvm::UndefValue>(value)) {
        return new CoqVariable("EXP_Undef");
      }
    } else if (isa<llvm::Instruction>(value)) {
      return createLocalID(value->getName().str());
    }
  }

  assert(false);
}

ref<CoqExpr> ModuleTranslator::translateType(Type *t) {
  if (t->isIntegerTy()) {
    IntegerType *it = dyn_cast<IntegerType>(t);
    return new CoqApplication(
      new CoqVariable("TYPE_I"),
      { new CoqVariable(std::to_string(it->getBitWidth())), }
    );
  }
 
  if (t->isVoidTy()) {
    return new CoqVariable("TYPE_Void");
  }

  assert(false);
  return nullptr;
}

ref<CoqExpr> ModuleTranslator::createLocalID(const std::string &name) {
  return new CoqApplication(
    new CoqVariable("EXP_Ident"),
    {
      new CoqApplication(
        new CoqVariable("ID_Local"),
        { createName(name), }
      ),
    }
  );
}

ref<CoqExpr> ModuleTranslator::createGlobalID(const std::string &name) {
  return new CoqApplication(
    new CoqVariable("EXP_Ident"),
    {
      new CoqApplication(
        new CoqVariable("ID_Global"),
        { createName(name), }
      ),
    }
  );
}

ref<CoqExpr> ModuleTranslator::createName(const std::string &name) {
  return new CoqApplication(
    new CoqVariable("Name"),
    { new CoqString(name), }
  );
}

bool ModuleTranslator::isSupportedFunction(Function &f) {
  if (f.isIntrinsic()) {
    return false;
  }

  if (!isSupportedType(f.getReturnType())) {
    return false;
  }

  for (Argument &arg : f.args()) {
    if (!isSupportedType(arg.getType())) {
      return false;
    }
  }

  return true;
}

/* TODO: use in this module */
bool ModuleTranslator::isSupportedInst(Instruction &inst) {
  if (isa<CallInst>(&inst)) {
    return !shouldIgnoreCall(dyn_cast<CallInst>(&inst));
  }

  return true;
}

bool ModuleTranslator::isSupportedType(Type *t) {
  return (t->isIntegerTy() || t->isVoidTy());
}

uint64_t ModuleTranslator::getInstID(Instruction *inst) {
  uint64_t id;

  auto i = instIDs.find(inst);
  if (i == instIDs.end()) {
    id = instIDs.size();
    instIDs.insert(std::make_pair(inst, id));
  } else {
    id = i->second;
  }

  return id;
}

ModuleTranslator::~ModuleTranslator() {

}
