#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"

#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

#include <string>
#include <vector>

using namespace llvm;
using namespace klee;

ModuleTranslator::ModuleTranslator(Module &m) : m(m) {

}

ref<CoqExpr> ModuleTranslator::translate() {
  for (Function &f : m) {
    /* TODO: add predicate */
    if (!f.isIntrinsic()) {
      ref<CoqExpr> coq_f = translateFunction(f);
      errs() << coq_f->dump() << "\n";
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
      new CoqList({}),
      new CoqList({}),
    }
  );

  return coq_module;
}

ref<CoqExpr> ModuleTranslator::translateFunction(Function &f) {
  ref<CoqExpr> coq_f = new CoqApplication(
    new CoqVariable("mk_definition"),
    {
      new CoqVariable("_"),
      translateDecl(f),
      createArgs(f),
      createCFG(f),
    }
  );

  return coq_f;
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
    coq_bbs.push_back(translateBasicBlock(bb));
  }

  return new CoqApplication(
    new CoqVariable("mk_cfg"),
    {
      createName(entry.getName().str()),
      new CoqList(coq_bbs),
    }
  );
}

ref<CoqExpr> ModuleTranslator::translateBasicBlock(BasicBlock &bb) {
  std::vector<ref<CoqExpr>> coq_insts;

  for (Instruction &inst : bb) {
    ref<CoqExpr> coq_inst = translateInst(inst);
    coq_insts.push_back(coq_inst);
  }

  return new CoqApplication(
    new CoqVariable("mk_block"),
      {
        createName(bb.getName().str()),
        new CoqList(coq_insts),
      }
  );
}

ref<CoqExpr> ModuleTranslator::translateInst(Instruction &inst) {
  return new CoqVariable("None");
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

ref<CoqExpr> ModuleTranslator::createName(const std::string &name) {
  return new CoqApplication(
    new CoqVariable("Name"),
    { new CoqString(name), }
  );
}

ModuleTranslator::~ModuleTranslator() {

}
