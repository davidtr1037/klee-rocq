#include "klee/Coq/CoqLanguage.h"
#include "klee/Coq/Translation.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"

#include <iostream>
#include <string>
#include <vector>

using namespace std;
using namespace llvm;
using namespace klee;

int main(int argc, char *argv[]) {
    LLVMContext context;
    SMDiagnostic err;

    if (argc != 2) {
        return 0;
    }

    char *path = argv[1];
    std::unique_ptr<Module> m = parseIRFile(path, err, context);

    //for (Function &f : *m) {
    //    for (BasicBlock &bb : f) {
    //        for (Instruction &i : bb) {
    //            errs() << i << "\n";
    //        }
    //    }
    //}

    ModuleTranslator t(*m);
    klee::ref<CoqExpr> e = t.translate();
    cout << e->dump() << "\n";

    return 0;
}
