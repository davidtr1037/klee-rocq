#include "klee/ADT/Ref.h"

#include "klee/Coq/CoqLanguage.h"

#include <string>
#include <sstream>

using namespace std;
using namespace klee;

static string space(int indent) {
  ostringstream os;
  for (int i = 0; i < indent; i++) {
    os << "  ";
  }
  return os.str();
}

string CoqExpr::dump() const {
  assert(false);
}

CoqVariable::CoqVariable(const string &name) : name(name) {

}

string CoqVariable::dump() const {
  return name;
}

string CoqVariable::pretty_dump(int indent) const {
  ostringstream os;
  os << space(indent) << name;
  return os.str();
}

CoqString::CoqString(const string &s) : s(s) {

}

string CoqString::dump() const {
  ostringstream os;
  os << "\"" << s << "\"" << "\%string";
  return os.str();
}

string CoqString::pretty_dump(int indent) const {
  ostringstream os;
  os << space(indent) << "\"" << s << "\"" << "\%string";
  return os.str();
}

CoqInteger::CoqInteger(uint64_t n) : n(n) {

}

string CoqInteger::dump() const {
  return to_string(n);
}

string CoqInteger::pretty_dump(int indent) const {
  ostringstream os;
  os << space(indent) << to_string(n);
  return os.str();
}

CoqApplication::CoqApplication(const ref<CoqExpr> &function,
                               const vector<ref<CoqExpr>> &args) :
    function(function), args(args) {

}

string CoqApplication::dump() const {
  ostringstream os;

  os << "(" << function->dump();
  for (size_t i = 0; i < args.size(); i++) {
    os << " " << args[i]->dump();
  }
  os << ")";

  return os.str();
}

string CoqApplication::pretty_dump(int indent) const {
  ostringstream os;

  os << space(indent) << "(" << function->pretty_dump(0) << "\n";
  for (size_t i = 0; i < args.size(); i++) {
    os << args[i]->pretty_dump(indent + 1) << "\n";
  }
  os << space(indent) << ")";

  return os.str();
}

CoqPair::CoqPair(const ref<CoqExpr> &left, const ref<CoqExpr> &right) :
    left(left), right(right) {

}

string CoqPair::dump() const {
  ostringstream os;
  os << "(" << left->dump() << ", " << right->dump() << ")";
  return os.str();
}

string CoqPair::pretty_dump(int indent) const {
  ostringstream os;

  os << space(indent) << "(\n";
  os << left->pretty_dump(indent + 1) << ",\n";
  os << right->pretty_dump(indent + 1) << "\n";
  os << space(indent) << ")";

  return os.str();
}

CoqList::CoqList(const vector<ref<CoqExpr>> &args) :
    args(args) {

}

string CoqList::dump() const {
  ostringstream os;

  os << "[";
  for (size_t i = 0; i < args.size(); i++) {
    os << args[i]->dump();
    if (i != args.size() - 1) {
      os << "; ";
    }
  }
  os << "]";

  return os.str();
}

string CoqList::pretty_dump(int indent) const {
  ostringstream os;

  if (args.size() == 0) {
    os << space(indent) << "[]";
  } else {
    os << space(indent) << "[\n";
    for (size_t i = 0; i < args.size(); i++) {
      os << args[i]->pretty_dump(indent + 1);
      if (i != args.size() - 1) {
        os << ";";
      }
      os << "\n";
    }
    os << space(indent) << "]";
  }

  return os.str();
}

CoqBinOp::CoqBinOp(const string &op,
                   const ref<CoqExpr> &left,
                   const ref<CoqExpr> &right) :
  op(op), left(left), right(right) {

}

string CoqBinOp::dump() const {
  ostringstream os;
  os << "(" << left->dump() << ") " << op << " (" << right->dump() << ")";
  return os.str();
}

string CoqBinOp::pretty_dump(int indent) const {
  ostringstream os;
  os << space(indent);
  os << "(" << left->pretty_dump() << ") " << op << " (" << right->pretty_dump() << ")";
  return os.str();
}

CoqEq::CoqEq(const ref<CoqExpr> &left, const ref<CoqExpr> &right) :
    CoqBinOp("=", left, right) {

}

CoqAnd::CoqAnd(const ref<CoqExpr> &left, const ref<CoqExpr> &right) :
    CoqBinOp("/\\", left, right) {

}

CoqImply::CoqImply(const ref<CoqExpr> &left, const ref<CoqExpr> &right) :
    CoqBinOp("->", left, right) {

}

CoqImport::CoqImport(const string &module_name) : module_name(module_name) {

}

string CoqImport::dump() const {
  ostringstream os;
  os << "Import " << module_name << ".";
  return os.str();
}

CoqRequire::CoqRequire(const string &path, const string &module_name, bool use_import) :
  path(path), module_name(module_name), use_import(use_import) {

}

string CoqRequire::dump() const {
  ostringstream os;
  os << "From " << path << " Require " << (use_import ? "Import " : "") << module_name << ".";
  return os.str();
}

CoqDefinition::CoqDefinition(const string &name,
                             const string &type,
                             const ref<CoqExpr> &body) :
  name(name), type(type), body(body) {

}

string CoqDefinition::dump() const {
  ostringstream os;
  os << "Definition " << name << " : " << type << " := " << body->dump() << ".\n";
  return os.str();
}

string CoqDefinition::pretty_dump(int indent) const {
  ostringstream os;
  os << "Definition " << name << " : " << type << " :=\n";
  os << body->pretty_dump(indent + 1) << ".\n";
  return os.str();
}

static klee::ref<CoqExpr> coqTrue = nullptr;

klee::ref<CoqExpr> klee::createTrue() {
  if (coqTrue.isNull()) {
    coqTrue = new CoqVariable("true");
  }
  return coqTrue;
}

static klee::ref<CoqExpr> coqFalse = nullptr;

klee::ref<CoqExpr> klee::createFalse() {
  if (coqTrue.isNull()) {
    coqFalse = new CoqVariable("false");
  }
  return coqFalse;
}

klee::ref<CoqExpr> klee::createZ(uint64_t n) {
  ostringstream os;
  os << "(" << n << ")" << "%Z";
  return new CoqVariable(os.str());
}

static klee::ref<CoqExpr> coqEmptyList = nullptr;

klee::ref<CoqExpr> klee::createEmptyList() {
  if (coqEmptyList.isNull()) {
    coqEmptyList = new CoqList({});
  }
  return coqEmptyList;
}

static klee::ref<CoqExpr> coqNone = nullptr;

klee::ref<CoqExpr> klee::createNone() {
  if (coqNone.isNull()) {
    coqNone = new CoqVariable("None");
  }
  return coqNone;
}

static klee::ref<CoqExpr> coqSomeConstructor = nullptr;

klee::ref<CoqExpr> klee::createSome(ref<CoqExpr> e) {
  if (coqSomeConstructor.isNull()) {
    coqSomeConstructor = new CoqVariable("Some");
  }
  return new CoqApplication(coqSomeConstructor, {e});
}

static klee::ref<CoqExpr> coqPlaceHolder = nullptr;

klee::ref<CoqExpr> klee::createPlaceHolder() {
  if (coqPlaceHolder.isNull()) {
    coqPlaceHolder = new CoqVariable("_");
  }
  return coqPlaceHolder;
}

/* Tactics */

string CoqTactic::dump() const {
  assert(false);
}

string CoqTactic::dump(int indent) const {
  return dump(indent, true);
}

string CoqTactic::pretty_dump(int indent) const {
  return dump(indent);
}

string CoqTactic::dump(int indent, bool end) const {
  assert(false);
}

BasicTactic::BasicTactic(const string &name) : name(name) {

}

BasicTactic::BasicTactic(const string &name, const vector<ref<CoqExpr>> &args) :
  name(name), args(args) {

}

string BasicTactic::dump(int indent) const {
  ostringstream os;
  os << space(indent) << name;
  for (ref<CoqExpr> e : args) {
    os << " " << e->dump();
  }
  os << ".";
  return os.str();
}

Block::Block(const vector<ref<CoqTactic>> &tactics) :
  tactics(tactics) {

}

string Block::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "{\n";
  for (ref<CoqTactic> t : tactics) {
    os << t->dump(indent + 1) << "\n";
  }
  os << space(indent) << "}";
  return os.str();
}

string Apply::dump(int indent) const {
  ostringstream os;
  os << space(indent);
  if (args.empty()) {
    os << "apply " << name;
    if (!in.empty()) {
      os << " in " << in;
    }
    os << ".";
  } else {
    os << "apply " << "(" << name;
    for (ref<CoqExpr> e : args) {
      os << " " << "(" << e->dump() << ")";
    }
    os << ")";
    if (!in.empty()) {
      os << " in " << in;
    }
    os << ".";
  }
  return os.str();
}

Concat::Concat(const vector<ref<CoqTactic>> &tactics) :
  tactics(tactics) {

}

string Concat::dump(int indent) const {
  ostringstream os;
  for (size_t i = 0; i < tactics.size(); i++) {
    if (i != tactics.size() - 1) {
      os << tactics[i]->dump(indent, false) << "\n";
    } else {
      os << tactics[i]->dump(indent);
    }
  }
  return os.str();
}

Destruct::Destruct(const string &var) : var(var) {

}

Destruct::Destruct(const string &var,
                   const vector<vector<string>> &schemes) :
  var(var), schemes(schemes) {

}

Destruct::Destruct(const string &var,
                   const vector<vector<string>> &schemes,
                   const string &eqn) :
  var(var), schemes(schemes), eqn(eqn) {

}

string Destruct::dump(int indent, bool end) const {
  ostringstream os;
  os << space(indent) << "destruct " << var;
  if (!schemes.empty()) {
    os << " as [";
    for (size_t i = 0; i < schemes.size(); i++) {
      for (size_t j = 0; j < schemes[i].size(); j++) {
        os << schemes[i][j];
        if (j != schemes[i].size() - 1) {
          os << " ";
        }
      }
      if (i != schemes.size() - 1) {
        os << " | ";
      }
    }
    os << "]";
  }
  if (!eqn.empty()) {
    os << " eqn:" << eqn;
  }
  os << (end ? "." : ";");
  return os.str();
}

Discriminate::Discriminate(const string &hypothesis) : hypothesis(hypothesis) {

}

string Discriminate::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "discriminate " << hypothesis << ".";
  return os.str();
}

Exists::Exists(ref<CoqExpr> e) : e(e) {

}

string Exists::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "exists (" << e->dump() << ").";
  return os.str();
}

Intros::Intros(const vector<string> &vars) : vars(vars) {

}

string Intros::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "intros";
  for (string v : vars) {
    os << " " << v;
  }
  os << ".";
  return os.str();
}

Inversion::Inversion(const string &hypothesis) : hypothesis(hypothesis) {

}

string Inversion::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "inversion " << hypothesis << ".";
  return os.str();
}

Split::Split(ref<CoqTactic> t1, ref<CoqTactic> t2) :
  t1(t1), t2(t2) {

}

string Split::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "split.\n";
  os << t1->dump(indent) << "\n";
  os << t2->dump(indent);
  return os.str();
}

Rewrite::Rewrite(const string &hypothesis, bool forward) :
  hypothesis(hypothesis), forward(forward) {

}

string Rewrite::dump(int indent) const {
  ostringstream os;
  os << space(indent) << "rewrite " << (forward ? "" : "<- ") << hypothesis << ".";
  return os.str();
}

CoqLemma::CoqLemma(const string &name,
                   const ref<CoqExpr> &body,
                   const ref<CoqTactic> &proof,
                   bool isAdmitted) :
  name(name), body(body), proof(proof), isAdmitted(isAdmitted) {

}

CoqLemma::CoqLemma(const string &name,
                   const vector<string> &vars,
                   const ref<CoqExpr> &body,
                   const ref<CoqTactic> &proof,
                   bool isAdmitted) :
  name(name), vars(vars), body(body), proof(proof), isAdmitted(isAdmitted) {

}

string CoqLemma::dump() const {
  ostringstream os;
  os << "Lemma " << name << " : ";
  if (!vars.empty()) {
    os << "forall";
    for (string v : vars) {
      os << " " << v;
    }
    os << ", ";
  }
  os << body->dump() << ".\n";

  os << "Proof.\n";
  if (!proof.isNull()) {
    os << proof->dump(0) << "\n";
  }
  if (isAdmitted) {
    os << "Admitted.\n";
  } else {
    os << "Qed.\n";
  }
  return os.str();
}
