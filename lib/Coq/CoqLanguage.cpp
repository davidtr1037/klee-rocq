#include "klee/ADT/Ref.h"

#include "klee/Coq/CoqLanguage.h"

#include <string>
#include <sstream>

using namespace std;
using namespace klee;

/* TODO: don't use std:: */

static string space(int indent) {
  std::ostringstream os;
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
  std::ostringstream os;
  os << space(indent) << name;
  return os.str();
}

CoqString::CoqString(const string &s) : s(s) {

}

string CoqString::dump() const {
  std::ostringstream os;
  os << "\"" << s << "\"" << "\%string";
  return os.str();
}

string CoqString::pretty_dump(int indent) const {
  std::ostringstream os;
  os << space(indent) << "\"" << s << "\"" << "\%string";
  return os.str();
}

CoqInteger::CoqInteger(uint64_t n) : n(n) {

}

string CoqInteger::dump() const {
  return std::to_string(n);
}

string CoqInteger::pretty_dump(int indent) const {
  std::ostringstream os;
  os << space(indent) << std::to_string(n);
  return os.str();
}

CoqApplication::CoqApplication(const ref<CoqExpr> &function,
                               const std::vector<ref<CoqExpr>> &args) :
    function(function), args(args) {

}

string CoqApplication::dump() const {
  std::ostringstream os;

  os << "(" << function->dump();
  for (size_t i = 0; i < args.size(); i++) {
    os << " " << args[i]->dump();
  }
  os << ")";

  return os.str();
}

string CoqApplication::pretty_dump(int indent) const {
  std::ostringstream os;

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
  std::ostringstream os;
  os << "(\n" << left->dump() << ", " << right->dump() << ")";
  return os.str();
}

string CoqPair::pretty_dump(int indent) const {
  std::ostringstream os;

  os << space(indent) << "(\n";
  os << left->pretty_dump(indent + 1) << ",\n";
  os << right->pretty_dump(indent + 1) << "\n";
  os << space(indent) << ")";

  return os.str();
}

CoqList::CoqList(const std::vector<ref<CoqExpr>> &args) :
    args(args) {

}

string CoqList::dump() const {
  std::ostringstream os;

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
  std::ostringstream os;

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

klee::ref<CoqExpr> klee::createZ(uint64_t n) {
  std::ostringstream os;
  os << "(" << n << ")" << "%Z";
  return new CoqVariable(os.str());
}

CoqImport::CoqImport(const string &module_name) : module_name(module_name) {

}

string CoqImport::dump() const {
  std::ostringstream os;
  os << "Import " << module_name << ".";
  return os.str();
}

CoqRequire::CoqRequire(const string &path, const std::string &module_name, bool use_import) :
  path(path), module_name(module_name), use_import(use_import) {

}

string CoqRequire::dump() const {
  std::ostringstream os;
  os << "From " << path << " Require " << (use_import ? "Import " : "") << module_name << ".";
  return os.str();
}

CoqDefinition::CoqDefinition(const std::string &name,
                             const std::string &type,
                             const ref<CoqExpr> &body) :
  name(name), type(type), body(body) {

}

string CoqDefinition::dump() const {
  std::ostringstream os;
  os << "Definition " << name << " : " << type << " := " << body->dump() << ".\n";
  return os.str();
}

string CoqDefinition::pretty_dump(int indent) const {
  std::ostringstream os;
  os << "Definition " << name << " : " << type << " :=\n";
  os << body->pretty_dump(indent + 1) << ".\n";
  return os.str();
}

static klee::ref<CoqExpr> coqNone = nullptr;

/* TODO: use where needed */
klee::ref<CoqExpr> klee::createNone() {
  if (coqNone.isNull()) {
    coqNone = new CoqVariable("None");
  }
  return coqNone;
}

static klee::ref<CoqExpr> coqSomeConstructor = nullptr;

/* TODO: use where needed */
klee::ref<CoqExpr> klee::createSome(ref<CoqExpr> e) {
  if (coqSomeConstructor.isNull()) {
    coqSomeConstructor = new CoqVariable("Some");
  }
  return new CoqApplication(coqSomeConstructor, {e});
}
