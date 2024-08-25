#include "klee/ADT/Ref.h"

#include "klee/Coq/CoqLanguage.h"

//#include <iostream>
#include <string>
#include <sstream>

using namespace std;
using namespace klee;

string CoqExpr::dump() const {
  assert(false);
}

CoqVariable::CoqVariable(const string &name) : name(name) {

}

string CoqVariable::dump() const {
  return name;
}

CoqString::CoqString(const string &s) : s(s) {

}

string CoqString::dump() const {
  return "\"" + s + "\"" + "%string";
}

CoqApplication::CoqApplication(const ref<CoqExpr> &function,
                               const std::vector<ref<CoqExpr>> &args) :
    function(function), args(args) {

}

string CoqApplication::dump() const {
  std::ostringstream os;

  os << "(";
  os << function->dump();
  os << " ";

  for (size_t i = 0; i < args.size(); i++) {
    if (i != 0) {
      os << " ";
    }
    os << args[i]->dump();
  }

  os << ")";

  return os.str();
}

CoqPair::CoqPair(const ref<CoqExpr> &left, const ref<CoqExpr> &right) :
    left(left), right(right) {

}

string CoqPair::dump() const {
  std::ostringstream os;

  os << "(";
  os << left->dump();
  os << ", ";
  os << right->dump();
  os << ")";

  return os.str();
}

CoqList::CoqList(const std::vector<ref<CoqExpr>> &args) :
    args(args) {

}

string CoqList::dump() const {
  std::ostringstream os;

  os << "[";

  for (size_t i = 0; i < args.size(); i++) {
    if (i != 0) {
      os << "; ";
    }
    os << args[i]->dump();
  }

  os << "]";

  return os.str();
}
