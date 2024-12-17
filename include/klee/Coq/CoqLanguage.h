#ifndef KLEE_COQLANGUAGE_H
#define KLEE_COQLANGUAGE_H

#include "klee/ADT/Ref.h"

#include <map>
#include <string>
#include <vector>
#include <cstdint>

namespace klee {

template<class T> class ref;

class CoqExpr {

public:

  class ReferenceCounter _refCount;
  
  virtual std::string dump() const;

  virtual std::string pretty_dump(int indent = 0) const {
    return dump();
  }

  virtual ~CoqExpr() { }

};

class CoqVariable : public CoqExpr {

public:

    std::string name;

    CoqVariable(const std::string &name);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqInteger : public CoqExpr {

public:

    uint64_t n;

    CoqInteger(uint64_t n);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqString : public CoqExpr {

public:

    std::string s;

    CoqString(const std::string &s);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqApplication : public CoqExpr {

public:

    ref<CoqExpr> function;
    std::vector<ref<CoqExpr>> args;

    CoqApplication(const ref<CoqExpr> &function, const std::vector<ref<CoqExpr>> &args);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqPair : public CoqExpr {

public:

    ref<CoqExpr> left;
    ref<CoqExpr> right;

    CoqPair(const ref<CoqExpr> &left, const ref<CoqExpr> &right);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqListCons : public CoqExpr {

public:

    ref<CoqExpr> head;

    ref<CoqExpr> tail;

    CoqListCons(const ref<CoqExpr> &head, const ref<CoqExpr> &tail);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqList : public CoqExpr {

public:

    std::vector<ref<CoqExpr>> args;

    CoqList(const std::vector<ref<CoqExpr>> &args);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

class CoqBinOp : public CoqExpr {

public:

  std::string op;

  ref<CoqExpr> left;

  ref<CoqExpr> right;

  CoqBinOp(const std::string &op, const ref<CoqExpr> &left, const ref<CoqExpr> &right);

  std::string dump() const;

  std::string pretty_dump(int indent = 0) const;

};

class CoqEq : public CoqBinOp {

public:

  CoqEq(const ref<CoqExpr> &left, const ref<CoqExpr> &right);

};

class CoqAnd : public CoqBinOp {

public:

  CoqAnd(const ref<CoqExpr> &left, const ref<CoqExpr> &right);

};

class CoqImply : public CoqBinOp {

public:

  CoqImply(const ref<CoqExpr> &left, const ref<CoqExpr> &right);

};

class CoqImport : public CoqExpr {

public:

    std::string module_name;

    CoqImport(const std::string &module_name);

    std::string dump() const;
};

class CoqRequire : public CoqExpr {

public:

    std::string path;
    std::string module_name;
    bool use_import;

    CoqRequire(const std::string &path, const std::string &module_name, bool use_import = true);

    std::string dump() const;

};

class CoqDefinition : public CoqExpr {

public:

    std::string name;
    std::string type;
    ref<CoqExpr> body;

    CoqDefinition(const std::string &name, const std::string &type, const ref<CoqExpr> &body);

    CoqDefinition(const std::string &name, const ref<CoqExpr> &body);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;
};

ref<CoqExpr> createFalse();

ref<CoqExpr> createTrue();

ref<CoqExpr> createNat(uint64_t n);

ref<CoqExpr> createZ(uint64_t n);

ref<CoqExpr> createEmptyList();

ref<CoqExpr> createNone();

ref<CoqExpr> createSome(ref<CoqExpr> e);

ref<CoqExpr> createPlaceHolder();

class CoqTactic : public CoqExpr {

public:

    CoqTactic() : CoqExpr() {}

    virtual std::string dump() const;

    virtual std::string dump(int indent) const;

    virtual std::string pretty_dump(int indent = 0) const;

    virtual std::string dump(int indent, bool end) const;
};

class BasicTactic : public CoqTactic {

public:

    std::string name;

    std::vector<ref<CoqExpr>> args;

    BasicTactic(const std::string &name);

    BasicTactic(const std::string &name, const std::vector<ref<CoqExpr>> &args);

    std::string dump(int indent) const;
};

class Block : public CoqTactic {

public:

    std::vector<ref<CoqTactic>> tactics;

    Block(const std::vector<ref<CoqTactic>> &tactics);

    std::string dump(int indent) const;
};

class Admit : public BasicTactic {

public:

  Admit() : BasicTactic("admit") {}

};

class Assumption : public BasicTactic {

public:

  Assumption() : BasicTactic("assumption") {}

};

class Concat : public CoqTactic {

public:

    std::vector<ref<CoqTactic>> tactics;

    Concat(const std::vector<ref<CoqTactic>> &tactics);

    std::string dump(int indent) const;
};

class Destruct : public CoqTactic {

public:

  std::string var;

  std::vector<std::vector<std::string>> schemes;

  std::string eqn;

  Destruct(const std::string &var);

  Destruct(const std::string &var,
           const std::vector<std::vector<std::string>> &schemes);

  Destruct(const std::string &var,
           const std::vector<std::vector<std::string>> &schemes,
           const std::string &eqn);

  std::string dump(int indent, bool end) const;

};

/* TODO: inherit from some base class */
class Discriminate : public CoqTactic {

public:

  std::string hypothesis;

  Discriminate(const std::string &hypothesis);

  std::string dump(int indent) const;

};

class Exists : public CoqTactic {

public:

  ref<CoqExpr> e;

  Exists(ref<CoqExpr> e);

  std::string dump(int indent) const;

};

/* TODO: inherit from some base class */
class Intros : public CoqTactic {

public:

  std::vector<std::string> vars;

  Intros(const std::vector<std::string> &vars);

  std::string dump(int indent) const;

};

/* TODO: inherit from some base class */
class Inversion : public CoqTactic {

public:

  std::string hypothesis;

  Inversion(const std::string &hypothesis);

  std::string dump(int indent) const;

};

class Left : public BasicTactic {

public:

  Left() : BasicTactic("left") {}

};

class LIA : public BasicTactic {

public:

  LIA() : BasicTactic("lia") {}

};

class Simpl : public BasicTactic {

public:

  Simpl() : BasicTactic("simpl") {}

};

class Split : public CoqTactic {

public:

  ref<CoqTactic> t1, t2;

  Split(ref<CoqTactic> t1, ref<CoqTactic> t2);

  std::string dump(int indent) const;

};

class Subst : public BasicTactic {

public:

  Subst() : BasicTactic("subst") {}

};

class Reflexivity : public BasicTactic {

public:

  Reflexivity() : BasicTactic("reflexivity") {}

};

/* TODO: inherit from some base class */
class Rewrite : public CoqTactic {

public:

  std::string hypothesis;

  bool forward;

  Rewrite(const std::string &hypothesis, bool forward = true);

  std::string dump(int indent) const;

};

class Try : public CoqTactic {

public:

  std::vector<ref<CoqTactic>> tactics;

  Try(const std::vector<ref<CoqTactic>> &tactics);

  std::string dump(int indent) const;

  std::string dump(int indent, bool end) const;

};

class Right : public BasicTactic {

public:

  Right() : BasicTactic("right") {}

};

class Apply : public CoqTactic {

public:

  std::string name;

  std::vector<ref<CoqExpr>> args;

  std::map<std::string, ref<CoqExpr>> kwargs;

  std::string in;

  Apply(const std::string &name) : name(name) {}

  Apply(const std::string &name, const std::string &in) : name(name), in(in) {}

  Apply(const std::string &name, const std::vector<ref<CoqExpr>> &args) :
    name(name), args(args) {}

  Apply(const std::string &name,
        const std::map<std::string, ref<CoqExpr>> &kwargs,
        const std::string &in) :
    name(name), kwargs(kwargs), in(in) {}

  std::string dump(int indent) const;

  std::string dump(int indent, bool end) const;

};

class CoqLemma : public CoqExpr {

public:

  std::string name;

  std::vector<std::string> vars;

  ref<CoqExpr> body;

  ref<CoqTactic> proof;

  bool isAdmitted;

  CoqLemma(const std::string &name,
           const ref<CoqExpr> &body,
           const ref<CoqTactic> &proof,
           bool isAdmitted = false);

  CoqLemma(const std::string &name,
           const std::vector<std::string> &vars,
           const ref<CoqExpr> &body,
           const ref<CoqTactic> &proof,
           bool isAdmitted = false);

  std::string dump() const;

};

}

#endif
