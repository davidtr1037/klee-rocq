#ifndef KLEE_COQLANGUAGE_H
#define KLEE_COQLANGUAGE_H

#include "klee/ADT/Ref.h"

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

class CoqList : public CoqExpr {

public:

    std::vector<ref<CoqExpr>> args;

    CoqList(const std::vector<ref<CoqExpr>> &args);

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;

};

ref<CoqExpr> createZ(uint64_t n);

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

    std::string dump() const;

    std::string pretty_dump(int indent = 0) const;
};

ref<CoqExpr> createEmptyList();

ref<CoqExpr> createNone();

ref<CoqExpr> createSome(ref<CoqExpr> e);

class CoqTactic : public CoqExpr {

public:

    CoqTactic() : CoqExpr() {}

    virtual std::string dump() const;

    virtual std::string dump(int indent) const;

    virtual std::string pretty_dump(int indent = 0) const;
};

class BasicTactic : public CoqTactic {

public:

    std::string name;

    std::vector<ref<CoqExpr>> args;

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

  Admit() : BasicTactic("admit", {}) {}

};

class Apply : public CoqTactic {

public:

  std::string name;

  std::vector<ref<CoqExpr>> args;

  Apply(const std::string &name) : name(name) {}

  Apply(const std::string &name, const std::vector<ref<CoqExpr>> &args) :
    name(name), args(args) {}

  std::string dump(int indent) const;
};

class CoqLemma : public CoqExpr {

public:

  std::string name;

  ref<CoqExpr> body;

  ref<CoqTactic> proof;

  bool isAdmitted;

  CoqLemma(const std::string &name,
           const ref<CoqExpr> &body,
           const ref<CoqTactic> &proof,
           bool isAdmitted = false);

  std::string dump() const;
};

}

#endif
