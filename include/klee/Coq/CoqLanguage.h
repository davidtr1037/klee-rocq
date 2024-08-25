#ifndef KLEE_COQLANGUAGE_H
#define KLEE_COQLANGUAGE_H

#include "klee/ADT/Ref.h"

#include <string>
#include <vector>

namespace klee {

template<class T> class ref;

class CoqExpr {

public:

  class ReferenceCounter _refCount;
  
  virtual std::string dump() const;

  virtual ~CoqExpr() { }

};

class CoqVariable : public CoqExpr {

public:

    std::string name;

    CoqVariable(std::string name);

    std::string dump() const;

};

class CoqString : public CoqExpr {

public:

    std::string s;

    CoqString(std::string s);

    std::string dump() const;

};

class CoqApplication : public CoqExpr {

public:

    ref<CoqExpr> function;
    std::vector<ref<CoqExpr>> args;

    CoqApplication(const ref<CoqExpr> &function, const std::vector<ref<CoqExpr>> &args);

    std::string dump() const;

};

class CoqPair : public CoqExpr {

public:

    ref<CoqExpr> left;
    ref<CoqExpr> right;

    CoqPair(const ref<CoqExpr> &left, const ref<CoqExpr> &right);

    std::string dump() const;

};

class CoqList : public CoqExpr {

public:

    std::vector<ref<CoqExpr>> args;

    CoqList(const std::vector<ref<CoqExpr>> &args);

    std::string dump() const;

};

}

#endif
