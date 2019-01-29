#ifndef CHECKER_H
#define CHECKER_H

#include "Bridge.h"
using namespace bridge;

class Checker {
public:
    Checker(Bridge& d) : dom_(d) {}
    bool Check();
private:
    Bridge& dom_;
};

#endif
