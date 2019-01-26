#ifndef CHECKER_H
#define CHECKER_H

#include "Domain.h"

class Checker {
public:
    Checker(Domain& d) : dom_(d) {}
    bool Check();
private:
    Domain& dom_;
};

#endif
