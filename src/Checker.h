#ifndef CHECKER_H
#define CHECKER_H

#include "Domain.h"

class Checker {
public:
    Checker(domain::Domain& d) : dom_(d) {}
    bool Check();
private:
    domain::Domain& dom_;
};

#endif
