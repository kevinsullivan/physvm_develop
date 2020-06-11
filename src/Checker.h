#ifndef CHECKER_H
#define CHECKER_H

#include "Interpretation.h" 

class Checker {
public:
    Checker(interp::Interpretation* i) : interp_(i) {}
    bool Check(); 
private:
    interp::Interpretation* interp_;
};

#endif
