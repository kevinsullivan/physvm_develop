

#ifndef CHECKER_H
#define CHECKER_H
#include <unistd.h>
#include <iostream>

#include "Interpretation.h" 
struct aFile {
    FILE* file;
    const char* name;
};

class Checker {
public:
    Checker(interp::Interpretation* i) : interp_(i) {}
    bool Check(); 
    bool RebuildOutput();//std::string);
    bool Setup();
private:
    interp::Interpretation* interp_;
    //aFile* to_check_;
};

#endif
