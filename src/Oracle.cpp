// oracle.cpp
// implement the member functions in oracle header file

#include "Oracle.h"

Oracle::Oracle() {}

Space& Oracle::getSpaceForVector(const VectorASTNode& n) {
    /*
    STUB: Associate the same space with every vector.
    */
    static Space s;
    return s;
}

