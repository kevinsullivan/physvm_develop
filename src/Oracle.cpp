// oracle.cpp
// implement the member functions in oracle header file

#include "Oracle.h"
#include "Domain.h"

Space& Oracle::getSpaceForVector(const VectorASTNode& n) {
    /*
    TODO: Associate the same space with every vector.
    */
    list<Space>& spaces = dom_.getSpaces();
    // now ask user which space to return!

    // delete this when preceding code is complete
    static Space s;
    return s;
}

