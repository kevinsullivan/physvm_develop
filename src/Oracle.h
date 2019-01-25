#ifndef ORACLE_H
#define ORACLE_H

#include "Code.h"
#include "Domain.h"

class Oracle
{
public:
	Oracle(Domain& d) : dom_(d) {};

	// Precondition: true
	// Effects: get space annotation from environment
	// Postcondition: return value is space to associate with vector
	//
	Space& getSpaceForVector(const VectorASTNode& n);

	

private:

	Domain& dom_;
};

#endif