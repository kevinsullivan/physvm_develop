#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include "Domain.h"
#include "CodeCoordinate.h"


class Oracle
{
public:
	Oracle(Domain& d) : dom_(d) {};

	// Precondition: true
	// Effects: get space annotation from environment
	// Postcondition: return value is space to associate with vector
	//
	Space& getSpaceForVector(string where);

	

private:

	Domain& dom_;
};

#endif