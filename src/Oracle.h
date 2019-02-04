#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include "CodeCoordinate.h"
#include "Bridge.h"

using namespace bridge;

class Oracle
{
public:
	Oracle(Bridge& d) : dom_(d) {};

	// Precondition: true
	// Effects: get space annotation from environment
	// Postcondition: return value is space to associate with vector
	//
	Space& getSpaceForVector(string where);

	Space& getSpaceForAddExpression(bridge::Expr * left_br, bridge::Expr * right_br)
	{
		return *new Space("");
	}

	

private:

	Bridge& dom_;
};

#endif