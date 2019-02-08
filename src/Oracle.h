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
		//cerr << "Returning stub space for expression.\n";
		cout << "Space for add expression?\n";
		return getSpace();
	}

	Space& getSpaceForIdentifier(const clang::VarDecl* v) {
		//cerr << "Returning stub space for identifier.\n";
		cout << "Space for identifier?\n";
		return getSpace();
	}

	Space& getSpaceForLitVector(const clang::Expr* v) {
		//cerr << "Space for literal?\n";
		cout << "Space for literal?\n";
		return getSpace();
	}

private:
	Space& getSpace();
	Bridge& dom_;
};

#endif