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
		cerr << "Space for add expression?\n";
		cerr << "Left is \n" << left_br->toString() << "\n";
		cerr << "Right is \n" << right_br->toString() << "\n";
		return getSpace();
	}

	Space& getSpaceForIdentifier(const clang::VarDecl* v) {
		//cerr << "Returning stub space for identifier.\n";
		cerr << "Space for identifier?\n";
		v->dump();
		return getSpace();
	}

	Space& getSpaceForLitVector(const clang::Expr* v) {
		//cerr << "Space for literal?\n";
		cerr << "Space for literal?\n";
		v->dump();
		return getSpace();
	}

private:
	Space& getSpace();
	Bridge& dom_;
};

#endif