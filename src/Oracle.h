#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include "Coords.h"
#include "Domain.h"

namespace oracle {

class Oracle
{
public:
	Oracle(domain::Domain* d) : dom_(d) {};

	// Precondition: true
	// Effects: get space annotation from environment
	// Postcondition: return value is space to associate with vector
	//
	domain::Space& getSpaceForVector(string where);

	domain::Space& getSpaceForAddExpression(const domain::Expr * left_br, const domain::Expr * right_br)
	{
		//cerr << "Returning stub space for expression.\n";
		cerr << "Space for add expression?\n";
	//	cerr << "Right is \n" << right_br->toString() << "\n";
	//	cerr << "Left is \n" << left_br->toString() << "\n";
		return getSpace();
	}

	domain::Space& getSpaceForIdentifier(const clang::VarDecl* v) {
		//cerr << "Returning stub space for identifier.\n";
		cerr << "Space for identifier?\n";
		//v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForLitVector(const clang::CXXConstructExpr* v) {
		//cerr << "Space for literal?\n";
		cerr << "Space for literal?\n";
		v->dump();
		return getSpace();
	}

private:
	domain::Space& getSpace();
	domain::Domain* dom_;
};

} // namespace

#endif