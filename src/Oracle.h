#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include <iostream>
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
	domain::Space& getSpaceForVector(std::string where);

	domain::Space& getSpaceForAddExpression(Coords::VecExpr * left_br, coords::VecExpr * right_br)
	{
		//std::cerr << "Returning stub space for expression.\n";
		std::cerr << "Space for add expression?\n";
	//	std::cerr << "Right is \n" << right_br->toString() << "\n";
	//	std::cerr << "Left is \n" << left_br->toString() << "\n";
		return getSpace();
	}

	domain::Space& getSpaceForVecIdent(const clang::VarDecl* v) {
		//std::cerr << "Returning stub space for identifier.\n";
		std::cerr << "Space for identifier?\n";
		//v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVector_Lit(const clang::CXXConstructExpr* v) {
		//std::cerr << "Space for literal?\n";
		std::cerr << "Space for literal?\n";
		v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVecVarExpr(ast::VecVarExpr *ast)  {
		//std::cerr << "Space for literal?\n";
		std::cerr << "Space for variable expression?\n";
		ast->dump();
		return getSpace();
	}


	domain::Space& getSpaceForVecVarExp(ast::VecVarExpr *ast)  {
		//std::cerr << "Space for literal?\n";
		std::cerr << "Space for variable expression?\n";
		ast->dump();
		return getSpace();
	}
private:
	domain::Space& getSpace();
	domain::Domain* dom_;
};

} // namespace

#endif