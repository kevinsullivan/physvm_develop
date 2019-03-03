#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include "easylogging++.h"


namespace oracle {

class Oracle
{
public:
	Oracle(domain::Domain* d) : dom_(d), space_(*new domain::Space("Oracle:: Error. Stub Space.\n")) {};

	domain::Space &getSpace();

	//domain::Space& getSpace() { return space_; }
	//domain::Space& getSpaceForVector(std::string where);

	domain::Space& getSpaceForAddExpression(coords::VecExpr * left_br, coords::VecExpr * right_br)
	{
		//LOG(DEBUG) <<"Returning stub space for expression.\n";
		std::cout <<"Space for add expression?\n";
	//	LOG(DEBUG) <<"Right is \n" << right_br->toString() << "\n";
	//	LOG(DEBUG) <<"Left is \n" << left_br->toString() << "\n";
		return getSpace();
	}

	// TODO Change argument types here and below to those abstracted in AST.h, rather than clang

	domain::Space& getSpaceForVecIdent(const clang::VarDecl* v) {
		//LOG(DEBUG) <<"Returning stub space for identifier.\n";
		std::cout <<"Space for identifier?\n";
		//v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVector_Expr(ast::Vector_Expr *ctor_ast) {
		//LOG(DEBUG) <<"Space for vector constructed from expression?\n";
		std::cout <<"Space for literal?\n";
		//v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVector_Lit(const clang::CXXConstructExpr* v) {
		//LOG(DEBUG) <<"Space for vector constructed from literal?\n";
		std::cout <<"Space for literal?\n";
		//v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVecVarExpr(ast::VecVarExpr *ast)  {
		//LOG(DEBUG) <<"Space for literal?\n";
		std::cout <<"Space for variable expression?\n";
		ast->dump();
		return getSpace();
	}


	domain::Space& getSpaceForVecVarExp(ast::VecVarExpr *ast)  {
		//LOG(DEBUG) <<"Space for literal?\n";
		std::cout <<"Space for variable expression?\n";
		//ast->dump();
		return getSpace();
	}
private:
	domain::Space& space_;
	domain::Domain* dom_;
};

} // namespace

#endif