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
	domain::Space& getSpaceForVector(std::string where);

	domain::Space& getSpaceForAddExpression(coords::VecExpr * left_br, coords::VecExpr * right_br)
	{
		//LOG(INFO) <<"Returning stub space for expression.\n";
		LOG(INFO) <<"Space for add expression?\n";
	//	LOG(INFO) <<"Right is \n" << right_br->toString() << "\n";
	//	LOG(INFO) <<"Left is \n" << left_br->toString() << "\n";
		return getSpace();
	}

	domain::Space& getSpaceForVecIdent(const clang::VarDecl* v) {
		//LOG(INFO) <<"Returning stub space for identifier.\n";
		LOG(INFO) <<"Space for identifier?\n";
		//v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVector_Lit(const clang::CXXConstructExpr* v) {
		//LOG(INFO) <<"Space for literal?\n";
		LOG(INFO) <<"Space for literal?\n";
		v->dump();
		return getSpace();
	}

	domain::Space& getSpaceForVecVarExpr(ast::VecVarExpr *ast)  {
		//LOG(INFO) <<"Space for literal?\n";
		LOG(INFO) <<"Space for variable expression?\n";
		ast->dump();
		return getSpace();
	}


	domain::Space& getSpaceForVecVarExp(ast::VecVarExpr *ast)  {
		//LOG(INFO) <<"Space for literal?\n";
		LOG(INFO) <<"Space for variable expression?\n";
		ast->dump();
		return getSpace();
	}
private:
	domain::Space& space_;
	domain::Domain* dom_;
};

} // namespace

#endif