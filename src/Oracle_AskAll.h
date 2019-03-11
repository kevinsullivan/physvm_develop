#ifndef ORACLE_ASKALL_H
#define ORACLE_ASKALL_H

#include "Oracle.h"
#include "Domain.h"

namespace oracle {

class Oracle_AskAll : public Oracle 
{
public:
	Oracle_AskAll(domain::Domain* d) : dom_(d) {}; 

	domain::Space &getSpace();

	domain::Space& getSpaceForAddExpression(coords::VecExpr *mem, coords::VecExpr *arg)
	{
		std::string query = "";
		query += "Space for expression, add  ";
		query += mem->toString();
		query += " ";
		query += arg->toString();
		query += ", at ";
		query += mem->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVecIdent(coords::VecIdent* v) {
	std::string query = "Space for vector identifier, ";
	query += v->toString();
	query += " at ";
	query += v->getSourceLoc();
	query += "? ";
	std::cout << query;
	return getSpace();
	}

	domain::Space& getSpaceForVector_Expr(coords::VecExpr *expr) {
		std::string query = "Space for vector constructed from expression, \n";
		query += expr->toString();  
		query += " at ";
		query += expr->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}


	domain::Space& getSpaceForVecParenExpr(coords::VecExpr *expr) {
		std::string query = "Space for vector parenthesized expression, \n";
		query += expr->toString();  
		query += " at ";
		query += expr->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}



	domain::Space& getSpaceForVector_Lit(coords::Vector_Lit *lit) {
		std::string query = "Space for vector constructed from literal, ";
		query += lit->toString();
		query += " at ";
		query += lit->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVecVarExpr(coords::VecVarExpr *var)  {
		std::string query = "Space for vector variable expression, ";
		query += var->toString();
		query += " at ";
		query += var->getSourceLoc();
		query += "? ";
		std::cout << query;
		return getSpace();
	}
private:
	domain::Domain* dom_;
};

} // namespace

#endif