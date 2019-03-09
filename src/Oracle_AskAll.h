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
		query += "Space for vector-vector add expression, ";
		query += mem->toString();
		query += " "; 
		query += arg->toString();
		query += "?";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVecIdent(coords::VecIdent* v) {
	std::string query = "Space for vector identifier, ";
	query += v->toString();
	query += "? ";
	std::cout << query;
	return getSpace();
	}

	domain::Space& getSpaceForVector_Expr(coords::VecExpr *expr_coords) {
		std::string query = "Space for vector constructed from expression, ?\n";
		query += expr_coords->toString();  
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVector_Lit(coords::Vector_Lit *coords) {
		std::string query = "Space for vector constructed from literal, ";
		query += coords->toString();
		query += "? ";
		std::cout << query;
		return getSpace();
	}

	domain::Space& getSpaceForVecVarExpr(coords::VecVarExpr *coords)  {
		std::string query = "Space for vector variable expression, ";
		query += coords->toString();
		query += "? ";
		std::cout << query;
		return getSpace();
	}
private:
	domain::Domain* dom_;
};

} // namespace

#endif