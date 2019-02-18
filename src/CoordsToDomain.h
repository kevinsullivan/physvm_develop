#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include <unordered_map>

/*
	When putting, we know precise subclass, so we don't include
	putters for Expr and Vector super-classes. When getting, we 
	generally don't know, so we can return superclass pointers.
*/

/*
We currently require client to create domain nodes, which we 
then map to and from the given coordinates. From coordinates 
is currently implement as unordered map. From domain object is
currently implemented as domain object method. This enables us
to return precisely typed objects without having to maintain a
lot of separate mapping tables.
*/

namespace coords2domain {

class CoordsToDomain
{
  public:

// Ident

	void putVecIdent(coords::VecIdent *key, domain::VecIdent *i);
	domain::VecIdent *getVecIdent(coords::VecIdent *c) const;
	coords::VecIdent *getVecIdent(domain::VecIdent *d) const;

// Expr

	domain::VecExpr *getVecExpr(coords::VecExpr* c);
	coords::VecExpr *getVecExpr(domain::VecExpr* d) const;

/*	void putVecLitExpr(coords::VecLitExpr n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(coords::VecLitExpr c) const;
	coords::VecLitExpr *getLitInterp(domain::VecLitExpr d) const;*/

	void PutVecVarExpr(coords::VecVarExpr *n, domain::VecVarExpr *e);
	domain::VecVarExpr *getVecVarExpr(coords::VecVarExpr* c) const;
	coords::VecVarExpr *getVecVarExpr(domain::VecVarExpr* d) const;

	void PutVecVecAddExpr(coords::VecVecAddExpr *n, domain::VecVecAddExpr *e);
	domain::VecVecAddExpr *getVecVecAddExpr(coords::VecVecAddExpr* c) const;
	coords::VecVecAddExpr *getVecVecAddExpr(domain::VecVecAddExpr* d) const;

// Vector

	void putVector_Lit(coords::Vector *ast, domain::Vector_Lit *v);
	domain::Vector *getVector(coords::Vector_Lit* c) const;
	coords::Vector *getVector(domain::Vector_Lit* d) const;

	void putVector_Expr(coords::Vector *ast, domain::Vector_Expr *v);
	domain::Vector *getVector(coords::Vector_Expr* c) const;
	coords::Vector *getVector(domain::Vector_Expr* d) const;

// Def

	void putVector_Def(coords::Vector_Def *vardecl_wrapper, domain::Vector_Def *b);
	domain::Vector_Def *getVector_Def(coords::Vector_Def* c) const;
	coords::Vector_Def *getVector_Def(domain::Vector_Def* d) const;

	void dump();

  private:
	/* 
	We implement an interpretation as a collection of typed maps. 
	The keys are "Code Coordinate" objects, which, in turn, are 
	currently just containers for pointers to AST nodes, basically
	just adding operator==() and hash functions.

	TODO: Compare with ast2coords. There it's clear that every
	AST node maps to a coords::Coords. But here we distinguish
	between different kinds of coords. Re-evaluate.
	*/

	// TODO: delete "interp" prefixes here -- minor
	std::unordered_map<coords::VecExpr, domain::VecExpr *, coords::VecExprHasher> interpExpression;
	std::unordered_map<coords::Vector, domain::Vector *, coords::VectorHasher> interpVector;
	std::unordered_map<coords::VecIdent, domain::VecIdent *, coords::VecIdentHasher> interpIdent;
	std::unordered_map<coords::Vector_Def, domain::Vector_Def *, coords::Vector_DefHasher> interpVector_Def;
/*
	std::unordered_map<coords::VecIdent, domain::VecIdent *, coords::VecIdentHasher> interpIdent;
	std::unordered_map<coords::VecExpr, domain::VecExpr *, coords::VecExprHasher> interpExpression;
	std::unordered_map<coords::VecIdent, domain::VecIdent *, coords::VecIdentHasher> interpVector;
	std::unordered_map<coords::Vector_Def, domain::Vector_Def *, coords::Vector_DefHasher> interpVector_Def;
*/
};

} // namespace

#endif