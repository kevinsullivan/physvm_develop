#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include <unordered_map>

namespace coords2domain {

class CoordsToDomain
{
  public:
	void putIdentifierInterp(const coords::VecIdent *key, domain::Identifier *bi);
	const domain::Identifier *getIdentifierInterp(const coords::VecIdent *key);

	// ??? delete ???
	/*
	void putVectorInterp(const Vector& n, VecVarExpr& v);
	VecVarExpr* getVectorInterp(const Vector& n);
	*/

	void putVectorLitInterp(const coords::VectorLit &n, domain::VecLitExpr &v);
	domain::VecLitExpr *getLitInterp(const coords::VectorLit &n) const;

	void putExpressionInterp(const coords::VecExpr *n, domain::VecExpr *e);
	domain::VecExpr *getExpressionInterp(const coords::VecExpr* n);

	void putBindingInterp(coords::Binding *vardecl_wrapper, domain::Binding &b);
	const domain::Binding *getBindingInterp(const coords::Binding* vardecl_wrapper);

	void dumpExpressions() const {
		for (auto it = interpExpression.begin(); it != interpExpression.end(); ++it) {
			//std::cerr << std::hex << &it->first << " : " << std::hex << it.second << "\n";
			cerr << "InterpExpr!\n";
		}
		std::cerr << std::endl;
	}

  private:
	/* 
	We implement an interpretation as a collection of typed maps. 
	The keys are "Code Coordinate" objects, which, in turn, are 
	currently just containers for pointers to AST nodes, basically
	just adding operator==() and hash functions.

	TODO: Compare with ast2coords. There it's clear that every
	AST node maps to a coords::VecExpr. But here we distinguish
	between different kinds of coords. Re-evaluate.
	*/
	unordered_map<coords::VecIdent, domain::Identifier *, coords::IdentifierHasher> interpIdent;
	unordered_map<coords::VecExpr, domain::VecExpr *, coords::VecExprHasher> interpExpression;
	unordered_map<coords::Binding, domain::Binding *, coords::BindingHasher> interpBinding;
};

} // namespace

#endif