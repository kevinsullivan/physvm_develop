#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include<iostream>

#include "CodeCoordinate.h"
#include "Bridge.h"

#include <unordered_map>

using namespace std;
using namespace bridge;

class Interpretation {
public:

	void putIdentifier(const VarDecl* vardecl, bridge::Identifier* bi) {
		std::cerr << "In interpretation::putIdentifier. STUB.\n";
	}
	const bridge::Identifier* getIdentifier() {
		std::cerr << "In interpretation::getIdentifier. STUB.\n";
		return NULL;
	}

	// Add a vector tuple to the interpretation
	// Precondition: key not already defined in map
	// Postcondition: map' = map + (n,v) 
	void putVectorInterp(const VectorASTNode& n, VecVarExpr& v);

	// Lookup existing association in map
	// Precondition: key defined in map
	// Postcondition: result as associated abstract vector value
	VecVarExpr* getVectorInterp(const VectorASTNode& n);

	// As above but for expressions
	void putExpressionInterp(const ExprASTNode& n, VecAddExpr& e);

	// As above but for expressions
	VecAddExpr* getExpressionInterp(const ExprASTNode& n);
private:
	// We implement an interpretation as a collection of typed maps
	unordered_map<VectorASTNode, VecVarExpr*, VectorASTNodeHasher> interpVector;
	unordered_map<ExprASTNode, VecAddExpr*, ExprASTNodeHasher> interpExpression;

	//unordered_map<clang::VarDecl, Vector> m; // no AST hash!
};

#endif