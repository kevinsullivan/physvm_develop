#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include "Code.h"
#include "Domain.h"
#include <unordered_map>

using namespace std;

class Interpretation {
public:
	// Add a vector tuple to the interpretation
	// Precondition: key not already defined in map
	// Postcondition: map' = map + (n,v) 
	void putVectorInterp(const VectorASTNode& n, const Vector& v);

	// Lookup existing association in map
	// Precondition: key defined in map
	// Postcondition: result as associated abstract vector value
	Vector& getVectorInterp(const VectorASTNode& n);

	// As above but for expressions
	void putExpressionInterp(const ExprASTNode& n, const Expression& e);

	// As above but for expressions
	Expression& getExpressionInterp(const ExprASTNode& n);
private:
	// We implement an interpretation as a collection of typed maps
	unordered_map<VectorASTNode, Vector, VectorASTNodeHasher> interpVector;
	unordered_map<ExprASTNode, Expression, ExprASTNodeHasher> interpExpression;
};

#endif