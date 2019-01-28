#include "Interpretation.h"

#include <iostream>

using namespace std;

void Interpretation::putVectorInterp(const VectorASTNode& n, Vector& av) {
    interpVector.insert(std::make_pair(n,&av));

    // TEST! DELETE THIS
    // cout << "av inserted = " << &av << "\n";
    // cout << "av lookuped = " << getVectorInterp(n) << "\n";
}

Vector* Interpretation::getVectorInterp(const VectorASTNode& n) {
    return interpVector[n];
}

void Interpretation::putExpressionInterp(const ExprASTNode& n, Expression& e) {
    interpExpression.emplace(n, &e);
}

Expression* Interpretation::getExpressionInterp(const ExprASTNode& n) {
   return interpExpression[n]; 
}