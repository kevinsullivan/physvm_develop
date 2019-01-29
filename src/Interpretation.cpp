#include "Interpretation.h"

#include <iostream>

using namespace std;

void Interpretation::putVectorInterp(const VectorASTNode& n, VecVarExpr& av) {
    interpVector.insert(std::make_pair(n,&av));

    // TEST! DELETE THIS
    // cout << "av inserted = " << &av << "\n";
    // cout << "av lookuped = " << getVectorInterp(n) << "\n";
}

VecVarExpr* Interpretation::getVectorInterp(const VectorASTNode& n) {
    return interpVector[n];
}

void Interpretation::putExpressionInterp(const ExprASTNode& n, VecAddExpr& e) {
    interpExpression.emplace(n, &e);
}

VecAddExpr* Interpretation::getExpressionInterp(const ExprASTNode& n) {
   return interpExpression[n]; 
}