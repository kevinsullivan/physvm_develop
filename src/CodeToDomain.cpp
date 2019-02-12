#include "CodeToDomain.h"

#include <iostream>

using namespace std;

/*************
 * Identifiers
 *************/

void CodeToDomain::putIdentifierInterp(const coords::IdentifierASTNode *key, domain::Identifier *v) {
    cerr << "CodeToDomain::putIdentifierInterp: " << key->toString() << "\n";
    interpIdent.insert(std::make_pair(*key, v));
    //cerr << "Put Ident Interp.\n";
}

const domain::Identifier* CodeToDomain::getIdentifierInterp(const coords::IdentifierASTNode* n) 
{
    return interpIdent[*n];
    cerr << "Get Ident Interp.\n";
}

/****************
 * Add Expression
 ****************/

void CodeToDomain::putExpressionInterp(const coords::ExprASTNode* n, const domain::Expr* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

const domain::Expr* CodeToDomain::getExpressionInterp
        (const coords::ExprASTNode* n)  {
   return interpExpression[*n]; 
}

/*********
 * Binding
 *********/

// TODO: Make first arg a reference &
void CodeToDomain::putBindingInterp(coords::BindingASTNode *key, Binding& b)
{
    interpBinding.insert(std::make_pair(*key,&b));
    //cerr << "CodeToDomain::putBindingInterp called but stubbed out.\n";
}


const Binding* CodeToDomain::getBindingInterp(const coords::BindingASTNode* key)  {
   return interpBinding[*key];     
   //cerr << "CodeToDomain::getBindingInterp called but stubbed out. Returning NULL.\n";
}
