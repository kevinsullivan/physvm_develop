#include "CoordsToDomain.h"

#include <iostream>

using namespace std;
using namespace coords2domain;

/*************
 * Identifiers
 *************/

void CoordsToDomain::putIdentifierInterp(const coords::VecIdent *key, domain::Identifier *v) {
    cerr << "CoordsToDomain::putIdentifierInterp: " << key->toString() << "\n";
    interpIdent.insert(std::make_pair(*key, v));
    //cerr << "Put Ident Interp.\n";
}

const domain::Identifier* CoordsToDomain::getIdentifierInterp(const coords::VecIdent* n) 
{
    return interpIdent[*n];
    cerr << "Get Ident Interp.\n";
}

/****************
 * Add Expression
 ****************/

void CoordsToDomain::putExpressionInterp(const coords::VecExpr* n, domain::Expr* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

domain::Expr* CoordsToDomain::getExpressionInterp
        (const coords::VecExpr* n)  {
   return interpExpression[*n]; 
}

/*********
 * Binding
 *********/

// TODO: Make first arg a reference &
void CoordsToDomain::putBindingInterp(coords::Binding *key, domain::Binding& b)
{
    interpBinding.insert(std::make_pair(*key,&b));
    //cerr << "CoordsToDomain::putBindingInterp called but stubbed out.\n";
}


const domain::Binding* CoordsToDomain::getBindingInterp(const coords::Binding* key)  {
   return interpBinding[*key];     
   //cerr << "CoordsToDomain::getBindingInterp called but stubbed out. Returning NULL.\n";
}
