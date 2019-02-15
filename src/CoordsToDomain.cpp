#include "CoordsToDomain.h"

#include <iostream>

//using namespace std;
using namespace coords2domain;

/*************
 * VecIdents
 *************/

void CoordsToDomain::putVecIdentInterp(const coords::VecIdent *key, domain::VecIdent *v) {
    std::cerr << "CoordsToDomain::putVecIdentInterp: " << key->toString() << "\n";
    interpIdent.insert(std::make_pair(*key, v));
    //std::cerr << "Put Ident Interp.\n";
}

const domain::VecIdent* CoordsToDomain::getVecIdentInterp(const coords::VecIdent* n) 
{
    return interpIdent[*n];
    std::cerr << "Get Ident Interp.\n";
}

/****************
 * Add Expression
 ****************/

void CoordsToDomain::putExpressionInterp(const coords::VecExpr* n, domain::VecExpr* e) {
    interpExpression.insert(std::make_pair(*n, e));
}

domain::VecExpr* CoordsToDomain::getExpressionInterp
        (const coords::VecExpr* n)  {
   return interpExpression[*n]; 
}

/*********
 * VecDef
 *********/

// TODO: Make first arg a reference &
void CoordsToDomain::putVecDefInterp(coords::VecDef *key, domain::VecDef& b)
{
    interpVecDef.insert(std::make_pair(*key,&b));
    //std::cerr << "CoordsToDomain::putVecDefInterp called but stubbed out.\n";
}


const domain::VecDef* CoordsToDomain::getVecDefInterp(const coords::VecDef* key)  {
   return interpVecDef[*key];     
   //std::cerr << "CoordsToDomain::getVecDefInterp called but stubbed out. Returning NULL.\n";
}
