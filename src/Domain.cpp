#include <vector>
#include <iostream>
#include <string>


// DONE: Separate clients from Domain
// #include "Checker.h"

#include "Domain.h"

//#include <g3log/g3log.hpp>

#ifndef leanInferenceWildcard
#define leanInferenceWildcard "_"
#endif

using namespace std;
using namespace domain;


/******
* Space
******/


Space &Domain::mkSpace(const string &name)
{
    Space *s = new Space(name);
    spaces.push_back(s);
    return *s;
}


std::vector<Space*> &Domain::getSpaces() 
{
    return spaces; 
}

// TODO: MOVE THIS STUFF
std::string Space::getName() const { return name_; }



/****
Ident
****/


VecIdent *Domain::mkVecIdent(Space *s)
{
    VecIdent *id = new VecIdent(*s);
    idents.push_back(id);
    return id;
}

VecIdent* Domain::mkVecIdent()
{
   VecIdent *id = new VecIdent();
   idents.push_back(id);
   return id; 
}

/****
 * Set
 * **/

void VecIdent::setSpace(Space* space) {
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::SpaceContainer();
    this->spaceContainer_->setSpace(space);
}

void VecExpr::setSpace(Space* space) {
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::SpaceContainer();
    this->spaceContainer_->setSpace(space);
}

/****
 * Get
 * **/


/****
 Expr
****/

domain::VecVarExpr *Domain::mkVecVarExpr(Space *s)
{
    domain::VecVarExpr *var = new domain::VecVarExpr(s);
    exprs.push_back(var);
    return var;
}

domain::VecVarExpr* Domain::mkVecVarExpr()
{
    domain::VecVarExpr *var = new domain::VecVarExpr();
    exprs.push_back(var);
    return var;
}

domain::FloatVarExpr *Domain::mkFloatVarExpr(Space *s)
{
    domain::FloatVarExpr *var = new domain::FloatVarExpr(s);
    float_exprs.push_back(var);
    return var;
}

domain::FloatVarExpr* Domain::mkFloatVarExpr()
{
    domain::FloatVarExpr *var = new domain::FloatVarExpr();
    float_exprs.push_back(var);
    return var;
}

domain::VecVecAddExpr *Domain::mkVecVecAddExpr(Space *s, domain::VecExpr *mem, domain::VecExpr *arg)
{
    domain::VecVecAddExpr *be = new domain::VecVecAddExpr(s, mem, arg);
    exprs.push_back(be);
    return be;
}

domain::VecVecAddExpr* Domain::mkVecVecAddExpr(domain::VecExpr* mem, domain::VecExpr* arg)
{
    domain::VecVecAddExpr *b = new domain::VecVecAddExpr(mem, arg);
    exprs.push_back(b);
    return b;
}

domain::VecExpr *VecVecAddExpr::getMemberVecExpr()
{
    return mem_;
}

domain::VecExpr *VecVecAddExpr::getArgVecExpr()
{
    return arg_;
}



domain::FloatFloatAddExpr *Domain::mkFloatFloatAddExpr(Space *s, domain::FloatExpr *lhs, domain::FloatExpr *rhs)
{
    domain::FloatFloatAddExpr *be = new domain::FloatFloatAddExpr(s, lhs, rhs);
    float_exprs.push_back(be);
    return be;
}

domain::FloatFloatAddExpr* Domain::mkFloatFloatAddExpr(domain::FloatExpr* lhs, domain::FloatExpr* rhs)
{
    domain::FloatFloatAddExpr *b = new domain::FloatFloatAddExpr(lhs, rhs);
    float_exprs.push_back(b);
    return b;
}

domain::FloatExpr *FloatFloatAddExpr::getLHSFloatExpr()
{
    return lhs_;
}

domain::FloatExpr *FloatFloatAddExpr::getRHSFloatExpr()
{
    return rhs_;
}

domain::FloatFloatMulExpr *Domain::mkFloatFloatMulExpr(Space *s, domain::FloatExpr *lhs, domain::FloatExpr *rhs)
{
    domain::FloatFloatMulExpr *be = new domain::FloatFloatMulExpr(s, lhs, rhs);
    float_exprs.push_back(be);
    return be;
}

domain::FloatFloatMulExpr* Domain::mkFloatFloatMulExpr(domain::FloatExpr* lhs, domain::FloatExpr* rhs)
{
    domain::FloatFloatMulExpr *b = new domain::FloatFloatMulExpr(lhs, rhs);
    float_exprs.push_back(b);
    return b;
}

domain::FloatExpr *FloatFloatMulExpr::getLHSFloatExpr()
{
    return lhs_;
}

domain::FloatExpr *FloatFloatMulExpr::getRHSFloatExpr()
{
    return rhs_;
}


// KEVIN: Added for VecParen module, has to stay in Domain.h
domain::FloatParenExpr *Domain::mkFloatParenExpr(Space *s, domain::FloatExpr *expr)
{
		domain::FloatParenExpr *var = new domain::FloatParenExpr(s, expr);
		float_exprs.push_back(var);
		return var;
}

domain::FloatParenExpr* Domain::mkFloatParenExpr(domain::FloatExpr* expr)
{
    domain::FloatParenExpr* var = new domain::FloatParenExpr(expr);
    float_exprs.push_back(var);
    return var;
}

domain::VecParenExpr *Domain::mkVecParenExpr(Space *s, domain::VecExpr *expr)
{
		domain::VecParenExpr *var = new domain::VecParenExpr(s, expr);
		exprs.push_back(var);
		return var;
}

domain::VecParenExpr* Domain::mkVecParenExpr(domain::VecExpr* expr)
{
    domain::VecParenExpr* var = new domain::VecParenExpr(expr);
    exprs.push_back(var);
    return var;
}
/******
* Value
*******/

void Vector::setSpace(Space* space){

    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::SpaceContainer();
    this->spaceContainer_->setSpace(space);
}

Vector_Lit* Domain::mkVector_Lit(Space* space, float x, float y, float z) {
    Vector_Lit* vec = new domain::Vector_Lit(*space, x, y, z); 
    vectors.push_back(vec); 
    return vec;
}

Vector_Lit* Domain::mkVector_Lit(float x, float y, float z)
{
    Vector_Lit* vec = new domain::Vector_Lit(x, y, z);
    vectors.push_back(vec);
    return vec;
}

Vector_Expr* Domain::mkVector_Expr(Space* s, domain::VecExpr* exp) {
    Vector_Expr* vec = new domain::Vector_Expr(*s, exp);
    vectors.push_back(vec);
    return vec;
}

Vector_Expr* Domain::mkVector_Expr(domain::VecExpr* exp){
    Vector_Expr* vec = new domain::Vector_Expr(exp);
    vectors.push_back(vec);
    return vec;
}


/****
* Def
*****/


// TODO: Should be binding to Vector, not Expr
// 
Vector_Def *Domain::mkVector_Def(domain::VecIdent* i, domain::Vector* v)
{
    //LOG(DEBUG) <<"Domain::mkVector_Def ";
    Vector_Def *bd = new Vector_Def(i, v);  
    defs.push_back(bd); 
    return bd;
}


/*

	FloatIdent* mkFloatIdent(Space* s); 
	FloatIdent* mkFloatIdent();

	FloatExpr* mkFloatExpr(Space* s);
	FloatExpr* mkFloatExpr();

*/

FloatIdent* Domain::mkFloatIdent(Space* s){
    domain::FloatIdent* flt = new domain::FloatIdent(*s);
    float_idents.push_back(flt);
    return flt;
}

FloatIdent* Domain::mkFloatIdent(){
    domain::FloatIdent* flt = new domain::FloatIdent();
    float_idents.push_back(flt);
    return flt;
}

FloatExpr* Domain::mkFloatExpr(Space* s){
    domain::FloatExpr* flt = new domain::FloatExpr(s);
    float_exprs.push_back(flt);
    return flt;
}

FloatExpr* Domain::mkFloatExpr(){
    domain::FloatExpr* flt = new domain::FloatExpr();
    float_exprs.push_back(flt);
    return flt;
}


/*  
	VecScalarMulExpr* mkScalarMulExpr(Space* s, domain::FloatExpr* flt_, domain::VecExpr* vec_);
	VecScalarMulExpr* mkScalarMulExpr(domain::Float_Expr* flt_, domain::VecExpr* vec_);
*/

VecScalarMulExpr* Domain::mkVecScalarMulExpr(Space* s, domain::VecExpr *vec, domain::FloatExpr *flt){
    domain::VecScalarMulExpr* expr = new domain::VecScalarMulExpr(s, vec, flt);
    exprs.push_back(expr);
    return expr;
}

VecScalarMulExpr* Domain::mkVecScalarMulExpr(domain::VecExpr *vec, domain::FloatExpr *flt){
    auto expr = new domain::VecScalarMulExpr(vec, flt);
    exprs.push_back(expr);
    return expr;
}


/*

	Float_Lit* mkFloat_Lit(Space* space, float scalar);
	Float_Lit* mkFloat_Lit(float scalar);

	Float* mkFloat_Var(Space* s);
	Float* mkFloat_Var();

	Float_Expr* mkFloat_Expr(Space* space, domain::FloatExpr *vec);
	Float_Expr* mkFloat_Expr(domain::FloatExpr *vec);
    
	std::vector<FloatIdent*> float_idents;
	std::vector<FloatExpr*> float_exprs;
	std::vector<Float*> floats;
	std::vector<Float_Def*> float_defs;
*/

Float_Lit* Domain::mkFloat_Lit(Space* space, float scalar){
    auto flt = new domain::Float_Lit(*space, scalar);
    floats.push_back(flt);
    return flt;
}

Float_Lit* Domain::mkFloat_Lit(float scalar){
    auto flt = new domain::Float_Lit(scalar);
    floats.push_back(flt);
    return flt;
}

Float_Expr* Domain::mkFloat_Expr(Space* s, domain::FloatExpr* exp) {
    Float_Expr* flt = new domain::Float_Expr(*s, exp);
    floats.push_back(flt);
    return flt;
}

Float_Expr* Domain::mkFloat_Expr(domain::FloatExpr* exp){
    Float_Expr* flt = new domain::Float_Expr(exp);
    floats.push_back(flt);
    return flt;
}


/****
* Def
*****/


// TODO: Should be binding to Vector, not Expr
// 
Float_Def *Domain::mkFloat_Def(domain::FloatIdent* i, domain::Float* v)
{
    //LOG(DEBUG) <<"Domain::mkVector_Def ";
    Float_Def *bd = new Float_Def(i, v);  
    float_defs.push_back(bd); 
    return bd;
}

