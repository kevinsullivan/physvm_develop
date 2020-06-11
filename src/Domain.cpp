#include <vector>
#include <iostream>
#include <string>
#include <utility>

// DONE: Separate clients from Domain
// #include "Checker.h"

#include "Domain.h"

#include <g3log/g3log.hpp>

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

std::string MapSpace::getName() const { 
    return this->domain_.toString() + " " + this->codomain_.toString(); 
}

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


ScalarIdent* Domain::mkScalarIdent(Space* s){
    domain::ScalarIdent* flt = new domain::ScalarIdent(*s);
    float_idents.push_back(flt);
    return flt;
}

ScalarIdent* Domain::mkScalarIdent(){
    domain::ScalarIdent* flt = new domain::ScalarIdent();
    float_idents.push_back(flt);
    return flt;
}


TransformIdent* Domain::mkTransformIdent(MapSpace* s){
    domain::TransformIdent* flt = new domain::TransformIdent(*s);
    tfm_idents.push_back(flt);
    return flt;
}

TransformIdent* Domain::mkTransformIdent(){
    domain::TransformIdent* flt = new domain::TransformIdent();
    tfm_idents.push_back(flt);
    return flt;
}

ScalarExpr* Domain::mkScalarExpr(Space* s){
    domain::ScalarExpr* flt = new domain::ScalarExpr(s);
    float_exprs.push_back(flt);
    return flt;
}

ScalarExpr* Domain::mkScalarExpr(){
    domain::ScalarExpr* flt = new domain::ScalarExpr();
    float_exprs.push_back(flt);
    return flt;
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
void ScalarIdent::setSpace(Space* space) {
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::SpaceContainer();
    this->spaceContainer_->setSpace(space);
}

void ScalarExpr::setSpace(Space* space) {
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::SpaceContainer();
    this->spaceContainer_->setSpace(space);
}

void TransformIdent::setSpace(MapSpace space) {
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::MapSpaceContainer();
    this->spaceContainer_->setSpace(space);
}

void TransformExpr::setSpace(MapSpace space) {
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::MapSpaceContainer();
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

domain::ScalarVarExpr *Domain::mkScalarVarExpr(Space *s)
{
    domain::ScalarVarExpr *var = new domain::ScalarVarExpr(s);
    float_exprs.push_back(var);
    return var;
}

domain::ScalarVarExpr* Domain::mkScalarVarExpr()
{
    domain::ScalarVarExpr *var = new domain::ScalarVarExpr();
    float_exprs.push_back(var);
    return var;
}

domain::TransformVarExpr *Domain::mkTransformVarExpr(MapSpace *s)
{
    domain::TransformVarExpr *var = new domain::TransformVarExpr(s);
    tfm_exprs.push_back(var);
    return var;
}

domain::TransformVarExpr* Domain::mkTransformVarExpr()
{
    domain::TransformVarExpr *var = new domain::TransformVarExpr();
    tfm_exprs.push_back(var);
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

domain::TransformVecApplyExpr* Domain::mkTransformVecApplyExpr(Space* s, domain::TransformExpr* lhs, domain::VecExpr* rhs)
{
    domain::TransformVecApplyExpr *b = new domain::TransformVecApplyExpr(s, lhs, rhs);
    exprs.push_back(b);
    return b;
}

domain::TransformVecApplyExpr* Domain::mkTransformVecApplyExpr(domain::TransformExpr* lhs, domain::VecExpr* rhs)
{
    domain::TransformVecApplyExpr *b = new domain::TransformVecApplyExpr(lhs, rhs);
    exprs.push_back(b);
    return b;
}

domain::TransformExpr *TransformVecApplyExpr::getLHSTransformExpr()
{
    return lhs_;
}

domain::VecExpr *TransformVecApplyExpr::getRHSVecExpr()
{
    return rhs_;
}

VecScalarMulExpr* Domain::mkVecScalarMulExpr(Space* s, domain::VecExpr *vec, domain::ScalarExpr *flt){
    domain::VecScalarMulExpr* expr = new domain::VecScalarMulExpr(s, vec, flt);
    exprs.push_back(expr);
    return expr;
}

VecScalarMulExpr* Domain::mkVecScalarMulExpr(domain::VecExpr *vec, domain::ScalarExpr *flt){
    auto expr = new domain::VecScalarMulExpr(vec, flt);
    exprs.push_back(expr);
    return expr;
}

domain::VecExpr *VecScalarMulExpr::getVecExpr()
{
    return vec_;
}

domain::ScalarExpr *VecScalarMulExpr::getScalarExpr()
{
    return flt_;
}


domain::ScalarScalarAddExpr *Domain::mkScalarScalarAddExpr(Space *s, domain::ScalarExpr *lhs, domain::ScalarExpr *rhs)
{
    domain::ScalarScalarAddExpr *be = new domain::ScalarScalarAddExpr(s, lhs, rhs);
    float_exprs.push_back(be);
    return be;
}

domain::ScalarScalarAddExpr* Domain::mkScalarScalarAddExpr(domain::ScalarExpr* lhs, domain::ScalarExpr* rhs)
{
    domain::ScalarScalarAddExpr *b = new domain::ScalarScalarAddExpr(lhs, rhs);
    float_exprs.push_back(b);
    return b;
}

domain::ScalarExpr *ScalarScalarAddExpr::getLHSScalarExpr()
{
    return lhs_;
}

domain::ScalarExpr *ScalarScalarAddExpr::getRHSScalarExpr()
{
    return rhs_;
}

domain::ScalarScalarMulExpr *Domain::mkScalarScalarMulExpr(Space *s, domain::ScalarExpr *lhs, domain::ScalarExpr *rhs)
{
    domain::ScalarScalarMulExpr *be = new domain::ScalarScalarMulExpr(s, lhs, rhs);
    float_exprs.push_back(be);
    return be;
}

domain::ScalarScalarMulExpr* Domain::mkScalarScalarMulExpr(domain::ScalarExpr* lhs, domain::ScalarExpr* rhs)
{
    domain::ScalarScalarMulExpr *b = new domain::ScalarScalarMulExpr(lhs, rhs);
    float_exprs.push_back(b);
    return b;
}

domain::ScalarExpr *ScalarScalarMulExpr::getLHSScalarExpr()
{
    return lhs_;
}

domain::ScalarExpr *ScalarScalarMulExpr::getRHSScalarExpr()
{
    return rhs_;
}

domain::TransformTransformComposeExpr* Domain::mkTransformTransformComposeExpr(domain::TransformExpr* lhs, domain::TransformExpr* rhs)
{
    domain::TransformTransformComposeExpr *b = new domain::TransformTransformComposeExpr(lhs, rhs);
    tfm_exprs.push_back(b);
    return b;
}

domain::TransformExpr *TransformTransformComposeExpr::getLHSTransformExpr()
{
    return lhs_;
}

domain::TransformExpr *TransformTransformComposeExpr::getRHSTransformExpr()
{
    return rhs_;
}

// KEVIN: Added for VecParen module, has to stay in Domain.h
domain::ScalarParenExpr *Domain::mkScalarParenExpr(Space *s, domain::ScalarExpr *expr)
{
		domain::ScalarParenExpr *var = new domain::ScalarParenExpr(s, expr);
		float_exprs.push_back(var);
		return var;
}

domain::ScalarParenExpr* Domain::mkScalarParenExpr(domain::ScalarExpr* expr)
{
    domain::ScalarParenExpr* var = new domain::ScalarParenExpr(expr);
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

domain::TransformParenExpr *Domain::mkTransformParenExpr(MapSpace *s, domain::TransformExpr *expr)
{
	domain::TransformParenExpr *var = new domain::TransformParenExpr(s, expr);
	tfm_exprs.push_back(var);
	return var;
}

domain::TransformParenExpr* Domain::mkTransformParenExpr(domain::TransformExpr* expr)
{
    domain::TransformParenExpr* var = new domain::TransformParenExpr(expr);
    tfm_exprs.push_back(var);
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
void Scalar::setSpace(Space* space){

    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::SpaceContainer();
    this->spaceContainer_->setSpace(space);
}

void Transform::setSpace(MapSpace space){
    if(!this->spaceContainer_)
        this->spaceContainer_ = new domain::MapSpaceContainer();
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
    LOG(DBUG) <<"Domain::mkVector_Def ";
    Vector_Def *bd = new Vector_Def(i, v);  
    defs.push_back(bd); 
    return bd;
}


Vector_Assign *Domain::mkVector_Assign(domain::VecVarExpr* i, domain::Vector* v)
{
    LOG(DBUG) <<"Domain::mkVector_Assign ";
    Vector_Assign *bd = new Vector_Assign(i, v);  
    assigns.push_back(bd); 
    return bd;
}



Scalar_Lit* Domain::mkScalar_Lit(Space* space, float scalar){
    auto flt = new domain::Scalar_Lit(*space, scalar);
    floats.push_back(flt);
    return flt;
}

Scalar_Lit* Domain::mkScalar_Lit(float scalar){
    auto flt = new domain::Scalar_Lit(scalar);
    floats.push_back(flt);
    return flt;
}

Scalar_Expr* Domain::mkScalar_Expr(Space* s, domain::ScalarExpr* exp) {
    Scalar_Expr* flt = new domain::Scalar_Expr(*s, exp);
    floats.push_back(flt);
    return flt;
}

Scalar_Expr* Domain::mkScalar_Expr(domain::ScalarExpr* exp){
    Scalar_Expr* flt = new domain::Scalar_Expr(exp);
    floats.push_back(flt);
    return flt;
}


/****
* Def
*****/


Scalar_Def *Domain::mkScalar_Def(domain::ScalarIdent* i, domain::Scalar* v)
{
    LOG(DBUG) <<"Domain::mkScalar_Def ";
    Scalar_Def *bd = new Scalar_Def(i, v);  
    float_defs.push_back(bd); 
    return bd;
}


Scalar_Assign *Domain::mkScalar_Assign(domain::ScalarVarExpr* i, domain::Scalar* v)
{
    LOG(DBUG) <<"Domain::mkScalar_Assign ";
    Scalar_Assign *bd = new Scalar_Assign(i, v);  
    float_assigns.push_back(bd); 
    return bd;
}



Transform_Lit* Domain::mkTransform_Lit(MapSpace* space,
		domain::VecExpr* arg1, 
		domain::VecExpr* arg2,
		domain::VecExpr* arg3){
    auto tfm = new domain::Transform_Lit(*space, arg1, arg2, arg3);
    transforms.push_back(tfm);
    return tfm;
}

Transform_Lit* Domain::mkTransform_Lit(
		domain::VecExpr* arg1, 
		domain::VecExpr* arg2,
		domain::VecExpr* arg3){
    auto tfm = new domain::Transform_Lit(arg1, arg2, arg3);
    transforms.push_back(tfm);
    return tfm;
}

Transform_Expr* Domain::mkTransform_Expr(MapSpace* s, domain::TransformExpr* exp) {
    Transform_Expr* tfm = new domain::Transform_Expr(*s, exp);
    transforms.push_back(tfm);
    return tfm;
}

Transform_Expr* Domain::mkTransform_Expr(domain::TransformExpr* exp){
    Transform_Expr* tfm = new domain::Transform_Expr(exp);
    transforms.push_back(tfm);
    return tfm;
}


/****
* Def
*****/


Transform_Def *Domain::mkTransform_Def(domain::TransformIdent* i, domain::Transform* v)
{
    LOG(DBUG) <<"Domain::mkTransform_Def ";
    Transform_Def *bd = new Transform_Def(i, v);  
    transform_defs.push_back(bd); 
    return bd;
}


Transform_Assign *Domain::mkTransform_Assign(domain::TransformVarExpr* i, domain::Transform* v)
{
    LOG(DBUG) <<"Domain::mkTransform_Assign ";
    Transform_Assign *bd = new Transform_Assign(i, v);  
    transform_assigns.push_back(bd); 
    return bd;
}

