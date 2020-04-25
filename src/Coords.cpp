#include "Coords.h"

#include <g3log/g3log.hpp>


namespace coords {

/*
Code coordinates provide for ontology translation, between the 
concrete types used to represent pertinent code elements in a 
given programming language and system (code language), and the 
abstract terms of a domain language. Here the code language is
Clang as used to map applications built on our simple vector
class (Vec). The domain language is one of simple vector space
expressions and objects. 
*/

// Ontology of code object types that can be coordinatized
// clang::Decl unused by Peirce, here for generalizability
//


ASTState::ASTState(
    std::string file_id,
    std::string file_name,
    std::string file_path,
    std::string name,
    int begin_line_no,
    int begin_col_no,
    int end_line_no,
    int end_col_no
  ) : file_id_{file_id}, file_name_{file_name}, file_path_{file_path}, name_{name}, begin_line_no_{begin_line_no}, begin_col_no_{begin_col_no}, end_line_no_{end_line_no}, end_col_no_{end_col_no} {}

Coords::Coords(){
}

bool Coords::operator==(const Coords &other) const {
    return this->state_ == other.state_;
}

std::string Coords::toString() const {
    LOG(FATAL) << "Coords::toString. Error. Should not be called. Abstract.\n";
    return NULL;
}

std::string Coords::getSourceLoc() const {
    /*clang::FullSourceLoc FullLocation;
    if (ast_type_tag_ == CLANG_AST_STMT)
    {
      FullLocation = context_->getFullLoc(clang_stmt_->getSourceRange().getEnd());
    } else {
      FullLocation = context_->getFullLoc(clang_decl_->getLocation());
    }*/
    //std::cout<<this->toString()<<std::endl;
    std::string retval = "Begin: line ";
    retval += std::to_string(this->state_->begin_line_no_); 
    retval +=  ", column ";
    retval +=  std::to_string(this->state_->begin_col_no_);
    retval += " End: line ";
    retval += std::to_string(this->state_->end_line_no_);
    retval += ", column ";
    retval += std::to_string(this->state_->end_col_no_);

    return retval;
}

/*************************************************************
* Coordinate subclasses, for type checking, override behaviors
*************************************************************/

/******
* Ident
******/

VecIdent::VecIdent() : Coords() {}

std::string VecIdent::toString() const { 
    return state_->name_;
}


ScalarIdent::ScalarIdent() : Coords() {}

std::string ScalarIdent::toString() const { 
    return  state_->name_;
}


TransformIdent::TransformIdent() : Coords() {}

std::string TransformIdent::toString() const { 
    return  state_->name_;
}



/*****
* Expr
*****/

VecExpr::VecExpr() : Coords() {}

std::string VecExpr::toString() const { 
    LOG(FATAL) << "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
    return NULL; 
}

ScalarExpr::ScalarExpr() : Coords() {}

std::string ScalarExpr::toString() const { 
    //LOG(FATAL) << "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
    return NULL; 
}

TransformExpr::TransformExpr() : Coords() {}

std::string TransformExpr::toString() const { 
    //LOG(FATAL) << "Coords::VecExpr::toString. Error. Should not be called. Abstract.\n"; 
    return NULL; 
}


/*
No such intermediate node in Clang AST.
Straight to CXXConstructExpr (Vector_Lit).
Included here as stub for possible future use.
class VecLitExpr : public VecExpr {}
*/
VecVarExpr::VecVarExpr() : VecExpr() {}

std::string VecVarExpr::toString() const { 
    return state_->name_; 
}


ScalarVarExpr::ScalarVarExpr() : ScalarExpr() {}

std::string ScalarVarExpr::toString() const { 
    return state_->name_; 
}

TransformVarExpr::TransformVarExpr() : TransformExpr() {}

std::string TransformVarExpr::toString() const { 
    return state_->name_; 
}



VecVecAddExpr::VecVecAddExpr(
    coords::VecExpr *mem, coords::VecExpr *arg) 
        : VecExpr(), mem_(mem), arg_(arg) {
}

std::string VecVecAddExpr::toString() const {
    return "(add (" + mem_->toString() + ") (" + arg_->toString() + "))";
}



 // VecScalarMulExpr(const ast::VecScalarMulExpr *mce, clang::ASTContext *c, coords::ScalarExpr *flt, coords::VecExpr *vec);
 // const ast::VecScalarMulExpr *getVecScalarMulExpr();
VecScalarMulExpr::VecScalarMulExpr(
    coords::ScalarExpr *flt, coords::VecExpr *vec) 
        : VecExpr(), flt_(flt), vec_(vec) {
}

std::string VecScalarMulExpr::toString() const {
    return "(mul (" + flt_->toString() + ") (" + vec_->toString() + "))";
}

TransformVecApplyExpr::TransformVecApplyExpr(
    coords::TransformExpr *lhs, coords::VecExpr *rhs) 
        : VecExpr(), lhs_(lhs), rhs_(rhs) {
}

std::string TransformVecApplyExpr::toString() const {
    return "(compose (" + lhs_->toString() + ") (" + rhs_->toString() + "))";
}


ScalarScalarAddExpr::ScalarScalarAddExpr(
    coords::ScalarExpr *lhs, coords::ScalarExpr *rhs) 
        : ScalarExpr(), lhs_(lhs), rhs_(rhs) {
}

std::string ScalarScalarAddExpr::toString() const {
    return "(add (" + lhs_->toString() + ") (" + rhs_->toString() + "))";
}


ScalarScalarMulExpr::ScalarScalarMulExpr(
    coords::ScalarExpr *lhs, coords::ScalarExpr *rhs) 
        : ScalarExpr(), lhs_(lhs), rhs_(rhs) {
}

std::string ScalarScalarMulExpr::toString() const {
    return "(mul (" + lhs_->toString() + ") (" + rhs_->toString() + "))";
}

TransformTransformComposeExpr::TransformTransformComposeExpr(
    coords::TransformExpr *lhs, coords::TransformExpr *rhs) 
        : TransformExpr(), lhs_(lhs), rhs_(rhs) {
}

std::string TransformTransformComposeExpr::toString() const {
    return "(compose (" + lhs_->toString() + ") (" + rhs_->toString() + "))";
}








VecParenExpr::VecParenExpr(coords::VecExpr *expr) 
        : VecExpr(), expr_(expr) { 
}

std::string VecParenExpr::toString() const {
    return "(" + expr_->toString() + ")";
}


ScalarParenExpr::ScalarParenExpr(coords::ScalarExpr *expr) 
        : ScalarExpr(), expr_(expr) { 
}

std::string ScalarParenExpr::toString() const {
    return "(" + expr_->toString() + ")";
}


TransformParenExpr::TransformParenExpr(coords::TransformExpr *expr) 
        : TransformExpr(), expr_(expr) { 
}

std::string TransformParenExpr::toString() const {
    return "(" + expr_->toString() + ")";
}




/*******
* Values
*******/

Vector::Vector(coords::VectorCtorType tag)
      : VecExpr(), tag_(tag) {
}

VectorCtorType Vector::getVectorType() { return tag_; }

std::string Vector::toString() const { 
    LOG(FATAL) << "Coords::Vector::toPrint: Error. Should not be called. Abstract.\n";
    return NULL;
}

Scalar::Scalar(coords::ScalarCtorType tag)
      : ScalarExpr(), tag_(tag) {
}

ScalarCtorType Scalar::getScalarType() { return tag_; }

std::string Scalar::toString() const { 
    LOG(FATAL) << "Coords::Scalar::toPrint: Error. Should not be called. Abstract.\n";
    return NULL;
}

Transform::Transform(coords::TransformCtorType tag)
      : TransformExpr(), tag_(tag) {
}

TransformCtorType Transform::getTransformType() { return tag_; }

std::string Transform::toString() const { 
    LOG(FATAL) << "Coords::Transform::toPrint: Error. Should not be called. Abstract.\n";
    return NULL;
}



Vector_Lit::Vector_Lit() 
    : Vector(VEC_CTOR_LIT) {} 
  
std::string Vector_Lit::toString() const  {
    std::string retval = "";
    retval += "0"; 
    retval.append(" ");
    retval += "0"; 
    retval.append(" ");
    retval += "0";
    //retval = "(" + retval + ")";
    return retval;
}


Scalar_Lit::Scalar_Lit() 
    : Scalar(FLOAT_CTOR_LIT){} 
  
std::string Scalar_Lit::toString() const  {
    std::string retval = "";
    retval += "0"; 
    //retval = "(" + retval + ")";
    return retval;
}

Transform_Lit::Transform_Lit() 
    : Transform(TRANSFORM_CTOR_LIT){} 
  
std::string Transform_Lit::toString() const  {
    std::string retval = "";
    retval += "3x3 Matrix representation"; 
    //retval = "(" + retval + ")";
    return retval;
}

Vector_Var::Vector_Var(coords::VecVarExpr* expr) 
    : Vector(VEC_CTOR_VAR), expr_(expr) { 
}

std::string Vector_Var::toString() const { 
    LOG(FATAL) << ("Vector_Var::toString() NOT YET IMPLEMENTED!\n"); 
    return NULL;
}

Scalar_Var::Scalar_Var(coords::ScalarVarExpr* expr) 
    : Scalar(FLOAT_CTOR_VAR), expr_(expr) { 
}

std::string Scalar_Var::toString() const { 
    LOG(FATAL) << ("Vector_Var::toString() NOT YET IMPLEMENTED!\n"); 
    return NULL;
}

Transform_Var::Transform_Var(coords::TransformVarExpr* expr) 
    : Transform(TRANSFORM_CTOR_VAR), expr_(expr) { 
}

std::string Transform_Var::toString() const { 
    LOG(FATAL) << ("Vector_Var::toString() NOT YET IMPLEMENTED!\n"); 
    return NULL;
}

std::string Vector_Expr::toString() const { 
    return expr_->toString();
    //std::string("Vector_Expr::toString() STUB.\n"); 
}

Vector_Expr::Vector_Expr(
                     coords::VecExpr* expr_coords) 
    : Vector(VEC_CTOR_EXPR), expr_(expr_coords) {
}

std::string Scalar_Expr::toString() const { 
    return expr_->toString();
    //std::string("Vector_Expr::toString() STUB.\n"); 
}

Scalar_Expr::Scalar_Expr(
                     coords::ScalarExpr* expr_coords) 
    : Scalar(FLOAT_CTOR_EXPR), expr_(expr_coords) {
}

std::string Transform_Expr::toString() const { 
    return expr_->toString();
    //std::string("Vector_Expr::toString() STUB.\n"); 
}

Transform_Expr::Transform_Expr(
                     coords::TransformExpr* expr_coords) 
    : Transform(TRANSFORM_CTOR_EXPR), expr_(expr_coords) {
}

/****
* Def
****/

Vector_Def::Vector_Def(coords::VecIdent *id, coords::VecExpr *expr)
      : Coords(), id_(id), expr_(expr) {
}

coords::VecIdent *Vector_Def::getIdent() const {
    return id_;
}

coords::VecExpr *Vector_Def::getExpr() const {
    return expr_;
}

// The coup d'grace.
std::string Vector_Def::toString() const { 
    std::string retval = "def ";
    retval += id_->toString();
    retval += " := ";
    if(expr_)
        retval += expr_->toString();
    return retval;
}

Scalar_Def::Scalar_Def(coords::ScalarIdent *id, coords::ScalarExpr *expr)
      : Coords(), id_(id), expr_(expr) {
}

coords::ScalarIdent *Scalar_Def::getIdent() const {
    return id_;
}

coords::ScalarExpr *Scalar_Def::getExpr() const {
    return expr_;
}

std::string Scalar_Def::toString() const { 
    std::string retval = "def ";
    retval += id_->toString();
    retval += " := ";
    if(expr_)
        retval += expr_->toString();
    return retval;
}

Transform_Def::Transform_Def(coords::TransformIdent *id, coords::TransformExpr *expr)
      : Coords(), id_(id), expr_(expr) {
}

coords::TransformIdent *Transform_Def::getIdent() const {
    return id_;
}

coords::TransformExpr *Transform_Def::getExpr() const {
    return expr_;
}

std::string Transform_Def::toString() const { 
    std::string retval = "def ";
    retval += id_->toString();
    retval += " := ";
    if(expr_)
        retval += expr_->toString();
    return retval;
}

/****
* Assign
****/
Vector_Assign::Vector_Assign(coords::VecVarExpr *id, coords::VecExpr *expr)
      : Coords(), id_(id), expr_(expr) {
}

coords::VecVarExpr *Vector_Assign::getVarExpr() const {
    return id_;
}

coords::VecExpr *Vector_Assign::getExpr() const {
    return expr_;
}

std::string Vector_Assign::toString() const { 
    std::string retval = "assign ";
    retval += id_->toString();
    retval += " := ";
    if(expr_)
        retval += expr_->toString();
    return retval;
}

Scalar_Assign::Scalar_Assign(coords::ScalarVarExpr *id, coords::ScalarExpr *expr)
      : Coords(), id_(id), expr_(expr) {
}

coords::ScalarVarExpr *Scalar_Assign::getVarExpr() const {
    return id_;
}

coords::ScalarExpr *Scalar_Assign::getExpr() const {
    return expr_;
}

std::string Scalar_Assign::toString() const { 
    std::string retval = "assign ";
    retval += id_->toString();
    retval += " := ";
    if(expr_)
        retval += expr_->toString();
    return retval;
}

Transform_Assign::Transform_Assign(coords::TransformVarExpr *id, coords::TransformExpr *expr)
      : Coords(), id_(id), expr_(expr) {
}

coords::TransformVarExpr *Transform_Assign::getVarExpr() const {
    return  id_;
}

coords::TransformExpr *Transform_Assign::getExpr() const {
    return expr_;
}

std::string Transform_Assign::toString() const { 
    std::string retval = "assign ";
    retval += id_->toString();
    retval += " := ";
    if(expr_)
        retval += expr_->toString();
    return retval;
}


} // namespace codecoords
