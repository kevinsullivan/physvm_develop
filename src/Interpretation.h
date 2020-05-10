#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
#include "AST.h"
#include "Coords.h"
#include "Domain.h"
#include "ASTToCoords.h"
#include "CoordsToDomain.h"
#include "Oracle.h"
#include "CoordsToInterp.h"
#include "InterpToDomain.h"
#include <g3log/g3log.hpp> 


#include <unordered_map>

namespace interp {


// TODO: Take clang::ASTContext
class Interpretation {
public:
    Interpretation();

    void setOracle(oracle::Oracle* oracle) {
        oracle_ = oracle;
    }

    void setASTContext(clang::ASTContext *context) {
        context_ = context;
    }

    void addSpace(std::string name) { 
        domain_->mkSpace(name);
    }

    domain::Domain* getDomain() { 
        return domain_; 
    }

    /*
    These operations work by side-effecting interpretation state.
    Precondition: subsequent ast arguments already interpretated.
    */

    void mkVecIdent(ast::VecIdent *ast);
    void mkVecVarExpr(ast::VecVarExpr *ast);

    // TODO: remove the following two const constraints
    void mkVecVecAddExpr(ast::VecVecAddExpr *ast, const ast::VecExpr *mem, 
                         const ast::VecExpr *arg);

    // KEVIN: Added for new horizontal module
    void mkVecParenExpr(ast::VecParenExpr *ast, ast::VecExpr *expr);

    void mkVector_Lit(ast::Vector_Lit *ast, float x, float y, float z);
    void mkVector_Expr(ast::Vector_Expr *ast, ast::VecExpr* expr);
    void mkVector_Var(ast::VecLitExpr *ast);
    void mkVector_Def(ast::Vector_Def *ast, ast::VecIdent *id, ast::VecExpr *exp);
    void mkVector_Assign(ast::Vector_Assign *ast, ast::VecVarExpr *id, ast::VecExpr *exp);
    
    void mkScalarIdent(ast::ScalarIdent *ast);
    void mkScalarVarExpr(ast::ScalarVarExpr *ast);

    // TODO: remove the following two const constraints
    void mkVecScalarMulExpr(ast::VecScalarMulExpr *ast, const ast::ScalarExpr *mem, 
                         const ast::ScalarExpr *arg);

    // KEVIN: Added for new horizontal module
    void mkScalarParenExpr(ast::ScalarParenExpr *ast, ast::ScalarExpr *expr);

    void mkScalarScalarAddExpr(ast::ScalarScalarAddExpr *ast, const ast::ScalarExpr *lhs, const ast::ScalarExpr *rhs);
    void mkScalarScalarMulExpr(ast::ScalarScalarMulExpr *ast, const ast::ScalarExpr *lhs, const ast::ScalarExpr *rhs);

    void mkScalar_Lit(ast::Scalar_Lit *ast, float scalar);
    void mkScalar_Expr(ast::Scalar_Expr *ast, ast::ScalarExpr* expr);
    void mkScalar_Var(ast::ScalarLitExpr *ast);
    void mkScalar_Def(ast::Scalar_Def *ast, ast::ScalarIdent *id, ast::ScalarExpr *exp);
    void mkScalar_Assign(ast::Scalar_Assign *Ast, ast::ScalarVarExpr *id, ast::ScalarExpr *exp);
    
    void mkTransformIdent(ast::TransformIdent *ast);
    void mkTransformVarExpr(ast::TransformVarExpr *ast);

    // TODO: remove the following two const constraints
    void mkTransformVecApplyExpr(ast::TransformVecApplyExpr *ast, const ast::TransformExpr *tfm, 
                         const ast::VecExpr *vec);
    void mkTransformTransformComposeExpr(ast::TransformTransformComposeExpr *ast, const ast::TransformExpr *tfm, 
                         const ast::TransformExpr *vec);

    // KEVIN: Added for new horizontal module
    void mkTransformParenExpr(ast::TransformParenExpr *ast, ast::TransformExpr *expr);

    void mkTransform_Lit(ast::Transform_Lit *ast, ast::VecExpr *vec1, ast::VecExpr *vec2, ast::VecExpr *vec3);
    void mkTransform_Expr(ast::Transform_Expr *ast, ast::TransformExpr* expr);
    void mkTransform_Var(ast::TransformLitExpr *ast);
    void mkTransform_Def(ast::Transform_Def *ast, ast::TransformIdent *id, ast::TransformExpr *exp);
    void mkTransform_Assign(ast::Transform_Assign *ast, ast::TransformVarExpr *id, ast::TransformExpr *exp);
    // Precondition: coords2domain_ is defined for ast


    domain::VecExpr *getVecExpr(ast::VecExpr *ast);

    domain::ScalarExpr *getScalarExpr(ast::ScalarExpr *ast);

    // TODO: Factor this out into client
    std::string toString_Spaces();

    std::string toString_Idents();
    std::string toString_Exprs();
    std::string toString_Vectors();
    std::string toString_Defs();
    std::string toString_Assigns();

    std::string toString_ScalarIdents();
    std::string toString_ScalarExprs();
    std::string toString_Scalars();
    std::string toString_ScalarDefs();
    std::string toString_ScalarAssigns();

    std::string toString_TransformIdents();
    std::string toString_TransformExprs();
    std::string toString_Transforms();
    std::string toString_TransformDefs();
    std::string toString_TransformAssigns();
    
    void setAll_Spaces();

    void mkVarTable();//make a printable, indexed table of variables that can have their types assigned by a user or oracle
    void printVarTable();//print the indexed variable table for the user
    void updateVarTable();//while loop where user can select a variable by index and provide a physical type for that variable

    /*
    * Builds a list of variables that have a type either assigned or inferred.
    * Used for runtime constraint generation/logging 
    */
    void buildTypedDeclList();
    
    
    /*
    used for generating dynamic constraints.
    given a variable, determine whether or not it does not have a type available (if so, a constraint must be registered)
    */
    bool needsConstraint(clang::VarDecl* var);

// TODO: Make private
    domain::Domain *domain_;
    oracle::Oracle *oracle_;
    clang::ASTContext *context_;
    coords2domain::CoordsToDomain *coords2dom_;
    ast2coords::ASTToCoords *ast2coords_;
    coords2interp::CoordsToInterp *coords2interp_;
    interp2domain::InterpToDomain *interp2domain_; 

    std::unordered_map<int, coords::Coords*> index2coords_;
    std::unordered_map<int, void*> index2dom_;

    //populated after initial pass of AST
    //list of scalars/vecs that do not have any assigned or inferred type
    std::vector<ast::VecIdent*> unconstrained_vecs;
    std::vector<std::string> unconstrained_vec_names;
    std::vector<ast::ScalarIdent*> unconstrained_floats;
    std::vector<std::string> unconstrained_float_names;
    std::vector<ast::TransformIdent*> unconstrained_transforms;
    std::vector<std::string> unconstrained_transform_names;
}; 

} // namespaceT

#endif



