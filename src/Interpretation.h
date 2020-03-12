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
//#include <g3log/g3log.hpp> 


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
    
    // Precondition: coords2domain_ is defined for ast
    domain::VecExpr *getVecExpr(ast::VecExpr *ast);

    // TODO: Factor this out into client
    std::string toString_Spaces();
    std::string toString_Idents();
    std::string toString_Exprs();
    std::string toString_Vectors();
    std::string toString_Defs();

    void setAll_Spaces();

    void mkVarTable();
    void printVarTable();
    void updateVarTable();

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
}; 

} // namespaceT

#endif



