#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include "AST.h"
#include "Coords.h"
#include "ASTToCoords.h"
#include "Oracle.h"
#include "Domain.h"
#include "CoordsToDomain.h"

namespace interp {

class Interpretation {
public:
    Interpretation();
    domain::VecIdent *mkVecIdent(ast::VecIdent *ast);
    // TODO: Have this take coord, not domain, arguments
    void mkVecDef(ast::VecDef *ast, domain::VecIdent *id, domain::VecExpr *exp);
    // TODO: Use AST.h name in next method
    void mkVector(CXXConstructExpr *ctor_ast, ASTContext *context); 
    void mkVector(ast::VecLitExpr *ast, ASTContext *context); 
    void mkVecVecAddExpr(ast::AddExpr *ast, domain::VecExpr *mem, domain::VecExpr *arg);
    void mkVecExpr(ast::VecExpr *ast, ASTContext *context);
    // TODO: Use AST.h name in next method return
    const coords::VecExpr *getCoords(ast::VecExpr *expr)  
    {
        ast2coords_->getASTExprCoords(expr);
    }
    

    // Precondition: coords2domain_ is defined for exp
    //
    domain::VecExpr* getExpressionInterp(ast::VecExpr* ast) {
        // we use these objects as key for query purposes
        const coords::VecExpr *coords = new coords::VecExpr(ast);
        domain::VecExpr* dom = coords2dom_->getExpressionInterp(coords);
        if (!expr) {
            cerr << "Interpretation::getExpressionInterp. Error. Undefined for key!\n";
        }
        return dom;
    }
//private:
    // TO DO: normalize domain, factor out need to know coords
    //coords::Coords* coords_;
    domain::Domain *domain_;
    oracle::Oracle *oracle_;
    ast2coords::ASTToCoords *ast2coords_;
    coords2domain::CoordsToDomain *coords2dom_;
};

} // namespace

#endif



