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
    domain::Identifier *mkVecIdent(ast::Ident *ast);
    // TODO: Have this take coord, not domain, arguments
    void mkVecBinding(ast::Stmt *ast, domain::Identifier *id, domain::Expr *exp);
    // TODO: Use AST.h name in next method
    void mkVector(CXXConstructExpr *ctor_ast, ASTContext *context); 
    void mkVector(ast::VectorLiteral *ast, ASTContext *context); 
    void mkVecAddExpr(ast::AddExpr *ast, domain::Expr *mem, domain::Expr *arg);
    void mkVecExpr(ast::Expr *ast, ASTContext *context);
    // TODO: Use AST.h name in next method return
    const coords::VectorExpr *getCoords(ast::Expr *expr)  
    {
        ast2coords_->getASTExprCoords(expr);
    }

    // Precondition: coords2domain_ is defined for exp
    //
    domain::Expr* getExpressionInterp(ast::Expr* ast) {
        // we use these objects as key for query purposes
        const coords::Expr *coords = new coords::Expr(ast);
        domain::Expr* dom = coords2dom::getExpressionInterp(coords);
        if (expr == NULL) {
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



