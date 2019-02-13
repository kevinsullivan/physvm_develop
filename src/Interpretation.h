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
    void mkVector(CXXConstructExpr *ctor_ast, ASTContext context); 
    void mkVector(ast::Literal *ast, ASTContext *context); 
    void mkVecAddExpr(ast::AddExpr *ast, domain::Expr *mem, domain::Expr *arg);
    void mkVecExpr(ast::Expr *ast);
    // TODO: Use AST.h name in next method return
    const coords::ExprASTNode *getCoords(ast::Expr *expr)  
    {
        ast2coords_->getASTExprCoords(expr);
    }

    // Precondition: coords2domain_ is defined for exp
    //
    Expr* getExpressionInterp(ast::Expr* exp) {
        // we use these objects as key for query purposes
        const ExprASTNode *coords = new ExprASTNode(memexpr);
        domain::Expr* expr = coords2domain_[coords];
        if (expr == NULL) {
            cerr << "Interpretation::getExpressionInterp. Error. Undefined for key!\n";
        }
    }
//private:
    // TO DO: normalize domain, factor out need to know coords
    coords::Coords* coords_;
    domain::Domain *domain_;
    oracle::Oracle *oracle_;
    ast2coords::ASTToCoords *ast2coords_;
    coords2domain::CoordsToDomain *coords2dom_;
};

} // namespace

#endif



