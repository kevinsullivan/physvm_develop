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
    Interpretation() {
        coords_ = new coords::Coords();
        domain_ = new domain::Domain();
        oracle_ = new oracle::Oracle(domain_);
        coords2dom_ = new coords2domain::CoordsToDomain();
        ast2coords_ = new ast2coords::ASTToCoords();
    }

    domain::Identifier *mkVecIdent(ast::Ident *ast);

    // TODO: Have this take coord, not domain, arguments
    void mkVecBinding(ast::Stmt *ast, domain::Identifier *id, domain::Expr *exp);

    // TO DO: normalize domain, factor out need to know coords
    coords::Coords* coords_;
    domain::Domain *domain_;
    oracle::Oracle *oracle_;
    ast2coords::ASTToCoords *ast2coords_;
    coords2domain::CoordsToDomain *coords2dom_;       // augmented AST to domain 
};

} // namespace

#endif



