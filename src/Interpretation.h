#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include "AST.h"

namespace interp {

class Interpretation {
public:
    Interpretation() {
        coords_ = new coords::Coords();
        domain_ = new domain::Domain();
        oracle_ = new oracle::Oracle(domain_);
        coords2dom_ = new coords2domain::CoordsToDomain();
        code2coords_ = new code2coords::CodeToCoords();
    }

    domain::Identifier *mkVecIdent(ast::Ident *ast) {
        cerr << "BEG interp::VecIdent *addVecIdent\n";
        domain::Space &space = oracle_->getSpaceForIdentifier(ast);
        const coords::VecIdent *coords = coords_->makeCoordsForVecIdent(ast);
        domain::Identifier* dom = domain_->addIdentifier(space, coords); 
        coords2dom_->putIdentifierInterp(coords, dom);
        cerr << "domain::Identifier *mkVecIdent: AST at " << std::hex << ast << "; Coords at " << std::hex << coords << ";  coords.toString is " << coords->toString() << "; dom at " << std::hex << dom << "\n";    
        cerr << "END interp::VecIdent *addVecIdent\n";
        return dom;
    }

    // TO DO: normalize domain, factor out need to know coords
    coords::Coords* coords_;
    domain::Domain *domain_;
    oracle::Oracle *oracle_;
    code2coords::CodeToCoords *code2coords_;
    coords2domain::CoordsToDomain *coords2dom_;       // augmented AST to domain 
};

} // namespace

#endif



