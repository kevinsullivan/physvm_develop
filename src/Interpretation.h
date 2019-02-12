#ifndef INTERPRETATION_H
#define INTERPRETATION_H

namespace interp {

class Interpretation {
public:
    Interpretation() {
        code_ = new code::Code();
        coords_ = new coords::Coords();
        domain_ = new domain::Domain();
        oracle_ = new oracle::Oracle(domain_);
        coords2dom_ = new coords2domain::CoordsToDomain();
        code2coords_ = new code2coords::CodeToCoords();
    }

    domain::Identifier *mkVecIdent(const clang::VarDecl *code) {
        cerr << "BEG interp::VecIdent *addVecIdent\n";
        domain::Space &space = oracle_->getSpaceForIdentifier(code);
        const coords::VecIdent *coords = coords_->makeCoordsForVecIdent(code);
        // TO DO: normalize domain, factor out need to know coords
        domain::Identifier* ident = domain_->addIdentifier(space, coords); 
        coords2dom_->putIdentifierInterp(coords, ident);
        cerr << "domain::Identifier *mkVecIdent: Coord object at " << std::hex << coords << " for code identifer at " << std::hex << code << "; coord toString is : " << coords->toString() << "\n";    
        cerr << "END interp::VecIdent *addVecIdent\n";
        return ident;
    }

    // TODO: Encapsulate
    code::Code *code_;                 // imaginary
    coords::Coords* coords_;
    domain::Domain *domain_;
    oracle::Oracle *oracle_;
    code2coords::CodeToCoords *code2coords_;
    coords2domain::CoordsToDomain *coords2dom_;       // augmented AST to domain 
};

} // namespace

#endif



