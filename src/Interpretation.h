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

namespace interp {


// TODO: Either remove or complete adding clang::ASTContext
class Interpretation {
public:
    Interpretation();

    void addSpace(std::string name) {
        domain_->mkSpace(name);
    }

    /*
    These operations work by side-effecting interpretation state.
    Precondition: sub-arguments already have interpretations.
    */
 
    void mkVecIdent(ast::VecIdent *ast);
    void mkVecVarExpr(ast::VecVarExpr *ast);
    void mkVecVecAddExpr(ast::VecVecAddExpr *ast, const ast::VecExpr *mem, 
                         const ast::VecExpr *arg);
    void mkVector_Lit(ast::Vector_Lit *ast);
    void mkVector_Expr(ast::Vector_Expr *ast, ast::VecExpr* expr);
    void mkVector_Var(ast::VecLitExpr *ast);
    void mkVector_Def(ast::Vector_Def *ast, ast::VecIdent *id, ast::VecExpr *exp);
    
    // Precondition: coords2domain_ is defined for exp
    //
    domain::VecExpr* getVecExpr(ast::VecExpr* ast) {
        // we use these objects as key for query purposes
        coords::VecExpr *coords = 
            static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(ast));
        domain::VecExpr* dom = coords2dom_->getVecExpr(coords);
        if (!dom) {
            LOG(DEBUG) <<"Interpretation::getVecExpr. Error. Undefined for key!\n";
        }
        return dom;
    }

/*
    std::string toString() {
        for (std::vector<int>::iterator it = myvector.begin() ; it != myvector.end(); ++it)
    std::cout << ' ' << *it;
    }
*/


/******
 * 
 * TODO: Replace all this with direct calls to interp objects
 * 
 * ****/

// private
    std::string toString_Spaces() {
        std::string retval = "";
        std::vector<domain::Space*> &s = domain_->getSpaces();
        for (std::vector<domain::Space*>::iterator it = s.begin(); it != s.end(); ++it)
            retval = retval .append("(")
                            .append((*it)->toString())
                            .append(" : space)\n");
        return retval;
    }

    // TODO: Private
    //
    std::string toString_Idents() {
        std::string retval = "";
        std::vector<domain::VecIdent*> &id = domain_->getVecIdents();
        for (std::vector<domain::VecIdent *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::VecIdent* coords = coords2dom_->getVecIdent(*it);
            interp::VecIdent *interp = coords2interp_->getVecIdent(coords);
            retval = retval.append(interp->toString());
            retval = retval.append("\n"); 
        }
        return retval;
    }

    // TODO: Factor toPrint (printing) out of coords, put here in, or in client of, interpretation
    //
    std::string toString_Exprs() {
        std::string retval = "";
        std::vector<domain::VecExpr*> &id = domain_->getVecExprs();
        for (std::vector<domain::VecExpr *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::VecExpr* coords = coords2dom_->getVecExpr(*it);
            interp::VecExpr *interp = coords2interp_->getVecExpr(coords);
            retval = retval.append(interp->toString());
            retval = retval.append("\n");
        }
        return retval;
    }

    std::string toString_Vectors() {
        std::string retval = "";
        std::vector<domain::Vector*> &id = domain_->getVectors();
        for (std::vector<domain::Vector *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::Vector* coords = coords2dom_->getVector(*it);
            retval = retval
            .append("(")
            .append(coords->toString())
            .append(" : vector ")
            .append((*it)->getSpace()->toString())
            .append(")\n");
        }
        return retval;
    }

    std::string toString_Defs() {
        std::string retval = "";
        std::vector<domain::Vector_Def*> &id = domain_->getVectorDefs();
        for (std::vector<domain::Vector_Def *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::Vector_Def* coords = coords2dom_->getVector_Def(*it);
            retval = retval.append(coords->toString()).append("\n");
        }
        return retval;
    }

    //private:
    // TO DO: normalize domain, factor out need to know coords
    //coords::Coords* coords_;
    domain::Domain *domain_;
    oracle::Oracle *oracle_;

    coords2domain::CoordsToDomain *coords2dom_;
    ast2coords::ASTToCoords *ast2coords_;

    coords2interp::CoordsToInterp *coords2interp_;
    interp2domain::InterpToDomain *interp2domain_; 
}; 

} // namespaceT

#endif



