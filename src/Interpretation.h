#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
#include "AST.h"
#include "Coords.h"
#include "ASTToCoords.h"
#include "Oracle.h"
#include "Domain.h"
#include "CoordsToDomain.h"

namespace interp {


// TODO: Either remove or complete adding clang::ASTContext
class Interpretation {
public:
    Interpretation();

    void addSpace(std::string name) {
        domain_->mkSpace(name);
    }

    /*
    All of these operations work by producing side-effects
    on ast2_coords_ and on coords2dom.
    */
 
    void mkVecIdent(ast::VecIdent *ast);

    //void mkVecLitExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/);
    void mkVecVarExpr(ast::VecVarExpr *ast/*, clang::ASTContext *c*/);

    // Precondition! Both mem and arg already have interpretations.
    //
    void mkVecVecAddExpr(ast::VecVecAddExpr *ast, const ast::VecExpr *mem, 
                         const ast::VecExpr *arg);
    void mkVector_Lit(ast::Vector_Lit *ast/*, clang::ASTContext *context*/);
    void mkVector_Expr(ast::Vector_Expr *ast, ast::VecExpr* expr/*, clang::ASTContext *context*/);
//    void mkVector_Var(ast::VecLitExpr *ast, clang::ASTContext *context);
    void mkVector_Def(ast::Vector_Def *ast, ast::VecIdent *id, ast::VecExpr *exp);
    
    //coords::VecExpr *getCoords(ast::VecExpr *expr);
    

    // Precondition: coords2domain_ is defined for exp
    //
    domain::VecExpr* getVecExpr(ast::VecExpr* ast) {
        // we use these objects as key for query purposes
        coords::VecExpr *coords = 
            static_cast<coords::VecExpr *>(ast2coords_->getStmtCoords(ast));
        domain::VecExpr* dom = coords2dom_->getVecExpr(coords);
        if (!dom) {
            std::cerr << "Interpretation::getVecExpr. Error. Undefined for key!\n";
        }
        return dom;
    }

/*
    std::string toString() {
        for (std::vector<int>::iterator it = myvector.begin() ; it != myvector.end(); ++it)
    std::cout << ' ' << *it;
    }
*/

// private
    std::string toString_Spaces() {
        std::string retval = "";
        std::vector<domain::Space*> &s = domain_->getSpaces();
        for (std::vector<domain::Space*>::iterator it = s.begin(); it != s.end(); ++it)
            retval = retval.append((*it)->toString()).append("\n");
        return retval;
    }

    // TODO: Private
    //
    std::string toString_Idents() {
        std::string retval = "";
        std::vector<domain::VecIdent*> &id = domain_->getVecIdents();
        for (std::vector<domain::VecIdent *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::VecIdent* coords = coords2dom_->getVecIdent(*it);
            retval = retval.append(coords->toString()).append("\n");
        }
        return retval;
    }

    std::string toString_Exprs() {
        std::string retval = "";
        std::vector<domain::VecExpr*> &id = domain_->getVecExprs();
        for (std::vector<domain::VecExpr *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::VecExpr* coords = coords2dom_->getVecExpr(*it);
            retval = retval.append(coords->toString()).append("\n");
        }
        return retval;
    }

    std::string toString_Vectors() {
        std::string retval = "";
        std::vector<domain::Vector*> &id = domain_->getVectors();
        for (std::vector<domain::Vector *>::iterator it = id.begin(); it != id.end(); ++it) {
            coords::Vector* coords = coords2dom_->getVector(*it);
            retval = retval.append(coords->toString()).append("\n");
        }
        return retval;
    }

    std::string toString_Defs() {
        return std::string("Defs: Stub.");  
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



