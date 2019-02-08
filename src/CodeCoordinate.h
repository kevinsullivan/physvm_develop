#ifndef CODECOORDINATE_H
#define CODECOORDINATE_H

#include <cstddef>  
#include <iostream>             // for cheap logging only
#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace std;

/*
Objects of this class will be "keys" in an interpretation
*/
class ExprASTNode {
public:
    ExprASTNode(const clang::Expr* expr) 
                : expr_(expr) {
    }
    const clang::Expr* getASTNode() const { return expr_; }

    bool operator==(const ExprASTNode &other) const { 
        return (expr_ == other.expr_); 
    }
    virtual string toString() const { 
        return "ExprASTNode::toPrint";
    }
private:
    const clang::Expr* expr_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct ExprASTNodeHasher
{
    std::size_t operator()(const ExprASTNode& k) const
    {
        std::size_t hash = 10101010;
        cerr << "ExprASTNodeHasher: Fix has function\n";
        return hash;
    }
};


/*
BIG TODO: Have all of these nodes implement operator== against same type,
as in Lit below.
*/


//////////////
/*
Objects of this class will be "keys" in an interpretation.

NOTE TODO: Delete MatchFinder and id_ stuff from other classes
*/
class LitASTNode : public ExprASTNode {
public:
    LitASTNode(const clang::CXXConstructExpr* constrExpr) : ExprASTNode(constrExpr), constrExpr_(constrExpr) {
    }
    const clang::CXXConstructExpr* getASTNode() const {return constrExpr_; }

    // for now, an address-based equality predicate
    bool operator==(const LitASTNode &other) const { 
        cerr << "LitASTNode::operator==(), address comparison on underlying AST nodes.\n";
        return (constrExpr_ == other.constrExpr_); 
    }
private:
    const clang::CXXConstructExpr* constrExpr_;
//    const MatchFinder::MatchResult &Result_;
//    int64_t id_;

};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct LitASTNodeHasher
{
    std::size_t operator()(const LitASTNode& k) const
    {
        std::size_t hash = 10101010;
/*
            //(const_cast<clang::DeclStmt*>
            //    (k.getASTNode()))
            //        ->getID();

            (const_cast<clang::CXXConstructExpr*>
                (k.getASTNode()))
                    ->getID(*k.getContext());
*/
        cerr << "LitASTNodeHasher: Replace hash function\n";
        return hash;
    }
};


//////////////

/*
VectorVarDeclNode, Identifier*, VarDeclHasher
*/

/*
Objects of this class will be "keys" in an interpretation
*/
class VarDeclASTNode : ExprASTNode {
public:
    VarDeclASTNode(const clang::VarDecl* varDecl) 
                : varDecl_(varDecl) {            
    }

    const clang::VarDecl* getVarDecl() const {return varDecl_; }

    // for now, an address-based equality predicate
    bool operator==(const VarDeclASTNode &other) const { 
        return (varDecl_ == other.varDecl_); 
    }
private:
    const clang::VarDecl* varDecl_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct VarDeclASTNodeHasher
{
    std::size_t operator()(const VarDeclASTNode& k) const
    {
        std::size_t hash = 101010;
        cerr << "VectorVarDeclNodeHasher has function needs fixing\n";
/*
        std::size_t hash = 
            (const_cast<clang::VarDecl*>
                (k.getVarDeclNode()))
                    ->getID(*k.getContext());
*/
        return hash;
    }
};




#endif