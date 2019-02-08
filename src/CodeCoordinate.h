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
ABSTRACT

Objects of this class will be "keys" in an interpretation.
Subclasses should be defined for each kind of AST node to
be lifted to a corresponding bridge type.
*/

enum ast_type {EXPR, DECL} ;

class ExprASTNode {
public:
    ExprASTNode(const clang::Expr* expr) 
                : expr_(expr), ast_type_(EXPR) {
    }
    ExprASTNode(const clang::Decl* decl) 
                : decl_(decl), ast_type_(DECL) {
    }


    const clang::Expr* getASTNode() const { return expr_; }

    bool operator==(const ExprASTNode &other) const { 
        return (expr_ == other.expr_); 
    }
    virtual string toString() const { 
        return "ExprASTNode::toPrint -- Error should not be called";
    }
private:
    ast_type ast_type_;
    const clang::Expr* expr_;
    const clang::Decl* decl_;
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
// TODO Fix hash function
        return hash;
    }
};


class LitASTNode : public ExprASTNode {
public:
    LitASTNode(const clang::CXXConstructExpr* constrExpr) : ExprASTNode(constrExpr), constrExpr_(constrExpr) {
    }
    const clang::CXXConstructExpr* getASTNode() const {return constrExpr_; }

    // for now, an address-based equality predicate
    bool operator==(const LitASTNode &other) const { 

        return (constrExpr_ == other.constrExpr_); 
    }
    virtual string toString() const { 
        return "LitASTNode::toPrint";
    }
private:
    const clang::CXXConstructExpr* constrExpr_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct LitASTNodeHasher
{
    std::size_t operator()(const LitASTNode& k) const
    {
        // TODO -- fix
        std::size_t hash = 10101010;
        return hash;
    }
};


class VarDeclASTNode : public ExprASTNode {
public:
    VarDeclASTNode(const clang::VarDecl* varDecl) 
                : ExprASTNode(varDecl), varDecl_(varDecl) {            
    }
    const clang::VarDecl* getVarDecl() const {return varDecl_; }

    // for now, an address-based equality predicate
    bool operator==(const VarDeclASTNode &other) const { 
        return (varDecl_ == other.varDecl_); 
    }
    virtual string toString() const { 
        return "VarDeclASTNode::toPrint";
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
        // TODO Fix hash function 
        return hash;
    }
};

//---------------

class VarDeclRefASTNode : public ExprASTNode {
public:
    VarDeclRefASTNode(const clang::DeclRefExpr* varDeclRef) 
                : ExprASTNode(varDeclRef), varDeclRef_(varDeclRef) {            
    }
    const clang::DeclRefExpr* getVarDeclRef() const {return varDeclRef_; }

    // for now, an address-based equality predicate
    bool operator==(const VarDeclRefASTNode &other) const { 
        return (varDeclRef_ == other.varDeclRef_); 
    }
    virtual string toString() const { 
        return "VarDeclRefASTNode::toPrint";
    }
private:
    const clang::DeclRefExpr* varDeclRef_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct VarDeclRefASTNodeHasher
{
    std::size_t operator()(const VarDeclRefASTNode& k) const
    {
        std::size_t hash = 101010;
        // TODO Fix hash function 
        return hash;
    }
};

//-----------------

//---------------

// For Add expressions

class CXXConstructExprASTNode : public ExprASTNode {
public:
    CXXConstructExprASTNode(const clang::CXXConstructExpr* exp) 
                : ExprASTNode(exp), cxxConstructExpr_(exp) {            
    }
    const clang::CXXConstructExpr* getXXConstructExpr() const {return cxxConstructExpr_; }

    // for now, an address-based equality predicate
    bool operator==(const CXXConstructExprASTNode &other) const { 
        return (cxxConstructExpr_ == other.cxxConstructExpr_); 
    }
    virtual string toString() const { 
        return "CXXConstructExprASTNode::toPrint";
    }
private:
    const clang::CXXConstructExpr* cxxConstructExpr_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct CXXConstructExprASTNodeHasher
{
    std::size_t operator()(const CXXConstructExprASTNode& k) const
    {
        std::size_t hash = 101010;
        // TODO Fix hash function 
        return hash;
    }
};



#endif