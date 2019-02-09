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
    ExprASTNode() : expr_(NULL) {}
    ExprASTNode(const clang::Expr* expr) : expr_(expr) {}
    ExprASTNode(const clang::Decl* decl) : decl_(decl) {}
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


struct ExprASTNodeHasher
{
    std::size_t operator()(const ExprASTNode& k) const
    {
        std::size_t hash = 10101010;
// TODO Fix hash function
        return hash;
    }
};

// TODO -- don't need to store pointers in superclass
// TODO -- change name to LitExprASTNode
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
        return "(mk_vector 0)";
    }
private:
    const clang::CXXConstructExpr* constrExpr_;
};


struct LitASTNodeHasher
{
    std::size_t operator()(const LitASTNode& k) const
    {
        // TODO -- fix
        std::size_t hash = 10101010;
        return hash;
    }
};

//---------------

// Identifier implemented as VarDecl
class IdentifierASTNode : public ExprASTNode {
public:
    IdentifierASTNode(const clang::VarDecl* varDecl) 
                : ExprASTNode(varDecl), varDecl_(varDecl) {            
    }
    const clang::VarDecl* getVarDecl() const {return varDecl_; }

    // for now, an address-based equality predicate
    bool operator==(const IdentifierASTNode &other) const { 
        return (varDecl_ == other.varDecl_); 
    }
    virtual string toString() const { 
        return varDecl_->getNameAsString();
    }
private:
    const clang::VarDecl* varDecl_;
};


struct IdentifierASTNodeHasher
{
    std::size_t operator()(const IdentifierASTNode& k) const
    {
        std::size_t hash = 101010;
        // TODO Fix hash function 
        return hash;
    }
};


// ToDo -- change name to VariableExpr (implemented as VarDeclRef)

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
        return varDeclRef_->getDecl()->getNameAsString();
    }
private:
    const clang::DeclRefExpr* varDeclRef_;
};


struct VarDeclRefASTNodeHasher
{
    std::size_t operator()(const VarDeclRefASTNode& k) const
    {
        std::size_t hash = 101010;
        // TODO Fix hash function 
        return hash;
    }
};


// TODO -- Change to AddExpr, implemented as CXXConstructExpr

class VectorAddExprASTNode : public ExprASTNode {
public:
    VectorAddExprASTNode(const clang::CXXConstructExpr* exp, const ExprASTNode *left, const ExprASTNode *right) 
                : ExprASTNode(exp), cxxConstructExpr_(exp), left_(left), right_(right) {            
    }
    const clang::CXXConstructExpr* getXXConstructExpr() const {return cxxConstructExpr_; }

    // for now, an address-based equality predicate
    bool operator==(const VectorAddExprASTNode &other) const { 
        return (cxxConstructExpr_ == other.cxxConstructExpr_); 
    }
    virtual string toString() const { 
        return "add (" + left_->toString() + ") (" + right_->toString() + ")"; 
    }
private:
    const clang::CXXConstructExpr* cxxConstructExpr_;
    const ExprASTNode* left_;
    const ExprASTNode* right_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct VectorAddExprASTNodeHasher
{
    std::size_t operator()(const VectorAddExprASTNode& k) const
    {
        std::size_t hash = 101010;
        // TODO Fix hash function 
        return hash;
    }
};

// TODO -- Binding hides VarDecl
class BindingASTNode : public ExprASTNode {
public:
    BindingASTNode(const clang::VarDecl* varDecl) 
                : ExprASTNode(varDecl), varDecl_(varDecl) {            
    }
    const clang::VarDecl* getVarDecl() const {return varDecl_;}

    // for now, an address-based equality predicate
    bool operator==(const BindingASTNode &other) const { 
        return (varDecl_ == other.varDecl_); 
    }
    virtual string toString() const { 
        return "Binding";
    }
private:
    const clang::VarDecl* varDecl_;
};


struct BindingASTNodeHasher
{
    std::size_t operator()(const BindingASTNode& k) const
    {
        std::size_t hash = 101010;
        // TODO Fix hash function 
        return hash;
    }
};



#endif