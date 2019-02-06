#ifndef CODECOORDINATE_H
#define CODECOORDINATE_H

#include <cstddef>  
#include <iostream>             // for cheap logging only
#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
//#include "Bridge.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace std;
//using namespace bridge;


class VectorASTNode {
public:
    VectorASTNode(const clang::DeclStmt* vecInstStmt, 
                  const MatchFinder::MatchResult &Result) 
                  : ptr_vecInstStmt(vecInstStmt), 
                  Result_(Result) {
                      id_ = ((clang::Stmt*)vecInstStmt)->getID(*(Result_.Context));
    }

    void setASTNode(const clang::DeclStmt* vecInstStmt);
    const clang::DeclStmt* getASTNode() const { return ptr_vecInstStmt; }
    
    /*
    Implementing == is required for use as a key in a map
    */
    
    bool operator==(const VectorASTNode &other) const { 
        return (id_ == other.id_); 
    }
    ASTContext* getContext() const { return Result_.Context; }

private: 
    const clang::DeclStmt* ptr_vecInstStmt;
    const MatchFinder::MatchResult &Result_;
    int64_t id_;
};

/*
Provide has function for VectorASTNode class, as required
for the use of objects of this class as keys in a map.
*/
struct VectorASTNodeHasher
{
// public:
    std::size_t operator() (const VectorASTNode& k) const
    {
        std::size_t hash = 
            ((clang::Stmt*)(k.getASTNode()))
                ->getID(*k.getContext());
        return hash;
/*
        return k.memLoc;
*/
    }
};


/*
Objects of this class will be "keys" in an interpretation
*/
class ExprASTNode {
public:
    ExprASTNode(const clang::CXXMemberCallExpr* exprCall, 
                const MatchFinder::MatchResult &Result) 
                : ptr_exprCall(exprCall), Result_(Result) {
                    id_ = ((clang::Stmt*)exprCall)->getID(*(Result_.Context));
                }
    const clang::CXXMemberCallExpr* getASTNode() const {return ptr_exprCall; }

    // for now, an address-based equality predicate
    bool operator==(const ExprASTNode &other) const { 
        return (id_ == other.id_); 
    }
    ASTContext* getContext() const { return Result_.Context; }
private:
    const clang::CXXMemberCallExpr* ptr_exprCall;
    const MatchFinder::MatchResult &Result_;
    int64_t id_;

};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct ExprASTNodeHasher
{
    std::size_t operator()(const ExprASTNode& k) const
    {
        std::size_t hash = 

            //(const_cast<clang::DeclStmt*>
            //    (k.getASTNode()))
            //        ->getID();

            (const_cast<clang::CXXMemberCallExpr*>
                (k.getASTNode()))
                    ->getID(*k.getContext());
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
class LitASTNode {
public:
    LitASTNode(const clang::CXXConstructExpr* constrExpr):
        constrExpr_(constrExpr) {
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
class VectorVarDeclNode {
public:
    VectorVarDeclNode(const clang::VarDecl* varDecl, 
                const MatchFinder::MatchResult &Result) 
                : varDecl_(varDecl), Result_(Result) {
                    id_ = ((clang::Stmt*)varDecl)->getID(*(Result_.Context));
                }
    const clang::VarDecl* getVarDeclNode() const {return varDecl_; }

    // for now, an address-based equality predicate
    bool operator==(const VectorVarDeclNode &other) const { 
        return (id_ == other.id_); 
    }
    ASTContext* getContext() const { return Result_.Context; }
private:
    const clang::VarDecl* varDecl_;
    const MatchFinder::MatchResult &Result_;
    int64_t id_;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct VectorVarDeclNodeHasher
{
    std::size_t operator()(const VectorVarDeclNode& k) const
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