#ifndef CODECOORDINATE_H
#define CODECOORDINATE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang;
using namespace clang::ast_matchers;

class VectorASTNode {
public:
    VectorASTNode(const clang::VarDecl* vecInstStmt, 
                  const MatchFinder::MatchResult &Result) 
                  : ptr_vecInstStmt(vecInstStmt), 
                  Result_(Result) {
                      id_ = ((clang::Stmt*)vecInstStmt)->getID(*(Result_.Context));
                  }
    void setASTNode(const clang::VarDecl* vecInstStmt);
    const clang::VarDecl* getASTNode() const { return ptr_vecInstStmt; }
    
    /*
    Implementing == is required for use as a key in a map
    */
    bool operator==(const VectorASTNode &other) const { 
        return (id_ == other.id_); 
    }
    ASTContext* getContext() const { return Result_.Context; }

private: 
    const clang::VarDecl* ptr_vecInstStmt;
    const MatchFinder::MatchResult &Result_;
    int64_t id_;
};

/*
Provide has function for VectorASTNode class, as required
for the use of objects of this class as keys in a map.
*/
struct VectorASTNodeHasher
{
public:
    std::size_t operator() (const VectorASTNode& k) const
    {
        std::size_t hash = 
            ((clang::Stmt*)(k.getASTNode()))
                ->getID(*k.getContext());
        return hash;
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

            //(const_cast<clang::VarDecl*>
            //    (k.getASTNode()))
            //        ->getID();

            (const_cast<clang::CXXMemberCallExpr*>
                (k.getASTNode()))
                    ->getID(*k.getContext());
        return hash;
    }
};

#endif