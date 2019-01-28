#ifndef CODECOORDINATE_H
#define CODECOORDINATE_H

#include <cstddef>  
#include "clang/AST/AST.h"

class VectorASTNode {
public:
    VectorASTNode(const clang::VarDecl* vecInstStmt,
                    int64_t memLoc_):ptr_vecInstStmt(vecInstStmt),memLoc(memLoc_) 
    {
        this->memLoc = vecInstStmt->getID();
    }

    void setASTNode(const clang::VarDecl* vecInstStmt);
    clang::VarDecl* getASTNode();


    int64_t getMemLoc() const;
    /*
    Implementing == is required for use as a key in a map
    */
    
    bool operator==(const VectorASTNode &other) const { 
        return (this->memLoc == other.memLoc); 
    }

//when 'int64_t memLoc' becomes private, Hannah got the following err msg:
//     /tmp/ccQSNVEH.o: In function `VectorASTNodeHasher::operator()(VectorASTNode const&) const':
// /pierce/src/CodeCoordinate.h:41: undefined reference to `VectorASTNode::getMemLoc() const'
    int64_t memLoc;
private: 
    const clang::VarDecl* ptr_vecInstStmt;
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
        return k.memLoc;
    }
};


/*
Objects of this class will be "keys" in an interpretation
*/
class ExprASTNode {
public:
    ExprASTNode(const clang::CXXMemberCallExpr* exprCall):ptr_exprCall(exprCall) {}
    // for now, an address-based equality predicate
    bool operator==(const ExprASTNode &other) const { 
        return (this == &other); 
    }
private:
    const clang::CXXMemberCallExpr* ptr_exprCall;
};

/*
Provide has function for ExprASTNodeHasher class, as required
for the use of objects of this class as keys in a map.
*/
struct ExprASTNodeHasher
{
    std::size_t operator()(const ExprASTNode& k) const
    {
        std::size_t hash = 0;
        return hash;
    }
};

#endif