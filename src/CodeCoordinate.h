#ifndef CODE_H
#define CODE_H

#include <cstddef>  
#include "clang/AST/AST.h"
/*
Objects of this class will be "keys" in an interpretation
*/
class VectorASTNode {
public:
    VectorASTNode(const clang::Stmt* vecInstStmt):ref_vecInstStmt(vecInstStmt) {}
    void setASTNode(const clang::Stmt* vecInstStmt);
    clang::Stmt* getASTNode();
    /*
    Implementing == is required for use as a key in a map
    */
    bool operator==(const VectorASTNode &other) const { 
        return (this == &other); 
    }
private: 
    const clang::Stmt* ref_vecInstStmt;
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
        std::size_t hash = 0;
        return hash;
    }
};


/*
Objects of this class will be "keys" in an interpretation
*/
class ExprASTNode {
public:
    ExprASTNode() {}
    // for now, an address-based equality predicate
    bool operator==(const ExprASTNode &other) const { 
        return (this == &other); 
    }
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