#ifndef CODECOORDINATE_H
#define CODECOORDINATE_H

#include <cstddef>  
#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

using namespace std;

class VectorASTNode {
public:
    // constructor
    VectorASTNode(const clang::VarDecl* vecInstStmt, 
        const MatchFinder::MatchResult &vecInstResult):ptr_vecInstStmt(vecInstStmt),
                        ref_result(vecInstResult)
    {
        setASTNodeName(vecInstStmt);
        setASTNodeFilePath(vecInstStmt, vecInstResult);
        setASTNodeMemLoc(vecInstStmt, vecInstResult);

    }

    void setASTNode(const clang::VarDecl* vecInstStmt, const MatchFinder::MatchResult &ref_result);
    void setASTNodeName(const clang::VarDecl* _vecInstStmt);
    void setASTNodeFilePath(const clang::VarDecl* _vecInstStmt, const MatchFinder::MatchResult& _ref_result);
    void setASTNodeMemLoc(const clang::VarDecl* _vecInstStmt, const MatchFinder::MatchResult& _ref_result);
    
    VectorASTNode& getASTNode();

    const string& getName();
    const string& getFilePath();
    const string& getDeclLoc();
    const string& getMemLoc();

    /*
    Implementing == is required for use as a key in a map
    */
    bool operator==(const VectorASTNode &other) const { 
        return (this == &other); 
    }
private: 
    const clang::VarDecl* ptr_vecInstStmt;
    const MatchFinder::MatchResult &ref_result;

    const string* name;
    const string* file;
    const string* loc;
    const string* memLoc;

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
    ExprASTNode(const clang::CXXMemberCallExpr* exprCall):ptr_exprCall(exprCall) {}
    // for now, an address-based equality predicate
    bool operator==(const ExprASTNode &other) const { 
        return (this == &other); 
    }
private:
    const clang::CXXMemberCallExpr* ptr_exprCall;
    const MatchFinder::MatchResult &ref_result;

    const VectorASTNode& param1;
    const VectorASTNode& param2;

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