// CodeCoordinate class function implementation
#include <cstddef>  
#include <string>

#include "clang/AST/AST.h"

// CLASS VECTORASTNODE MEMBER FUNCTIONS IMPLEMENTATION

// VectorASTNode set methods implemetation
void setASTNode(const clang::VarDecl* vecInstStmt, 
		const MatchFinder::MatchResult &vecInstResult){

	this->ptr_vecInstStmt = vecInstStmt;
	this->ref_result = vecInstResult;
}

void setASTNodeName(const clang::VarDecl* _vecInstStmt){

	this->name_ = vecInstStmt->getNameAsString();

}
void setASTNodeFilePath(const clang::VarDecl* _vecInstStmt, 
		const MatchFinder::MatchResult& _ref_result){

	this->filepath_ = _vecInstStmt->getPointOfInstantiation().pringToString(*(_ref_result));

}

void setASTNodeMemLoc(const clang::VarDecl* _vecInstStmt, const MatchFinder::MatchResult& _ref_result)
{
	return "To be implemented!\n";
}

// VectorASTNode get methods implemetation

VectorASTNode & getASTNode(){
	return *this;
}

const string& name getName(){
	return this->name_;
}

const string& filepath getFilePath(){
	return this->filepath_;
}

const string& loc getDeclLoc(){
	return this->loc_;
}


const string& memLoc_ getMemLoc(){
	return this->memLoc_;
}




// CLASS EXPRASTNODE MEMBER FUNCTIONS IMPLEMENTATION








