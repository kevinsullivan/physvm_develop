// CodeCoordinate class function implementation
#include <cstddef>  
#include <string>

#include "clang/AST/AST.h"

// class VectorASTNode member functions
void setASTNode(clang::Stmt& vecInstStmt){
	this->vecInstStmt_ = vecInstStmt;
}


clang::Stmt& getASTNode(){
	return this->vecInstStmt_;
}








