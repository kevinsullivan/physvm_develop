// CodeCoordinate class function implementation
#include <cstddef>  
#include <string>

#include "clang/AST/AST.h"

// CLASS VECTORASTNODE MEMBER FUNCTIONS IMPLEMENTATION

// VectorASTNode set methods implemetation
void VectorASTNode::setASTNode(const clang::VarDecl* vecInstStmt, 
		const MatchFinder::MatchResult &vecInstResult){

	this->ptr_vecInstStmt = vecInstStmt;
	this->ref_result = vecInstResult;
}

void VectorASTNode::setASTNodeName(const clang::VarDecl* _vecInstStmt){

	this->name_ = vecInstStmt->getNameAsString();

}
void VectorASTNode::setASTNodeFilePath(const clang::VarDecl* _vecInstStmt, 
		const MatchFinder::MatchResult& _ref_result){

	this->filepath_ = _vecInstStmt->getPointOfInstantiation().pringToString(*(_ref_result));

}

void VectorASTNode::setASTNodeMemLoc(const clang::VarDecl* _vecInstStmt, const MatchFinder::MatchResult& _ref_result)
{
	return "To be implemented!\n";
}

// VectorASTNode get methods implemetation

VectorASTNode & VectorASTNode::getASTNode(){
	return *this;
}

const string& name VectorASTNode::getName(){
	return this->name_;
}

const string& filepath VectorASTNode::getFilePath(){
	return this->filepath_;
}

const string& loc VectorASTNode::getDeclLoc(){
	return this->loc_;
}


// int64_t VectorASTNode::getMemLoc() const{
// 	return memLoc;
// }

std::size_t VectorASTNodeHasher::operator() (const VectorASTNode& k) const
{
	return k.getMemLoc();
}



// CLASS EXPRASTNODE MEMBER FUNCTIONS IMPLEMENTATION


// CLASS CODECOORDINATES MEMBER FUNCTIONS IMPLEMENTATION
void CodeCoordinates::InsertVectorASTNodeRef(const VectorASTNode& vecASTNode) {
	this->VectorASTNodeList.push_back( vecASTNode);
}

const VectorASTNode& CodeCoordinates::getVectorASTNodeRef(const string& memLocation){
	for(list<const VectorASTNode& >::iterator it = this->VectorASTNodeList.begin();
				it != this->VectorASTNodeList.end(); ++it)
	{
		if(it->getMemLoc() == memLocation)
			return it;
	}
}

















