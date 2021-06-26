
#ifndef ASTTOCOORDS_H
#define ASTTOCOORDS_H

//#include "AST.h"
#include "clang/AST/AST.h"
#include "../Coords.h"

#include <memory>

#include <iostream>
#include <unordered_map>
/*
This relational class maps Clang AST nodes to code coordinates
in our ontology. We want a single base type for all coordinates. 
Clang does not have a single base type for all AST nodes. This is
a special case of the broader reality that we will want to have
code coordinates for diverse types of code elements. So we will
need multiple function types, from various code element types to
our uniform (base class for) code coordinates. Coords subclasses
add specialized state and behavior corresponding to their concrete
code element types.

Note: At present, the only kind of Clang AST nodes that we need
are Stmt nodes. Stmt is a deep base class for Clang AST nodes,
including clang::Expr, clang::DeclRefExpr, clang:MemberCallExpr,
and so forth. So the current class is overbuilt in a sense; but
we design it as we have to show the intended path to generality.

To use this class, apply the mk methods to Clang AST nodes of 
the appropriate types. These methods create Coord objects of the
corresponding types, wrape the AST nodes in the Coords objects,
update the relational map, and return the constructed Coords. 
Client code is responsible for deleting (TBD).

Also note that Vector_Lit doesn't have a sub-expression.
*/

namespace ast2coords {

/*
When generating interpretation, we know subtypes of vector expressions
(literal, variable, function application), and so do not need and should
not use a generic putter. So here there are no superclass mkVecExpr or
Vector mk oprations. 
*/

class ASTToCoords
{
public:

    ASTToCoords();

    void setASTState(coords::Coords* coords, std::shared_ptr<ast::NodeContainer> astNode, clang::ASTContext* c);
    //void setASTState(coords::Coords* coords, clang::Stmt* stmt, clang::ASTContext* c);
    //void setASTState(coords::Coords* coords, clang::Decl* decl, clang::ASTContext* c);
	coords::Coords* getCoords(std::shared_ptr<ast::NodeContainer> astNode){
		//std::string TagConversion[] = {"UnitDecl", "FuncDecl", "Stmt", "VarDecl", "ConsDecl","ParamDecl"};
		switch(astNode->ASTTag_){
			case ast::ASTTag::Stmt__: {
				if(stmt_edges.find(astNode->ASTNode_.Stmt_) == stmt_edges.end()){
					return nullptr;
				}
				else return stmt_edges[astNode->ASTNode_.Stmt_];
			} 	break;
			case ast::ASTTag::VarDecl__: {
				if(var_edges.find(astNode->ASTNode_.VarDecl_) == var_edges.end())
					return nullptr;
				else return var_edges[astNode->ASTNode_.VarDecl_];
			}	break;
			case ast::ASTTag::FuncDecl__: {
				if(func_edges.find(astNode->ASTNode_.FuncDecl_) == func_edges.end())
					return nullptr;
				return func_edges[astNode->ASTNode_.FuncDecl_];
			}	break;
			case ast::ASTTag::UnitDecl__: {
				if(unit_edges.find(astNode->ASTNode_.UnitDecl_) == unit_edges.end())
					return nullptr;
				return unit_edges[astNode->ASTNode_.UnitDecl_];
			}	break;
			case ast::ASTTag::ConsDecl__: {
				if(cons_edges.find(astNode->ASTNode_.ConsDecl_) == cons_edges.end())
					return nullptr;
				return cons_edges[astNode->ASTNode_.ConsDecl_];
			}	break;
			case ast::ASTTag::ParamDecl__: {
				if(param_edges.find(astNode->ASTNode_.ParamDecl_) == param_edges.end())
					return nullptr;
				return param_edges[astNode->ASTNode_.ParamDecl_];
			}	break;
		}
	}
	bool put(std::shared_ptr<ast::NodeContainer> astNode, coords::Coords* coords);
private:
	std::unordered_map<ast::Stmt*, coords::Coords*> stmt_edges;
	std::unordered_map<ast::VarDecl*, coords::Coords*> var_edges;
	std::unordered_map<ast::FuncDecl*, coords::Coords*> func_edges;
	std::unordered_map<ast::UnitDecl*, coords::Coords*> unit_edges;
	std::unordered_map<ast::ConsDecl*, coords::Coords*> cons_edges;
	std::unordered_map<ast::ParamDecl*, coords::Coords*> param_edges;

};


} // namespace

#endif


