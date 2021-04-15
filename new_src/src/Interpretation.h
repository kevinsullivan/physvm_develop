
#include "Checker.h"
class Checker;

#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
//#include "AST.h"
#include "Coords.h"
#include "Domain.h"
//#include "Space.h"
#include "maps/ASTToCoords.h"
#include "maps/CoordsToDomain.h"
#include "oracles/Oracle.h"
#include "oracles/Oracle_AskAll.h"//need this one for now
#include "maps/CoordsToInterp.h"
#include "maps/InterpToDomain.h"
#include <g3log/g3log.hpp> 
#include <memory>


#include <unordered_map>

namespace interp {


// TODO: Take clang::ASTContext
class Interpretation
{
public:
    Interpretation();

    std::string toString_AST();

    void setOracle(oracle::Oracle_AskAll* oracle)
    {
        oracle_ = oracle;
    }

    void setASTContext(clang::ASTContext* context)
    {
        context_ = context;
    }

    //void addSpace(std::string type, std::string name, int dimension)
    //{
    //    domain_->mkSpace(type, name, dimension);
    //}

    domain::Domain* getDomain()
    {
        return domain_;
    }

    void setSources(std::vector<std::string> sources)
    {
        this->sources_ = sources;
    }

    std::vector<std::string> getSources()
    {
        return this->sources_;
    }

	/*
	move isAST and capture into configuration file
	*/
	void mkNode(std::string internalNodeType, std::shared_ptr<ast::NodeContainer> astNode, bool capture=false, bool isAST = false);
	
	void mkNode(std::string internalNodeType, ast::Stmt* node, bool capture=false, bool isAST = false){
        mkNode(internalNodeType,ast::mkContainer(node),capture,isAST);
    };
	void mkNode(std::string internalNodeType, ast::UnitDecl* node, bool capture=false, bool isAST = false){
        mkNode(internalNodeType,ast::mkContainer(node),capture,isAST);
    };
	void mkNode(std::string internalNodeType, ast::VarDecl* node, bool capture=false, bool isAST = false){
        //node->dump();
        mkNode(internalNodeType,ast::mkContainer(node),capture,isAST);
    };
	void mkNode(std::string internalNodeType, ast::FuncDecl* node, bool capture=false, bool isAST = false){
        mkNode(internalNodeType,ast::mkContainer(node),capture,isAST);
    };
	void buffer_link(ast::Stmt* stmt){
		auto node = ast::mkContainer(stmt);
		this->link = node;
	};
	void buffer_link(ast::UnitDecl* udecl){
		auto node = ast::mkContainer(udecl);
		this->link = node;
	};
	void buffer_link(ast::VarDecl* varDecl){
		auto node = ast::mkContainer(varDecl);
		this->link = node;
	};
	void buffer_link(ast::FuncDecl* funcDecl){
		auto node = ast::mkContainer(funcDecl);
		this->link = node;
	};

	//when constructing ast node, buffer immediate descendants
	void buffer_operand(std::shared_ptr<ast::NodeContainer> node){
		this->astBuffer.push_back(node);
	};
	void buffer_operand(ast::Stmt* stmt){
		auto node = ast::mkContainer(stmt);
		this->astBuffer.push_back(node);
	};
	void buffer_operand(ast::UnitDecl* udecl){
		auto node = ast::mkContainer(udecl);
		this->astBuffer.push_back(node);
	};
	void buffer_operand(ast::VarDecl* varDecl){
		auto node = ast::mkContainer(varDecl);
		this->astBuffer.push_back(node);
	};
	void buffer_operand(ast::FuncDecl* funcDecl){
		auto node = ast::mkContainer(funcDecl);
		this->astBuffer.push_back(node);
	};
    void buffer_operands(std::vector<ast::Stmt*> stmts){
        for(auto stmt:stmts){
            auto node = ast::mkContainer(stmt);
            this->astBuffer.push_back(node);
        }
    }
    void buffer_operands(std::vector<ast::FuncDecl*> decls){
        for(auto decl_:decls){
            auto node = ast::mkContainer(decl_);
            this->astBuffer.push_back(node);
        }
    }

	void clear_buffer(){//to make it clear
		this->astBuffer.clear();
        link = nullptr;
	};

    void printChoices();//print to file*

    //void setAll_Spaces();
    void printSpaces();
    //void mkVarTable();//make a printable, indexed table of variables that can have their types assigned by a user or oracle
    //void printVarTable();//print the indexed variable table for the user
    //void updateVarTable();//while loop where user can select a variable by index and provide a physical type for that variable
    //void printChoices();//to replay annotation sessions

	void printVarTable();
	void interpretProgram();//central loop to interact with human

    /*
    * Builds a list of variables that have a type either assigned or inferred.
    * Used for runtime constraint generation/logging 
    */
    //void buildTypedDeclList();
    
    
    /*
    used for generating dynamic constraints.
    given a variable, determine whether or not it does not have a type available (if so, a constraint must be registered)
    */
    //bool needsConstraint(clang::VarDecl* var);

// TODO: Make private
    domain::Domain *domain_;
    oracle::Oracle_AskAll *oracle_;
    clang::ASTContext *context_;
    coords2domain::CoordsToDomain *coords2dom_;
    ast2coords::ASTToCoords *ast2coords_;
    coords2interp::CoordsToInterp *coords2interp_;
    interp2domain::InterpToDomain *interp2domain_; 
    Checker *checker_;
    std::vector<std::string> sources_;
    //std::unordered_map<int, coords::Coords*> index2coords_;
    //std::unordered_map<int, void*> index2dom_;
	coords::Coords* AST;
	std::vector<coords::Coords*> captureCache;//used to store Coords

    std::shared_ptr<ast::NodeContainer> link;
	std::vector<std::shared_ptr<ast::NodeContainer>> astBuffer;


}; 

} // namespaceT

#endif
