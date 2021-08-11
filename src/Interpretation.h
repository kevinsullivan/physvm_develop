
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
#include "oracles/Oracle_LeanInference.h"
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

    std::string toStringAST(bool typecheck_mode_ = true);

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
	coords::Coords* mkNode(std::string internalNodeType, std::shared_ptr<ast::NodeContainer> astNode, bool capture=false, bool isAST = false);
	
    bool existsConstructor(std::shared_ptr<ast::NodeContainer> astNode){
        return this->ast2coords_->getCoords(astNode) != nullptr;
    }
    bool existsConstructor(ast::ConsDecl* node){
        return existsConstructor(ast::mkContainer(node));
    }

    void mkConstructor(std::shared_ptr<ast::NodeContainer> astNode);
    void mkConstructor(ast::ConsDecl* node){
        return mkConstructor(ast::mkContainer(node));
    }
    void mkFunction(std::shared_ptr<ast::NodeContainer> astNode);
    void mkFunction(ast::FuncDecl* node){
        return mkFunction(ast::mkContainer(node));
    }
    void mkFunctionWithReturn(std::string nodeRef, std::shared_ptr<ast::NodeContainer> astNode);
    void mkFunctionWithReturn(std::string nodeRef, ast::FuncDecl* node){
        return mkFunctionWithReturn(nodeRef, ast::mkContainer(node));
    }

    bool tryMkCallExpr(std::shared_ptr<ast::NodeContainer> astNode);

    void mkFunctionCall(std::shared_ptr<ast::NodeContainer> astNode, bool capture = false);

    void mkFunctionCall(ast::Stmt* node, bool capture= false){
        return mkFunctionCall(ast::mkContainer(node));
    };

    bool checkFuncExists(std::shared_ptr<ast::NodeContainer> astNode);
    bool checkFuncExists(ast::FuncDecl* node){
        return checkFuncExists(ast::mkContainer(node));
    };

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
	void mkNode(std::string internalNodeType, ast::ConsDecl* node, bool capture=false, bool isAST = false){
        //node->dump();
        mkNode(internalNodeType,ast::mkContainer(node),capture,isAST);
    };
	void mkNode(std::string internalNodeType, ast::ParamDecl* node, bool capture=false, bool isAST = false){
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

    
	void buffer_container(ast::VarDecl* varDecl){
		auto node = ast::mkContainer(varDecl);
		this->container = node;
	};
	void buffer_container(ast::ParamDecl* paramDecl){
		auto node = ast::mkContainer(paramDecl);
		this->container = node;
	};

    void buffer_constructor(ast::ConsDecl* consDecl){
        auto node = ast::mkContainer(consDecl);
        this->constructor = node;
    }

	//when constructing ast node, buffer immediate descendants
	void buffer_operand(std::shared_ptr<ast::NodeContainer> node){
		this->astOperandBuffer.push_back(node);
	};
	void buffer_operand(ast::Stmt* stmt){
		auto node = ast::mkContainer(stmt);
		this->astOperandBuffer.push_back(node);
	};
	void buffer_operand(ast::UnitDecl* udecl){
		auto node = ast::mkContainer(udecl);
		this->astOperandBuffer.push_back(node);
	};
	void buffer_operand(ast::VarDecl* varDecl){
		auto node = ast::mkContainer(varDecl);
		this->astOperandBuffer.push_back(node);
	};
	void buffer_operand(ast::FuncDecl* funcDecl){
		auto node = ast::mkContainer(funcDecl);
		this->astOperandBuffer.push_back(node);
	};
    void buffer_operands(std::vector<ast::Stmt*> stmts){
        for(auto stmt:stmts){
            auto node = ast::mkContainer(stmt);
            this->astOperandBuffer.push_back(node);
        }
    }
    void buffer_operands(std::vector<ast::FuncDecl*> decls){
        for(auto decl_:decls){
            auto node = ast::mkContainer(decl_);
            this->astOperandBuffer.push_back(node);
        }
    }
    void buffer_operands(std::vector<ast::ParamDecl*> decls){
        for(auto decl_:decls){
            auto node = ast::mkContainer(decl_);
            this->astOperandBuffer.push_back(node);
        }
    }
	void buffer_body(ast::Stmt* stmt){
		auto node = ast::mkContainer(stmt);
		this->astBodyBuffer.push_back(node);
	};
	void buffer_body(ast::UnitDecl* udecl){
		auto node = ast::mkContainer(udecl);
		this->astBodyBuffer.push_back(node);
	};
	void buffer_body(ast::VarDecl* varDecl){
		auto node = ast::mkContainer(varDecl);
		this->astBodyBuffer.push_back(node);
	};
	void buffer_body(ast::FuncDecl* funcDecl){
		auto node = ast::mkContainer(funcDecl);
		this->astBodyBuffer.push_back(node);
	};
    void buffer_body(std::vector<ast::Stmt*> stmts){
        for(auto stmt:stmts){
            auto node = ast::mkContainer(stmt);
            this->astBodyBuffer.push_back(node);
        }
    }
    void buffer_body(std::vector<ast::FuncDecl*> decls){
        for(auto decl_:decls){
            auto node = ast::mkContainer(decl_);
            this->astBodyBuffer.push_back(node);
        }
    }

	void clear_buffer(){//to make it clear
		this->astOperandBuffer.clear();
		this->astBodyBuffer.clear();
        link = nullptr;
        constructor = nullptr;
        container = nullptr;
	};

    void printChoices();//print to file*

    //void setAll_Spaces();
    void printSpaces();
    //void mkVarTable();//make a printable, indexed table of variables that can have their types assigned by a user or oracle
    //void printVarTable();//print the indexed variable table for the user
    //void updateVarTable();//while loop where user can select a variable by index and provide a physical type for that variable
    //void printChoices();//to replay annotation sessions
    //void printAllErrors();
	void printVarTable();
    void printAllTerms();
    void printConstructorTable();
    void interpretConstructors();
    void printFunctionTable();
    void interpretFunctions();
    void clearInferredInterpretations();
    void performInference();
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
    oracle::Oracle_LeanInference *oracle_infer_;
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
    std::vector<coords::Coords*> allCoords;

    std::shared_ptr<ast::NodeContainer> link;
    std::shared_ptr<ast::NodeContainer> constructor;
    std::shared_ptr<ast::NodeContainer> container;
	std::vector<std::shared_ptr<ast::NodeContainer>> astOperandBuffer;
	std::vector<std::shared_ptr<ast::NodeContainer>> astBodyBuffer;

    std::vector<coords::Coords*> constructors;
    std::vector<coords::Coords*> functions;
    std::vector<coords::Coords*> functions_with_return;
}; 

} // namespaceT

#endif
