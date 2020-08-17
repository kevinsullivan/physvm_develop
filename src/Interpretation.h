
#include "Checker.h"
class Checker;

#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
#include "AST.h"
#include "Coords.h"
#include "Domain.h"
//#include "Space.h"
#include "ASTToCoords.h"
#include "CoordsToDomain.h"
#include "Oracle.h"
#include "CoordsToInterp.h"
#include "InterpToDomain.h"
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

    void setOracle(oracle::Oracle* oracle)
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


	std::string toString_SEQ_GLOBALSTMTs();

	void mkSEQ_GLOBALSTMT(const ast::SEQ_GLOBALSTMT * ast , std::vector < ast::GLOBALSTMT *> operands );
                    
	std::string toString_PROGRAMs();

	std::string toString_GLOBALSTMTs();

	std::string toString_COMPOUND_STMTs();

	void mkCOMPOUND_STMT(const ast::COMPOUND_STMT * ast , std::vector < ast::STMT *> operands );
                    
	std::string toString_STMTs();

	std::string toString_FUNC_DECLs();

	void mkVOID_FUNC_DECL_STMT(const ast::VOID_FUNC_DECL_STMT * ast ,ast::STMT* operand1);
                    
	std::string toString_VOID_FUNC_DECL_STMTs();

	void mkMAIN_FUNC_DECL_STMT(const ast::MAIN_FUNC_DECL_STMT * ast ,ast::STMT* operand1);
                    
	std::string toString_MAIN_FUNC_DECL_STMTs();

	std::string toString_Spaces();
	std::vector<interp::Space*> getSpaceInterps();
	std::vector<std::string> getSpaceNames();
	std::vector<interp::Frame*> getFrameInterps();
	std::vector<std::string> getFrameNames();
	    void buildDefaultSpaces();

    void buildSpace();
    void buildFrame();

    //void setAll_Spaces();
    void printSpaces();
    void printFrames();
    void mkVarTable();//make a printable, indexed table of variables that can have their types assigned by a user or oracle
    void printVarTable();//print the indexed variable table for the user
    void updateVarTable();//while loop where user can select a variable by index and provide a physical type for that variable
    void remap(coords::Coords c, domain::DomainObject newinterp);

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
    oracle::Oracle *oracle_;
    clang::ASTContext *context_;
    coords2domain::CoordsToDomain *coords2dom_;
    ast2coords::ASTToCoords *ast2coords_;
    coords2interp::CoordsToInterp *coords2interp_;
    interp2domain::InterpToDomain *interp2domain_; 
    Checker *checker_;
    std::vector<std::string> sources_;
	std::vector<coords::PROGRAM*> PROGRAM_vec;
	std::vector<coords::GLOBALSTMT*> GLOBALSTMT_vec;
	std::vector<coords::STMT*> STMT_vec;
	std::vector<coords::FUNC_DECL*> FUNC_DECL_vec;
	std::vector<coords::VOID_FUNC_DECL_STMT*> VOID_FUNC_DECL_STMT_vec;
	std::vector<coords::MAIN_FUNC_DECL_STMT*> MAIN_FUNC_DECL_STMT_vec;	std::vector<coords::SEQ_GLOBALSTMT*> SEQ_GLOBALSTMT_vec;
	std::vector<coords::COMPOUND_STMT*> COMPOUND_STMT_vec;

    std::unordered_map<int, coords::Coords*> index2coords_;
    std::unordered_map<int, void*> index2dom_;

    //populated after initial pass of AST
    //list of scalars/vecs that do not have any assigned or inferred type
   // std::vector<ast::VecIdent*> unconstrained_vecs;
    //std::vector<std::string> unconstrained_vec_names;
    //std::vector<ast::ScalarIdent*> unconstrained_floats;
    //std::vector<std::string> unconstrained_float_names;
    //std::vector<ast::TransformIdent*> unconstrained_transforms;
   // std::vector<std::string> unconstrained_transform_names;
}; 

} // namespaceT

#endif
