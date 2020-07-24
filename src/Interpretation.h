
#include "Checker.h"
class Checker;

#ifndef INTERPRETATION_H
#define INTERPRETATION_H

#include <iostream>
#include "AST.h"
#include "Coords.h"
#include "Domain.h"
#include "ASTToCoords.h"
#include "CoordsToDomain.h"
#include "Oracle.h"
#include "CoordsToInterp.h"
#include "InterpToDomain.h"
#include <g3log/g3log.hpp> 


#include <unordered_map>

namespace interp {

// TODO: Take clang::ASTContext
class Interpretation
{
public:
    Interpretation();

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


	std::string toString_SEQ_GLOBALSTMTs();

	void mkSEQ_GLOBALSTMT(const ast::SEQ_GLOBALSTMT * ast , std::vector < ast::GLOBALSTMT *> operands );
                    
	std::string toString_PROGRAMs();

	void mkMAIN_STMT(const ast::MAIN_STMT * ast ,ast::STMT* operand1);
                    
	void mkFUNCTION_STMT(const ast::FUNCTION_STMT * ast ,ast::STMT* operand1);
                    
	std::string toString_GLOBALSTMTs();

	std::string toString_COMPOUND_STMTs();

	void mkCOMPOUND_STMT(const ast::COMPOUND_STMT * ast , std::vector < ast::STMT *> operands );
                    
	std::string toString_STMTs();

	void mkIFTHEN_EXPR_STMT(const ast::IFTHEN_EXPR_STMT * ast ,ast::EXPR* operand1,ast::STMT* operand2);
                    
	void mkIFTHENELSEIF_EXPR_STMT_IFCOND(const ast::IFTHENELSEIF_EXPR_STMT_IFCOND * ast ,ast::EXPR* operand1,ast::STMT* operand2,ast::IFCOND* operand3);
                    
	void mkIFTHENELSE_EXPR_STMT_STMT(const ast::IFTHENELSE_EXPR_STMT_STMT * ast ,ast::EXPR* operand1,ast::STMT* operand2,ast::STMT* operand3);
                    
	std::string toString_IFCONDs();

	std::string toString_EXPRs();

	void mkASSIGN_REAL1_VAR_REAL1_EXPR(const ast::ASSIGN_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkASSIGN_REAL3_VAR_REAL3_EXPR(const ast::ASSIGN_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkASSIGN_REAL4_VAR_REAL4_EXPR(const ast::ASSIGN_REAL4_VAR_REAL4_EXPR * ast ,ast::REAL4_VAR_IDENT* operand1,ast::REAL4_EXPR* operand2);
                    
	void mkASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR * ast ,ast::REALMATRIX_VAR_IDENT* operand1,ast::REALMATRIX_EXPR* operand2);
                    
	std::string toString_ASSIGNMENTs();

	void mkDECL_REAL1_VAR_REAL1_EXPR(const ast::DECL_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkDECL_REAL3_VAR_REAL3_EXPR(const ast::DECL_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkDECL_REAL4_VAR_REAL4_EXPR(const ast::DECL_REAL4_VAR_REAL4_EXPR * ast ,ast::REAL4_VAR_IDENT* operand1,ast::REAL4_EXPR* operand2);
                    
	void mkDECL_REALMATRIX_VAR_REALMATRIX_EXPR(const ast::DECL_REALMATRIX_VAR_REALMATRIX_EXPR * ast ,ast::REALMATRIX_VAR_IDENT* operand1,ast::REALMATRIX_EXPR* operand2);
                    
	void mkDECL_REAL1_VAR(const ast::DECL_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1);
                    
	void mkDECL_REAL3_VAR(const ast::DECL_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1);
                    
	void mkDECL_REAL4_VAR(const ast::DECL_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1);
                    
	void mkDECL_REALMATRIX_VAR(const ast::DECL_REALMATRIX_VAR * ast ,ast::REALMATRIX_VAR_IDENT* operand1);
                    
	std::string toString_DECLAREs();

	void mkPAREN_REAL1_EXPR(const ast::PAREN_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1);
                    
	void mkINV_REAL1_EXPR(const ast::INV_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1);
                    
	void mkNEG_REAL1_EXPR(const ast::NEG_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1);
                    
	void mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkSUB_REAL1_EXPR_REAL1_EXPR(const ast::SUB_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkDIV_REAL1_EXPR_REAL1_EXPR(const ast::DIV_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkREF_REAL1_VAR(const ast::REF_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1);
                    
	std::string toString_REAL1_EXPRs();

	void mkPAREN_REAL3_EXPR(const ast::PAREN_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1);
                    
	void mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkSUB_REAL3_EXPR_REAL3_EXPR(const ast::SUB_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkINV_REAL3_EXPR(const ast::INV_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1);
                    
	void mkNEG_REAL3_EXPR(const ast::NEG_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1);
                    
	void mkMUL_REAL3_EXPR_REAL1_EXPR(const ast::MUL_REAL3_EXPR_REAL1_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkMUL_REALMATRIX_EXPR_REAL3_EXPR(const ast::MUL_REALMATRIX_EXPR_REAL3_EXPR * ast ,ast::REALMATRIX_EXPR* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkDIV_REAL3_EXPR_REAL1_EXPR(const ast::DIV_REAL3_EXPR_REAL1_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkREF_REAL3_VAR(const ast::REF_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1);
                    
	std::string toString_REAL3_EXPRs();

	void mkPAREN_REAL4_EXPR(const ast::PAREN_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1);
                    
	void mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL4_EXPR* operand2);
                    
	void mkMUL_REAL4_EXPR_REAL1_EXPR(const ast::MUL_REAL4_EXPR_REAL1_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkREF_REAL4_VAR(const ast::REF_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1);
                    
	std::string toString_REAL4_EXPRs();

	void mkPAREN_REALMATRIX_EXPR(const ast::PAREN_REALMATRIX_EXPR * ast ,ast::REALMATRIX_EXPR* operand1);
                    
	void mkMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(const ast::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR * ast ,ast::REALMATRIX_EXPR* operand1,ast::REALMATRIX_EXPR* operand2);
                    
	void mkREF_EXPR_REALMATRIX_VAR(const ast::REF_EXPR_REALMATRIX_VAR * ast ,ast::REALMATRIX_VAR_IDENT* operand1);
                    
	std::string toString_REALMATRIX_EXPRs();

	void mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT * ast );
                    
	std::string toString_REAL1_VAR_IDENTs();

	void mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT * ast );
                    
	std::string toString_REAL3_VAR_IDENTs();

	void mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT * ast );
                    
	std::string toString_REAL4_VAR_IDENTs();

	void mkREALMATRIX_VAR_IDENT(const ast::REALMATRIX_VAR_IDENT * ast );
                    
	std::string toString_REALMATRIX_VAR_IDENTs();

	void mkREAL1_LITERAL1(const ast::REAL1_LITERAL1 * ast );
                    
	std::string toString_REAL1_LITERALs();

	void mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3);
                    
	void mkREAL3_LITERAL3(const ast::REAL3_LITERAL3 * ast );
                    
	std::string toString_REAL3_LITERALs();

	void mkREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3,ast::REAL1_EXPR* operand4);
                    
	void mkREAL4_LITERAL4(const ast::REAL4_LITERAL4 * ast );
                    
	std::string toString_REAL4_LITERALs();

	void mkREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(const ast::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2,ast::REAL3_EXPR* operand3);
                    
	void mkREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3,ast::REAL1_EXPR* operand4,ast::REAL1_EXPR* operand5,ast::REAL1_EXPR* operand6,ast::REAL1_EXPR* operand7,ast::REAL1_EXPR* operand8,ast::REAL1_EXPR* operand9);
                    
	void mkREALMATRIX_LITERAL9(const ast::REALMATRIX_LITERAL9 * ast );
                    
	std::string toString_REALMATRIX_LITERALs();

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
	std::vector<coords::PROGRAM*> PROGRAM_vec;
	std::vector<coords::GLOBALSTMT*> GLOBALSTMT_vec;
	std::vector<coords::STMT*> STMT_vec;
	std::vector<coords::IFCOND*> IFCOND_vec;
	std::vector<coords::EXPR*> EXPR_vec;
	std::vector<coords::ASSIGNMENT*> ASSIGNMENT_vec;
	std::vector<coords::DECLARE*> DECLARE_vec;
	std::vector<coords::REAL1_EXPR*> REAL1_EXPR_vec;
	std::vector<coords::REAL3_EXPR*> REAL3_EXPR_vec;
	std::vector<coords::REAL4_EXPR*> REAL4_EXPR_vec;
	std::vector<coords::REALMATRIX_EXPR*> REALMATRIX_EXPR_vec;
	std::vector<coords::REAL1_VAR_IDENT*> REAL1_VAR_IDENT_vec;
	std::vector<coords::REAL3_VAR_IDENT*> REAL3_VAR_IDENT_vec;
	std::vector<coords::REAL4_VAR_IDENT*> REAL4_VAR_IDENT_vec;
	std::vector<coords::REALMATRIX_VAR_IDENT*> REALMATRIX_VAR_IDENT_vec;
	std::vector<coords::REAL1_LITERAL*> REAL1_LITERAL_vec;
	std::vector<coords::REAL3_LITERAL*> REAL3_LITERAL_vec;
	std::vector<coords::REAL4_LITERAL*> REAL4_LITERAL_vec;
	std::vector<coords::REALMATRIX_LITERAL*> REALMATRIX_LITERAL_vec;	std::vector<coords::SEQ_GLOBALSTMT*> SEQ_GLOBALSTMT_vec;
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
