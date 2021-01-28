
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

	void mkWHILE_BOOL_EXPR_STMT(const ast::WHILE_BOOL_EXPR_STMT * ast ,ast::BOOL_EXPR* operand1,ast::STMT* operand2);
                    
	std::string toString_WHILEs();

	void mkTRY_STMT(const ast::TRY_STMT * ast ,ast::STMT* operand1);
                    
	std::string toString_TRYs();

	void mkDECL_REAL1_VAR_REAL1_EXPR(const ast::DECL_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkDECL_REAL3_VAR_REAL3_EXPR(const ast::DECL_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(const ast::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1,ast::REALMATRIX4_EXPR* operand2);
                    
	void mkDECL_REAL4_VAR_REAL4_EXPR(const ast::DECL_REAL4_VAR_REAL4_EXPR * ast ,ast::REAL4_VAR_IDENT* operand1,ast::REAL4_EXPR* operand2);
                    
	void mkDECL_BOOL_VAR_BOOL_EXPR(const ast::DECL_BOOL_VAR_BOOL_EXPR * ast ,ast::BOOL_VAR_IDENT* operand1,ast::BOOL_EXPR* operand2);
                    
	void mkDECL_REAL1_VAR(const ast::DECL_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1);
                    
	void mkDECL_REAL3_VAR(const ast::DECL_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1);
                    
	void mkDECL_REALMATRIX4_VAR(const ast::DECL_REALMATRIX4_VAR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1);
                    
	void mkDECL_REAL4_VAR(const ast::DECL_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1);
                    
	void mkDECL_BOOL_VAR(const ast::DECL_BOOL_VAR * ast ,ast::BOOL_VAR_IDENT* operand1);
                    
	std::string toString_DECLAREs();

	void mkASNR1_REAL1_VAR_REAL1_EXPR(const ast::ASNR1_REAL1_VAR_REAL1_EXPR * ast ,ast::REAL1_VAR_IDENT* operand1,ast::REAL1_EXPR* operand2);
                    
	void mkASNR3_REAL3_VAR_REAL3_EXPR(const ast::ASNR3_REAL3_VAR_REAL3_EXPR * ast ,ast::REAL3_VAR_IDENT* operand1,ast::REAL3_EXPR* operand2);
                    
	void mkASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(const ast::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1,ast::REALMATRIX4_EXPR* operand2);
                    
	std::string toString_ASSIGNs();

	std::string toString_REXPRs();

	std::string toString_LEXPRs();

	void mkREF_BOOL_VAR(const ast::REF_BOOL_VAR * ast ,ast::BOOL_VAR_IDENT* operand1,std::shared_ptr<bool> value0=nullptr);
                    
	std::string toString_BOOL_EXPRs();

	void mkREF_REALMATRIX4_VAR(const ast::REF_REALMATRIX4_VAR * ast ,ast::REALMATRIX4_VAR_IDENT* operand1);
                    
	void mkMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(const ast::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_EXPR* operand1,ast::REALMATRIX4_EXPR* operand2);
                    
	std::string toString_REALMATRIX4_EXPRs();

	void mkREF_REAL4_VAR(const ast::REF_REAL4_VAR * ast ,ast::REAL4_VAR_IDENT* operand1,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr,std::shared_ptr<float> value3=nullptr);
                    
	void mkADD_REAL4_EXPR_REAL4_EXPR(const ast::ADD_REAL4_EXPR_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL4_EXPR* operand2,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr,std::shared_ptr<float> value3=nullptr);
                    
	void mkMUL_REAL4_EXPR_REAL4_EXPR(const ast::MUL_REAL4_EXPR_REAL4_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL4_EXPR* operand2,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr,std::shared_ptr<float> value3=nullptr);
                    
	std::string toString_REAL4_EXPRs();

	void mkREF_REAL3_VAR(const ast::REF_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	void mkADD_REAL3_EXPR_REAL3_EXPR(const ast::ADD_REAL3_EXPR_REAL3_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL3_EXPR* operand2,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	void mkLMUL_REAL1_EXPR_REAL3_EXPR(const ast::LMUL_REAL1_EXPR_REAL3_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL3_EXPR* operand2,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	void mkRMUL_REAL3_EXPR_REAL1_EXPR(const ast::RMUL_REAL3_EXPR_REAL1_EXPR * ast ,ast::REAL3_EXPR* operand1,ast::REAL1_EXPR* operand2,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	void mkTMUL_REALMATRIX4_EXPR_REAL3_EXPR(const ast::TMUL_REALMATRIX4_EXPR_REAL3_EXPR * ast ,ast::REALMATRIX4_EXPR* operand1,ast::REAL3_EXPR* operand2,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	std::string toString_REAL3_EXPRs();

	void mkLREF_REAL3_VAR(const ast::LREF_REAL3_VAR * ast ,ast::REAL3_VAR_IDENT* operand1,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	std::string toString_REAL3_LEXPRs();

	void mkREF_REAL1_VAR(const ast::REF_REAL1_VAR * ast ,ast::REAL1_VAR_IDENT* operand1,std::shared_ptr<float> value0=nullptr);
                    
	void mkADD_REAL1_EXPR_REAL1_EXPR(const ast::ADD_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,std::shared_ptr<float> value0=nullptr);
                    
	void mkMUL_REAL1_EXPR_REAL1_EXPR(const ast::MUL_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,std::shared_ptr<float> value0=nullptr);
                    
	std::string toString_REAL1_EXPRs();

	void mkBOOL_VAR_IDENT(const ast::BOOL_VAR_IDENT * ast ,std::shared_ptr<float> value0=nullptr);
                    
	std::string toString_BOOL_VAR_IDENTs();

	void mkREAL1_VAR_IDENT(const ast::REAL1_VAR_IDENT * ast ,std::shared_ptr<float> value0=nullptr);
                    
	std::string toString_REAL1_VAR_IDENTs();

	void mkREAL3_VAR_IDENT(const ast::REAL3_VAR_IDENT * ast ,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	std::string toString_REAL3_VAR_IDENTs();

	void mkREAL4_VAR_IDENT(const ast::REAL4_VAR_IDENT * ast ,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr,std::shared_ptr<float> value3=nullptr);
                    
	std::string toString_REAL4_VAR_IDENTs();

	void mkREALMATRIX4_VAR_IDENT(const ast::REALMATRIX4_VAR_IDENT * ast );
                    
	std::string toString_REALMATRIX4_VAR_IDENTs();

	void mkREAL4_EMPTY(const ast::REAL4_EMPTY * ast ,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr,std::shared_ptr<float> value3=nullptr);
                    
	std::string toString_REAL4_LITERALs();

	void mkREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(const ast::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR * ast ,ast::REAL1_EXPR* operand1,ast::REAL1_EXPR* operand2,ast::REAL1_EXPR* operand3,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	void mkREAL3_EMPTY(const ast::REAL3_EMPTY * ast ,std::shared_ptr<float> value0=nullptr,std::shared_ptr<float> value1=nullptr,std::shared_ptr<float> value2=nullptr);
                    
	std::string toString_REAL3_LITERALs();

	void mkREAL1_LIT(const ast::REAL1_LIT * ast ,std::shared_ptr<float> value0=nullptr);
                    
	std::string toString_REAL1_LITERALs();

	void mkREALMATRIX4_EMPTY(const ast::REALMATRIX4_EMPTY * ast );
                    
	void mkREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(const ast::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR * ast ,ast::REALMATRIX4_EXPR* operand1);
                    
	void mkR4R3_LIT_REAL4_EXPR_REAL3_EXPR(const ast::R4R3_LIT_REAL4_EXPR_REAL3_EXPR * ast ,ast::REAL4_EXPR* operand1,ast::REAL3_EXPR* operand2);
                    
	std::string toString_REALMATRIX4_LITERALs();

	void mkIGNORE(const ast::IGNORE * ast );
                    
	std::string toString_SINKs();

	void mkBOOL_LIT(const ast::BOOL_LIT * ast ,std::shared_ptr<bool> value0=nullptr);
                    
	std::string toString_BOOL_LITERALs();

	std::string toString_Spaces();
	std::vector<interp::Space*> getSpaceInterps();
	std::vector<std::string> getSpaceNames();
	std::vector<interp::MeasurementSystem*> getMSInterps();std::vector<std::string> getMSNames();
	std::vector<interp::AxisOrientation*> getAxisInterps();std::vector<std::string> getAxisNames();
	std::vector<interp::Frame*> getFrameInterps();
	std::vector<std::string> getFrameNames();
	    void buildDefaultSpaces();

    void buildSpace();
    void buildFrame();

    void buildMeasurementSystem();
    void printMeasurementSystems();

    void buildAxisOrientation();
    void printAxisOrientations();

    //void setAll_Spaces();
    void printSpaces();
    void printFrames();
    void mkVarTable();//make a printable, indexed table of variables that can have their types assigned by a user or oracle
    void printVarTable();//print the indexed variable table for the user
    void updateVarTable();//while loop where user can select a variable by index and provide a physical type for that variable
    void printChoices();//to replay annotation sessions
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
	std::vector<coords::MAIN_FUNC_DECL_STMT*> MAIN_FUNC_DECL_STMT_vec;
	std::vector<coords::WHILE*> WHILE_vec;
	std::vector<coords::TRY*> TRY_vec;
	std::vector<coords::DECLARE*> DECLARE_vec;
	std::vector<coords::ASSIGN*> ASSIGN_vec;
	std::vector<coords::REXPR*> REXPR_vec;
	std::vector<coords::LEXPR*> LEXPR_vec;
	std::vector<coords::BOOL_EXPR*> BOOL_EXPR_vec;
	std::vector<coords::REALMATRIX4_EXPR*> REALMATRIX4_EXPR_vec;
	std::vector<coords::REAL4_EXPR*> REAL4_EXPR_vec;
	std::vector<coords::REAL3_EXPR*> REAL3_EXPR_vec;
	std::vector<coords::REAL3_LEXPR*> REAL3_LEXPR_vec;
	std::vector<coords::REAL1_EXPR*> REAL1_EXPR_vec;
	std::vector<coords::BOOL_VAR_IDENT*> BOOL_VAR_IDENT_vec;
	std::vector<coords::REAL1_VAR_IDENT*> REAL1_VAR_IDENT_vec;
	std::vector<coords::REAL3_VAR_IDENT*> REAL3_VAR_IDENT_vec;
	std::vector<coords::REAL4_VAR_IDENT*> REAL4_VAR_IDENT_vec;
	std::vector<coords::REALMATRIX4_VAR_IDENT*> REALMATRIX4_VAR_IDENT_vec;
	std::vector<coords::REAL4_LITERAL*> REAL4_LITERAL_vec;
	std::vector<coords::REAL3_LITERAL*> REAL3_LITERAL_vec;
	std::vector<coords::REAL1_LITERAL*> REAL1_LITERAL_vec;
	std::vector<coords::REALMATRIX4_LITERAL*> REALMATRIX4_LITERAL_vec;
	std::vector<coords::SINK*> SINK_vec;
	std::vector<coords::BOOL_LITERAL*> BOOL_LITERAL_vec;	std::vector<coords::SEQ_GLOBALSTMT*> SEQ_GLOBALSTMT_vec;
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
