#ifndef INTERPTODOMAIN_H
#define INTERPTODOMAIN_H

#include <iostream>
#include "Domain.h"

namespace interp
{
    class Space;
    class MeasurementSystem;
    class AxisOrientation;
    class Frame;
    class PROGRAM;
class GLOBALSTMT;
class STMT;
class FUNC_DECL;
class VOID_FUNC_DECL_STMT;
class MAIN_FUNC_DECL_STMT;
class WHILE;
class TRY;
class FOR;
class DECLARE;
class ASSIGN;
class REXPR;
class LEXPR;
class BOOL_EXPR;
class REALMATRIX4_EXPR;
class REAL4_EXPR;
class REAL3_EXPR;
class REAL3_LEXPR;
class REAL1_EXPR;
class BOOL_VAR_IDENT;
class REAL1_VAR_IDENT;
class REAL3_VAR_IDENT;
class REAL4_VAR_IDENT;
class REALMATRIX4_VAR_IDENT;
class REAL4_LITERAL;
class REAL3_LITERAL;
class REAL1_LITERAL;
class REALMATRIX4_LITERAL;
class SINK;
class BOOL_LITERAL;class SEQ_GLOBALSTMT;
class FUNC_DECL;
class COMPOUND_STMT;
class DECLARE;
class ASSIGN;
class REXPR;
class LEXPR;
class WHILE;
class FOR;
class TRY;
class MAIN_FUNC;
class VOID_FUNC;
class DECL_STMT;
class DECL_STMT;
class WHILE_BOOL_EXPR_STMT;
class TRY_STMT;
class FOR_BOOL_EXPR_STMT;
class DECL_REAL1_VAR_REAL1_EXPR;
class DECL_REAL3_VAR_REAL3_EXPR;
class DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR;
class DECL_REAL4_VAR_REAL4_EXPR;
class DECL_BOOL_VAR_BOOL_EXPR;
class DECL_REAL1_VAR;
class DECL_REAL3_VAR;
class DECL_REALMATRIX4_VAR;
class DECL_REAL4_VAR;
class DECL_BOOL_VAR;
class ASNR1_REAL1_VAR_REAL1_EXPR;
class ASNR3_REAL3_VAR_REAL3_EXPR;
class ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR;
class BOOL_EXPR;
class REAL3_EXPR;
class REAL1_EXPR;
class REALMATRIX4_EXPR;
class REAL4_EXPR;
class REAL3_LEXPR;
class REF_BOOL_VAR;
class BOOL_LITERAL;
class REF_REALMATRIX4_VAR;
class MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR;
class REALMATRIX4_LITERAL;
class REF_REAL4_VAR;
class ADD_REAL4_EXPR_REAL4_EXPR;
class MUL_REAL4_EXPR_REAL4_EXPR;
class REF_REAL3_VAR;
class ADD_REAL3_EXPR_REAL3_EXPR;
class LMUL_REAL1_EXPR_REAL3_EXPR;
class RMUL_REAL3_EXPR_REAL1_EXPR;
class TMUL_REALMATRIX4_EXPR_REAL3_EXPR;
class REAL3_LITERAL;
class LREF_REAL3_VAR;
class REF_REAL1_VAR;
class ADD_REAL1_EXPR_REAL1_EXPR;
class MUL_REAL1_EXPR_REAL1_EXPR;
class REAL1_LITERAL;
class IDENT;
class IDENT;
class IDENT;
class IDENT;
class IDENT;
class REAL4_EMPTY;
class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL3_EMPTY;
class REAL1_LIT;
class REALMATRIX4_EMPTY;
class REALMATRIX4_EMPTY2_REALMATRIX4_EXPR;
class R4R3_LIT_REAL4_EXPR_REAL3_EXPR;
class IGNORE;
class BOOL_LIT;
} // namespace

#ifndef INTERP_H
#include "Interp.h"
#endif

#include <unordered_map>

namespace interp2domain{

class InterpToDomain
{
    public:
	void putSpace(interp::Space* key, domain::Space* val);
	domain::Space* getSpace(interp::Space* c) const;
	interp::Space* getSpace(domain::Space* d) const;

	void putMeasurementSystem(interp::MeasurementSystem* key, domain::MeasurementSystem* val);
	domain::MeasurementSystem* getMeasurementSystem(interp::MeasurementSystem* c) const;
	interp::MeasurementSystem* getMeasurementSystem(domain::MeasurementSystem* d) const;

	void putAxisOrientation(interp::AxisOrientation* key, domain::AxisOrientation* val);
	domain::AxisOrientation* getAxisOrientation(interp::AxisOrientation* c) const;
	interp::AxisOrientation* getAxisOrientation(domain::AxisOrientation* d) const;

	void putFrame(interp::Frame* key, domain::Frame* val);
	domain::Frame* getFrame(interp::Frame* c) const;
	interp::Frame* getFrame(domain::Frame* d) const;

	domain::DomainObject* getPROGRAM(interp::PROGRAM* c) const;
	interp::PROGRAM* getPROGRAM(domain::DomainObject* d) const;
	
	void putSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* key, domain::DomainObject* val);
	domain::DomainObject* getSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* c) const;
	interp::SEQ_GLOBALSTMT* getSEQ_GLOBALSTMT(domain::DomainObject* d) const;
void eraseSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* key, domain::DomainObject* val);

	domain::DomainObject* getGLOBALSTMT(interp::GLOBALSTMT* c) const;
	interp::GLOBALSTMT* getGLOBALSTMT(domain::DomainObject* d) const;
	
	domain::DomainObject* getSTMT(interp::STMT* c) const;
	interp::STMT* getSTMT(domain::DomainObject* d) const;
	
	void putCOMPOUND_STMT(interp::COMPOUND_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getCOMPOUND_STMT(interp::COMPOUND_STMT* c) const;
	interp::COMPOUND_STMT* getCOMPOUND_STMT(domain::DomainObject* d) const;
void eraseCOMPOUND_STMT(interp::COMPOUND_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getFUNC_DECL(interp::FUNC_DECL* c) const;
	interp::FUNC_DECL* getFUNC_DECL(domain::DomainObject* d) const;
	
	void putVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* c) const;
	interp::VOID_FUNC_DECL_STMT* getVOID_FUNC_DECL_STMT(domain::DomainObject* d) const;
void eraseVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);

	void putMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* c) const;
	interp::MAIN_FUNC_DECL_STMT* getMAIN_FUNC_DECL_STMT(domain::DomainObject* d) const;
void eraseMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getWHILE(interp::WHILE* c) const;
	interp::WHILE* getWHILE(domain::DomainObject* d) const;
	
	void putWHILE_BOOL_EXPR_STMT(interp::WHILE_BOOL_EXPR_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getWHILE_BOOL_EXPR_STMT(interp::WHILE_BOOL_EXPR_STMT* c) const;
	interp::WHILE_BOOL_EXPR_STMT* getWHILE_BOOL_EXPR_STMT(domain::DomainObject* d) const;
void eraseWHILE_BOOL_EXPR_STMT(interp::WHILE_BOOL_EXPR_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getTRY(interp::TRY* c) const;
	interp::TRY* getTRY(domain::DomainObject* d) const;
	
	void putTRY_STMT(interp::TRY_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getTRY_STMT(interp::TRY_STMT* c) const;
	interp::TRY_STMT* getTRY_STMT(domain::DomainObject* d) const;
void eraseTRY_STMT(interp::TRY_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getFOR(interp::FOR* c) const;
	interp::FOR* getFOR(domain::DomainObject* d) const;
	
	void putFOR_BOOL_EXPR_STMT(interp::FOR_BOOL_EXPR_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getFOR_BOOL_EXPR_STMT(interp::FOR_BOOL_EXPR_STMT* c) const;
	interp::FOR_BOOL_EXPR_STMT* getFOR_BOOL_EXPR_STMT(domain::DomainObject* d) const;
void eraseFOR_BOOL_EXPR_STMT(interp::FOR_BOOL_EXPR_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getDECLARE(interp::DECLARE* c) const;
	interp::DECLARE* getDECLARE(domain::DomainObject* d) const;
	
	void putDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* c) const;
	interp::DECL_REAL1_VAR_REAL1_EXPR* getDECL_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* c) const;
	interp::DECL_REAL3_VAR_REAL3_EXPR* getDECL_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const;
	interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* c) const;
	interp::DECL_REAL4_VAR_REAL4_EXPR* getDECL_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);

	void putDECL_BOOL_VAR_BOOL_EXPR(interp::DECL_BOOL_VAR_BOOL_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_BOOL_VAR_BOOL_EXPR(interp::DECL_BOOL_VAR_BOOL_EXPR* c) const;
	interp::DECL_BOOL_VAR_BOOL_EXPR* getDECL_BOOL_VAR_BOOL_EXPR(domain::DomainObject* d) const;
void eraseDECL_BOOL_VAR_BOOL_EXPR(interp::DECL_BOOL_VAR_BOOL_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL1_VAR(interp::DECL_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL1_VAR(interp::DECL_REAL1_VAR* c) const;
	interp::DECL_REAL1_VAR* getDECL_REAL1_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL1_VAR(interp::DECL_REAL1_VAR* key, domain::DomainObject* val);

	void putDECL_REAL3_VAR(interp::DECL_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL3_VAR(interp::DECL_REAL3_VAR* c) const;
	interp::DECL_REAL3_VAR* getDECL_REAL3_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL3_VAR(interp::DECL_REAL3_VAR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX4_VAR(interp::DECL_REALMATRIX4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX4_VAR(interp::DECL_REALMATRIX4_VAR* c) const;
	interp::DECL_REALMATRIX4_VAR* getDECL_REALMATRIX4_VAR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX4_VAR(interp::DECL_REALMATRIX4_VAR* key, domain::DomainObject* val);

	void putDECL_REAL4_VAR(interp::DECL_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR(interp::DECL_REAL4_VAR* c) const;
	interp::DECL_REAL4_VAR* getDECL_REAL4_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR(interp::DECL_REAL4_VAR* key, domain::DomainObject* val);

	void putDECL_BOOL_VAR(interp::DECL_BOOL_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_BOOL_VAR(interp::DECL_BOOL_VAR* c) const;
	interp::DECL_BOOL_VAR* getDECL_BOOL_VAR(domain::DomainObject* d) const;
void eraseDECL_BOOL_VAR(interp::DECL_BOOL_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getASSIGN(interp::ASSIGN* c) const;
	interp::ASSIGN* getASSIGN(domain::DomainObject* d) const;
	
	void putASNR1_REAL1_VAR_REAL1_EXPR(interp::ASNR1_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASNR1_REAL1_VAR_REAL1_EXPR(interp::ASNR1_REAL1_VAR_REAL1_EXPR* c) const;
	interp::ASNR1_REAL1_VAR_REAL1_EXPR* getASNR1_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseASNR1_REAL1_VAR_REAL1_EXPR(interp::ASNR1_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);

	void putASNR3_REAL3_VAR_REAL3_EXPR(interp::ASNR3_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASNR3_REAL3_VAR_REAL3_EXPR(interp::ASNR3_REAL3_VAR_REAL3_EXPR* c) const;
	interp::ASNR3_REAL3_VAR_REAL3_EXPR* getASNR3_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseASNR3_REAL3_VAR_REAL3_EXPR(interp::ASNR3_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);

	void putASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const;
	interp::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* getASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREXPR(interp::REXPR* c) const;
	interp::REXPR* getREXPR(domain::DomainObject* d) const;
	
	domain::DomainObject* getLEXPR(interp::LEXPR* c) const;
	interp::LEXPR* getLEXPR(domain::DomainObject* d) const;
	
	domain::DomainObject* getBOOL_EXPR(interp::BOOL_EXPR* c) const;
	interp::BOOL_EXPR* getBOOL_EXPR(domain::DomainObject* d) const;
	
	void putREF_BOOL_VAR(interp::REF_BOOL_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_BOOL_VAR(interp::REF_BOOL_VAR* c) const;
	interp::REF_BOOL_VAR* getREF_BOOL_VAR(domain::DomainObject* d) const;
void eraseREF_BOOL_VAR(interp::REF_BOOL_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX4_EXPR(interp::REALMATRIX4_EXPR* c) const;
	interp::REALMATRIX4_EXPR* getREALMATRIX4_EXPR(domain::DomainObject* d) const;
	
	void putREF_REALMATRIX4_VAR(interp::REF_REALMATRIX4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REALMATRIX4_VAR(interp::REF_REALMATRIX4_VAR* c) const;
	interp::REF_REALMATRIX4_VAR* getREF_REALMATRIX4_VAR(domain::DomainObject* d) const;
void eraseREF_REALMATRIX4_VAR(interp::REF_REALMATRIX4_VAR* key, domain::DomainObject* val);

	void putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* c) const;
	interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_EXPR(interp::REAL4_EXPR* c) const;
	interp::REAL4_EXPR* getREAL4_EXPR(domain::DomainObject* d) const;
	
	void putREF_REAL4_VAR(interp::REF_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL4_VAR(interp::REF_REAL4_VAR* c) const;
	interp::REF_REAL4_VAR* getREF_REAL4_VAR(domain::DomainObject* d) const;
void eraseREF_REAL4_VAR(interp::REF_REAL4_VAR* key, domain::DomainObject* val);

	void putADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* c) const;
	interp::ADD_REAL4_EXPR_REAL4_EXPR* getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL4_EXPR_REAL4_EXPR(interp::MUL_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL4_EXPR_REAL4_EXPR(interp::MUL_REAL4_EXPR_REAL4_EXPR* c) const;
	interp::MUL_REAL4_EXPR_REAL4_EXPR* getMUL_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL4_EXPR_REAL4_EXPR(interp::MUL_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_EXPR(interp::REAL3_EXPR* c) const;
	interp::REAL3_EXPR* getREAL3_EXPR(domain::DomainObject* d) const;
	
	void putREF_REAL3_VAR(interp::REF_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL3_VAR(interp::REF_REAL3_VAR* c) const;
	interp::REF_REAL3_VAR* getREF_REAL3_VAR(domain::DomainObject* d) const;
void eraseREF_REAL3_VAR(interp::REF_REAL3_VAR* key, domain::DomainObject* val);

	void putADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* c) const;
	interp::ADD_REAL3_EXPR_REAL3_EXPR* getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* c) const;
	interp::LMUL_REAL1_EXPR_REAL3_EXPR* getLMUL_REAL1_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* c) const;
	interp::RMUL_REAL3_EXPR_REAL1_EXPR* getRMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* c) const;
	interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_LEXPR(interp::REAL3_LEXPR* c) const;
	interp::REAL3_LEXPR* getREAL3_LEXPR(domain::DomainObject* d) const;
	
	void putLREF_REAL3_VAR(interp::LREF_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getLREF_REAL3_VAR(interp::LREF_REAL3_VAR* c) const;
	interp::LREF_REAL3_VAR* getLREF_REAL3_VAR(domain::DomainObject* d) const;
void eraseLREF_REAL3_VAR(interp::LREF_REAL3_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_EXPR(interp::REAL1_EXPR* c) const;
	interp::REAL1_EXPR* getREAL1_EXPR(domain::DomainObject* d) const;
	
	void putREF_REAL1_VAR(interp::REF_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL1_VAR(interp::REF_REAL1_VAR* c) const;
	interp::REF_REAL1_VAR* getREF_REAL1_VAR(domain::DomainObject* d) const;
void eraseREF_REAL1_VAR(interp::REF_REAL1_VAR* key, domain::DomainObject* val);

	void putADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::ADD_REAL1_EXPR_REAL1_EXPR* getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::MUL_REAL1_EXPR_REAL1_EXPR* getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putBOOL_VAR_IDENT(interp::BOOL_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getBOOL_VAR_IDENT(interp::BOOL_VAR_IDENT* c) const;
	interp::BOOL_VAR_IDENT* getBOOL_VAR_IDENT(domain::DomainObject* d) const;
void eraseBOOL_VAR_IDENT(interp::BOOL_VAR_IDENT* key, domain::DomainObject* val);

	void putREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* c) const;
	interp::REAL1_VAR_IDENT* getREAL1_VAR_IDENT(domain::DomainObject* d) const;
void eraseREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* key, domain::DomainObject* val);

	void putREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* c) const;
	interp::REAL3_VAR_IDENT* getREAL3_VAR_IDENT(domain::DomainObject* d) const;
void eraseREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* key, domain::DomainObject* val);

	void putREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* c) const;
	interp::REAL4_VAR_IDENT* getREAL4_VAR_IDENT(domain::DomainObject* d) const;
void eraseREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* key, domain::DomainObject* val);

	void putREALMATRIX4_VAR_IDENT(interp::REALMATRIX4_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX4_VAR_IDENT(interp::REALMATRIX4_VAR_IDENT* c) const;
	interp::REALMATRIX4_VAR_IDENT* getREALMATRIX4_VAR_IDENT(domain::DomainObject* d) const;
void eraseREALMATRIX4_VAR_IDENT(interp::REALMATRIX4_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_LITERAL(interp::REAL4_LITERAL* c) const;
	interp::REAL4_LITERAL* getREAL4_LITERAL(domain::DomainObject* d) const;
	
	void putREAL4_EMPTY(interp::REAL4_EMPTY* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_EMPTY(interp::REAL4_EMPTY* c) const;
	interp::REAL4_EMPTY* getREAL4_EMPTY(domain::DomainObject* d) const;
void eraseREAL4_EMPTY(interp::REAL4_EMPTY* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_LITERAL(interp::REAL3_LITERAL* c) const;
	interp::REAL3_LITERAL* getREAL3_LITERAL(domain::DomainObject* d) const;
	
	void putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREAL3_EMPTY(interp::REAL3_EMPTY* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_EMPTY(interp::REAL3_EMPTY* c) const;
	interp::REAL3_EMPTY* getREAL3_EMPTY(domain::DomainObject* d) const;
void eraseREAL3_EMPTY(interp::REAL3_EMPTY* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_LITERAL(interp::REAL1_LITERAL* c) const;
	interp::REAL1_LITERAL* getREAL1_LITERAL(domain::DomainObject* d) const;
	
	void putREAL1_LIT(interp::REAL1_LIT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL1_LIT(interp::REAL1_LIT* c) const;
	interp::REAL1_LIT* getREAL1_LIT(domain::DomainObject* d) const;
void eraseREAL1_LIT(interp::REAL1_LIT* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX4_LITERAL(interp::REALMATRIX4_LITERAL* c) const;
	interp::REALMATRIX4_LITERAL* getREALMATRIX4_LITERAL(domain::DomainObject* d) const;
	
	void putREALMATRIX4_EMPTY(interp::REALMATRIX4_EMPTY* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX4_EMPTY(interp::REALMATRIX4_EMPTY* c) const;
	interp::REALMATRIX4_EMPTY* getREALMATRIX4_EMPTY(domain::DomainObject* d) const;
void eraseREALMATRIX4_EMPTY(interp::REALMATRIX4_EMPTY* key, domain::DomainObject* val);

	void putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* c) const;
	interp::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(interp::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	void putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* c) const;
	interp::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(interp::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getSINK(interp::SINK* c) const;
	interp::SINK* getSINK(domain::DomainObject* d) const;
	
	void putIGNORE(interp::IGNORE* key, domain::DomainObject* val);
	domain::DomainObject* getIGNORE(interp::IGNORE* c) const;
	interp::IGNORE* getIGNORE(domain::DomainObject* d) const;
void eraseIGNORE(interp::IGNORE* key, domain::DomainObject* val);

	domain::DomainObject* getBOOL_LITERAL(interp::BOOL_LITERAL* c) const;
	interp::BOOL_LITERAL* getBOOL_LITERAL(domain::DomainObject* d) const;
	
	void putBOOL_LIT(interp::BOOL_LIT* key, domain::DomainObject* val);
	domain::DomainObject* getBOOL_LIT(interp::BOOL_LIT* c) const;
	interp::BOOL_LIT* getBOOL_LIT(domain::DomainObject* d) const;
void eraseBOOL_LIT(interp::BOOL_LIT* key, domain::DomainObject* val);

private:

std::unordered_map<interp::Space*, domain::Space*> interp2dom_Spaces;

std::unordered_map<domain::Space*, interp::Space*> dom2interp_Spaces;

std::unordered_map<interp::MeasurementSystem*, domain::MeasurementSystem*> interp2dom_MeasurementSystems;

std::unordered_map<domain::MeasurementSystem*, interp::MeasurementSystem*> dom2interp_MeasurementSystems;

std::unordered_map<interp::AxisOrientation*, domain::AxisOrientation*> interp2dom_AxisOrientations;

std::unordered_map<domain::AxisOrientation*, interp::AxisOrientation*> dom2interp_AxisOrientations;

std::unordered_map<interp::Frame*, domain::Frame*> interp2dom_Frames;

std::unordered_map<domain::Frame*, interp::Frame*> dom2interp_Frames;

	std::unordered_map <interp::PROGRAM*,	domain::DomainObject*	> 	interp2dom_PROGRAM;
	std::unordered_map <domain::DomainObject*,	interp::PROGRAM*	> 	dom2interp_PROGRAM;

	std::unordered_map <interp::GLOBALSTMT*,	domain::DomainObject*	> 	interp2dom_GLOBALSTMT;
	std::unordered_map <domain::DomainObject*,	interp::GLOBALSTMT*	> 	dom2interp_GLOBALSTMT;

	std::unordered_map <interp::STMT*,	domain::DomainObject*	> 	interp2dom_STMT;
	std::unordered_map <domain::DomainObject*,	interp::STMT*	> 	dom2interp_STMT;

	std::unordered_map <interp::FUNC_DECL*,	domain::DomainObject*	> 	interp2dom_FUNC_DECL;
	std::unordered_map <domain::DomainObject*,	interp::FUNC_DECL*	> 	dom2interp_FUNC_DECL;

	std::unordered_map <interp::VOID_FUNC_DECL_STMT*,	domain::DomainObject*	> 	interp2dom_VOID_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	interp::VOID_FUNC_DECL_STMT*	> 	dom2interp_VOID_FUNC_DECL_STMT;

	std::unordered_map <interp::MAIN_FUNC_DECL_STMT*,	domain::DomainObject*	> 	interp2dom_MAIN_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	interp::MAIN_FUNC_DECL_STMT*	> 	dom2interp_MAIN_FUNC_DECL_STMT;

	std::unordered_map <interp::WHILE*,	domain::DomainObject*	> 	interp2dom_WHILE;
	std::unordered_map <domain::DomainObject*,	interp::WHILE*	> 	dom2interp_WHILE;

	std::unordered_map <interp::TRY*,	domain::DomainObject*	> 	interp2dom_TRY;
	std::unordered_map <domain::DomainObject*,	interp::TRY*	> 	dom2interp_TRY;

	std::unordered_map <interp::FOR*,	domain::DomainObject*	> 	interp2dom_FOR;
	std::unordered_map <domain::DomainObject*,	interp::FOR*	> 	dom2interp_FOR;

	std::unordered_map <interp::DECLARE*,	domain::DomainObject*	> 	interp2dom_DECLARE;
	std::unordered_map <domain::DomainObject*,	interp::DECLARE*	> 	dom2interp_DECLARE;

	std::unordered_map <interp::ASSIGN*,	domain::DomainObject*	> 	interp2dom_ASSIGN;
	std::unordered_map <domain::DomainObject*,	interp::ASSIGN*	> 	dom2interp_ASSIGN;

	std::unordered_map <interp::REXPR*,	domain::DomainObject*	> 	interp2dom_REXPR;
	std::unordered_map <domain::DomainObject*,	interp::REXPR*	> 	dom2interp_REXPR;

	std::unordered_map <interp::LEXPR*,	domain::DomainObject*	> 	interp2dom_LEXPR;
	std::unordered_map <domain::DomainObject*,	interp::LEXPR*	> 	dom2interp_LEXPR;

	std::unordered_map <interp::BOOL_EXPR*,	domain::DomainObject*	> 	interp2dom_BOOL_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::BOOL_EXPR*	> 	dom2interp_BOOL_EXPR;

	std::unordered_map <interp::REALMATRIX4_EXPR*,	domain::DomainObject*	> 	interp2dom_REALMATRIX4_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REALMATRIX4_EXPR*	> 	dom2interp_REALMATRIX4_EXPR;

	std::unordered_map <interp::REAL4_EXPR*,	domain::DomainObject*	> 	interp2dom_REAL4_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL4_EXPR*	> 	dom2interp_REAL4_EXPR;

	std::unordered_map <interp::REAL3_EXPR*,	domain::DomainObject*	> 	interp2dom_REAL3_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_EXPR*	> 	dom2interp_REAL3_EXPR;

	std::unordered_map <interp::REAL3_LEXPR*,	domain::DomainObject*	> 	interp2dom_REAL3_LEXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_LEXPR*	> 	dom2interp_REAL3_LEXPR;

	std::unordered_map <interp::REAL1_EXPR*,	domain::DomainObject*	> 	interp2dom_REAL1_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL1_EXPR*	> 	dom2interp_REAL1_EXPR;

	std::unordered_map <interp::BOOL_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_BOOL_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::BOOL_VAR_IDENT*	> 	dom2interp_BOOL_VAR_IDENT;

	std::unordered_map <interp::REAL1_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REAL1_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REAL1_VAR_IDENT*	> 	dom2interp_REAL1_VAR_IDENT;

	std::unordered_map <interp::REAL3_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REAL3_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_VAR_IDENT*	> 	dom2interp_REAL3_VAR_IDENT;

	std::unordered_map <interp::REAL4_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REAL4_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REAL4_VAR_IDENT*	> 	dom2interp_REAL4_VAR_IDENT;

	std::unordered_map <interp::REALMATRIX4_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REALMATRIX4_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REALMATRIX4_VAR_IDENT*	> 	dom2interp_REALMATRIX4_VAR_IDENT;

	std::unordered_map <interp::REAL4_LITERAL*,	domain::DomainObject*	> 	interp2dom_REAL4_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REAL4_LITERAL*	> 	dom2interp_REAL4_LITERAL;

	std::unordered_map <interp::REAL3_LITERAL*,	domain::DomainObject*	> 	interp2dom_REAL3_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_LITERAL*	> 	dom2interp_REAL3_LITERAL;

	std::unordered_map <interp::REAL1_LITERAL*,	domain::DomainObject*	> 	interp2dom_REAL1_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REAL1_LITERAL*	> 	dom2interp_REAL1_LITERAL;

	std::unordered_map <interp::REALMATRIX4_LITERAL*,	domain::DomainObject*	> 	interp2dom_REALMATRIX4_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REALMATRIX4_LITERAL*	> 	dom2interp_REALMATRIX4_LITERAL;

	std::unordered_map <interp::SINK*,	domain::DomainObject*	> 	interp2dom_SINK;
	std::unordered_map <domain::DomainObject*,	interp::SINK*	> 	dom2interp_SINK;

	std::unordered_map <interp::BOOL_LITERAL*,	domain::DomainObject*	> 	interp2dom_BOOL_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::BOOL_LITERAL*	> 	dom2interp_BOOL_LITERAL;
};

} // namespace

#endif