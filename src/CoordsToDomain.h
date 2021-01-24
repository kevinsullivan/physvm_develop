
#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include <unordered_map>

/*
	When putting, we know precise subclass, so we don't include
	putters for Expr and Vector super-classes. When getting, we 
	generally don't know, so we can return superclass pointers.
*/

/*
We currently require client to create domain nodes, which we 
then map to and from the given coordinates. From coordinates 
is currently implement as unordered map. From domain object is
currently implemented as domain object method. This enables us
to return precisely typed objects without having to maintain a
lot of separate mapping tables.
*/

namespace coords2domain{

class CoordsToDomain
{
public:


	domain::DomainObject* getPROGRAM(coords::PROGRAM* c) const;
	coords::PROGRAM* getPROGRAM(domain::DomainObject* d) const;

	void putSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* key, domain::DomainObject* val);
	domain::DomainObject* getSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c) const;
	coords::SEQ_GLOBALSTMT* getSEQ_GLOBALSTMT(domain::DomainObject* d) const;
void eraseSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* key, domain::DomainObject* val);

	domain::DomainObject* getGLOBALSTMT(coords::GLOBALSTMT* c) const;
	coords::GLOBALSTMT* getGLOBALSTMT(domain::DomainObject* d) const;

	domain::DomainObject* getSTMT(coords::STMT* c) const;
	coords::STMT* getSTMT(domain::DomainObject* d) const;

	void putCOMPOUND_STMT(coords::COMPOUND_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getCOMPOUND_STMT(coords::COMPOUND_STMT* c) const;
	coords::COMPOUND_STMT* getCOMPOUND_STMT(domain::DomainObject* d) const;
void eraseCOMPOUND_STMT(coords::COMPOUND_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getFUNC_DECL(coords::FUNC_DECL* c) const;
	coords::FUNC_DECL* getFUNC_DECL(domain::DomainObject* d) const;

	domain::DomainObject* getVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c) const;
	coords::VOID_FUNC_DECL_STMT* getVOID_FUNC_DECL_STMT(domain::DomainObject* d) const;

	void putVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);
void eraseVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c) const;
	coords::MAIN_FUNC_DECL_STMT* getMAIN_FUNC_DECL_STMT(domain::DomainObject* d) const;

	void putMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);
void eraseMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getWHILE(coords::WHILE* c) const;
	coords::WHILE* getWHILE(domain::DomainObject* d) const;

	void putWHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getWHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* c) const;
	coords::WHILE_BOOL_EXPR_STMT* getWHILE_BOOL_EXPR_STMT(domain::DomainObject* d) const;
void eraseWHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getTRY(coords::TRY* c) const;
	coords::TRY* getTRY(domain::DomainObject* d) const;

	void putTRY_STMT(coords::TRY_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getTRY_STMT(coords::TRY_STMT* c) const;
	coords::TRY_STMT* getTRY_STMT(domain::DomainObject* d) const;
void eraseTRY_STMT(coords::TRY_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getDECLARE(coords::DECLARE* c) const;
	coords::DECLARE* getDECLARE(domain::DomainObject* d) const;

	void putDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c) const;
	coords::DECL_REAL1_VAR_REAL1_EXPR* getDECL_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c) const;
	coords::DECL_REAL3_VAR_REAL3_EXPR* getDECL_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const;
	coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c) const;
	coords::DECL_REAL4_VAR_REAL4_EXPR* getDECL_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);

	void putDECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* c) const;
	coords::DECL_BOOL_VAR_BOOL_EXPR* getDECL_BOOL_VAR_BOOL_EXPR(domain::DomainObject* d) const;
void eraseDECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL1_VAR(coords::DECL_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c) const;
	coords::DECL_REAL1_VAR* getDECL_REAL1_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL1_VAR(coords::DECL_REAL1_VAR* key, domain::DomainObject* val);

	void putDECL_REAL3_VAR(coords::DECL_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c) const;
	coords::DECL_REAL3_VAR* getDECL_REAL3_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL3_VAR(coords::DECL_REAL3_VAR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* c) const;
	coords::DECL_REALMATRIX4_VAR* getDECL_REALMATRIX4_VAR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* key, domain::DomainObject* val);

	void putDECL_REAL4_VAR(coords::DECL_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c) const;
	coords::DECL_REAL4_VAR* getDECL_REAL4_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR(coords::DECL_REAL4_VAR* key, domain::DomainObject* val);

	void putDECL_BOOL_VAR(coords::DECL_BOOL_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_BOOL_VAR(coords::DECL_BOOL_VAR* c) const;
	coords::DECL_BOOL_VAR* getDECL_BOOL_VAR(domain::DomainObject* d) const;
void eraseDECL_BOOL_VAR(coords::DECL_BOOL_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getASSIGN(coords::ASSIGN* c) const;
	coords::ASSIGN* getASSIGN(domain::DomainObject* d) const;

	void putASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* c) const;
	coords::ASNR1_REAL1_VAR_REAL1_EXPR* getASNR1_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);

	void putASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* c) const;
	coords::ASNR3_REAL3_VAR_REAL3_EXPR* getASNR3_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);

	void putASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const;
	coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* getASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREXPR(coords::REXPR* c) const;
	coords::REXPR* getREXPR(domain::DomainObject* d) const;

	domain::DomainObject* getLEXPR(coords::LEXPR* c) const;
	coords::LEXPR* getLEXPR(domain::DomainObject* d) const;

	domain::DomainObject* getBOOL_EXPR(coords::BOOL_EXPR* c) const;
	coords::BOOL_EXPR* getBOOL_EXPR(domain::DomainObject* d) const;

	void putREF_BOOL_VAR(coords::REF_BOOL_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_BOOL_VAR(coords::REF_BOOL_VAR* c) const;
	coords::REF_BOOL_VAR* getREF_BOOL_VAR(domain::DomainObject* d) const;
void eraseREF_BOOL_VAR(coords::REF_BOOL_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX4_EXPR(coords::REALMATRIX4_EXPR* c) const;
	coords::REALMATRIX4_EXPR* getREALMATRIX4_EXPR(domain::DomainObject* d) const;

	void putREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* c) const;
	coords::REF_REALMATRIX4_VAR* getREF_REALMATRIX4_VAR(domain::DomainObject* d) const;
void eraseREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* key, domain::DomainObject* val);

	void putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* c) const;
	coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_EXPR(coords::REAL4_EXPR* c) const;
	coords::REAL4_EXPR* getREAL4_EXPR(domain::DomainObject* d) const;

	void putREF_REAL4_VAR(coords::REF_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL4_VAR(coords::REF_REAL4_VAR* c) const;
	coords::REF_REAL4_VAR* getREF_REAL4_VAR(domain::DomainObject* d) const;
void eraseREF_REAL4_VAR(coords::REF_REAL4_VAR* key, domain::DomainObject* val);

	void putADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c) const;
	coords::ADD_REAL4_EXPR_REAL4_EXPR* getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* c) const;
	coords::MUL_REAL4_EXPR_REAL4_EXPR* getMUL_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_EXPR(coords::REAL3_EXPR* c) const;
	coords::REAL3_EXPR* getREAL3_EXPR(domain::DomainObject* d) const;

	void putREF_REAL3_VAR(coords::REF_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const;
	coords::REF_REAL3_VAR* getREF_REAL3_VAR(domain::DomainObject* d) const;
void eraseREF_REAL3_VAR(coords::REF_REAL3_VAR* key, domain::DomainObject* val);

	void putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const;
	coords::ADD_REAL3_EXPR_REAL3_EXPR* getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c) const;
	coords::LMUL_REAL1_EXPR_REAL3_EXPR* getLMUL_REAL1_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c) const;
	coords::RMUL_REAL3_EXPR_REAL1_EXPR* getRMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* c) const;
	coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_LEXPR(coords::REAL3_LEXPR* c) const;
	coords::REAL3_LEXPR* getREAL3_LEXPR(domain::DomainObject* d) const;

	void putLREF_REAL3_VAR(coords::LREF_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c) const;
	coords::LREF_REAL3_VAR* getLREF_REAL3_VAR(domain::DomainObject* d) const;
void eraseLREF_REAL3_VAR(coords::LREF_REAL3_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_EXPR(coords::REAL1_EXPR* c) const;
	coords::REAL1_EXPR* getREAL1_EXPR(domain::DomainObject* d) const;

	void putREF_REAL1_VAR(coords::REF_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const;
	coords::REF_REAL1_VAR* getREF_REAL1_VAR(domain::DomainObject* d) const;
void eraseREF_REAL1_VAR(coords::REF_REAL1_VAR* key, domain::DomainObject* val);

	void putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::ADD_REAL1_EXPR_REAL1_EXPR* getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::MUL_REAL1_EXPR_REAL1_EXPR* getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* c) const;
	coords::BOOL_VAR_IDENT* getBOOL_VAR_IDENT(domain::DomainObject* d) const;

	void putBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* key, domain::DomainObject* val);
void eraseBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c) const;
	coords::REAL1_VAR_IDENT* getREAL1_VAR_IDENT(domain::DomainObject* d) const;

	void putREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* key, domain::DomainObject* val);
void eraseREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c) const;
	coords::REAL3_VAR_IDENT* getREAL3_VAR_IDENT(domain::DomainObject* d) const;

	void putREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* key, domain::DomainObject* val);
void eraseREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c) const;
	coords::REAL4_VAR_IDENT* getREAL4_VAR_IDENT(domain::DomainObject* d) const;

	void putREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* key, domain::DomainObject* val);
void eraseREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* c) const;
	coords::REALMATRIX4_VAR_IDENT* getREALMATRIX4_VAR_IDENT(domain::DomainObject* d) const;

	void putREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* key, domain::DomainObject* val);
void eraseREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_LITERAL(coords::REAL4_LITERAL* c) const;
	coords::REAL4_LITERAL* getREAL4_LITERAL(domain::DomainObject* d) const;

	void putREAL4_EMPTY(coords::REAL4_EMPTY* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_EMPTY(coords::REAL4_EMPTY* c) const;
	coords::REAL4_EMPTY* getREAL4_EMPTY(domain::DomainObject* d) const;
void eraseREAL4_EMPTY(coords::REAL4_EMPTY* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_LITERAL(coords::REAL3_LITERAL* c) const;
	coords::REAL3_LITERAL* getREAL3_LITERAL(domain::DomainObject* d) const;

	void putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREAL3_EMPTY(coords::REAL3_EMPTY* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_EMPTY(coords::REAL3_EMPTY* c) const;
	coords::REAL3_EMPTY* getREAL3_EMPTY(domain::DomainObject* d) const;
void eraseREAL3_EMPTY(coords::REAL3_EMPTY* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_LITERAL(coords::REAL1_LITERAL* c) const;
	coords::REAL1_LITERAL* getREAL1_LITERAL(domain::DomainObject* d) const;

	void putREAL1_LIT(coords::REAL1_LIT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL1_LIT(coords::REAL1_LIT* c) const;
	coords::REAL1_LIT* getREAL1_LIT(domain::DomainObject* d) const;
void eraseREAL1_LIT(coords::REAL1_LIT* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX4_LITERAL(coords::REALMATRIX4_LITERAL* c) const;
	coords::REALMATRIX4_LITERAL* getREALMATRIX4_LITERAL(domain::DomainObject* d) const;

	void putREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* c) const;
	coords::REALMATRIX4_EMPTY* getREALMATRIX4_EMPTY(domain::DomainObject* d) const;
void eraseREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* key, domain::DomainObject* val);

	void putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* c) const;
	coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(domain::DomainObject* d) const;
void eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* key, domain::DomainObject* val);

	void putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* c) const;
	coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	domain::DomainObject* getSINK(coords::SINK* c) const;
	coords::SINK* getSINK(domain::DomainObject* d) const;

	void putIGNORE(coords::IGNORE* key, domain::DomainObject* val);
	domain::DomainObject* getIGNORE(coords::IGNORE* c) const;
	coords::IGNORE* getIGNORE(domain::DomainObject* d) const;
void eraseIGNORE(coords::IGNORE* key, domain::DomainObject* val);

	domain::DomainObject* getBOOL_LITERAL(coords::BOOL_LITERAL* c) const;
	coords::BOOL_LITERAL* getBOOL_LITERAL(domain::DomainObject* d) const;

	void putBOOL_LIT(coords::BOOL_LIT* key, domain::DomainObject* val);
	domain::DomainObject* getBOOL_LIT(coords::BOOL_LIT* c) const;
	coords::BOOL_LIT* getBOOL_LIT(domain::DomainObject* d) const;
void eraseBOOL_LIT(coords::BOOL_LIT* key, domain::DomainObject* val);

private:

	std::unordered_map <coords::PROGRAM*,	domain::DomainObject*	> 	coords2dom_PROGRAM;
	std::unordered_map <domain::DomainObject*,	coords::PROGRAM*	> 	dom2coords_PROGRAM;

	std::unordered_map <coords::GLOBALSTMT*,	domain::DomainObject*	> 	coords2dom_GLOBALSTMT;
	std::unordered_map <domain::DomainObject*,	coords::GLOBALSTMT*	> 	dom2coords_GLOBALSTMT;

	std::unordered_map <coords::STMT*,	domain::DomainObject*	> 	coords2dom_STMT;
	std::unordered_map <domain::DomainObject*,	coords::STMT*	> 	dom2coords_STMT;

	std::unordered_map <coords::FUNC_DECL*,	domain::DomainObject*	> 	coords2dom_FUNC_DECL;
	std::unordered_map <domain::DomainObject*,	coords::FUNC_DECL*	> 	dom2coords_FUNC_DECL;

	std::unordered_map <coords::VOID_FUNC_DECL_STMT*,	domain::DomainObject*	> 	coords2dom_VOID_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	coords::VOID_FUNC_DECL_STMT*	> 	dom2coords_VOID_FUNC_DECL_STMT;

	std::unordered_map <coords::MAIN_FUNC_DECL_STMT*,	domain::DomainObject*	> 	coords2dom_MAIN_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	coords::MAIN_FUNC_DECL_STMT*	> 	dom2coords_MAIN_FUNC_DECL_STMT;

	std::unordered_map <coords::WHILE*,	domain::DomainObject*	> 	coords2dom_WHILE;
	std::unordered_map <domain::DomainObject*,	coords::WHILE*	> 	dom2coords_WHILE;

	std::unordered_map <coords::TRY*,	domain::DomainObject*	> 	coords2dom_TRY;
	std::unordered_map <domain::DomainObject*,	coords::TRY*	> 	dom2coords_TRY;

	std::unordered_map <coords::DECLARE*,	domain::DomainObject*	> 	coords2dom_DECLARE;
	std::unordered_map <domain::DomainObject*,	coords::DECLARE*	> 	dom2coords_DECLARE;

	std::unordered_map <coords::ASSIGN*,	domain::DomainObject*	> 	coords2dom_ASSIGN;
	std::unordered_map <domain::DomainObject*,	coords::ASSIGN*	> 	dom2coords_ASSIGN;

	std::unordered_map <coords::REXPR*,	domain::DomainObject*	> 	coords2dom_REXPR;
	std::unordered_map <domain::DomainObject*,	coords::REXPR*	> 	dom2coords_REXPR;

	std::unordered_map <coords::LEXPR*,	domain::DomainObject*	> 	coords2dom_LEXPR;
	std::unordered_map <domain::DomainObject*,	coords::LEXPR*	> 	dom2coords_LEXPR;

	std::unordered_map <coords::BOOL_EXPR*,	domain::DomainObject*	> 	coords2dom_BOOL_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::BOOL_EXPR*	> 	dom2coords_BOOL_EXPR;

	std::unordered_map <coords::REALMATRIX4_EXPR*,	domain::DomainObject*	> 	coords2dom_REALMATRIX4_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REALMATRIX4_EXPR*	> 	dom2coords_REALMATRIX4_EXPR;

	std::unordered_map <coords::REAL4_EXPR*,	domain::DomainObject*	> 	coords2dom_REAL4_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL4_EXPR*	> 	dom2coords_REAL4_EXPR;

	std::unordered_map <coords::REAL3_EXPR*,	domain::DomainObject*	> 	coords2dom_REAL3_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_EXPR*	> 	dom2coords_REAL3_EXPR;

	std::unordered_map <coords::REAL3_LEXPR*,	domain::DomainObject*	> 	coords2dom_REAL3_LEXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_LEXPR*	> 	dom2coords_REAL3_LEXPR;

	std::unordered_map <coords::REAL1_EXPR*,	domain::DomainObject*	> 	coords2dom_REAL1_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL1_EXPR*	> 	dom2coords_REAL1_EXPR;

	std::unordered_map <coords::BOOL_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_BOOL_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::BOOL_VAR_IDENT*	> 	dom2coords_BOOL_VAR_IDENT;

	std::unordered_map <coords::REAL1_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REAL1_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REAL1_VAR_IDENT*	> 	dom2coords_REAL1_VAR_IDENT;

	std::unordered_map <coords::REAL3_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REAL3_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_VAR_IDENT*	> 	dom2coords_REAL3_VAR_IDENT;

	std::unordered_map <coords::REAL4_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REAL4_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REAL4_VAR_IDENT*	> 	dom2coords_REAL4_VAR_IDENT;

	std::unordered_map <coords::REALMATRIX4_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REALMATRIX4_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REALMATRIX4_VAR_IDENT*	> 	dom2coords_REALMATRIX4_VAR_IDENT;

	std::unordered_map <coords::REAL4_LITERAL*,	domain::DomainObject*	> 	coords2dom_REAL4_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REAL4_LITERAL*	> 	dom2coords_REAL4_LITERAL;

	std::unordered_map <coords::REAL3_LITERAL*,	domain::DomainObject*	> 	coords2dom_REAL3_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_LITERAL*	> 	dom2coords_REAL3_LITERAL;

	std::unordered_map <coords::REAL1_LITERAL*,	domain::DomainObject*	> 	coords2dom_REAL1_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REAL1_LITERAL*	> 	dom2coords_REAL1_LITERAL;

	std::unordered_map <coords::REALMATRIX4_LITERAL*,	domain::DomainObject*	> 	coords2dom_REALMATRIX4_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REALMATRIX4_LITERAL*	> 	dom2coords_REALMATRIX4_LITERAL;

	std::unordered_map <coords::SINK*,	domain::DomainObject*	> 	coords2dom_SINK;
	std::unordered_map <domain::DomainObject*,	coords::SINK*	> 	dom2coords_SINK;

	std::unordered_map <coords::BOOL_LITERAL*,	domain::DomainObject*	> 	coords2dom_BOOL_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::BOOL_LITERAL*	> 	dom2coords_BOOL_LITERAL;
};

} // namespace

#endif