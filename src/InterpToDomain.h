#ifndef INTERPTODOMAIN_H
#define INTERPTODOMAIN_H

#include <iostream>
#include "Domain.h"
#include "Interp.h"

#include <unordered_map>

namespace interp2domain{

class InterpToDomain
{
    public:
	void putSpace(interp::Space* key, domain::Space* val);
	domain::Space* getSpace(interp::Space* c) const;
	interp::Space* getSpace(domain::Space* d) const;

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
	
	void putMAIN_STMT(interp::MAIN_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getMAIN_STMT(interp::MAIN_STMT* c) const;
	interp::MAIN_STMT* getMAIN_STMT(domain::DomainObject* d) const;
void eraseMAIN_STMT(interp::MAIN_STMT* key, domain::DomainObject* val);

	void putFUNCTION_STMT(interp::FUNCTION_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getFUNCTION_STMT(interp::FUNCTION_STMT* c) const;
	interp::FUNCTION_STMT* getFUNCTION_STMT(domain::DomainObject* d) const;
void eraseFUNCTION_STMT(interp::FUNCTION_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getSTMT(interp::STMT* c) const;
	interp::STMT* getSTMT(domain::DomainObject* d) const;
	
	void putCOMPOUND_STMT(interp::COMPOUND_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getCOMPOUND_STMT(interp::COMPOUND_STMT* c) const;
	interp::COMPOUND_STMT* getCOMPOUND_STMT(domain::DomainObject* d) const;
void eraseCOMPOUND_STMT(interp::COMPOUND_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getIFCOND(interp::IFCOND* c) const;
	interp::IFCOND* getIFCOND(domain::DomainObject* d) const;
	
	void putIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* c) const;
	interp::IFTHEN_EXPR_STMT* getIFTHEN_EXPR_STMT(domain::DomainObject* d) const;
void eraseIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* key, domain::DomainObject* val);

	void putIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* key, domain::DomainObject* val);
	domain::DomainObject* getIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* c) const;
	interp::IFTHENELSEIF_EXPR_STMT_IFCOND* getIFTHENELSEIF_EXPR_STMT_IFCOND(domain::DomainObject* d) const;
void eraseIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* key, domain::DomainObject* val);

	void putIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* c) const;
	interp::IFTHENELSE_EXPR_STMT_STMT* getIFTHENELSE_EXPR_STMT_STMT(domain::DomainObject* d) const;
void eraseIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getEXPR(interp::EXPR* c) const;
	interp::EXPR* getEXPR(domain::DomainObject* d) const;
	
	domain::DomainObject* getASSIGNMENT(interp::ASSIGNMENT* c) const;
	interp::ASSIGNMENT* getASSIGNMENT(domain::DomainObject* d) const;
	
	void putASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* c) const;
	interp::ASSIGN_REAL1_VAR_REAL1_EXPR* getASSIGN_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);

	void putASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* c) const;
	interp::ASSIGN_REAL3_VAR_REAL3_EXPR* getASSIGN_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);

	void putASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* c) const;
	interp::ASSIGN_REAL4_VAR_REAL4_EXPR* getASSIGN_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);

	void putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c) const;
	interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);

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

	void putDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* c) const;
	interp::DECL_REAL4_VAR_REAL4_EXPR* getDECL_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c) const;
	interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL1_VAR(interp::DECL_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL1_VAR(interp::DECL_REAL1_VAR* c) const;
	interp::DECL_REAL1_VAR* getDECL_REAL1_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL1_VAR(interp::DECL_REAL1_VAR* key, domain::DomainObject* val);

	void putDECL_REAL3_VAR(interp::DECL_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL3_VAR(interp::DECL_REAL3_VAR* c) const;
	interp::DECL_REAL3_VAR* getDECL_REAL3_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL3_VAR(interp::DECL_REAL3_VAR* key, domain::DomainObject* val);

	void putDECL_REAL4_VAR(interp::DECL_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR(interp::DECL_REAL4_VAR* c) const;
	interp::DECL_REAL4_VAR* getDECL_REAL4_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR(interp::DECL_REAL4_VAR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* c) const;
	interp::DECL_REALMATRIX_VAR* getDECL_REALMATRIX_VAR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_EXPR(interp::REAL1_EXPR* c) const;
	interp::REAL1_EXPR* getREAL1_EXPR(domain::DomainObject* d) const;
	
	void putPAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* c) const;
	interp::PAREN_REAL1_EXPR* getPAREN_REAL1_EXPR(domain::DomainObject* d) const;
void erasePAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* key, domain::DomainObject* val);

	void putINV_REAL1_EXPR(interp::INV_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getINV_REAL1_EXPR(interp::INV_REAL1_EXPR* c) const;
	interp::INV_REAL1_EXPR* getINV_REAL1_EXPR(domain::DomainObject* d) const;
void eraseINV_REAL1_EXPR(interp::INV_REAL1_EXPR* key, domain::DomainObject* val);

	void putNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* c) const;
	interp::NEG_REAL1_EXPR* getNEG_REAL1_EXPR(domain::DomainObject* d) const;
void eraseNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* key, domain::DomainObject* val);

	void putADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::ADD_REAL1_EXPR_REAL1_EXPR* getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::SUB_REAL1_EXPR_REAL1_EXPR* getSUB_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::MUL_REAL1_EXPR_REAL1_EXPR* getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::DIV_REAL1_EXPR_REAL1_EXPR* getDIV_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREF_REAL1_VAR(interp::REF_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL1_VAR(interp::REF_REAL1_VAR* c) const;
	interp::REF_REAL1_VAR* getREF_REAL1_VAR(domain::DomainObject* d) const;
void eraseREF_REAL1_VAR(interp::REF_REAL1_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_EXPR(interp::REAL3_EXPR* c) const;
	interp::REAL3_EXPR* getREAL3_EXPR(domain::DomainObject* d) const;
	
	void putPAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* c) const;
	interp::PAREN_REAL3_EXPR* getPAREN_REAL3_EXPR(domain::DomainObject* d) const;
void erasePAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* key, domain::DomainObject* val);

	void putADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* c) const;
	interp::ADD_REAL3_EXPR_REAL3_EXPR* getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* c) const;
	interp::SUB_REAL3_EXPR_REAL3_EXPR* getSUB_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putINV_REAL3_EXPR(interp::INV_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getINV_REAL3_EXPR(interp::INV_REAL3_EXPR* c) const;
	interp::INV_REAL3_EXPR* getINV_REAL3_EXPR(domain::DomainObject* d) const;
void eraseINV_REAL3_EXPR(interp::INV_REAL3_EXPR* key, domain::DomainObject* val);

	void putNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* c) const;
	interp::NEG_REAL3_EXPR* getNEG_REAL3_EXPR(domain::DomainObject* d) const;
void eraseNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* c) const;
	interp::MUL_REAL3_EXPR_REAL1_EXPR* getMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* c) const;
	interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* getMUL_REALMATRIX_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* c) const;
	interp::DIV_REAL3_EXPR_REAL1_EXPR* getDIV_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREF_REAL3_VAR(interp::REF_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL3_VAR(interp::REF_REAL3_VAR* c) const;
	interp::REF_REAL3_VAR* getREF_REAL3_VAR(domain::DomainObject* d) const;
void eraseREF_REAL3_VAR(interp::REF_REAL3_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_EXPR(interp::REAL4_EXPR* c) const;
	interp::REAL4_EXPR* getREAL4_EXPR(domain::DomainObject* d) const;
	
	void putPAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* c) const;
	interp::PAREN_REAL4_EXPR* getPAREN_REAL4_EXPR(domain::DomainObject* d) const;
void erasePAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* key, domain::DomainObject* val);

	void putADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* c) const;
	interp::ADD_REAL4_EXPR_REAL4_EXPR* getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* c) const;
	interp::MUL_REAL4_EXPR_REAL1_EXPR* getMUL_REAL4_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREF_REAL4_VAR(interp::REF_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL4_VAR(interp::REF_REAL4_VAR* c) const;
	interp::REF_REAL4_VAR* getREF_REAL4_VAR(domain::DomainObject* d) const;
void eraseREF_REAL4_VAR(interp::REF_REAL4_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX_EXPR(interp::REALMATRIX_EXPR* c) const;
	interp::REALMATRIX_EXPR* getREALMATRIX_EXPR(domain::DomainObject* d) const;
	
	void putPAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* c) const;
	interp::PAREN_REALMATRIX_EXPR* getPAREN_REALMATRIX_EXPR(domain::DomainObject* d) const;
void erasePAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* key, domain::DomainObject* val);

	void putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c) const;
	interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(domain::DomainObject* d) const;
void eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* key, domain::DomainObject* val);

	void putREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* c) const;
	interp::REF_EXPR_REALMATRIX_VAR* getREF_EXPR_REALMATRIX_VAR(domain::DomainObject* d) const;
void eraseREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* key, domain::DomainObject* val);

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

	void putREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* c) const;
	interp::REALMATRIX_VAR_IDENT* getREALMATRIX_VAR_IDENT(domain::DomainObject* d) const;
void eraseREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_LITERAL(interp::REAL1_LITERAL* c) const;
	interp::REAL1_LITERAL* getREAL1_LITERAL(domain::DomainObject* d) const;
	
	void putREAL1_LITERAL1(interp::REAL1_LITERAL1* key, domain::DomainObject* val);
	domain::DomainObject* getREAL1_LITERAL1(interp::REAL1_LITERAL1* c) const;
	interp::REAL1_LITERAL1* getREAL1_LITERAL1(domain::DomainObject* d) const;
void eraseREAL1_LITERAL1(interp::REAL1_LITERAL1* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_LITERAL(interp::REAL3_LITERAL* c) const;
	interp::REAL3_LITERAL* getREAL3_LITERAL(domain::DomainObject* d) const;
	
	void putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREAL3_LITERAL3(interp::REAL3_LITERAL3* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_LITERAL3(interp::REAL3_LITERAL3* c) const;
	interp::REAL3_LITERAL3* getREAL3_LITERAL3(domain::DomainObject* d) const;
void eraseREAL3_LITERAL3(interp::REAL3_LITERAL3* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_LITERAL(interp::REAL4_LITERAL* c) const;
	interp::REAL4_LITERAL* getREAL4_LITERAL(domain::DomainObject* d) const;
	
	void putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREAL4_LITERAL4(interp::REAL4_LITERAL4* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_LITERAL4(interp::REAL4_LITERAL4* c) const;
	interp::REAL4_LITERAL4* getREAL4_LITERAL4(domain::DomainObject* d) const;
void eraseREAL4_LITERAL4(interp::REAL4_LITERAL4* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX_LITERAL(interp::REALMATRIX_LITERAL* c) const;
	interp::REALMATRIX_LITERAL* getREALMATRIX_LITERAL(domain::DomainObject* d) const;
	
	void putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c) const;
	interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* c) const;
	interp::REALMATRIX_LITERAL9* getREALMATRIX_LITERAL9(domain::DomainObject* d) const;
void eraseREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* key, domain::DomainObject* val);

private:

std::unordered_map<interp::Space*, domain::Space*> interp2dom_Spaces;

std::unordered_map<domain::Space*, interp::Space*> dom2interp_Spaces;

std::unordered_map<interp::Frame*, domain::Frame*> interp2dom_Frames;

std::unordered_map<domain::Frame*, interp::Frame*> dom2interp_Frames;

	std::unordered_map <interp::PROGRAM*,	domain::DomainObject*	> 	interp2dom_PROGRAM;
	std::unordered_map <domain::DomainObject*,	interp::PROGRAM*	> 	dom2interp_PROGRAM;

	std::unordered_map <interp::GLOBALSTMT*,	domain::DomainObject*	> 	interp2dom_GLOBALSTMT;
	std::unordered_map <domain::DomainObject*,	interp::GLOBALSTMT*	> 	dom2interp_GLOBALSTMT;

	std::unordered_map <interp::STMT*,	domain::DomainObject*	> 	interp2dom_STMT;
	std::unordered_map <domain::DomainObject*,	interp::STMT*	> 	dom2interp_STMT;

	std::unordered_map <interp::IFCOND*,	domain::DomainObject*	> 	interp2dom_IFCOND;
	std::unordered_map <domain::DomainObject*,	interp::IFCOND*	> 	dom2interp_IFCOND;

	std::unordered_map <interp::EXPR*,	domain::DomainObject*	> 	interp2dom_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::EXPR*	> 	dom2interp_EXPR;

	std::unordered_map <interp::ASSIGNMENT*,	domain::DomainObject*	> 	interp2dom_ASSIGNMENT;
	std::unordered_map <domain::DomainObject*,	interp::ASSIGNMENT*	> 	dom2interp_ASSIGNMENT;

	std::unordered_map <interp::DECLARE*,	domain::DomainObject*	> 	interp2dom_DECLARE;
	std::unordered_map <domain::DomainObject*,	interp::DECLARE*	> 	dom2interp_DECLARE;

	std::unordered_map <interp::REAL1_EXPR*,	domain::DomainObject*	> 	interp2dom_REAL1_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL1_EXPR*	> 	dom2interp_REAL1_EXPR;

	std::unordered_map <interp::REAL3_EXPR*,	domain::DomainObject*	> 	interp2dom_REAL3_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_EXPR*	> 	dom2interp_REAL3_EXPR;

	std::unordered_map <interp::REAL4_EXPR*,	domain::DomainObject*	> 	interp2dom_REAL4_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REAL4_EXPR*	> 	dom2interp_REAL4_EXPR;

	std::unordered_map <interp::REALMATRIX_EXPR*,	domain::DomainObject*	> 	interp2dom_REALMATRIX_EXPR;
	std::unordered_map <domain::DomainObject*,	interp::REALMATRIX_EXPR*	> 	dom2interp_REALMATRIX_EXPR;

	std::unordered_map <interp::REAL1_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REAL1_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REAL1_VAR_IDENT*	> 	dom2interp_REAL1_VAR_IDENT;

	std::unordered_map <interp::REAL3_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REAL3_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_VAR_IDENT*	> 	dom2interp_REAL3_VAR_IDENT;

	std::unordered_map <interp::REAL4_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REAL4_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REAL4_VAR_IDENT*	> 	dom2interp_REAL4_VAR_IDENT;

	std::unordered_map <interp::REALMATRIX_VAR_IDENT*,	domain::DomainObject*	> 	interp2dom_REALMATRIX_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	interp::REALMATRIX_VAR_IDENT*	> 	dom2interp_REALMATRIX_VAR_IDENT;

	std::unordered_map <interp::REAL1_LITERAL*,	domain::DomainObject*	> 	interp2dom_REAL1_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REAL1_LITERAL*	> 	dom2interp_REAL1_LITERAL;

	std::unordered_map <interp::REAL3_LITERAL*,	domain::DomainObject*	> 	interp2dom_REAL3_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REAL3_LITERAL*	> 	dom2interp_REAL3_LITERAL;

	std::unordered_map <interp::REAL4_LITERAL*,	domain::DomainObject*	> 	interp2dom_REAL4_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REAL4_LITERAL*	> 	dom2interp_REAL4_LITERAL;

	std::unordered_map <interp::REALMATRIX_LITERAL*,	domain::DomainObject*	> 	interp2dom_REALMATRIX_LITERAL;
	std::unordered_map <domain::DomainObject*,	interp::REALMATRIX_LITERAL*	> 	dom2interp_REALMATRIX_LITERAL;
};

} // namespace

#endif