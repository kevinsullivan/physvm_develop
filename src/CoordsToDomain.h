
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

	void putMAIN_STMT(coords::MAIN_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getMAIN_STMT(coords::MAIN_STMT* c) const;
	coords::MAIN_STMT* getMAIN_STMT(domain::DomainObject* d) const;
void eraseMAIN_STMT(coords::MAIN_STMT* key, domain::DomainObject* val);

	void putFUNCTION_STMT(coords::FUNCTION_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getFUNCTION_STMT(coords::FUNCTION_STMT* c) const;
	coords::FUNCTION_STMT* getFUNCTION_STMT(domain::DomainObject* d) const;
void eraseFUNCTION_STMT(coords::FUNCTION_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getSTMT(coords::STMT* c) const;
	coords::STMT* getSTMT(domain::DomainObject* d) const;

	void putCOMPOUND_STMT(coords::COMPOUND_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getCOMPOUND_STMT(coords::COMPOUND_STMT* c) const;
	coords::COMPOUND_STMT* getCOMPOUND_STMT(domain::DomainObject* d) const;
void eraseCOMPOUND_STMT(coords::COMPOUND_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getIFCOND(coords::IFCOND* c) const;
	coords::IFCOND* getIFCOND(domain::DomainObject* d) const;

	void putIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c) const;
	coords::IFTHEN_EXPR_STMT* getIFTHEN_EXPR_STMT(domain::DomainObject* d) const;
void eraseIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* key, domain::DomainObject* val);

	void putIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* key, domain::DomainObject* val);
	domain::DomainObject* getIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c) const;
	coords::IFTHENELSEIF_EXPR_STMT_IFCOND* getIFTHENELSEIF_EXPR_STMT_IFCOND(domain::DomainObject* d) const;
void eraseIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* key, domain::DomainObject* val);

	void putIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c) const;
	coords::IFTHENELSE_EXPR_STMT_STMT* getIFTHENELSE_EXPR_STMT_STMT(domain::DomainObject* d) const;
void eraseIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getEXPR(coords::EXPR* c) const;
	coords::EXPR* getEXPR(domain::DomainObject* d) const;

	domain::DomainObject* getASSIGNMENT(coords::ASSIGNMENT* c) const;
	coords::ASSIGNMENT* getASSIGNMENT(domain::DomainObject* d) const;

	void putASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c) const;
	coords::ASSIGN_REAL1_VAR_REAL1_EXPR* getASSIGN_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* key, domain::DomainObject* val);

	void putASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c) const;
	coords::ASSIGN_REAL3_VAR_REAL3_EXPR* getASSIGN_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* key, domain::DomainObject* val);

	void putASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c) const;
	coords::ASSIGN_REAL4_VAR_REAL4_EXPR* getASSIGN_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);

	void putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c) const;
	coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const;
void eraseASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);

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

	void putDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c) const;
	coords::DECL_REAL4_VAR_REAL4_EXPR* getDECL_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c) const;
	coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* key, domain::DomainObject* val);

	void putDECL_REAL1_VAR(coords::DECL_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c) const;
	coords::DECL_REAL1_VAR* getDECL_REAL1_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL1_VAR(coords::DECL_REAL1_VAR* key, domain::DomainObject* val);

	void putDECL_REAL3_VAR(coords::DECL_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c) const;
	coords::DECL_REAL3_VAR* getDECL_REAL3_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL3_VAR(coords::DECL_REAL3_VAR* key, domain::DomainObject* val);

	void putDECL_REAL4_VAR(coords::DECL_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c) const;
	coords::DECL_REAL4_VAR* getDECL_REAL4_VAR(domain::DomainObject* d) const;
void eraseDECL_REAL4_VAR(coords::DECL_REAL4_VAR* key, domain::DomainObject* val);

	void putDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c) const;
	coords::DECL_REALMATRIX_VAR* getDECL_REALMATRIX_VAR(domain::DomainObject* d) const;
void eraseDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_EXPR(coords::REAL1_EXPR* c) const;
	coords::REAL1_EXPR* getREAL1_EXPR(domain::DomainObject* d) const;

	void putPAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c) const;
	coords::PAREN_REAL1_EXPR* getPAREN_REAL1_EXPR(domain::DomainObject* d) const;
void erasePAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* key, domain::DomainObject* val);

	void putINV_REAL1_EXPR(coords::INV_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getINV_REAL1_EXPR(coords::INV_REAL1_EXPR* c) const;
	coords::INV_REAL1_EXPR* getINV_REAL1_EXPR(domain::DomainObject* d) const;
void eraseINV_REAL1_EXPR(coords::INV_REAL1_EXPR* key, domain::DomainObject* val);

	void putNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c) const;
	coords::NEG_REAL1_EXPR* getNEG_REAL1_EXPR(domain::DomainObject* d) const;
void eraseNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* key, domain::DomainObject* val);

	void putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::ADD_REAL1_EXPR_REAL1_EXPR* getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::SUB_REAL1_EXPR_REAL1_EXPR* getSUB_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::MUL_REAL1_EXPR_REAL1_EXPR* getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::DIV_REAL1_EXPR_REAL1_EXPR* getDIV_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREF_REAL1_VAR(coords::REF_REAL1_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const;
	coords::REF_REAL1_VAR* getREF_REAL1_VAR(domain::DomainObject* d) const;
void eraseREF_REAL1_VAR(coords::REF_REAL1_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_EXPR(coords::REAL3_EXPR* c) const;
	coords::REAL3_EXPR* getREAL3_EXPR(domain::DomainObject* d) const;

	void putPAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c) const;
	coords::PAREN_REAL3_EXPR* getPAREN_REAL3_EXPR(domain::DomainObject* d) const;
void erasePAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* key, domain::DomainObject* val);

	void putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const;
	coords::ADD_REAL3_EXPR_REAL3_EXPR* getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c) const;
	coords::SUB_REAL3_EXPR_REAL3_EXPR* getSUB_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putINV_REAL3_EXPR(coords::INV_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getINV_REAL3_EXPR(coords::INV_REAL3_EXPR* c) const;
	coords::INV_REAL3_EXPR* getINV_REAL3_EXPR(domain::DomainObject* d) const;
void eraseINV_REAL3_EXPR(coords::INV_REAL3_EXPR* key, domain::DomainObject* val);

	void putNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c) const;
	coords::NEG_REAL3_EXPR* getNEG_REAL3_EXPR(domain::DomainObject* d) const;
void eraseNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c) const;
	coords::MUL_REAL3_EXPR_REAL1_EXPR* getMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c) const;
	coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* getMUL_REALMATRIX_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c) const;
	coords::DIV_REAL3_EXPR_REAL1_EXPR* getDIV_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREF_REAL3_VAR(coords::REF_REAL3_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const;
	coords::REF_REAL3_VAR* getREF_REAL3_VAR(domain::DomainObject* d) const;
void eraseREF_REAL3_VAR(coords::REF_REAL3_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_EXPR(coords::REAL4_EXPR* c) const;
	coords::REAL4_EXPR* getREAL4_EXPR(domain::DomainObject* d) const;

	void putPAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c) const;
	coords::PAREN_REAL4_EXPR* getPAREN_REAL4_EXPR(domain::DomainObject* d) const;
void erasePAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* key, domain::DomainObject* val);

	void putADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c) const;
	coords::ADD_REAL4_EXPR_REAL4_EXPR* getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const;
void eraseADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* key, domain::DomainObject* val);

	void putMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c) const;
	coords::MUL_REAL4_EXPR_REAL1_EXPR* getMUL_REAL4_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREF_REAL4_VAR(coords::REF_REAL4_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_REAL4_VAR(coords::REF_REAL4_VAR* c) const;
	coords::REF_REAL4_VAR* getREF_REAL4_VAR(domain::DomainObject* d) const;
void eraseREF_REAL4_VAR(coords::REF_REAL4_VAR* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX_EXPR(coords::REALMATRIX_EXPR* c) const;
	coords::REALMATRIX_EXPR* getREALMATRIX_EXPR(domain::DomainObject* d) const;

	void putPAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getPAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c) const;
	coords::PAREN_REALMATRIX_EXPR* getPAREN_REALMATRIX_EXPR(domain::DomainObject* d) const;
void erasePAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* key, domain::DomainObject* val);

	void putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c) const;
	coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(domain::DomainObject* d) const;
void eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* key, domain::DomainObject* val);

	void putREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* key, domain::DomainObject* val);
	domain::DomainObject* getREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c) const;
	coords::REF_EXPR_REALMATRIX_VAR* getREF_EXPR_REALMATRIX_VAR(domain::DomainObject* d) const;
void eraseREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* key, domain::DomainObject* val);

	void putREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c) const;
	coords::REAL1_VAR_IDENT* getREAL1_VAR_IDENT(domain::DomainObject* d) const;
void eraseREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* key, domain::DomainObject* val);

	void putREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c) const;
	coords::REAL3_VAR_IDENT* getREAL3_VAR_IDENT(domain::DomainObject* d) const;
void eraseREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* key, domain::DomainObject* val);

	void putREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c) const;
	coords::REAL4_VAR_IDENT* getREAL4_VAR_IDENT(domain::DomainObject* d) const;
void eraseREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* key, domain::DomainObject* val);

	void putREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c) const;
	coords::REALMATRIX_VAR_IDENT* getREALMATRIX_VAR_IDENT(domain::DomainObject* d) const;
void eraseREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* key, domain::DomainObject* val);

	domain::DomainObject* getREAL1_LITERAL(coords::REAL1_LITERAL* c) const;
	coords::REAL1_LITERAL* getREAL1_LITERAL(domain::DomainObject* d) const;

	void putREAL1_LITERAL1(coords::REAL1_LITERAL1* key, domain::DomainObject* val);
	domain::DomainObject* getREAL1_LITERAL1(coords::REAL1_LITERAL1* c) const;
	coords::REAL1_LITERAL1* getREAL1_LITERAL1(domain::DomainObject* d) const;
void eraseREAL1_LITERAL1(coords::REAL1_LITERAL1* key, domain::DomainObject* val);

	domain::DomainObject* getREAL3_LITERAL(coords::REAL3_LITERAL* c) const;
	coords::REAL3_LITERAL* getREAL3_LITERAL(domain::DomainObject* d) const;

	void putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREAL3_LITERAL3(coords::REAL3_LITERAL3* key, domain::DomainObject* val);
	domain::DomainObject* getREAL3_LITERAL3(coords::REAL3_LITERAL3* c) const;
	coords::REAL3_LITERAL3* getREAL3_LITERAL3(domain::DomainObject* d) const;
void eraseREAL3_LITERAL3(coords::REAL3_LITERAL3* key, domain::DomainObject* val);

	domain::DomainObject* getREAL4_LITERAL(coords::REAL4_LITERAL* c) const;
	coords::REAL4_LITERAL* getREAL4_LITERAL(domain::DomainObject* d) const;

	void putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREAL4_LITERAL4(coords::REAL4_LITERAL4* key, domain::DomainObject* val);
	domain::DomainObject* getREAL4_LITERAL4(coords::REAL4_LITERAL4* c) const;
	coords::REAL4_LITERAL4* getREAL4_LITERAL4(domain::DomainObject* d) const;
void eraseREAL4_LITERAL4(coords::REAL4_LITERAL4* key, domain::DomainObject* val);

	domain::DomainObject* getREALMATRIX_LITERAL(coords::REALMATRIX_LITERAL* c) const;
	coords::REALMATRIX_LITERAL* getREALMATRIX_LITERAL(domain::DomainObject* d) const;

	void putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c) const;
	coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const;
void eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* key, domain::DomainObject* val);

	void putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const;
void eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, domain::DomainObject* val);

	void putREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* key, domain::DomainObject* val);
	domain::DomainObject* getREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c) const;
	coords::REALMATRIX_LITERAL9* getREALMATRIX_LITERAL9(domain::DomainObject* d) const;
void eraseREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* key, domain::DomainObject* val);

private:

	std::unordered_map <coords::PROGRAM*,	domain::DomainObject*	> 	coords2dom_PROGRAM;
	std::unordered_map <domain::DomainObject*,	coords::PROGRAM*	> 	dom2coords_PROGRAM;

	std::unordered_map <coords::GLOBALSTMT*,	domain::DomainObject*	> 	coords2dom_GLOBALSTMT;
	std::unordered_map <domain::DomainObject*,	coords::GLOBALSTMT*	> 	dom2coords_GLOBALSTMT;

	std::unordered_map <coords::STMT*,	domain::DomainObject*	> 	coords2dom_STMT;
	std::unordered_map <domain::DomainObject*,	coords::STMT*	> 	dom2coords_STMT;

	std::unordered_map <coords::IFCOND*,	domain::DomainObject*	> 	coords2dom_IFCOND;
	std::unordered_map <domain::DomainObject*,	coords::IFCOND*	> 	dom2coords_IFCOND;

	std::unordered_map <coords::EXPR*,	domain::DomainObject*	> 	coords2dom_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::EXPR*	> 	dom2coords_EXPR;

	std::unordered_map <coords::ASSIGNMENT*,	domain::DomainObject*	> 	coords2dom_ASSIGNMENT;
	std::unordered_map <domain::DomainObject*,	coords::ASSIGNMENT*	> 	dom2coords_ASSIGNMENT;

	std::unordered_map <coords::DECLARE*,	domain::DomainObject*	> 	coords2dom_DECLARE;
	std::unordered_map <domain::DomainObject*,	coords::DECLARE*	> 	dom2coords_DECLARE;

	std::unordered_map <coords::REAL1_EXPR*,	domain::DomainObject*	> 	coords2dom_REAL1_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL1_EXPR*	> 	dom2coords_REAL1_EXPR;

	std::unordered_map <coords::REAL3_EXPR*,	domain::DomainObject*	> 	coords2dom_REAL3_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_EXPR*	> 	dom2coords_REAL3_EXPR;

	std::unordered_map <coords::REAL4_EXPR*,	domain::DomainObject*	> 	coords2dom_REAL4_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REAL4_EXPR*	> 	dom2coords_REAL4_EXPR;

	std::unordered_map <coords::REALMATRIX_EXPR*,	domain::DomainObject*	> 	coords2dom_REALMATRIX_EXPR;
	std::unordered_map <domain::DomainObject*,	coords::REALMATRIX_EXPR*	> 	dom2coords_REALMATRIX_EXPR;

	std::unordered_map <coords::REAL1_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REAL1_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REAL1_VAR_IDENT*	> 	dom2coords_REAL1_VAR_IDENT;

	std::unordered_map <coords::REAL3_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REAL3_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_VAR_IDENT*	> 	dom2coords_REAL3_VAR_IDENT;

	std::unordered_map <coords::REAL4_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REAL4_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REAL4_VAR_IDENT*	> 	dom2coords_REAL4_VAR_IDENT;

	std::unordered_map <coords::REALMATRIX_VAR_IDENT*,	domain::DomainObject*	> 	coords2dom_REALMATRIX_VAR_IDENT;
	std::unordered_map <domain::DomainObject*,	coords::REALMATRIX_VAR_IDENT*	> 	dom2coords_REALMATRIX_VAR_IDENT;

	std::unordered_map <coords::REAL1_LITERAL*,	domain::DomainObject*	> 	coords2dom_REAL1_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REAL1_LITERAL*	> 	dom2coords_REAL1_LITERAL;

	std::unordered_map <coords::REAL3_LITERAL*,	domain::DomainObject*	> 	coords2dom_REAL3_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REAL3_LITERAL*	> 	dom2coords_REAL3_LITERAL;

	std::unordered_map <coords::REAL4_LITERAL*,	domain::DomainObject*	> 	coords2dom_REAL4_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REAL4_LITERAL*	> 	dom2coords_REAL4_LITERAL;

	std::unordered_map <coords::REALMATRIX_LITERAL*,	domain::DomainObject*	> 	coords2dom_REALMATRIX_LITERAL;
	std::unordered_map <domain::DomainObject*,	coords::REALMATRIX_LITERAL*	> 	dom2coords_REALMATRIX_LITERAL;
};

} // namespace

#endif