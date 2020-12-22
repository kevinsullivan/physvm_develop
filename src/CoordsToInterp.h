#ifndef COORDSTOINTERP_H
#define COORDSTOINTERP_H

# include <iostream>
# include "Coords.h"
# include "Interp.h"

# include <unordered_map>

namespace coords2interp{

class CoordsToInterp
{
public:


	interp::PROGRAM* getPROGRAM(coords::PROGRAM* c) const;
	coords::PROGRAM* getPROGRAM(interp::PROGRAM* i) const;

	void putSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* key, interp::SEQ_GLOBALSTMT* val);
	interp::SEQ_GLOBALSTMT* getSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c) const;
	coords::SEQ_GLOBALSTMT* getSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* i) const;

	interp::GLOBALSTMT* getGLOBALSTMT(coords::GLOBALSTMT* c) const;
	coords::GLOBALSTMT* getGLOBALSTMT(interp::GLOBALSTMT* i) const;

	interp::STMT* getSTMT(coords::STMT* c) const;
	coords::STMT* getSTMT(interp::STMT* i) const;

	void putCOMPOUND_STMT(coords::COMPOUND_STMT* key, interp::COMPOUND_STMT* val);
	interp::COMPOUND_STMT* getCOMPOUND_STMT(coords::COMPOUND_STMT* c) const;
	coords::COMPOUND_STMT* getCOMPOUND_STMT(interp::COMPOUND_STMT* i) const;

	interp::FUNC_DECL* getFUNC_DECL(coords::FUNC_DECL* c) const;
	coords::FUNC_DECL* getFUNC_DECL(interp::FUNC_DECL* i) const;

	void putVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* key, interp::VOID_FUNC_DECL_STMT* val);
	interp::VOID_FUNC_DECL_STMT* getVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c) const;
	coords::VOID_FUNC_DECL_STMT* getVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* i) const;

	void putMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* key, interp::MAIN_FUNC_DECL_STMT* val);
	interp::MAIN_FUNC_DECL_STMT* getMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c) const;
	coords::MAIN_FUNC_DECL_STMT* getMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* i) const;

	interp::DECLARE* getDECLARE(coords::DECLARE* c) const;
	coords::DECLARE* getDECLARE(interp::DECLARE* i) const;

	void putDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* key, interp::DECL_REAL1_VAR_REAL1_EXPR* val);
	interp::DECL_REAL1_VAR_REAL1_EXPR* getDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c) const;
	coords::DECL_REAL1_VAR_REAL1_EXPR* getDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* i) const;

	void putDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* key, interp::DECL_REAL3_VAR_REAL3_EXPR* val);
	interp::DECL_REAL3_VAR_REAL3_EXPR* getDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c) const;
	coords::DECL_REAL3_VAR_REAL3_EXPR* getDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* i) const;

	void putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* key, interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* val);
	interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const;
	coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(interp::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* i) const;

	void putDECL_REAL1_VAR(coords::DECL_REAL1_VAR* key, interp::DECL_REAL1_VAR* val);
	interp::DECL_REAL1_VAR* getDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c) const;
	coords::DECL_REAL1_VAR* getDECL_REAL1_VAR(interp::DECL_REAL1_VAR* i) const;

	void putDECL_REAL3_VAR(coords::DECL_REAL3_VAR* key, interp::DECL_REAL3_VAR* val);
	interp::DECL_REAL3_VAR* getDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c) const;
	coords::DECL_REAL3_VAR* getDECL_REAL3_VAR(interp::DECL_REAL3_VAR* i) const;

	void putDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* key, interp::DECL_REALMATRIX4_VAR* val);
	interp::DECL_REALMATRIX4_VAR* getDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* c) const;
	coords::DECL_REALMATRIX4_VAR* getDECL_REALMATRIX4_VAR(interp::DECL_REALMATRIX4_VAR* i) const;

	interp::REXPR* getREXPR(coords::REXPR* c) const;
	coords::REXPR* getREXPR(interp::REXPR* i) const;

	interp::LEXPR* getLEXPR(coords::LEXPR* c) const;
	coords::LEXPR* getLEXPR(interp::LEXPR* i) const;

	interp::REALMATRIX4_EXPR* getREALMATRIX4_EXPR(coords::REALMATRIX4_EXPR* c) const;
	coords::REALMATRIX4_EXPR* getREALMATRIX4_EXPR(interp::REALMATRIX4_EXPR* i) const;

	void putREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* key, interp::REF_REALMATRIX4_VAR* val);
	interp::REF_REALMATRIX4_VAR* getREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* c) const;
	coords::REF_REALMATRIX4_VAR* getREF_REALMATRIX4_VAR(interp::REF_REALMATRIX4_VAR* i) const;

	void putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* key, interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* val);
	interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* c) const;
	coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(interp::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* i) const;

	interp::REAL3_EXPR* getREAL3_EXPR(coords::REAL3_EXPR* c) const;
	coords::REAL3_EXPR* getREAL3_EXPR(interp::REAL3_EXPR* i) const;

	void putREF_REAL3_VAR(coords::REF_REAL3_VAR* key, interp::REF_REAL3_VAR* val);
	interp::REF_REAL3_VAR* getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const;
	coords::REF_REAL3_VAR* getREF_REAL3_VAR(interp::REF_REAL3_VAR* i) const;

	void putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* key, interp::ADD_REAL3_EXPR_REAL3_EXPR* val);
	interp::ADD_REAL3_EXPR_REAL3_EXPR* getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const;
	coords::ADD_REAL3_EXPR_REAL3_EXPR* getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i) const;

	void putLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* key, interp::LMUL_REAL1_EXPR_REAL3_EXPR* val);
	interp::LMUL_REAL1_EXPR_REAL3_EXPR* getLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c) const;
	coords::LMUL_REAL1_EXPR_REAL3_EXPR* getLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* i) const;

	void putRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* key, interp::RMUL_REAL3_EXPR_REAL1_EXPR* val);
	interp::RMUL_REAL3_EXPR_REAL1_EXPR* getRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c) const;
	coords::RMUL_REAL3_EXPR_REAL1_EXPR* getRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* i) const;

	void putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* key, interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* val);
	interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* c) const;
	coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(interp::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* i) const;

	interp::REAL3_LEXPR* getREAL3_LEXPR(coords::REAL3_LEXPR* c) const;
	coords::REAL3_LEXPR* getREAL3_LEXPR(interp::REAL3_LEXPR* i) const;

	void putLREF_REAL3_VAR(coords::LREF_REAL3_VAR* key, interp::LREF_REAL3_VAR* val);
	interp::LREF_REAL3_VAR* getLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c) const;
	coords::LREF_REAL3_VAR* getLREF_REAL3_VAR(interp::LREF_REAL3_VAR* i) const;

	interp::REAL1_EXPR* getREAL1_EXPR(coords::REAL1_EXPR* c) const;
	coords::REAL1_EXPR* getREAL1_EXPR(interp::REAL1_EXPR* i) const;

	void putREF_REAL1_VAR(coords::REF_REAL1_VAR* key, interp::REF_REAL1_VAR* val);
	interp::REF_REAL1_VAR* getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const;
	coords::REF_REAL1_VAR* getREF_REAL1_VAR(interp::REF_REAL1_VAR* i) const;

	void putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* key, interp::ADD_REAL1_EXPR_REAL1_EXPR* val);
	interp::ADD_REAL1_EXPR_REAL1_EXPR* getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::ADD_REAL1_EXPR_REAL1_EXPR* getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i) const;

	void putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* key, interp::MUL_REAL1_EXPR_REAL1_EXPR* val);
	interp::MUL_REAL1_EXPR_REAL1_EXPR* getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::MUL_REAL1_EXPR_REAL1_EXPR* getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i) const;

	void putREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* key, interp::REAL1_VAR_IDENT* val);
	interp::REAL1_VAR_IDENT* getREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c) const;
	coords::REAL1_VAR_IDENT* getREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* i) const;

	void putREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* key, interp::REAL3_VAR_IDENT* val);
	interp::REAL3_VAR_IDENT* getREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c) const;
	coords::REAL3_VAR_IDENT* getREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* i) const;

	void putREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* key, interp::REALMATRIX4_VAR_IDENT* val);
	interp::REALMATRIX4_VAR_IDENT* getREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* c) const;
	coords::REALMATRIX4_VAR_IDENT* getREALMATRIX4_VAR_IDENT(interp::REALMATRIX4_VAR_IDENT* i) const;

	interp::REAL3_LITERAL* getREAL3_LITERAL(coords::REAL3_LITERAL* c) const;
	coords::REAL3_LITERAL* getREAL3_LITERAL(interp::REAL3_LITERAL* i) const;

	void putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* key, interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* val);
	interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const;
	coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const;

	void putREAL3_EMPTY(coords::REAL3_EMPTY* key, interp::REAL3_EMPTY* val);
	interp::REAL3_EMPTY* getREAL3_EMPTY(coords::REAL3_EMPTY* c) const;
	coords::REAL3_EMPTY* getREAL3_EMPTY(interp::REAL3_EMPTY* i) const;

	interp::REAL1_LITERAL* getREAL1_LITERAL(coords::REAL1_LITERAL* c) const;
	coords::REAL1_LITERAL* getREAL1_LITERAL(interp::REAL1_LITERAL* i) const;

	void putREAL1_LIT(coords::REAL1_LIT* key, interp::REAL1_LIT* val);
	interp::REAL1_LIT* getREAL1_LIT(coords::REAL1_LIT* c) const;
	coords::REAL1_LIT* getREAL1_LIT(interp::REAL1_LIT* i) const;

	interp::REALMATRIX4_LITERAL* getREALMATRIX4_LITERAL(coords::REALMATRIX4_LITERAL* c) const;
	coords::REALMATRIX4_LITERAL* getREALMATRIX4_LITERAL(interp::REALMATRIX4_LITERAL* i) const;

	void putREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* key, interp::REALMATRIX4_EMPTY* val);
	interp::REALMATRIX4_EMPTY* getREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* c) const;
	coords::REALMATRIX4_EMPTY* getREALMATRIX4_EMPTY(interp::REALMATRIX4_EMPTY* i) const;

private:

	std::unordered_map <coords::PROGRAM*,	interp::PROGRAM*	> 	coords2interp_PROGRAM;
	std::unordered_map <interp::PROGRAM*,	coords::PROGRAM*	> 	interp2coords_PROGRAM;

	std::unordered_map <coords::GLOBALSTMT*,	interp::GLOBALSTMT*	> 	coords2interp_GLOBALSTMT;
	std::unordered_map <interp::GLOBALSTMT*,	coords::GLOBALSTMT*	> 	interp2coords_GLOBALSTMT;

	std::unordered_map <coords::STMT*,	interp::STMT*	> 	coords2interp_STMT;
	std::unordered_map <interp::STMT*,	coords::STMT*	> 	interp2coords_STMT;

	std::unordered_map <coords::FUNC_DECL*,	interp::FUNC_DECL*	> 	coords2interp_FUNC_DECL;
	std::unordered_map <interp::FUNC_DECL*,	coords::FUNC_DECL*	> 	interp2coords_FUNC_DECL;

	std::unordered_map <coords::VOID_FUNC_DECL_STMT*,	interp::VOID_FUNC_DECL_STMT*	> 	coords2interp_VOID_FUNC_DECL_STMT;
	std::unordered_map <interp::VOID_FUNC_DECL_STMT*,	coords::VOID_FUNC_DECL_STMT*	> 	interp2coords_VOID_FUNC_DECL_STMT;

	std::unordered_map <coords::MAIN_FUNC_DECL_STMT*,	interp::MAIN_FUNC_DECL_STMT*	> 	coords2interp_MAIN_FUNC_DECL_STMT;
	std::unordered_map <interp::MAIN_FUNC_DECL_STMT*,	coords::MAIN_FUNC_DECL_STMT*	> 	interp2coords_MAIN_FUNC_DECL_STMT;

	std::unordered_map <coords::DECLARE*,	interp::DECLARE*	> 	coords2interp_DECLARE;
	std::unordered_map <interp::DECLARE*,	coords::DECLARE*	> 	interp2coords_DECLARE;

	std::unordered_map <coords::REXPR*,	interp::REXPR*	> 	coords2interp_REXPR;
	std::unordered_map <interp::REXPR*,	coords::REXPR*	> 	interp2coords_REXPR;

	std::unordered_map <coords::LEXPR*,	interp::LEXPR*	> 	coords2interp_LEXPR;
	std::unordered_map <interp::LEXPR*,	coords::LEXPR*	> 	interp2coords_LEXPR;

	std::unordered_map <coords::REALMATRIX4_EXPR*,	interp::REALMATRIX4_EXPR*	> 	coords2interp_REALMATRIX4_EXPR;
	std::unordered_map <interp::REALMATRIX4_EXPR*,	coords::REALMATRIX4_EXPR*	> 	interp2coords_REALMATRIX4_EXPR;

	std::unordered_map <coords::REAL3_EXPR*,	interp::REAL3_EXPR*	> 	coords2interp_REAL3_EXPR;
	std::unordered_map <interp::REAL3_EXPR*,	coords::REAL3_EXPR*	> 	interp2coords_REAL3_EXPR;

	std::unordered_map <coords::REAL3_LEXPR*,	interp::REAL3_LEXPR*	> 	coords2interp_REAL3_LEXPR;
	std::unordered_map <interp::REAL3_LEXPR*,	coords::REAL3_LEXPR*	> 	interp2coords_REAL3_LEXPR;

	std::unordered_map <coords::REAL1_EXPR*,	interp::REAL1_EXPR*	> 	coords2interp_REAL1_EXPR;
	std::unordered_map <interp::REAL1_EXPR*,	coords::REAL1_EXPR*	> 	interp2coords_REAL1_EXPR;

	std::unordered_map <coords::REAL1_VAR_IDENT*,	interp::REAL1_VAR_IDENT*	> 	coords2interp_REAL1_VAR_IDENT;
	std::unordered_map <interp::REAL1_VAR_IDENT*,	coords::REAL1_VAR_IDENT*	> 	interp2coords_REAL1_VAR_IDENT;

	std::unordered_map <coords::REAL3_VAR_IDENT*,	interp::REAL3_VAR_IDENT*	> 	coords2interp_REAL3_VAR_IDENT;
	std::unordered_map <interp::REAL3_VAR_IDENT*,	coords::REAL3_VAR_IDENT*	> 	interp2coords_REAL3_VAR_IDENT;

	std::unordered_map <coords::REALMATRIX4_VAR_IDENT*,	interp::REALMATRIX4_VAR_IDENT*	> 	coords2interp_REALMATRIX4_VAR_IDENT;
	std::unordered_map <interp::REALMATRIX4_VAR_IDENT*,	coords::REALMATRIX4_VAR_IDENT*	> 	interp2coords_REALMATRIX4_VAR_IDENT;

	std::unordered_map <coords::REAL3_LITERAL*,	interp::REAL3_LITERAL*	> 	coords2interp_REAL3_LITERAL;
	std::unordered_map <interp::REAL3_LITERAL*,	coords::REAL3_LITERAL*	> 	interp2coords_REAL3_LITERAL;

	std::unordered_map <coords::REAL1_LITERAL*,	interp::REAL1_LITERAL*	> 	coords2interp_REAL1_LITERAL;
	std::unordered_map <interp::REAL1_LITERAL*,	coords::REAL1_LITERAL*	> 	interp2coords_REAL1_LITERAL;

	std::unordered_map <coords::REALMATRIX4_LITERAL*,	interp::REALMATRIX4_LITERAL*	> 	coords2interp_REALMATRIX4_LITERAL;
	std::unordered_map <interp::REALMATRIX4_LITERAL*,	coords::REALMATRIX4_LITERAL*	> 	interp2coords_REALMATRIX4_LITERAL;
};

} // namespace

#endif