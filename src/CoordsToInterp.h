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
};

} // namespace

#endif