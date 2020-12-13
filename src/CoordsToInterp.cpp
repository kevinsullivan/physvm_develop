
#include "CoordsToInterp.h"

#include <iostream>

#include <g3log/g3log.hpp>


using namespace coords2interp;

coords::PROGRAM *CoordsToInterp::getPROGRAM(interp::PROGRAM *i) const
    {
        coords::PROGRAM *coords = NULL;
        try {
            coords = interp2coords_PROGRAM.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::PROGRAM*)coords;
    }
interp::PROGRAM *CoordsToInterp::getPROGRAM(coords::PROGRAM *c) const
    {
        interp::PROGRAM*interp = NULL;
        try {
            interp = coords2interp_PROGRAM.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::PROGRAM*)interp;
    }

void CoordsToInterp::putSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c, interp::SEQ_GLOBALSTMT* i)
{
    coords2interp_PROGRAM[c] = (interp::PROGRAM*)i;
    interp2coords_PROGRAM[(interp::PROGRAM*)i] = c;
}
coords::SEQ_GLOBALSTMT* CoordsToInterp::getSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* i) const
{
    coords::PROGRAM* coo = NULL;
    try {
        coo = interp2coords_PROGRAM.at((interp::PROGRAM*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::SEQ_GLOBALSTMT*>(coo);
}
interp::SEQ_GLOBALSTMT* CoordsToInterp::getSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c) const
{
    interp::PROGRAM *interp = NULL;
    try {
        interp = coords2interp_PROGRAM.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::SEQ_GLOBALSTMT*>(interp);
}

coords::GLOBALSTMT *CoordsToInterp::getGLOBALSTMT(interp::GLOBALSTMT *i) const
    {
        coords::GLOBALSTMT *coords = NULL;
        try {
            coords = interp2coords_GLOBALSTMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::GLOBALSTMT*)coords;
    }
interp::GLOBALSTMT *CoordsToInterp::getGLOBALSTMT(coords::GLOBALSTMT *c) const
    {
        interp::GLOBALSTMT*interp = NULL;
        try {
            interp = coords2interp_GLOBALSTMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::GLOBALSTMT*)interp;
    }

coords::STMT *CoordsToInterp::getSTMT(interp::STMT *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::STMT*)coords;
    }
interp::STMT *CoordsToInterp::getSTMT(coords::STMT *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::STMT*)interp;
    }

void CoordsToInterp::putCOMPOUND_STMT(coords::COMPOUND_STMT* c, interp::COMPOUND_STMT* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::COMPOUND_STMT* CoordsToInterp::getCOMPOUND_STMT(interp::COMPOUND_STMT* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::STMT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::COMPOUND_STMT*>(coo);
}
interp::COMPOUND_STMT* CoordsToInterp::getCOMPOUND_STMT(coords::COMPOUND_STMT* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::COMPOUND_STMT*>(interp);
}

coords::FUNC_DECL *CoordsToInterp::getFUNC_DECL(interp::FUNC_DECL *i) const
    {
        coords::GLOBALSTMT *coords = NULL;
        try {
            coords = interp2coords_GLOBALSTMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::FUNC_DECL*)coords;
    }
interp::FUNC_DECL *CoordsToInterp::getFUNC_DECL(coords::FUNC_DECL *c) const
    {
        interp::GLOBALSTMT*interp = NULL;
        try {
            interp = coords2interp_GLOBALSTMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::FUNC_DECL*)interp;
    }

void CoordsToInterp::putVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c, interp::VOID_FUNC_DECL_STMT* i)
{
    coords2interp_GLOBALSTMT[c] = (interp::GLOBALSTMT*)i;
    interp2coords_GLOBALSTMT[(interp::GLOBALSTMT*)i] = c;
}
coords::VOID_FUNC_DECL_STMT *CoordsToInterp::getVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT *i) const
    {
        coords::GLOBALSTMT *coords = NULL;
        try {
            coords = interp2coords_GLOBALSTMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::VOID_FUNC_DECL_STMT*)coords;
    }
interp::VOID_FUNC_DECL_STMT *CoordsToInterp::getVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT *c) const
    {
        interp::GLOBALSTMT*interp = NULL;
        try {
            interp = coords2interp_GLOBALSTMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::VOID_FUNC_DECL_STMT*)interp;
    }

void CoordsToInterp::putMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c, interp::MAIN_FUNC_DECL_STMT* i)
{
    coords2interp_GLOBALSTMT[c] = (interp::GLOBALSTMT*)i;
    interp2coords_GLOBALSTMT[(interp::GLOBALSTMT*)i] = c;
}
coords::MAIN_FUNC_DECL_STMT *CoordsToInterp::getMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT *i) const
    {
        coords::GLOBALSTMT *coords = NULL;
        try {
            coords = interp2coords_GLOBALSTMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::MAIN_FUNC_DECL_STMT*)coords;
    }
interp::MAIN_FUNC_DECL_STMT *CoordsToInterp::getMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT *c) const
    {
        interp::GLOBALSTMT*interp = NULL;
        try {
            interp = coords2interp_GLOBALSTMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::MAIN_FUNC_DECL_STMT*)interp;
    }

coords::DECLARE *CoordsToInterp::getDECLARE(interp::DECLARE *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::DECLARE*)coords;
    }
interp::DECLARE *CoordsToInterp::getDECLARE(coords::DECLARE *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::DECLARE*)interp;
    }

void CoordsToInterp::putDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c, interp::DECL_REAL1_VAR_REAL1_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REAL1_VAR_REAL1_EXPR* CoordsToInterp::getDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REAL1_VAR_REAL1_EXPR*>(coo);
}
interp::DECL_REAL1_VAR_REAL1_EXPR* CoordsToInterp::getDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL1_VAR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c, interp::DECL_REAL3_VAR_REAL3_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REAL3_VAR_REAL3_EXPR* CoordsToInterp::getDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REAL3_VAR_REAL3_EXPR*>(coo);
}
interp::DECL_REAL3_VAR_REAL3_EXPR* CoordsToInterp::getDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL3_VAR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c, interp::DECL_REAL1_VAR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REAL1_VAR* CoordsToInterp::getDECL_REAL1_VAR(interp::DECL_REAL1_VAR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REAL1_VAR*>(coo);
}
interp::DECL_REAL1_VAR* CoordsToInterp::getDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL1_VAR*>(interp);
}

void CoordsToInterp::putDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c, interp::DECL_REAL3_VAR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REAL3_VAR* CoordsToInterp::getDECL_REAL3_VAR(interp::DECL_REAL3_VAR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REAL3_VAR*>(coo);
}
interp::DECL_REAL3_VAR* CoordsToInterp::getDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL3_VAR*>(interp);
}

coords::REXPR *CoordsToInterp::getREXPR(interp::REXPR *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REXPR*)coords;
    }
interp::REXPR *CoordsToInterp::getREXPR(coords::REXPR *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REXPR*)interp;
    }

coords::LEXPR *CoordsToInterp::getLEXPR(interp::LEXPR *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::LEXPR*)coords;
    }
interp::LEXPR *CoordsToInterp::getLEXPR(coords::LEXPR *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::LEXPR*)interp;
    }

coords::REAL3_EXPR *CoordsToInterp::getREAL3_EXPR(interp::REAL3_EXPR *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_EXPR*)coords;
    }
interp::REAL3_EXPR *CoordsToInterp::getREAL3_EXPR(coords::REAL3_EXPR *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_EXPR*)interp;
    }

void CoordsToInterp::putREF_REAL3_VAR(coords::REF_REAL3_VAR* c, interp::REF_REAL3_VAR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::REF_REAL3_VAR* CoordsToInterp::getREF_REAL3_VAR(interp::REF_REAL3_VAR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REF_REAL3_VAR*>(coo);
}
interp::REF_REAL3_VAR* CoordsToInterp::getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL3_VAR*>(interp);
}

void CoordsToInterp::putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, interp::ADD_REAL3_EXPR_REAL3_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::ADD_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(coo);
}
interp::ADD_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c, interp::LMUL_REAL1_EXPR_REAL3_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::LMUL_REAL1_EXPR_REAL3_EXPR* CoordsToInterp::getLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::LMUL_REAL1_EXPR_REAL3_EXPR*>(coo);
}
interp::LMUL_REAL1_EXPR_REAL3_EXPR* CoordsToInterp::getLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::LMUL_REAL1_EXPR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c, interp::RMUL_REAL3_EXPR_REAL1_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::RMUL_REAL3_EXPR_REAL1_EXPR* CoordsToInterp::getRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::RMUL_REAL3_EXPR_REAL1_EXPR*>(coo);
}
interp::RMUL_REAL3_EXPR_REAL1_EXPR* CoordsToInterp::getRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::RMUL_REAL3_EXPR_REAL1_EXPR*>(interp);
}

coords::REAL3_LEXPR *CoordsToInterp::getREAL3_LEXPR(interp::REAL3_LEXPR *i) const
    {
        coords::REAL3_LEXPR *coords = NULL;
        try {
            coords = interp2coords_REAL3_LEXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_LEXPR*)coords;
    }
interp::REAL3_LEXPR *CoordsToInterp::getREAL3_LEXPR(coords::REAL3_LEXPR *c) const
    {
        interp::REAL3_LEXPR*interp = NULL;
        try {
            interp = coords2interp_REAL3_LEXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_LEXPR*)interp;
    }

void CoordsToInterp::putLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c, interp::LREF_REAL3_VAR* i)
{
    coords2interp_REAL3_LEXPR[c] = (interp::REAL3_LEXPR*)i;
    interp2coords_REAL3_LEXPR[(interp::REAL3_LEXPR*)i] = c;
}
coords::LREF_REAL3_VAR* CoordsToInterp::getLREF_REAL3_VAR(interp::LREF_REAL3_VAR* i) const
{
    coords::REAL3_LEXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_LEXPR.at((interp::REAL3_LEXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::LREF_REAL3_VAR*>(coo);
}
interp::LREF_REAL3_VAR* CoordsToInterp::getLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c) const
{
    interp::REAL3_LEXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_LEXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::LREF_REAL3_VAR*>(interp);
}

coords::REAL1_EXPR *CoordsToInterp::getREAL1_EXPR(interp::REAL1_EXPR *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_EXPR*)coords;
    }
interp::REAL1_EXPR *CoordsToInterp::getREAL1_EXPR(coords::REAL1_EXPR *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_EXPR*)interp;
    }

void CoordsToInterp::putREF_REAL1_VAR(coords::REF_REAL1_VAR* c, interp::REF_REAL1_VAR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::REF_REAL1_VAR* CoordsToInterp::getREF_REAL1_VAR(interp::REF_REAL1_VAR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REF_REAL1_VAR*>(coo);
}
interp::REF_REAL1_VAR* CoordsToInterp::getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL1_VAR*>(interp);
}

void CoordsToInterp::putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, interp::ADD_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::ADD_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::ADD_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, interp::MUL_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::MUL_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::MUL_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, interp::REAL1_VAR_IDENT* i)
{
    coords2interp_REAL1_VAR_IDENT[c] = (interp::REAL1_VAR_IDENT*)i;
    interp2coords_REAL1_VAR_IDENT[(interp::REAL1_VAR_IDENT*)i] = c;
}
coords::REAL1_VAR_IDENT *CoordsToInterp::getREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT *i) const
    {
        coords::REAL1_VAR_IDENT *coords = NULL;
        try {
            coords = interp2coords_REAL1_VAR_IDENT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_VAR_IDENT*)coords;
    }
interp::REAL1_VAR_IDENT *CoordsToInterp::getREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT *c) const
    {
        interp::REAL1_VAR_IDENT*interp = NULL;
        try {
            interp = coords2interp_REAL1_VAR_IDENT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_VAR_IDENT*)interp;
    }

void CoordsToInterp::putREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, interp::REAL3_VAR_IDENT* i)
{
    coords2interp_REAL3_VAR_IDENT[c] = (interp::REAL3_VAR_IDENT*)i;
    interp2coords_REAL3_VAR_IDENT[(interp::REAL3_VAR_IDENT*)i] = c;
}
coords::REAL3_VAR_IDENT *CoordsToInterp::getREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT *i) const
    {
        coords::REAL3_VAR_IDENT *coords = NULL;
        try {
            coords = interp2coords_REAL3_VAR_IDENT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_VAR_IDENT*)coords;
    }
interp::REAL3_VAR_IDENT *CoordsToInterp::getREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT *c) const
    {
        interp::REAL3_VAR_IDENT*interp = NULL;
        try {
            interp = coords2interp_REAL3_VAR_IDENT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_VAR_IDENT*)interp;
    }

coords::REAL3_LITERAL *CoordsToInterp::getREAL3_LITERAL(interp::REAL3_LITERAL *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_LITERAL*)coords;
    }
interp::REAL3_LITERAL *CoordsToInterp::getREAL3_LITERAL(coords::REAL3_LITERAL *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_LITERAL*)interp;
    }

void CoordsToInterp::putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL3_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREAL3_EMPTY(coords::REAL3_EMPTY* c, interp::REAL3_EMPTY* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::REAL3_EMPTY* CoordsToInterp::getREAL3_EMPTY(interp::REAL3_EMPTY* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL3_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL3_EMPTY*>(coo);
}
interp::REAL3_EMPTY* CoordsToInterp::getREAL3_EMPTY(coords::REAL3_EMPTY* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_EMPTY*>(interp);
}

coords::REAL1_LITERAL *CoordsToInterp::getREAL1_LITERAL(interp::REAL1_LITERAL *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_LITERAL*)coords;
    }
interp::REAL1_LITERAL *CoordsToInterp::getREAL1_LITERAL(coords::REAL1_LITERAL *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_LITERAL*)interp;
    }

void CoordsToInterp::putREAL1_LIT(coords::REAL1_LIT* c, interp::REAL1_LIT* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::REAL1_LIT* CoordsToInterp::getREAL1_LIT(interp::REAL1_LIT* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::REAL1_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL1_LIT*>(coo);
}
interp::REAL1_LIT* CoordsToInterp::getREAL1_LIT(coords::REAL1_LIT* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL1_LIT*>(interp);
}
