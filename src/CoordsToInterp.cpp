
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

void CoordsToInterp::putMAIN_STMT(coords::MAIN_STMT* c, interp::MAIN_STMT* i)
{
    coords2interp_GLOBALSTMT[c] = (interp::GLOBALSTMT*)i;
    interp2coords_GLOBALSTMT[(interp::GLOBALSTMT*)i] = c;
}
coords::MAIN_STMT* CoordsToInterp::getMAIN_STMT(interp::MAIN_STMT* i) const
{
    coords::GLOBALSTMT* coo = NULL;
    try {
        coo = interp2coords_GLOBALSTMT.at((interp::GLOBALSTMT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MAIN_STMT*>(coo);
}
interp::MAIN_STMT* CoordsToInterp::getMAIN_STMT(coords::MAIN_STMT* c) const
{
    interp::GLOBALSTMT *interp = NULL;
    try {
        interp = coords2interp_GLOBALSTMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MAIN_STMT*>(interp);
}

void CoordsToInterp::putFUNCTION_STMT(coords::FUNCTION_STMT* c, interp::FUNCTION_STMT* i)
{
    coords2interp_GLOBALSTMT[c] = (interp::GLOBALSTMT*)i;
    interp2coords_GLOBALSTMT[(interp::GLOBALSTMT*)i] = c;
}
coords::FUNCTION_STMT* CoordsToInterp::getFUNCTION_STMT(interp::FUNCTION_STMT* i) const
{
    coords::GLOBALSTMT* coo = NULL;
    try {
        coo = interp2coords_GLOBALSTMT.at((interp::GLOBALSTMT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::FUNCTION_STMT*>(coo);
}
interp::FUNCTION_STMT* CoordsToInterp::getFUNCTION_STMT(coords::FUNCTION_STMT* c) const
{
    interp::GLOBALSTMT *interp = NULL;
    try {
        interp = coords2interp_GLOBALSTMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::FUNCTION_STMT*>(interp);
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

coords::IFCOND *CoordsToInterp::getIFCOND(interp::IFCOND *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::IFCOND*)coords;
    }
interp::IFCOND *CoordsToInterp::getIFCOND(coords::IFCOND *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::IFCOND*)interp;
    }

void CoordsToInterp::putIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c, interp::IFTHEN_EXPR_STMT* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::IFTHEN_EXPR_STMT* CoordsToInterp::getIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::IFCOND*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::IFTHEN_EXPR_STMT*>(coo);
}
interp::IFTHEN_EXPR_STMT* CoordsToInterp::getIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::IFTHEN_EXPR_STMT*>(interp);
}

void CoordsToInterp::putIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c, interp::IFTHENELSEIF_EXPR_STMT_IFCOND* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::IFTHENELSEIF_EXPR_STMT_IFCOND* CoordsToInterp::getIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::IFCOND*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::IFTHENELSEIF_EXPR_STMT_IFCOND*>(coo);
}
interp::IFTHENELSEIF_EXPR_STMT_IFCOND* CoordsToInterp::getIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::IFTHENELSEIF_EXPR_STMT_IFCOND*>(interp);
}

void CoordsToInterp::putIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c, interp::IFTHENELSE_EXPR_STMT_STMT* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::IFTHENELSE_EXPR_STMT_STMT* CoordsToInterp::getIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::IFCOND*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::IFTHENELSE_EXPR_STMT_STMT*>(coo);
}
interp::IFTHENELSE_EXPR_STMT_STMT* CoordsToInterp::getIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::IFTHENELSE_EXPR_STMT_STMT*>(interp);
}

coords::EXPR *CoordsToInterp::getEXPR(interp::EXPR *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::EXPR*)coords;
    }
interp::EXPR *CoordsToInterp::getEXPR(coords::EXPR *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::EXPR*)interp;
    }

coords::ASSIGNMENT *CoordsToInterp::getASSIGNMENT(interp::ASSIGNMENT *i) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = interp2coords_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::ASSIGNMENT*)coords;
    }
interp::ASSIGNMENT *CoordsToInterp::getASSIGNMENT(coords::ASSIGNMENT *c) const
    {
        interp::STMT*interp = NULL;
        try {
            interp = coords2interp_STMT.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::ASSIGNMENT*)interp;
    }

void CoordsToInterp::putASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c, interp::ASSIGN_REAL1_VAR_REAL1_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::ASSIGN_REAL1_VAR_REAL1_EXPR* CoordsToInterp::getASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::ASSIGNMENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ASSIGN_REAL1_VAR_REAL1_EXPR*>(coo);
}
interp::ASSIGN_REAL1_VAR_REAL1_EXPR* CoordsToInterp::getASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REAL1_VAR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c, interp::ASSIGN_REAL3_VAR_REAL3_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::ASSIGN_REAL3_VAR_REAL3_EXPR* CoordsToInterp::getASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::ASSIGNMENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ASSIGN_REAL3_VAR_REAL3_EXPR*>(coo);
}
interp::ASSIGN_REAL3_VAR_REAL3_EXPR* CoordsToInterp::getASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REAL3_VAR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c, interp::ASSIGN_REAL4_VAR_REAL4_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::ASSIGN_REAL4_VAR_REAL4_EXPR* CoordsToInterp::getASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::ASSIGNMENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ASSIGN_REAL4_VAR_REAL4_EXPR*>(coo);
}
interp::ASSIGN_REAL4_VAR_REAL4_EXPR* CoordsToInterp::getASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REAL4_VAR_REAL4_EXPR*>(interp);
}

void CoordsToInterp::putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c, interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* CoordsToInterp::getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::ASSIGNMENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR*>(coo);
}
interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* CoordsToInterp::getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR*>(interp);
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

void CoordsToInterp::putDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c, interp::DECL_REAL4_VAR_REAL4_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REAL4_VAR_REAL4_EXPR* CoordsToInterp::getDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REAL4_VAR_REAL4_EXPR*>(coo);
}
interp::DECL_REAL4_VAR_REAL4_EXPR* CoordsToInterp::getDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL4_VAR_REAL4_EXPR*>(interp);
}

void CoordsToInterp::putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c, interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* CoordsToInterp::getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR*>(coo);
}
interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* CoordsToInterp::getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR*>(interp);
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

void CoordsToInterp::putDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c, interp::DECL_REAL4_VAR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REAL4_VAR* CoordsToInterp::getDECL_REAL4_VAR(interp::DECL_REAL4_VAR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REAL4_VAR*>(coo);
}
interp::DECL_REAL4_VAR* CoordsToInterp::getDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL4_VAR*>(interp);
}

void CoordsToInterp::putDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c, interp::DECL_REALMATRIX_VAR* i)
{
    coords2interp_STMT[c] = (interp::STMT*)i;
    interp2coords_STMT[(interp::STMT*)i] = c;
}
coords::DECL_REALMATRIX_VAR* CoordsToInterp::getDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* i) const
{
    coords::STMT* coo = NULL;
    try {
        coo = interp2coords_STMT.at((interp::DECLARE*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DECL_REALMATRIX_VAR*>(coo);
}
interp::DECL_REALMATRIX_VAR* CoordsToInterp::getDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c) const
{
    interp::STMT *interp = NULL;
    try {
        interp = coords2interp_STMT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REALMATRIX_VAR*>(interp);
}

coords::REAL1_EXPR *CoordsToInterp::getREAL1_EXPR(interp::REAL1_EXPR *i) const
    {
        coords::REAL1_EXPR *coords = NULL;
        try {
            coords = interp2coords_REAL1_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_EXPR*)coords;
    }
interp::REAL1_EXPR *CoordsToInterp::getREAL1_EXPR(coords::REAL1_EXPR *c) const
    {
        interp::REAL1_EXPR*interp = NULL;
        try {
            interp = coords2interp_REAL1_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_EXPR*)interp;
    }

void CoordsToInterp::putPAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c, interp::PAREN_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::PAREN_REAL1_EXPR* CoordsToInterp::getPAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::PAREN_REAL1_EXPR*>(coo);
}
interp::PAREN_REAL1_EXPR* CoordsToInterp::getPAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putINV_REAL1_EXPR(coords::INV_REAL1_EXPR* c, interp::INV_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::INV_REAL1_EXPR* CoordsToInterp::getINV_REAL1_EXPR(interp::INV_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::INV_REAL1_EXPR*>(coo);
}
interp::INV_REAL1_EXPR* CoordsToInterp::getINV_REAL1_EXPR(coords::INV_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::INV_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c, interp::NEG_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::NEG_REAL1_EXPR* CoordsToInterp::getNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::NEG_REAL1_EXPR*>(coo);
}
interp::NEG_REAL1_EXPR* CoordsToInterp::getNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::NEG_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, interp::ADD_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::ADD_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::ADD_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c, interp::SUB_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::SUB_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::SUB_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::SUB_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::SUB_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, interp::MUL_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::MUL_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::MUL_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c, interp::DIV_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::DIV_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DIV_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::DIV_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DIV_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREF_REAL1_VAR(coords::REF_REAL1_VAR* c, interp::REF_REAL1_VAR* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::REF_REAL1_VAR* CoordsToInterp::getREF_REAL1_VAR(interp::REF_REAL1_VAR* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REF_REAL1_VAR*>(coo);
}
interp::REF_REAL1_VAR* CoordsToInterp::getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL1_VAR*>(interp);
}

coords::REAL3_EXPR *CoordsToInterp::getREAL3_EXPR(interp::REAL3_EXPR *i) const
    {
        coords::REAL3_EXPR *coords = NULL;
        try {
            coords = interp2coords_REAL3_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_EXPR*)coords;
    }
interp::REAL3_EXPR *CoordsToInterp::getREAL3_EXPR(coords::REAL3_EXPR *c) const
    {
        interp::REAL3_EXPR*interp = NULL;
        try {
            interp = coords2interp_REAL3_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_EXPR*)interp;
    }

void CoordsToInterp::putPAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c, interp::PAREN_REAL3_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::PAREN_REAL3_EXPR* CoordsToInterp::getPAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::PAREN_REAL3_EXPR*>(coo);
}
interp::PAREN_REAL3_EXPR* CoordsToInterp::getPAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, interp::ADD_REAL3_EXPR_REAL3_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::ADD_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(coo);
}
interp::ADD_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c, interp::SUB_REAL3_EXPR_REAL3_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::SUB_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::SUB_REAL3_EXPR_REAL3_EXPR*>(coo);
}
interp::SUB_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::SUB_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putINV_REAL3_EXPR(coords::INV_REAL3_EXPR* c, interp::INV_REAL3_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::INV_REAL3_EXPR* CoordsToInterp::getINV_REAL3_EXPR(interp::INV_REAL3_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::INV_REAL3_EXPR*>(coo);
}
interp::INV_REAL3_EXPR* CoordsToInterp::getINV_REAL3_EXPR(coords::INV_REAL3_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::INV_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c, interp::NEG_REAL3_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::NEG_REAL3_EXPR* CoordsToInterp::getNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::NEG_REAL3_EXPR*>(coo);
}
interp::NEG_REAL3_EXPR* CoordsToInterp::getNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::NEG_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c, interp::MUL_REAL3_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::MUL_REAL3_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MUL_REAL3_EXPR_REAL1_EXPR*>(coo);
}
interp::MUL_REAL3_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL3_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c, interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* CoordsToInterp::getMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(coo);
}
interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* CoordsToInterp::getMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c, interp::DIV_REAL3_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::DIV_REAL3_EXPR_REAL1_EXPR* CoordsToInterp::getDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::DIV_REAL3_EXPR_REAL1_EXPR*>(coo);
}
interp::DIV_REAL3_EXPR_REAL1_EXPR* CoordsToInterp::getDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DIV_REAL3_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREF_REAL3_VAR(coords::REF_REAL3_VAR* c, interp::REF_REAL3_VAR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::REF_REAL3_VAR* CoordsToInterp::getREF_REAL3_VAR(interp::REF_REAL3_VAR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REF_REAL3_VAR*>(coo);
}
interp::REF_REAL3_VAR* CoordsToInterp::getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL3_VAR*>(interp);
}

coords::REAL4_EXPR *CoordsToInterp::getREAL4_EXPR(interp::REAL4_EXPR *i) const
    {
        coords::REAL4_EXPR *coords = NULL;
        try {
            coords = interp2coords_REAL4_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL4_EXPR*)coords;
    }
interp::REAL4_EXPR *CoordsToInterp::getREAL4_EXPR(coords::REAL4_EXPR *c) const
    {
        interp::REAL4_EXPR*interp = NULL;
        try {
            interp = coords2interp_REAL4_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL4_EXPR*)interp;
    }

void CoordsToInterp::putPAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c, interp::PAREN_REAL4_EXPR* i)
{
    coords2interp_REAL4_EXPR[c] = (interp::REAL4_EXPR*)i;
    interp2coords_REAL4_EXPR[(interp::REAL4_EXPR*)i] = c;
}
coords::PAREN_REAL4_EXPR* CoordsToInterp::getPAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* i) const
{
    coords::REAL4_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL4_EXPR.at((interp::REAL4_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::PAREN_REAL4_EXPR*>(coo);
}
interp::PAREN_REAL4_EXPR* CoordsToInterp::getPAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL4_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REAL4_EXPR*>(interp);
}

void CoordsToInterp::putADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c, interp::ADD_REAL4_EXPR_REAL4_EXPR* i)
{
    coords2interp_REAL4_EXPR[c] = (interp::REAL4_EXPR*)i;
    interp2coords_REAL4_EXPR[(interp::REAL4_EXPR*)i] = c;
}
coords::ADD_REAL4_EXPR_REAL4_EXPR* CoordsToInterp::getADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* i) const
{
    coords::REAL4_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL4_EXPR.at((interp::REAL4_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(coo);
}
interp::ADD_REAL4_EXPR_REAL4_EXPR* CoordsToInterp::getADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL4_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL4_EXPR_REAL4_EXPR*>(interp);
}

void CoordsToInterp::putMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c, interp::MUL_REAL4_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL4_EXPR[c] = (interp::REAL4_EXPR*)i;
    interp2coords_REAL4_EXPR[(interp::REAL4_EXPR*)i] = c;
}
coords::MUL_REAL4_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* i) const
{
    coords::REAL4_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL4_EXPR.at((interp::REAL4_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MUL_REAL4_EXPR_REAL1_EXPR*>(coo);
}
interp::MUL_REAL4_EXPR_REAL1_EXPR* CoordsToInterp::getMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL4_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL4_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREF_REAL4_VAR(coords::REF_REAL4_VAR* c, interp::REF_REAL4_VAR* i)
{
    coords2interp_REAL4_EXPR[c] = (interp::REAL4_EXPR*)i;
    interp2coords_REAL4_EXPR[(interp::REAL4_EXPR*)i] = c;
}
coords::REF_REAL4_VAR* CoordsToInterp::getREF_REAL4_VAR(interp::REF_REAL4_VAR* i) const
{
    coords::REAL4_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL4_EXPR.at((interp::REAL4_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REF_REAL4_VAR*>(coo);
}
interp::REF_REAL4_VAR* CoordsToInterp::getREF_REAL4_VAR(coords::REF_REAL4_VAR* c) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL4_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL4_VAR*>(interp);
}

coords::REALMATRIX_EXPR *CoordsToInterp::getREALMATRIX_EXPR(interp::REALMATRIX_EXPR *i) const
    {
        coords::REALMATRIX_EXPR *coords = NULL;
        try {
            coords = interp2coords_REALMATRIX_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REALMATRIX_EXPR*)coords;
    }
interp::REALMATRIX_EXPR *CoordsToInterp::getREALMATRIX_EXPR(coords::REALMATRIX_EXPR *c) const
    {
        interp::REALMATRIX_EXPR*interp = NULL;
        try {
            interp = coords2interp_REALMATRIX_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REALMATRIX_EXPR*)interp;
    }

void CoordsToInterp::putPAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c, interp::PAREN_REALMATRIX_EXPR* i)
{
    coords2interp_REALMATRIX_EXPR[c] = (interp::REALMATRIX_EXPR*)i;
    interp2coords_REALMATRIX_EXPR[(interp::REALMATRIX_EXPR*)i] = c;
}
coords::PAREN_REALMATRIX_EXPR* CoordsToInterp::getPAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* i) const
{
    coords::REALMATRIX_EXPR* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_EXPR.at((interp::REALMATRIX_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::PAREN_REALMATRIX_EXPR*>(coo);
}
interp::PAREN_REALMATRIX_EXPR* CoordsToInterp::getPAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REALMATRIX_EXPR*>(interp);
}

void CoordsToInterp::putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c, interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* i)
{
    coords2interp_REALMATRIX_EXPR[c] = (interp::REALMATRIX_EXPR*)i;
    interp2coords_REALMATRIX_EXPR[(interp::REALMATRIX_EXPR*)i] = c;
}
coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* CoordsToInterp::getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* i) const
{
    coords::REALMATRIX_EXPR* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_EXPR.at((interp::REALMATRIX_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(coo);
}
interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* CoordsToInterp::getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(interp);
}

void CoordsToInterp::putREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c, interp::REF_EXPR_REALMATRIX_VAR* i)
{
    coords2interp_REALMATRIX_EXPR[c] = (interp::REALMATRIX_EXPR*)i;
    interp2coords_REALMATRIX_EXPR[(interp::REALMATRIX_EXPR*)i] = c;
}
coords::REF_EXPR_REALMATRIX_VAR* CoordsToInterp::getREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* i) const
{
    coords::REALMATRIX_EXPR* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_EXPR.at((interp::REALMATRIX_EXPR*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REF_EXPR_REALMATRIX_VAR*>(coo);
}
interp::REF_EXPR_REALMATRIX_VAR* CoordsToInterp::getREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_EXPR_REALMATRIX_VAR*>(interp);
}

void CoordsToInterp::putREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, interp::REAL1_VAR_IDENT* i)
{
    coords2interp_REAL1_VAR_IDENT[c] = (interp::REAL1_VAR_IDENT*)i;
    interp2coords_REAL1_VAR_IDENT[(interp::REAL1_VAR_IDENT*)i] = c;
}
coords::REAL1_VAR_IDENT* CoordsToInterp::getREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* i) const
{
    coords::REAL1_VAR_IDENT* coo = NULL;
    try {
        coo = interp2coords_REAL1_VAR_IDENT.at((interp::REAL1_VAR_IDENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL1_VAR_IDENT*>(coo);
}
interp::REAL1_VAR_IDENT* CoordsToInterp::getREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c) const
{
    interp::REAL1_VAR_IDENT *interp = NULL;
    try {
        interp = coords2interp_REAL1_VAR_IDENT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL1_VAR_IDENT*>(interp);
}

void CoordsToInterp::putREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, interp::REAL3_VAR_IDENT* i)
{
    coords2interp_REAL3_VAR_IDENT[c] = (interp::REAL3_VAR_IDENT*)i;
    interp2coords_REAL3_VAR_IDENT[(interp::REAL3_VAR_IDENT*)i] = c;
}
coords::REAL3_VAR_IDENT* CoordsToInterp::getREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* i) const
{
    coords::REAL3_VAR_IDENT* coo = NULL;
    try {
        coo = interp2coords_REAL3_VAR_IDENT.at((interp::REAL3_VAR_IDENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL3_VAR_IDENT*>(coo);
}
interp::REAL3_VAR_IDENT* CoordsToInterp::getREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c) const
{
    interp::REAL3_VAR_IDENT *interp = NULL;
    try {
        interp = coords2interp_REAL3_VAR_IDENT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_VAR_IDENT*>(interp);
}

void CoordsToInterp::putREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c, interp::REAL4_VAR_IDENT* i)
{
    coords2interp_REAL4_VAR_IDENT[c] = (interp::REAL4_VAR_IDENT*)i;
    interp2coords_REAL4_VAR_IDENT[(interp::REAL4_VAR_IDENT*)i] = c;
}
coords::REAL4_VAR_IDENT* CoordsToInterp::getREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* i) const
{
    coords::REAL4_VAR_IDENT* coo = NULL;
    try {
        coo = interp2coords_REAL4_VAR_IDENT.at((interp::REAL4_VAR_IDENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL4_VAR_IDENT*>(coo);
}
interp::REAL4_VAR_IDENT* CoordsToInterp::getREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c) const
{
    interp::REAL4_VAR_IDENT *interp = NULL;
    try {
        interp = coords2interp_REAL4_VAR_IDENT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL4_VAR_IDENT*>(interp);
}

void CoordsToInterp::putREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c, interp::REALMATRIX_VAR_IDENT* i)
{
    coords2interp_REALMATRIX_VAR_IDENT[c] = (interp::REALMATRIX_VAR_IDENT*)i;
    interp2coords_REALMATRIX_VAR_IDENT[(interp::REALMATRIX_VAR_IDENT*)i] = c;
}
coords::REALMATRIX_VAR_IDENT* CoordsToInterp::getREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* i) const
{
    coords::REALMATRIX_VAR_IDENT* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_VAR_IDENT.at((interp::REALMATRIX_VAR_IDENT*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REALMATRIX_VAR_IDENT*>(coo);
}
interp::REALMATRIX_VAR_IDENT* CoordsToInterp::getREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c) const
{
    interp::REALMATRIX_VAR_IDENT *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_VAR_IDENT.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_VAR_IDENT*>(interp);
}

coords::REAL1_LITERAL *CoordsToInterp::getREAL1_LITERAL(interp::REAL1_LITERAL *i) const
    {
        coords::REAL1_EXPR *coords = NULL;
        try {
            coords = interp2coords_REAL1_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_LITERAL*)coords;
    }
interp::REAL1_LITERAL *CoordsToInterp::getREAL1_LITERAL(coords::REAL1_LITERAL *c) const
    {
        interp::REAL1_EXPR*interp = NULL;
        try {
            interp = coords2interp_REAL1_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_LITERAL*)interp;
    }

void CoordsToInterp::putREAL1_LITERAL1(coords::REAL1_LITERAL1* c, interp::REAL1_LITERAL1* i)
{
    coords2interp_REAL1_EXPR[c] = (interp::REAL1_EXPR*)i;
    interp2coords_REAL1_EXPR[(interp::REAL1_EXPR*)i] = c;
}
coords::REAL1_LITERAL1* CoordsToInterp::getREAL1_LITERAL1(interp::REAL1_LITERAL1* i) const
{
    coords::REAL1_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL1_EXPR.at((interp::REAL1_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL1_LITERAL1*>(coo);
}
interp::REAL1_LITERAL1* CoordsToInterp::getREAL1_LITERAL1(coords::REAL1_LITERAL1* c) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL1_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL1_LITERAL1*>(interp);
}

coords::REAL3_LITERAL *CoordsToInterp::getREAL3_LITERAL(interp::REAL3_LITERAL *i) const
    {
        coords::REAL3_EXPR *coords = NULL;
        try {
            coords = interp2coords_REAL3_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_LITERAL*)coords;
    }
interp::REAL3_LITERAL *CoordsToInterp::getREAL3_LITERAL(coords::REAL3_LITERAL *c) const
    {
        interp::REAL3_EXPR*interp = NULL;
        try {
            interp = coords2interp_REAL3_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_LITERAL*)interp;
    }

void CoordsToInterp::putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREAL3_LITERAL3(coords::REAL3_LITERAL3* c, interp::REAL3_LITERAL3* i)
{
    coords2interp_REAL3_EXPR[c] = (interp::REAL3_EXPR*)i;
    interp2coords_REAL3_EXPR[(interp::REAL3_EXPR*)i] = c;
}
coords::REAL3_LITERAL3* CoordsToInterp::getREAL3_LITERAL3(interp::REAL3_LITERAL3* i) const
{
    coords::REAL3_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL3_EXPR.at((interp::REAL3_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL3_LITERAL3*>(coo);
}
interp::REAL3_LITERAL3* CoordsToInterp::getREAL3_LITERAL3(coords::REAL3_LITERAL3* c) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL3_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_LITERAL3*>(interp);
}

coords::REAL4_LITERAL *CoordsToInterp::getREAL4_LITERAL(interp::REAL4_LITERAL *i) const
    {
        coords::REAL4_EXPR *coords = NULL;
        try {
            coords = interp2coords_REAL4_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL4_LITERAL*)coords;
    }
interp::REAL4_LITERAL *CoordsToInterp::getREAL4_LITERAL(coords::REAL4_LITERAL *c) const
    {
        interp::REAL4_EXPR*interp = NULL;
        try {
            interp = coords2interp_REAL4_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL4_LITERAL*)interp;
    }

void CoordsToInterp::putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REAL4_EXPR[c] = (interp::REAL4_EXPR*)i;
    interp2coords_REAL4_EXPR[(interp::REAL4_EXPR*)i] = c;
}
coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REAL4_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL4_EXPR.at((interp::REAL4_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL4_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREAL4_LITERAL4(coords::REAL4_LITERAL4* c, interp::REAL4_LITERAL4* i)
{
    coords2interp_REAL4_EXPR[c] = (interp::REAL4_EXPR*)i;
    interp2coords_REAL4_EXPR[(interp::REAL4_EXPR*)i] = c;
}
coords::REAL4_LITERAL4* CoordsToInterp::getREAL4_LITERAL4(interp::REAL4_LITERAL4* i) const
{
    coords::REAL4_EXPR* coo = NULL;
    try {
        coo = interp2coords_REAL4_EXPR.at((interp::REAL4_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REAL4_LITERAL4*>(coo);
}
interp::REAL4_LITERAL4* CoordsToInterp::getREAL4_LITERAL4(coords::REAL4_LITERAL4* c) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = coords2interp_REAL4_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL4_LITERAL4*>(interp);
}

coords::REALMATRIX_LITERAL *CoordsToInterp::getREALMATRIX_LITERAL(interp::REALMATRIX_LITERAL *i) const
    {
        coords::REALMATRIX_EXPR *coords = NULL;
        try {
            coords = interp2coords_REALMATRIX_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REALMATRIX_LITERAL*)coords;
    }
interp::REALMATRIX_LITERAL *CoordsToInterp::getREALMATRIX_LITERAL(coords::REALMATRIX_LITERAL *c) const
    {
        interp::REALMATRIX_EXPR*interp = NULL;
        try {
            interp = coords2interp_REALMATRIX_EXPR.at(c);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REALMATRIX_LITERAL*)interp;
    }

void CoordsToInterp::putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c, interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* i)
{
    coords2interp_REALMATRIX_EXPR[c] = (interp::REALMATRIX_EXPR*)i;
    interp2coords_REALMATRIX_EXPR[(interp::REALMATRIX_EXPR*)i] = c;
}
coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* i) const
{
    coords::REALMATRIX_EXPR* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_EXPR.at((interp::REALMATRIX_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(coo);
}
interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* CoordsToInterp::getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void CoordsToInterp::putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i)
{
    coords2interp_REALMATRIX_EXPR[c] = (interp::REALMATRIX_EXPR*)i;
    interp2coords_REALMATRIX_EXPR[(interp::REALMATRIX_EXPR*)i] = c;
}
coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    coords::REALMATRIX_EXPR* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_EXPR.at((interp::REALMATRIX_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coo);
}
interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToInterp::getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void CoordsToInterp::putREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c, interp::REALMATRIX_LITERAL9* i)
{
    coords2interp_REALMATRIX_EXPR[c] = (interp::REALMATRIX_EXPR*)i;
    interp2coords_REALMATRIX_EXPR[(interp::REALMATRIX_EXPR*)i] = c;
}
coords::REALMATRIX_LITERAL9* CoordsToInterp::getREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* i) const
{
    coords::REALMATRIX_EXPR* coo = NULL;
    try {
        coo = interp2coords_REALMATRIX_EXPR.at((interp::REALMATRIX_LITERAL*)i);
    }
    catch (std::out_of_range &e) {
        coo = NULL;
    }
    return static_cast<coords::REALMATRIX_LITERAL9*>(coo);
}
interp::REALMATRIX_LITERAL9* CoordsToInterp::getREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = coords2interp_REALMATRIX_EXPR.at(c);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_LITERAL9*>(interp);
}
