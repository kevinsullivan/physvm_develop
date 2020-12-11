
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
