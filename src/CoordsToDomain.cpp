
#include "CoordsToDomain.h"

# include <iostream>

# include <g3log/g3log.hpp>



//using namespace std;
using namespace coords2domain;

coords::PROGRAM *CoordsToDomain::getPROGRAM(domain::DomainObject *d) const
    {
        coords::PROGRAM *coords = NULL;
        try {
            coords = dom2coords_PROGRAM.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::PROGRAM *)coords;
    }
domain::DomainObject *CoordsToDomain::getPROGRAM(coords::PROGRAM *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_PROGRAM.at((coords::PROGRAM*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c, domain::DomainObject *d)
{
    coords2dom_PROGRAM[(coords::PROGRAM*)c] = d;
    dom2coords_PROGRAM[d] = (coords::PROGRAM*)c;
}
void CoordsToDomain::eraseSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c, domain::DomainObject *d)
{
    coords2dom_PROGRAM.erase((coords::PROGRAM*)c);
    dom2coords_PROGRAM.erase(d);
}
domain::DomainObject* CoordsToDomain::getSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_PROGRAM.at((coords::PROGRAM*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::SEQ_GLOBALSTMT* CoordsToDomain::getSEQ_GLOBALSTMT(domain::DomainObject* d) const
{
    coords::PROGRAM *coords = NULL;
    try {
        coords = dom2coords_PROGRAM.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::SEQ_GLOBALSTMT*>(coords);
}

coords::GLOBALSTMT *CoordsToDomain::getGLOBALSTMT(domain::DomainObject *d) const
    {
        coords::GLOBALSTMT *coords = NULL;
        try {
            coords = dom2coords_GLOBALSTMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::GLOBALSTMT *)coords;
    }
domain::DomainObject *CoordsToDomain::getGLOBALSTMT(coords::GLOBALSTMT *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_GLOBALSTMT.at((coords::GLOBALSTMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

coords::STMT *CoordsToDomain::getSTMT(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::STMT *)coords;
    }
domain::DomainObject *CoordsToDomain::getSTMT(coords::STMT *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putCOMPOUND_STMT(coords::COMPOUND_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseCOMPOUND_STMT(coords::COMPOUND_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getCOMPOUND_STMT(coords::COMPOUND_STMT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::COMPOUND_STMT* CoordsToDomain::getCOMPOUND_STMT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::COMPOUND_STMT*>(coords);
}

coords::FUNC_DECL *CoordsToDomain::getFUNC_DECL(domain::DomainObject *d) const
    {
        coords::GLOBALSTMT *coords = NULL;
        try {
            coords = dom2coords_GLOBALSTMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::FUNC_DECL *)coords;
    }
domain::DomainObject *CoordsToDomain::getFUNC_DECL(coords::FUNC_DECL *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_GLOBALSTMT.at((coords::GLOBALSTMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c, domain::DomainObject *d)
{
    coords2dom_GLOBALSTMT[(coords::GLOBALSTMT*)c] = d;
    dom2coords_GLOBALSTMT[d] = c;
}
domain::DomainObject* CoordsToDomain::getVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_GLOBALSTMT.at((coords::GLOBALSTMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::VOID_FUNC_DECL_STMT* CoordsToDomain::getVOID_FUNC_DECL_STMT(domain::DomainObject* d) const
{
    coords::GLOBALSTMT *coords = NULL;
    try {
        coords = dom2coords_GLOBALSTMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::VOID_FUNC_DECL_STMT*>(coords);
}
void CoordsToDomain::eraseVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c, domain::DomainObject *d)
{
    coords2dom_GLOBALSTMT.erase((coords::GLOBALSTMT*)c);
    dom2coords_GLOBALSTMT.erase(d);
}

void CoordsToDomain::putMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c, domain::DomainObject *d)
{
    coords2dom_GLOBALSTMT[(coords::GLOBALSTMT*)c] = d;
    dom2coords_GLOBALSTMT[d] = c;
}
domain::DomainObject* CoordsToDomain::getMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_GLOBALSTMT.at((coords::GLOBALSTMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MAIN_FUNC_DECL_STMT* CoordsToDomain::getMAIN_FUNC_DECL_STMT(domain::DomainObject* d) const
{
    coords::GLOBALSTMT *coords = NULL;
    try {
        coords = dom2coords_GLOBALSTMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MAIN_FUNC_DECL_STMT*>(coords);
}
void CoordsToDomain::eraseMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c, domain::DomainObject *d)
{
    coords2dom_GLOBALSTMT.erase((coords::GLOBALSTMT*)c);
    dom2coords_GLOBALSTMT.erase(d);
}

coords::DECLARE *CoordsToDomain::getDECLARE(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::DECLARE *)coords;
    }
domain::DomainObject *CoordsToDomain::getDECLARE(coords::DECLARE *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REAL1_VAR_REAL1_EXPR(coords::DECL_REAL1_VAR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::DECL_REAL1_VAR_REAL1_EXPR* CoordsToDomain::getDECL_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REAL1_VAR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REAL3_VAR_REAL3_EXPR(coords::DECL_REAL3_VAR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::DECL_REAL3_VAR_REAL3_EXPR* CoordsToDomain::getDECL_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REAL3_VAR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REAL1_VAR(coords::DECL_REAL1_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::DECL_REAL1_VAR* CoordsToDomain::getDECL_REAL1_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REAL1_VAR*>(coords);
}

void CoordsToDomain::putDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REAL3_VAR(coords::DECL_REAL3_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::DECL_REAL3_VAR* CoordsToDomain::getDECL_REAL3_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REAL3_VAR*>(coords);
}

coords::REXPR *CoordsToDomain::getREXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREXPR(coords::REXPR *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

coords::LEXPR *CoordsToDomain::getLEXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::LEXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getLEXPR(coords::LEXPR *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

coords::REAL3_EXPR *CoordsToDomain::getREAL3_EXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL3_EXPR(coords::REAL3_EXPR *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREF_REAL3_VAR(coords::REF_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREF_REAL3_VAR(coords::REF_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REF_REAL3_VAR* CoordsToDomain::getREF_REAL3_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REAL3_VAR*>(coords);
}

void CoordsToDomain::putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::ADD_REAL3_EXPR_REAL3_EXPR* CoordsToDomain::getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getLMUL_REAL1_EXPR_REAL3_EXPR(coords::LMUL_REAL1_EXPR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::LMUL_REAL1_EXPR_REAL3_EXPR* CoordsToDomain::getLMUL_REAL1_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::LMUL_REAL1_EXPR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getRMUL_REAL3_EXPR_REAL1_EXPR(coords::RMUL_REAL3_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::RMUL_REAL3_EXPR_REAL1_EXPR* CoordsToDomain::getRMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::RMUL_REAL3_EXPR_REAL1_EXPR*>(coords);
}

coords::REAL3_LEXPR *CoordsToDomain::getREAL3_LEXPR(domain::DomainObject *d) const
    {
        coords::REAL3_LEXPR *coords = NULL;
        try {
            coords = dom2coords_REAL3_LEXPR.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_LEXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL3_LEXPR(coords::REAL3_LEXPR *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_REAL3_LEXPR.at((coords::REAL3_LEXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_LEXPR[(coords::REAL3_LEXPR*)c] = d;
    dom2coords_REAL3_LEXPR[d] = (coords::REAL3_LEXPR*)c;
}
void CoordsToDomain::eraseLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_LEXPR.erase((coords::REAL3_LEXPR*)c);
    dom2coords_REAL3_LEXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getLREF_REAL3_VAR(coords::LREF_REAL3_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_LEXPR.at((coords::REAL3_LEXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::LREF_REAL3_VAR* CoordsToDomain::getLREF_REAL3_VAR(domain::DomainObject* d) const
{
    coords::REAL3_LEXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_LEXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::LREF_REAL3_VAR*>(coords);
}

coords::REAL1_EXPR *CoordsToDomain::getREAL1_EXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL1_EXPR(coords::REAL1_EXPR *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREF_REAL1_VAR(coords::REF_REAL1_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREF_REAL1_VAR(coords::REF_REAL1_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REF_REAL1_VAR* CoordsToDomain::getREF_REAL1_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REAL1_VAR*>(coords);
}

void CoordsToDomain::putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::ADD_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MUL_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REAL1_VAR_IDENT[(coords::REAL1_VAR_IDENT*)c] = d;
    dom2coords_REAL1_VAR_IDENT[d] = c;
}
domain::DomainObject* CoordsToDomain::getREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_VAR_IDENT.at((coords::REAL1_VAR_IDENT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL1_VAR_IDENT* CoordsToDomain::getREAL1_VAR_IDENT(domain::DomainObject* d) const
{
    coords::REAL1_VAR_IDENT *coords = NULL;
    try {
        coords = dom2coords_REAL1_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL1_VAR_IDENT*>(coords);
}
void CoordsToDomain::eraseREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REAL1_VAR_IDENT.erase((coords::REAL1_VAR_IDENT*)c);
    dom2coords_REAL1_VAR_IDENT.erase(d);
}

void CoordsToDomain::putREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REAL3_VAR_IDENT[(coords::REAL3_VAR_IDENT*)c] = d;
    dom2coords_REAL3_VAR_IDENT[d] = c;
}
domain::DomainObject* CoordsToDomain::getREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_VAR_IDENT.at((coords::REAL3_VAR_IDENT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL3_VAR_IDENT* CoordsToDomain::getREAL3_VAR_IDENT(domain::DomainObject* d) const
{
    coords::REAL3_VAR_IDENT *coords = NULL;
    try {
        coords = dom2coords_REAL3_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL3_VAR_IDENT*>(coords);
}
void CoordsToDomain::eraseREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REAL3_VAR_IDENT.erase((coords::REAL3_VAR_IDENT*)c);
    dom2coords_REAL3_VAR_IDENT.erase(d);
}

coords::REAL3_LITERAL *CoordsToDomain::getREAL3_LITERAL(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL3_LITERAL *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL3_LITERAL(coords::REAL3_LITERAL *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREAL3_EMPTY(coords::REAL3_EMPTY* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREAL3_EMPTY(coords::REAL3_EMPTY* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL3_EMPTY(coords::REAL3_EMPTY* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL3_EMPTY* CoordsToDomain::getREAL3_EMPTY(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL3_EMPTY*>(coords);
}

coords::REAL1_LITERAL *CoordsToDomain::getREAL1_LITERAL(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL1_LITERAL *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL1_LITERAL(coords::REAL1_LITERAL *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_STMT.at((coords::STMT*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREAL1_LIT(coords::REAL1_LIT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREAL1_LIT(coords::REAL1_LIT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL1_LIT(coords::REAL1_LIT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_STMT.at((coords::STMT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL1_LIT* CoordsToDomain::getREAL1_LIT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL1_LIT*>(coords);
}
