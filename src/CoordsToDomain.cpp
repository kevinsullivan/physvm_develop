
#include "CoordsToDomain.h"

# include <iostream>

//# include <g3log/g3log.hpp>



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

coords::WHILE *CoordsToDomain::getWHILE(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::WHILE *)coords;
    }
domain::DomainObject *CoordsToDomain::getWHILE(coords::WHILE *c) const
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

void CoordsToDomain::putWHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseWHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getWHILE_BOOL_EXPR_STMT(coords::WHILE_BOOL_EXPR_STMT* c) const
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
coords::WHILE_BOOL_EXPR_STMT* CoordsToDomain::getWHILE_BOOL_EXPR_STMT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::WHILE_BOOL_EXPR_STMT*>(coords);
}

coords::TRY *CoordsToDomain::getTRY(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::TRY *)coords;
    }
domain::DomainObject *CoordsToDomain::getTRY(coords::TRY *c) const
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

void CoordsToDomain::putTRY_STMT(coords::TRY_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseTRY_STMT(coords::TRY_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getTRY_STMT(coords::TRY_STMT* c) const
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
coords::TRY_STMT* CoordsToDomain::getTRY_STMT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::TRY_STMT*>(coords);
}

coords::FOR *CoordsToDomain::getFOR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::FOR *)coords;
    }
domain::DomainObject *CoordsToDomain::getFOR(coords::FOR *c) const
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

void CoordsToDomain::putFOR_BOOL_EXPR_STMT(coords::FOR_BOOL_EXPR_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseFOR_BOOL_EXPR_STMT(coords::FOR_BOOL_EXPR_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getFOR_BOOL_EXPR_STMT(coords::FOR_BOOL_EXPR_STMT* c) const
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
coords::FOR_BOOL_EXPR_STMT* CoordsToDomain::getFOR_BOOL_EXPR_STMT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::FOR_BOOL_EXPR_STMT*>(coords);
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

void CoordsToDomain::putDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const
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
coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR* CoordsToDomain::getDECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR*>(coords);
}

void CoordsToDomain::putDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REAL4_VAR_REAL4_EXPR(coords::DECL_REAL4_VAR_REAL4_EXPR* c) const
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
coords::DECL_REAL4_VAR_REAL4_EXPR* CoordsToDomain::getDECL_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REAL4_VAR_REAL4_EXPR*>(coords);
}

void CoordsToDomain::putDECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_BOOL_VAR_BOOL_EXPR(coords::DECL_BOOL_VAR_BOOL_EXPR* c) const
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
coords::DECL_BOOL_VAR_BOOL_EXPR* CoordsToDomain::getDECL_BOOL_VAR_BOOL_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_BOOL_VAR_BOOL_EXPR*>(coords);
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

void CoordsToDomain::putDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REALMATRIX4_VAR(coords::DECL_REALMATRIX4_VAR* c) const
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
coords::DECL_REALMATRIX4_VAR* CoordsToDomain::getDECL_REALMATRIX4_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REALMATRIX4_VAR*>(coords);
}

void CoordsToDomain::putDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REAL4_VAR(coords::DECL_REAL4_VAR* c) const
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
coords::DECL_REAL4_VAR* CoordsToDomain::getDECL_REAL4_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REAL4_VAR*>(coords);
}

void CoordsToDomain::putDECL_BOOL_VAR(coords::DECL_BOOL_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_BOOL_VAR(coords::DECL_BOOL_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_BOOL_VAR(coords::DECL_BOOL_VAR* c) const
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
coords::DECL_BOOL_VAR* CoordsToDomain::getDECL_BOOL_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_BOOL_VAR*>(coords);
}

coords::ASSIGN *CoordsToDomain::getASSIGN(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::ASSIGN *)coords;
    }
domain::DomainObject *CoordsToDomain::getASSIGN(coords::ASSIGN *c) const
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

void CoordsToDomain::putASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASNR1_REAL1_VAR_REAL1_EXPR(coords::ASNR1_REAL1_VAR_REAL1_EXPR* c) const
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
coords::ASNR1_REAL1_VAR_REAL1_EXPR* CoordsToDomain::getASNR1_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASNR1_REAL1_VAR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASNR3_REAL3_VAR_REAL3_EXPR(coords::ASNR3_REAL3_VAR_REAL3_EXPR* c) const
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
coords::ASNR3_REAL3_VAR_REAL3_EXPR* CoordsToDomain::getASNR3_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASNR3_REAL3_VAR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* c) const
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
coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR* CoordsToDomain::getASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASNM4_REALMATRIX4_VAR_REALMATRIX4_EXPR*>(coords);
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

coords::BOOL_EXPR *CoordsToDomain::getBOOL_EXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::BOOL_EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getBOOL_EXPR(coords::BOOL_EXPR *c) const
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

void CoordsToDomain::putREF_BOOL_VAR(coords::REF_BOOL_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREF_BOOL_VAR(coords::REF_BOOL_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_BOOL_VAR(coords::REF_BOOL_VAR* c) const
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
coords::REF_BOOL_VAR* CoordsToDomain::getREF_BOOL_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_BOOL_VAR*>(coords);
}

coords::REALMATRIX4_EXPR *CoordsToDomain::getREALMATRIX4_EXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REALMATRIX4_EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREALMATRIX4_EXPR(coords::REALMATRIX4_EXPR *c) const
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

void CoordsToDomain::putREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REALMATRIX4_VAR(coords::REF_REALMATRIX4_VAR* c) const
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
coords::REF_REALMATRIX4_VAR* CoordsToDomain::getREF_REALMATRIX4_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REALMATRIX4_VAR*>(coords);
}

void CoordsToDomain::putMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* c) const
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
coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR* CoordsToDomain::getMUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR*>(coords);
}

coords::REAL4_EXPR *CoordsToDomain::getREAL4_EXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL4_EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL4_EXPR(coords::REAL4_EXPR *c) const
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

void CoordsToDomain::putREF_REAL4_VAR(coords::REF_REAL4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREF_REAL4_VAR(coords::REF_REAL4_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REAL4_VAR(coords::REF_REAL4_VAR* c) const
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
coords::REF_REAL4_VAR* CoordsToDomain::getREF_REAL4_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REAL4_VAR*>(coords);
}

void CoordsToDomain::putADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c) const
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
coords::ADD_REAL4_EXPR_REAL4_EXPR* CoordsToDomain::getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseMUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REAL4_EXPR_REAL4_EXPR(coords::MUL_REAL4_EXPR_REAL4_EXPR* c) const
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
coords::MUL_REAL4_EXPR_REAL4_EXPR* CoordsToDomain::getMUL_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REAL4_EXPR_REAL4_EXPR*>(coords);
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

void CoordsToDomain::putTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* c) const
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
coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR* CoordsToDomain::getTMUL_REALMATRIX4_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::TMUL_REALMATRIX4_EXPR_REAL3_EXPR*>(coords);
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

void CoordsToDomain::putBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_BOOL_VAR_IDENT[(coords::BOOL_VAR_IDENT*)c] = d;
    dom2coords_BOOL_VAR_IDENT[d] = c;
}
domain::DomainObject* CoordsToDomain::getBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_BOOL_VAR_IDENT.at((coords::BOOL_VAR_IDENT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::BOOL_VAR_IDENT* CoordsToDomain::getBOOL_VAR_IDENT(domain::DomainObject* d) const
{
    coords::BOOL_VAR_IDENT *coords = NULL;
    try {
        coords = dom2coords_BOOL_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::BOOL_VAR_IDENT*>(coords);
}
void CoordsToDomain::eraseBOOL_VAR_IDENT(coords::BOOL_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_BOOL_VAR_IDENT.erase((coords::BOOL_VAR_IDENT*)c);
    dom2coords_BOOL_VAR_IDENT.erase(d);
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

void CoordsToDomain::putREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REAL4_VAR_IDENT[(coords::REAL4_VAR_IDENT*)c] = d;
    dom2coords_REAL4_VAR_IDENT[d] = c;
}
domain::DomainObject* CoordsToDomain::getREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_VAR_IDENT.at((coords::REAL4_VAR_IDENT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL4_VAR_IDENT* CoordsToDomain::getREAL4_VAR_IDENT(domain::DomainObject* d) const
{
    coords::REAL4_VAR_IDENT *coords = NULL;
    try {
        coords = dom2coords_REAL4_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL4_VAR_IDENT*>(coords);
}
void CoordsToDomain::eraseREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REAL4_VAR_IDENT.erase((coords::REAL4_VAR_IDENT*)c);
    dom2coords_REAL4_VAR_IDENT.erase(d);
}

void CoordsToDomain::putREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX4_VAR_IDENT[(coords::REALMATRIX4_VAR_IDENT*)c] = d;
    dom2coords_REALMATRIX4_VAR_IDENT[d] = c;
}
domain::DomainObject* CoordsToDomain::getREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX4_VAR_IDENT.at((coords::REALMATRIX4_VAR_IDENT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REALMATRIX4_VAR_IDENT* CoordsToDomain::getREALMATRIX4_VAR_IDENT(domain::DomainObject* d) const
{
    coords::REALMATRIX4_VAR_IDENT *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX4_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX4_VAR_IDENT*>(coords);
}
void CoordsToDomain::eraseREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX4_VAR_IDENT.erase((coords::REALMATRIX4_VAR_IDENT*)c);
    dom2coords_REALMATRIX4_VAR_IDENT.erase(d);
}

coords::REAL4_LITERAL *CoordsToDomain::getREAL4_LITERAL(domain::DomainObject *d) const
    {
        coords::REAL4_LITERAL *coords = NULL;
        try {
            coords = dom2coords_REAL4_LITERAL.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REAL4_LITERAL *)coords;
    }
domain::DomainObject *CoordsToDomain::getREAL4_LITERAL(coords::REAL4_LITERAL *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_REAL4_LITERAL.at((coords::REAL4_LITERAL*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREAL4_EMPTY(coords::REAL4_EMPTY* c, domain::DomainObject *d)
{
    coords2dom_REAL4_LITERAL[(coords::REAL4_LITERAL*)c] = d;
    dom2coords_REAL4_LITERAL[d] = (coords::REAL4_LITERAL*)c;
}
void CoordsToDomain::eraseREAL4_EMPTY(coords::REAL4_EMPTY* c, domain::DomainObject *d)
{
    coords2dom_REAL4_LITERAL.erase((coords::REAL4_LITERAL*)c);
    dom2coords_REAL4_LITERAL.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL4_EMPTY(coords::REAL4_EMPTY* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_LITERAL.at((coords::REAL4_LITERAL*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL4_EMPTY* CoordsToDomain::getREAL4_EMPTY(domain::DomainObject* d) const
{
    coords::REAL4_LITERAL *coords = NULL;
    try {
        coords = dom2coords_REAL4_LITERAL.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL4_EMPTY*>(coords);
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

coords::REALMATRIX4_LITERAL *CoordsToDomain::getREALMATRIX4_LITERAL(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REALMATRIX4_LITERAL *)coords;
    }
domain::DomainObject *CoordsToDomain::getREALMATRIX4_LITERAL(coords::REALMATRIX4_LITERAL *c) const
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

void CoordsToDomain::putREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREALMATRIX4_EMPTY(coords::REALMATRIX4_EMPTY* c) const
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
coords::REALMATRIX4_EMPTY* CoordsToDomain::getREALMATRIX4_EMPTY(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX4_EMPTY*>(coords);
}

void CoordsToDomain::putREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* c) const
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
coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR* CoordsToDomain::getREALMATRIX4_EMPTY2_REALMATRIX4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX4_EMPTY2_REALMATRIX4_EXPR*>(coords);
}

void CoordsToDomain::putR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* c) const
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
coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR* CoordsToDomain::getR4R3_LIT_REAL4_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::R4R3_LIT_REAL4_EXPR_REAL3_EXPR*>(coords);
}

coords::SINK *CoordsToDomain::getSINK(domain::DomainObject *d) const
    {
        coords::SINK *coords = NULL;
        try {
            coords = dom2coords_SINK.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::SINK *)coords;
    }
domain::DomainObject *CoordsToDomain::getSINK(coords::SINK *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_SINK.at((coords::SINK*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putIGNORE(coords::IGNORE* c, domain::DomainObject *d)
{
    coords2dom_SINK[(coords::SINK*)c] = d;
    dom2coords_SINK[d] = (coords::SINK*)c;
}
void CoordsToDomain::eraseIGNORE(coords::IGNORE* c, domain::DomainObject *d)
{
    coords2dom_SINK.erase((coords::SINK*)c);
    dom2coords_SINK.erase(d);
}
domain::DomainObject* CoordsToDomain::getIGNORE(coords::IGNORE* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_SINK.at((coords::SINK*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::IGNORE* CoordsToDomain::getIGNORE(domain::DomainObject* d) const
{
    coords::SINK *coords = NULL;
    try {
        coords = dom2coords_SINK.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::IGNORE*>(coords);
}

coords::BOOL_LITERAL *CoordsToDomain::getBOOL_LITERAL(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::BOOL_LITERAL *)coords;
    }
domain::DomainObject *CoordsToDomain::getBOOL_LITERAL(coords::BOOL_LITERAL *c) const
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

void CoordsToDomain::putBOOL_LIT(coords::BOOL_LIT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseBOOL_LIT(coords::BOOL_LIT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getBOOL_LIT(coords::BOOL_LIT* c) const
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
coords::BOOL_LIT* CoordsToDomain::getBOOL_LIT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::BOOL_LIT*>(coords);
}
