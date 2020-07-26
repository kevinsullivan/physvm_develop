
#include "CoordsToDomain.h"

# include <iostream>

# include <g3log/g3log.hpp>



//using namespace std;
using namespace coords2domain;

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

coords::IFCOND *CoordsToDomain::getIFCOND(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::IFCOND *)coords;
    }
domain::DomainObject *CoordsToDomain::getIFCOND(coords::IFCOND *c) const
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

void CoordsToDomain::putIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getIFTHEN_EXPR_STMT(coords::IFTHEN_EXPR_STMT* c) const
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
coords::IFTHEN_EXPR_STMT* CoordsToDomain::getIFTHEN_EXPR_STMT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::IFTHEN_EXPR_STMT*>(coords);
}

void CoordsToDomain::putIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getIFTHENELSEIF_EXPR_STMT_IFCOND(coords::IFTHENELSEIF_EXPR_STMT_IFCOND* c) const
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
coords::IFTHENELSEIF_EXPR_STMT_IFCOND* CoordsToDomain::getIFTHENELSEIF_EXPR_STMT_IFCOND(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::IFTHENELSEIF_EXPR_STMT_IFCOND*>(coords);
}

void CoordsToDomain::putIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getIFTHENELSE_EXPR_STMT_STMT(coords::IFTHENELSE_EXPR_STMT_STMT* c) const
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
coords::IFTHENELSE_EXPR_STMT_STMT* CoordsToDomain::getIFTHENELSE_EXPR_STMT_STMT(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::IFTHENELSE_EXPR_STMT_STMT*>(coords);
}

coords::EXPR *CoordsToDomain::getEXPR(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getEXPR(coords::EXPR *c) const
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

coords::ASSIGNMENT *CoordsToDomain::getASSIGNMENT(domain::DomainObject *d) const
    {
        coords::STMT *coords = NULL;
        try {
            coords = dom2coords_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::ASSIGNMENT *)coords;
    }
domain::DomainObject *CoordsToDomain::getASSIGNMENT(coords::ASSIGNMENT *c) const
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

void CoordsToDomain::putASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASSIGN_REAL1_VAR_REAL1_EXPR(coords::ASSIGN_REAL1_VAR_REAL1_EXPR* c) const
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
coords::ASSIGN_REAL1_VAR_REAL1_EXPR* CoordsToDomain::getASSIGN_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASSIGN_REAL1_VAR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASSIGN_REAL3_VAR_REAL3_EXPR(coords::ASSIGN_REAL3_VAR_REAL3_EXPR* c) const
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
coords::ASSIGN_REAL3_VAR_REAL3_EXPR* CoordsToDomain::getASSIGN_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASSIGN_REAL3_VAR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASSIGN_REAL4_VAR_REAL4_EXPR(coords::ASSIGN_REAL4_VAR_REAL4_EXPR* c) const
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
coords::ASSIGN_REAL4_VAR_REAL4_EXPR* CoordsToDomain::getASSIGN_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASSIGN_REAL4_VAR_REAL4_EXPR*>(coords);
}

void CoordsToDomain::putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* c) const
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
coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* CoordsToDomain::getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR*>(coords);
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

void CoordsToDomain::putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* c) const
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
coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* CoordsToDomain::getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REALMATRIX_VAR_REALMATRIX_EXPR*>(coords);
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

void CoordsToDomain::putDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT[(coords::STMT*)c] = d;
    dom2coords_STMT[d] = (coords::STMT*)c;
}
void CoordsToDomain::eraseDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c, domain::DomainObject *d)
{
    coords2dom_STMT.erase((coords::STMT*)c);
    dom2coords_STMT.erase(d);
}
domain::DomainObject* CoordsToDomain::getDECL_REALMATRIX_VAR(coords::DECL_REALMATRIX_VAR* c) const
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
coords::DECL_REALMATRIX_VAR* CoordsToDomain::getDECL_REALMATRIX_VAR(domain::DomainObject* d) const
{
    coords::STMT *coords = NULL;
    try {
        coords = dom2coords_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DECL_REALMATRIX_VAR*>(coords);
}

coords::REAL1_EXPR *CoordsToDomain::getREAL1_EXPR(domain::DomainObject *d) const
    {
        coords::REAL1_EXPR *coords = NULL;
        try {
            coords = dom2coords_REAL1_EXPR.at(d);
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
            dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putPAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::erasePAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getPAREN_REAL1_EXPR(coords::PAREN_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::PAREN_REAL1_EXPR* CoordsToDomain::getPAREN_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::PAREN_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putINV_REAL1_EXPR(coords::INV_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseINV_REAL1_EXPR(coords::INV_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getINV_REAL1_EXPR(coords::INV_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::INV_REAL1_EXPR* CoordsToDomain::getINV_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::INV_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getNEG_REAL1_EXPR(coords::NEG_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::NEG_REAL1_EXPR* CoordsToDomain::getNEG_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::NEG_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getADD_REAL1_EXPR_REAL1_EXPR(coords::ADD_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::ADD_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ADD_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getSUB_REAL1_EXPR_REAL1_EXPR(coords::SUB_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::SUB_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getSUB_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::SUB_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(coords::MUL_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MUL_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getDIV_REAL1_EXPR_REAL1_EXPR(coords::DIV_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::DIV_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getDIV_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DIV_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREF_REAL1_VAR(coords::REF_REAL1_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseREF_REAL1_VAR(coords::REF_REAL1_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REAL1_VAR(coords::REF_REAL1_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REF_REAL1_VAR* CoordsToDomain::getREF_REAL1_VAR(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REAL1_VAR*>(coords);
}

coords::REAL3_EXPR *CoordsToDomain::getREAL3_EXPR(domain::DomainObject *d) const
    {
        coords::REAL3_EXPR *coords = NULL;
        try {
            coords = dom2coords_REAL3_EXPR.at(d);
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
            dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putPAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::erasePAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getPAREN_REAL3_EXPR(coords::PAREN_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::PAREN_REAL3_EXPR* CoordsToDomain::getPAREN_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::PAREN_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getADD_REAL3_EXPR_REAL3_EXPR(coords::ADD_REAL3_EXPR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::ADD_REAL3_EXPR_REAL3_EXPR* CoordsToDomain::getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ADD_REAL3_EXPR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getSUB_REAL3_EXPR_REAL3_EXPR(coords::SUB_REAL3_EXPR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::SUB_REAL3_EXPR_REAL3_EXPR* CoordsToDomain::getSUB_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::SUB_REAL3_EXPR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putINV_REAL3_EXPR(coords::INV_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseINV_REAL3_EXPR(coords::INV_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getINV_REAL3_EXPR(coords::INV_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::INV_REAL3_EXPR* CoordsToDomain::getINV_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::INV_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getNEG_REAL3_EXPR(coords::NEG_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::NEG_REAL3_EXPR* CoordsToDomain::getNEG_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::NEG_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REAL3_EXPR_REAL1_EXPR(coords::MUL_REAL3_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MUL_REAL3_EXPR_REAL1_EXPR* CoordsToDomain::getMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REAL3_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REALMATRIX_EXPR_REAL3_EXPR(coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MUL_REALMATRIX_EXPR_REAL3_EXPR* CoordsToDomain::getMUL_REALMATRIX_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getDIV_REAL3_EXPR_REAL1_EXPR(coords::DIV_REAL3_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::DIV_REAL3_EXPR_REAL1_EXPR* CoordsToDomain::getDIV_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::DIV_REAL3_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREF_REAL3_VAR(coords::REF_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseREF_REAL3_VAR(coords::REF_REAL3_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REAL3_VAR(coords::REF_REAL3_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REF_REAL3_VAR* CoordsToDomain::getREF_REAL3_VAR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REAL3_VAR*>(coords);
}

coords::REAL4_EXPR *CoordsToDomain::getREAL4_EXPR(domain::DomainObject *d) const
    {
        coords::REAL4_EXPR *coords = NULL;
        try {
            coords = dom2coords_REAL4_EXPR.at(d);
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
            dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putPAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR[(coords::REAL4_EXPR*)c] = d;
    dom2coords_REAL4_EXPR[d] = (coords::REAL4_EXPR*)c;
}
void CoordsToDomain::erasePAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR.erase((coords::REAL4_EXPR*)c);
    dom2coords_REAL4_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getPAREN_REAL4_EXPR(coords::PAREN_REAL4_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::PAREN_REAL4_EXPR* CoordsToDomain::getPAREN_REAL4_EXPR(domain::DomainObject* d) const
{
    coords::REAL4_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::PAREN_REAL4_EXPR*>(coords);
}

void CoordsToDomain::putADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR[(coords::REAL4_EXPR*)c] = d;
    dom2coords_REAL4_EXPR[d] = (coords::REAL4_EXPR*)c;
}
void CoordsToDomain::eraseADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR.erase((coords::REAL4_EXPR*)c);
    dom2coords_REAL4_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getADD_REAL4_EXPR_REAL4_EXPR(coords::ADD_REAL4_EXPR_REAL4_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::ADD_REAL4_EXPR_REAL4_EXPR* CoordsToDomain::getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const
{
    coords::REAL4_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::ADD_REAL4_EXPR_REAL4_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR[(coords::REAL4_EXPR*)c] = d;
    dom2coords_REAL4_EXPR[d] = (coords::REAL4_EXPR*)c;
}
void CoordsToDomain::eraseMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR.erase((coords::REAL4_EXPR*)c);
    dom2coords_REAL4_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REAL4_EXPR_REAL1_EXPR(coords::MUL_REAL4_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MUL_REAL4_EXPR_REAL1_EXPR* CoordsToDomain::getMUL_REAL4_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL4_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REAL4_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREF_REAL4_VAR(coords::REF_REAL4_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR[(coords::REAL4_EXPR*)c] = d;
    dom2coords_REAL4_EXPR[d] = (coords::REAL4_EXPR*)c;
}
void CoordsToDomain::eraseREF_REAL4_VAR(coords::REF_REAL4_VAR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR.erase((coords::REAL4_EXPR*)c);
    dom2coords_REAL4_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_REAL4_VAR(coords::REF_REAL4_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REF_REAL4_VAR* CoordsToDomain::getREF_REAL4_VAR(domain::DomainObject* d) const
{
    coords::REAL4_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_REAL4_VAR*>(coords);
}

coords::REALMATRIX_EXPR *CoordsToDomain::getREALMATRIX_EXPR(domain::DomainObject *d) const
    {
        coords::REALMATRIX_EXPR *coords = NULL;
        try {
            coords = dom2coords_REALMATRIX_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REALMATRIX_EXPR *)coords;
    }
domain::DomainObject *CoordsToDomain::getREALMATRIX_EXPR(coords::REALMATRIX_EXPR *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putPAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR[(coords::REALMATRIX_EXPR*)c] = d;
    dom2coords_REALMATRIX_EXPR[d] = (coords::REALMATRIX_EXPR*)c;
}
void CoordsToDomain::erasePAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR.erase((coords::REALMATRIX_EXPR*)c);
    dom2coords_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getPAREN_REALMATRIX_EXPR(coords::PAREN_REALMATRIX_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::PAREN_REALMATRIX_EXPR* CoordsToDomain::getPAREN_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    coords::REALMATRIX_EXPR *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::PAREN_REALMATRIX_EXPR*>(coords);
}

void CoordsToDomain::putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR[(coords::REALMATRIX_EXPR*)c] = d;
    dom2coords_REALMATRIX_EXPR[d] = (coords::REALMATRIX_EXPR*)c;
}
void CoordsToDomain::eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR.erase((coords::REALMATRIX_EXPR*)c);
    dom2coords_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* CoordsToDomain::getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    coords::REALMATRIX_EXPR *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(coords);
}

void CoordsToDomain::putREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR[(coords::REALMATRIX_EXPR*)c] = d;
    dom2coords_REALMATRIX_EXPR[d] = (coords::REALMATRIX_EXPR*)c;
}
void CoordsToDomain::eraseREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR.erase((coords::REALMATRIX_EXPR*)c);
    dom2coords_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREF_EXPR_REALMATRIX_VAR(coords::REF_EXPR_REALMATRIX_VAR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REF_EXPR_REALMATRIX_VAR* CoordsToDomain::getREF_EXPR_REALMATRIX_VAR(domain::DomainObject* d) const
{
    coords::REALMATRIX_EXPR *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REF_EXPR_REALMATRIX_VAR*>(coords);
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

void CoordsToDomain::putREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_VAR_IDENT[(coords::REALMATRIX_VAR_IDENT*)c] = d;
    dom2coords_REALMATRIX_VAR_IDENT[d] = c;
}
domain::DomainObject* CoordsToDomain::getREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_VAR_IDENT.at((coords::REALMATRIX_VAR_IDENT*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REALMATRIX_VAR_IDENT* CoordsToDomain::getREALMATRIX_VAR_IDENT(domain::DomainObject* d) const
{
    coords::REALMATRIX_VAR_IDENT *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX_VAR_IDENT*>(coords);
}
void CoordsToDomain::eraseREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_VAR_IDENT.erase((coords::REALMATRIX_VAR_IDENT*)c);
    dom2coords_REALMATRIX_VAR_IDENT.erase(d);
}

coords::REAL1_LITERAL *CoordsToDomain::getREAL1_LITERAL(domain::DomainObject *d) const
    {
        coords::REAL1_EXPR *coords = NULL;
        try {
            coords = dom2coords_REAL1_EXPR.at(d);
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
            dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREAL1_LITERAL1(coords::REAL1_LITERAL1* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR[(coords::REAL1_EXPR*)c] = d;
    dom2coords_REAL1_EXPR[d] = (coords::REAL1_EXPR*)c;
}
void CoordsToDomain::eraseREAL1_LITERAL1(coords::REAL1_LITERAL1* c, domain::DomainObject *d)
{
    coords2dom_REAL1_EXPR.erase((coords::REAL1_EXPR*)c);
    dom2coords_REAL1_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL1_LITERAL1(coords::REAL1_LITERAL1* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL1_EXPR.at((coords::REAL1_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL1_LITERAL1* CoordsToDomain::getREAL1_LITERAL1(domain::DomainObject* d) const
{
    coords::REAL1_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL1_LITERAL1*>(coords);
}

coords::REAL3_LITERAL *CoordsToDomain::getREAL3_LITERAL(domain::DomainObject *d) const
    {
        coords::REAL3_EXPR *coords = NULL;
        try {
            coords = dom2coords_REAL3_EXPR.at(d);
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
            dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREAL3_LITERAL3(coords::REAL3_LITERAL3* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR[(coords::REAL3_EXPR*)c] = d;
    dom2coords_REAL3_EXPR[d] = (coords::REAL3_EXPR*)c;
}
void CoordsToDomain::eraseREAL3_LITERAL3(coords::REAL3_LITERAL3* c, domain::DomainObject *d)
{
    coords2dom_REAL3_EXPR.erase((coords::REAL3_EXPR*)c);
    dom2coords_REAL3_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL3_LITERAL3(coords::REAL3_LITERAL3* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL3_EXPR.at((coords::REAL3_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL3_LITERAL3* CoordsToDomain::getREAL3_LITERAL3(domain::DomainObject* d) const
{
    coords::REAL3_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL3_LITERAL3*>(coords);
}

coords::REAL4_LITERAL *CoordsToDomain::getREAL4_LITERAL(domain::DomainObject *d) const
    {
        coords::REAL4_EXPR *coords = NULL;
        try {
            coords = dom2coords_REAL4_EXPR.at(d);
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
            dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR[(coords::REAL4_EXPR*)c] = d;
    dom2coords_REAL4_EXPR[d] = (coords::REAL4_EXPR*)c;
}
void CoordsToDomain::eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR.erase((coords::REAL4_EXPR*)c);
    dom2coords_REAL4_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REAL4_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREAL4_LITERAL4(coords::REAL4_LITERAL4* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR[(coords::REAL4_EXPR*)c] = d;
    dom2coords_REAL4_EXPR[d] = (coords::REAL4_EXPR*)c;
}
void CoordsToDomain::eraseREAL4_LITERAL4(coords::REAL4_LITERAL4* c, domain::DomainObject *d)
{
    coords2dom_REAL4_EXPR.erase((coords::REAL4_EXPR*)c);
    dom2coords_REAL4_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREAL4_LITERAL4(coords::REAL4_LITERAL4* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REAL4_EXPR.at((coords::REAL4_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REAL4_LITERAL4* CoordsToDomain::getREAL4_LITERAL4(domain::DomainObject* d) const
{
    coords::REAL4_EXPR *coords = NULL;
    try {
        coords = dom2coords_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REAL4_LITERAL4*>(coords);
}

coords::REALMATRIX_LITERAL *CoordsToDomain::getREALMATRIX_LITERAL(domain::DomainObject *d) const
    {
        coords::REALMATRIX_EXPR *coords = NULL;
        try {
            coords = dom2coords_REALMATRIX_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            coords = NULL;
        }
        return (coords::REALMATRIX_LITERAL *)coords;
    }
domain::DomainObject *CoordsToDomain::getREALMATRIX_LITERAL(coords::REALMATRIX_LITERAL *c) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void CoordsToDomain::putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR[(coords::REALMATRIX_EXPR*)c] = d;
    dom2coords_REALMATRIX_EXPR[d] = (coords::REALMATRIX_EXPR*)c;
}
void CoordsToDomain::eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR.erase((coords::REALMATRIX_EXPR*)c);
    dom2coords_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* CoordsToDomain::getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    coords::REALMATRIX_EXPR *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(coords);
}

void CoordsToDomain::putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR[(coords::REALMATRIX_EXPR*)c] = d;
    dom2coords_REALMATRIX_EXPR[d] = (coords::REALMATRIX_EXPR*)c;
}
void CoordsToDomain::eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR.erase((coords::REALMATRIX_EXPR*)c);
    dom2coords_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* CoordsToDomain::getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    coords::REALMATRIX_EXPR *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(coords);
}

void CoordsToDomain::putREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR[(coords::REALMATRIX_EXPR*)c] = d;
    dom2coords_REALMATRIX_EXPR[d] = (coords::REALMATRIX_EXPR*)c;
}
void CoordsToDomain::eraseREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c, domain::DomainObject *d)
{
    coords2dom_REALMATRIX_EXPR.erase((coords::REALMATRIX_EXPR*)c);
    dom2coords_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* CoordsToDomain::getREALMATRIX_LITERAL9(coords::REALMATRIX_LITERAL9* c) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = coords2dom_REALMATRIX_EXPR.at((coords::REALMATRIX_EXPR*)c);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
coords::REALMATRIX_LITERAL9* CoordsToDomain::getREALMATRIX_LITERAL9(domain::DomainObject* d) const
{
    coords::REALMATRIX_EXPR *coords = NULL;
    try {
        coords = dom2coords_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        coords = NULL;
    }
    return static_cast<coords::REALMATRIX_LITERAL9*>(coords);
}
