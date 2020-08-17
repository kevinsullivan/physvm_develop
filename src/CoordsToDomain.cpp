
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
