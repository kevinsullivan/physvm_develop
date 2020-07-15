
#include "InterpToDomain.h"

#include <iostream>

#include <g3log/g3log.hpp>

using namespace interp2domain;

	void InterpToDomain::putSpace(interp::Space* key, domain::Space* val){
    interp2dom_Spaces[key] = val;
    dom2interp_Spaces[val] = key;
}
	domain::Space* InterpToDomain::getSpace(interp::Space* i) const{
    domain::Space* dom = NULL;
    try {
        dom = interp2dom_Spaces.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}
	interp::Space* InterpToDomain::getSpace(domain::Space* d) const{
    interp::Space *interp = NULL;
    try {
        interp = dom2interp_Spaces.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

interp::STMT *InterpToDomain::getSTMT(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::STMT*)interp;
    }
domain::DomainObject *InterpToDomain::getSTMT(interp::STMT *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putCOMPOUND_STMT(interp::COMPOUND_STMT* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseCOMPOUND_STMT(interp::COMPOUND_STMT* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getCOMPOUND_STMT(interp::COMPOUND_STMT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::COMPOUND_STMT* InterpToDomain::getCOMPOUND_STMT(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::COMPOUND_STMT*>(interp);
}

interp::IFCOND *InterpToDomain::getIFCOND(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::IFCOND*)interp;
    }
domain::DomainObject *InterpToDomain::getIFCOND(interp::IFCOND *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getIFTHEN_EXPR_STMT(interp::IFTHEN_EXPR_STMT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::IFTHEN_EXPR_STMT* InterpToDomain::getIFTHEN_EXPR_STMT(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::IFTHEN_EXPR_STMT*>(interp);
}

void InterpToDomain::putIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getIFTHENELSEIF_EXPR_STMT_IFCOND(interp::IFTHENELSEIF_EXPR_STMT_IFCOND* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::IFTHENELSEIF_EXPR_STMT_IFCOND* InterpToDomain::getIFTHENELSEIF_EXPR_STMT_IFCOND(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::IFTHENELSEIF_EXPR_STMT_IFCOND*>(interp);
}

void InterpToDomain::putIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getIFTHENELSE_EXPR_STMT_STMT(interp::IFTHENELSE_EXPR_STMT_STMT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::IFTHENELSE_EXPR_STMT_STMT* InterpToDomain::getIFTHENELSE_EXPR_STMT_STMT(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::IFTHENELSE_EXPR_STMT_STMT*>(interp);
}

interp::EXPR *InterpToDomain::getEXPR(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::EXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getEXPR(interp::EXPR *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

interp::ASSIGNMENT *InterpToDomain::getASSIGNMENT(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::ASSIGNMENT*)interp;
    }
domain::DomainObject *InterpToDomain::getASSIGNMENT(interp::ASSIGNMENT *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getASSIGN_REAL1_VAR_REAL1_EXPR(interp::ASSIGN_REAL1_VAR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ASSIGN_REAL1_VAR_REAL1_EXPR* InterpToDomain::getASSIGN_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REAL1_VAR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getASSIGN_REAL3_VAR_REAL3_EXPR(interp::ASSIGN_REAL3_VAR_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ASSIGN_REAL3_VAR_REAL3_EXPR* InterpToDomain::getASSIGN_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REAL3_VAR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getASSIGN_REAL4_VAR_REAL4_EXPR(interp::ASSIGN_REAL4_VAR_REAL4_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ASSIGN_REAL4_VAR_REAL4_EXPR* InterpToDomain::getASSIGN_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REAL4_VAR_REAL4_EXPR*>(interp);
}

void InterpToDomain::putASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR* InterpToDomain::getASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR*>(interp);
}

interp::DECLARE *InterpToDomain::getDECLARE(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::DECLARE*)interp;
    }
domain::DomainObject *InterpToDomain::getDECLARE(interp::DECLARE *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REAL1_VAR_REAL1_EXPR(interp::DECL_REAL1_VAR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REAL1_VAR_REAL1_EXPR* InterpToDomain::getDECL_REAL1_VAR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL1_VAR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REAL3_VAR_REAL3_EXPR(interp::DECL_REAL3_VAR_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REAL3_VAR_REAL3_EXPR* InterpToDomain::getDECL_REAL3_VAR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL3_VAR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REAL4_VAR_REAL4_EXPR(interp::DECL_REAL4_VAR_REAL4_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REAL4_VAR_REAL4_EXPR* InterpToDomain::getDECL_REAL4_VAR_REAL4_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL4_VAR_REAL4_EXPR*>(interp);
}

void InterpToDomain::putDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR* InterpToDomain::getDECL_REALMATRIX_VAR_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REALMATRIX_VAR_REALMATRIX_EXPR*>(interp);
}

void InterpToDomain::putDECL_REAL1_VAR(interp::DECL_REAL1_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REAL1_VAR(interp::DECL_REAL1_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REAL1_VAR(interp::DECL_REAL1_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REAL1_VAR* InterpToDomain::getDECL_REAL1_VAR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL1_VAR*>(interp);
}

void InterpToDomain::putDECL_REAL3_VAR(interp::DECL_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REAL3_VAR(interp::DECL_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REAL3_VAR(interp::DECL_REAL3_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REAL3_VAR* InterpToDomain::getDECL_REAL3_VAR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL3_VAR*>(interp);
}

void InterpToDomain::putDECL_REAL4_VAR(interp::DECL_REAL4_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REAL4_VAR(interp::DECL_REAL4_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REAL4_VAR(interp::DECL_REAL4_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REAL4_VAR* InterpToDomain::getDECL_REAL4_VAR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REAL4_VAR*>(interp);
}

void InterpToDomain::putDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getDECL_REALMATRIX_VAR(interp::DECL_REALMATRIX_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_STMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DECL_REALMATRIX_VAR* InterpToDomain::getDECL_REALMATRIX_VAR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DECL_REALMATRIX_VAR*>(interp);
}

interp::REAL1_EXPR *InterpToDomain::getREAL1_EXPR(domain::DomainObject *d) const
    {
        interp::REAL1_EXPR *interp = NULL;
        try {
            interp = dom2interp_REAL1_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_EXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL1_EXPR(interp::REAL1_EXPR *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL1_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putPAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::erasePAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getPAREN_REAL1_EXPR(interp::PAREN_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::PAREN_REAL1_EXPR* InterpToDomain::getPAREN_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REAL1_EXPR*>(interp);
}

void InterpToDomain::putINV_REAL1_EXPR(interp::INV_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseINV_REAL1_EXPR(interp::INV_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getINV_REAL1_EXPR(interp::INV_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::INV_REAL1_EXPR* InterpToDomain::getINV_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::INV_REAL1_EXPR*>(interp);
}

void InterpToDomain::putNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getNEG_REAL1_EXPR(interp::NEG_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::NEG_REAL1_EXPR* InterpToDomain::getNEG_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::NEG_REAL1_EXPR*>(interp);
}

void InterpToDomain::putADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ADD_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getSUB_REAL1_EXPR_REAL1_EXPR(interp::SUB_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::SUB_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getSUB_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::SUB_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::MUL_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getDIV_REAL1_EXPR_REAL1_EXPR(interp::DIV_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DIV_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getDIV_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DIV_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREF_REAL1_VAR(interp::REF_REAL1_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseREF_REAL1_VAR(interp::REF_REAL1_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREF_REAL1_VAR(interp::REF_REAL1_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REF_REAL1_VAR* InterpToDomain::getREF_REAL1_VAR(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL1_VAR*>(interp);
}

interp::REAL3_EXPR *InterpToDomain::getREAL3_EXPR(domain::DomainObject *d) const
    {
        interp::REAL3_EXPR *interp = NULL;
        try {
            interp = dom2interp_REAL3_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_EXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL3_EXPR(interp::REAL3_EXPR *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL3_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putPAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::erasePAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getPAREN_REAL3_EXPR(interp::PAREN_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::PAREN_REAL3_EXPR* InterpToDomain::getPAREN_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REAL3_EXPR*>(interp);
}

void InterpToDomain::putADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ADD_REAL3_EXPR_REAL3_EXPR* InterpToDomain::getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getSUB_REAL3_EXPR_REAL3_EXPR(interp::SUB_REAL3_EXPR_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::SUB_REAL3_EXPR_REAL3_EXPR* InterpToDomain::getSUB_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::SUB_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putINV_REAL3_EXPR(interp::INV_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseINV_REAL3_EXPR(interp::INV_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getINV_REAL3_EXPR(interp::INV_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::INV_REAL3_EXPR* InterpToDomain::getINV_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::INV_REAL3_EXPR*>(interp);
}

void InterpToDomain::putNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getNEG_REAL3_EXPR(interp::NEG_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::NEG_REAL3_EXPR* InterpToDomain::getNEG_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::NEG_REAL3_EXPR*>(interp);
}

void InterpToDomain::putMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getMUL_REAL3_EXPR_REAL1_EXPR(interp::MUL_REAL3_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::MUL_REAL3_EXPR_REAL1_EXPR* InterpToDomain::getMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL3_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getMUL_REALMATRIX_EXPR_REAL3_EXPR(interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::MUL_REALMATRIX_EXPR_REAL3_EXPR* InterpToDomain::getMUL_REALMATRIX_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REALMATRIX_EXPR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getDIV_REAL3_EXPR_REAL1_EXPR(interp::DIV_REAL3_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::DIV_REAL3_EXPR_REAL1_EXPR* InterpToDomain::getDIV_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::DIV_REAL3_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREF_REAL3_VAR(interp::REF_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseREF_REAL3_VAR(interp::REF_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREF_REAL3_VAR(interp::REF_REAL3_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REF_REAL3_VAR* InterpToDomain::getREF_REAL3_VAR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL3_VAR*>(interp);
}

interp::REAL4_EXPR *InterpToDomain::getREAL4_EXPR(domain::DomainObject *d) const
    {
        interp::REAL4_EXPR *interp = NULL;
        try {
            interp = dom2interp_REAL4_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL4_EXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL4_EXPR(interp::REAL4_EXPR *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL4_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putPAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR[i] = d;
    dom2interp_REAL4_EXPR[d] = i;
}
void InterpToDomain::erasePAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR.erase(i);
    dom2interp_REAL4_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getPAREN_REAL4_EXPR(interp::PAREN_REAL4_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::PAREN_REAL4_EXPR* InterpToDomain::getPAREN_REAL4_EXPR(domain::DomainObject* d) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REAL4_EXPR*>(interp);
}

void InterpToDomain::putADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR[i] = d;
    dom2interp_REAL4_EXPR[d] = i;
}
void InterpToDomain::eraseADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR.erase(i);
    dom2interp_REAL4_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getADD_REAL4_EXPR_REAL4_EXPR(interp::ADD_REAL4_EXPR_REAL4_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::ADD_REAL4_EXPR_REAL4_EXPR* InterpToDomain::getADD_REAL4_EXPR_REAL4_EXPR(domain::DomainObject* d) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL4_EXPR_REAL4_EXPR*>(interp);
}

void InterpToDomain::putMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR[i] = d;
    dom2interp_REAL4_EXPR[d] = i;
}
void InterpToDomain::eraseMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR.erase(i);
    dom2interp_REAL4_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getMUL_REAL4_EXPR_REAL1_EXPR(interp::MUL_REAL4_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::MUL_REAL4_EXPR_REAL1_EXPR* InterpToDomain::getMUL_REAL4_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL4_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREF_REAL4_VAR(interp::REF_REAL4_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR[i] = d;
    dom2interp_REAL4_EXPR[d] = i;
}
void InterpToDomain::eraseREF_REAL4_VAR(interp::REF_REAL4_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR.erase(i);
    dom2interp_REAL4_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREF_REAL4_VAR(interp::REF_REAL4_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REF_REAL4_VAR* InterpToDomain::getREF_REAL4_VAR(domain::DomainObject* d) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL4_VAR*>(interp);
}

interp::REALMATRIX_EXPR *InterpToDomain::getREALMATRIX_EXPR(domain::DomainObject *d) const
    {
        interp::REALMATRIX_EXPR *interp = NULL;
        try {
            interp = dom2interp_REALMATRIX_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REALMATRIX_EXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getREALMATRIX_EXPR(interp::REALMATRIX_EXPR *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REALMATRIX_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putPAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR[i] = d;
    dom2interp_REALMATRIX_EXPR[d] = i;
}
void InterpToDomain::erasePAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR.erase(i);
    dom2interp_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getPAREN_REALMATRIX_EXPR(interp::PAREN_REALMATRIX_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::PAREN_REALMATRIX_EXPR* InterpToDomain::getPAREN_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::PAREN_REALMATRIX_EXPR*>(interp);
}

void InterpToDomain::putMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR[i] = d;
    dom2interp_REALMATRIX_EXPR[d] = i;
}
void InterpToDomain::eraseMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR.erase(i);
    dom2interp_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR* InterpToDomain::getMUL_REALMATRIX_EXPR_REALMATRIX_EXPR(domain::DomainObject* d) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REALMATRIX_EXPR_REALMATRIX_EXPR*>(interp);
}

void InterpToDomain::putREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR[i] = d;
    dom2interp_REALMATRIX_EXPR[d] = i;
}
void InterpToDomain::eraseREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR.erase(i);
    dom2interp_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREF_EXPR_REALMATRIX_VAR(interp::REF_EXPR_REALMATRIX_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REF_EXPR_REALMATRIX_VAR* InterpToDomain::getREF_EXPR_REALMATRIX_VAR(domain::DomainObject* d) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_EXPR_REALMATRIX_VAR*>(interp);
}

void InterpToDomain::putREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REAL1_VAR_IDENT[i] = d;
    dom2interp_REAL1_VAR_IDENT[d] = i;
}
void InterpToDomain::eraseREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REAL1_VAR_IDENT.erase(i);
    dom2interp_REAL1_VAR_IDENT.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL1_VAR_IDENT(interp::REAL1_VAR_IDENT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_VAR_IDENT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL1_VAR_IDENT* InterpToDomain::getREAL1_VAR_IDENT(domain::DomainObject* d) const
{
    interp::REAL1_VAR_IDENT *interp = NULL;
    try {
        interp = dom2interp_REAL1_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL1_VAR_IDENT*>(interp);
}

void InterpToDomain::putREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REAL3_VAR_IDENT[i] = d;
    dom2interp_REAL3_VAR_IDENT[d] = i;
}
void InterpToDomain::eraseREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REAL3_VAR_IDENT.erase(i);
    dom2interp_REAL3_VAR_IDENT.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL3_VAR_IDENT(interp::REAL3_VAR_IDENT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_VAR_IDENT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL3_VAR_IDENT* InterpToDomain::getREAL3_VAR_IDENT(domain::DomainObject* d) const
{
    interp::REAL3_VAR_IDENT *interp = NULL;
    try {
        interp = dom2interp_REAL3_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_VAR_IDENT*>(interp);
}

void InterpToDomain::putREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REAL4_VAR_IDENT[i] = d;
    dom2interp_REAL4_VAR_IDENT[d] = i;
}
void InterpToDomain::eraseREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REAL4_VAR_IDENT.erase(i);
    dom2interp_REAL4_VAR_IDENT.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL4_VAR_IDENT(interp::REAL4_VAR_IDENT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_VAR_IDENT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL4_VAR_IDENT* InterpToDomain::getREAL4_VAR_IDENT(domain::DomainObject* d) const
{
    interp::REAL4_VAR_IDENT *interp = NULL;
    try {
        interp = dom2interp_REAL4_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL4_VAR_IDENT*>(interp);
}

void InterpToDomain::putREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_VAR_IDENT[i] = d;
    dom2interp_REALMATRIX_VAR_IDENT[d] = i;
}
void InterpToDomain::eraseREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_VAR_IDENT.erase(i);
    dom2interp_REALMATRIX_VAR_IDENT.erase(d);
}
domain::DomainObject* InterpToDomain::getREALMATRIX_VAR_IDENT(interp::REALMATRIX_VAR_IDENT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_VAR_IDENT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REALMATRIX_VAR_IDENT* InterpToDomain::getREALMATRIX_VAR_IDENT(domain::DomainObject* d) const
{
    interp::REALMATRIX_VAR_IDENT *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_VAR_IDENT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_VAR_IDENT*>(interp);
}

interp::REAL1_LITERAL *InterpToDomain::getREAL1_LITERAL(domain::DomainObject *d) const
    {
        interp::REAL1_EXPR *interp = NULL;
        try {
            interp = dom2interp_REAL1_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL1_LITERAL*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL1_LITERAL(interp::REAL1_LITERAL *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL1_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREAL1_LITERAL1(interp::REAL1_LITERAL1* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR[i] = d;
    dom2interp_REAL1_EXPR[d] = i;
}
void InterpToDomain::eraseREAL1_LITERAL1(interp::REAL1_LITERAL1* i, domain::DomainObject* d)
{
    interp2dom_REAL1_EXPR.erase(i);
    dom2interp_REAL1_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL1_LITERAL1(interp::REAL1_LITERAL1* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL1_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL1_LITERAL1* InterpToDomain::getREAL1_LITERAL1(domain::DomainObject* d) const
{
    interp::REAL1_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL1_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL1_LITERAL1*>(interp);
}

interp::REAL3_LITERAL *InterpToDomain::getREAL3_LITERAL(domain::DomainObject *d) const
    {
        interp::REAL3_EXPR *interp = NULL;
        try {
            interp = dom2interp_REAL3_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_LITERAL*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL3_LITERAL(interp::REAL3_LITERAL *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL3_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREAL3_LITERAL3(interp::REAL3_LITERAL3* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR[i] = d;
    dom2interp_REAL3_EXPR[d] = i;
}
void InterpToDomain::eraseREAL3_LITERAL3(interp::REAL3_LITERAL3* i, domain::DomainObject* d)
{
    interp2dom_REAL3_EXPR.erase(i);
    dom2interp_REAL3_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL3_LITERAL3(interp::REAL3_LITERAL3* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL3_LITERAL3* InterpToDomain::getREAL3_LITERAL3(domain::DomainObject* d) const
{
    interp::REAL3_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_LITERAL3*>(interp);
}

interp::REAL4_LITERAL *InterpToDomain::getREAL4_LITERAL(domain::DomainObject *d) const
    {
        interp::REAL4_EXPR *interp = NULL;
        try {
            interp = dom2interp_REAL4_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL4_LITERAL*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL4_LITERAL(interp::REAL4_LITERAL *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL4_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR[i] = d;
    dom2interp_REAL4_EXPR[d] = i;
}
void InterpToDomain::eraseREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR.erase(i);
    dom2interp_REAL4_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getREAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREAL4_LITERAL4(interp::REAL4_LITERAL4* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR[i] = d;
    dom2interp_REAL4_EXPR[d] = i;
}
void InterpToDomain::eraseREAL4_LITERAL4(interp::REAL4_LITERAL4* i, domain::DomainObject* d)
{
    interp2dom_REAL4_EXPR.erase(i);
    dom2interp_REAL4_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL4_LITERAL4(interp::REAL4_LITERAL4* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL4_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REAL4_LITERAL4* InterpToDomain::getREAL4_LITERAL4(domain::DomainObject* d) const
{
    interp::REAL4_EXPR *interp = NULL;
    try {
        interp = dom2interp_REAL4_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL4_LITERAL4*>(interp);
}

interp::REALMATRIX_LITERAL *InterpToDomain::getREALMATRIX_LITERAL(domain::DomainObject *d) const
    {
        interp::REALMATRIX_EXPR *interp = NULL;
        try {
            interp = dom2interp_REALMATRIX_EXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REALMATRIX_LITERAL*)interp;
    }
domain::DomainObject *InterpToDomain::getREALMATRIX_LITERAL(interp::REALMATRIX_LITERAL *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REALMATRIX_EXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR[i] = d;
    dom2interp_REALMATRIX_EXPR[d] = i;
}
void InterpToDomain::eraseREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR.erase(i);
    dom2interp_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR* InterpToDomain::getREALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR[i] = d;
    dom2interp_REALMATRIX_EXPR[d] = i;
}
void InterpToDomain::eraseREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR.erase(i);
    dom2interp_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getREALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR[i] = d;
    dom2interp_REALMATRIX_EXPR[d] = i;
}
void InterpToDomain::eraseREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* i, domain::DomainObject* d)
{
    interp2dom_REALMATRIX_EXPR.erase(i);
    dom2interp_REALMATRIX_EXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getREALMATRIX_LITERAL9(interp::REALMATRIX_LITERAL9* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REALMATRIX_EXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::REALMATRIX_LITERAL9* InterpToDomain::getREALMATRIX_LITERAL9(domain::DomainObject* d) const
{
    interp::REALMATRIX_EXPR *interp = NULL;
    try {
        interp = dom2interp_REALMATRIX_EXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REALMATRIX_LITERAL9*>(interp);
}
