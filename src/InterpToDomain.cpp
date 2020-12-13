
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

	void InterpToDomain::putMeasurementSystem(interp::MeasurementSystem* key, domain::MeasurementSystem* val){
    interp2dom_MeasurementSystems[key] = val;
    dom2interp_MeasurementSystems[val] = key;
}
	domain::MeasurementSystem* InterpToDomain::getMeasurementSystem(interp::MeasurementSystem* i) const{
    domain::MeasurementSystem* dom = NULL;
    try {
        dom = interp2dom_MeasurementSystems.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}
	interp::MeasurementSystem* InterpToDomain::getMeasurementSystem(domain::MeasurementSystem* d) const{
    interp::MeasurementSystem *interp = NULL;
    try {
        interp = dom2interp_MeasurementSystems.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

	void InterpToDomain::putFrame(interp::Frame* key, domain::Frame* val){
    interp2dom_Frames[key] = val;
    dom2interp_Frames[val] = key;
}
	domain::Frame* InterpToDomain::getFrame(interp::Frame* i) const{
    domain::Frame* dom = NULL;
    try {
        dom = interp2dom_Frames.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return dom;
}
	interp::Frame* InterpToDomain::getFrame(domain::Frame* d) const{
    interp::Frame *interp = NULL;
    try {
        interp = dom2interp_Frames.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return interp;
}

interp::PROGRAM *InterpToDomain::getPROGRAM(domain::DomainObject *d) const
    {
        interp::PROGRAM *interp = NULL;
        try {
            interp = dom2interp_PROGRAM.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::PROGRAM*)interp;
    }
domain::DomainObject *InterpToDomain::getPROGRAM(interp::PROGRAM *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_PROGRAM.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* i, domain::DomainObject* d)
{
    interp2dom_PROGRAM[i] = d;
    dom2interp_PROGRAM[d] = i;
}
void InterpToDomain::eraseSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* i, domain::DomainObject* d)
{
    interp2dom_PROGRAM.erase(i);
    dom2interp_PROGRAM.erase(d);
}
domain::DomainObject* InterpToDomain::getSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_PROGRAM.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::SEQ_GLOBALSTMT* InterpToDomain::getSEQ_GLOBALSTMT(domain::DomainObject* d) const
{
    interp::PROGRAM *interp = NULL;
    try {
        interp = dom2interp_PROGRAM.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::SEQ_GLOBALSTMT*>(interp);
}

interp::GLOBALSTMT *InterpToDomain::getGLOBALSTMT(domain::DomainObject *d) const
    {
        interp::GLOBALSTMT *interp = NULL;
        try {
            interp = dom2interp_GLOBALSTMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::GLOBALSTMT*)interp;
    }
domain::DomainObject *InterpToDomain::getGLOBALSTMT(interp::GLOBALSTMT *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_GLOBALSTMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
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

interp::FUNC_DECL *InterpToDomain::getFUNC_DECL(domain::DomainObject *d) const
    {
        interp::GLOBALSTMT *interp = NULL;
        try {
            interp = dom2interp_GLOBALSTMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::FUNC_DECL*)interp;
    }
domain::DomainObject *InterpToDomain::getFUNC_DECL(interp::FUNC_DECL *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_GLOBALSTMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* i, domain::DomainObject* d)
{
    interp2dom_GLOBALSTMT[i] = d;
    dom2interp_GLOBALSTMT[d] = i;
}
void InterpToDomain::eraseVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* i, domain::DomainObject* d)
{
    interp2dom_GLOBALSTMT.erase(i);
    dom2interp_GLOBALSTMT.erase(d);
}
domain::DomainObject* InterpToDomain::getVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_GLOBALSTMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::VOID_FUNC_DECL_STMT* InterpToDomain::getVOID_FUNC_DECL_STMT(domain::DomainObject* d) const
{
    interp::GLOBALSTMT *interp = NULL;
    try {
        interp = dom2interp_GLOBALSTMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::VOID_FUNC_DECL_STMT*>(interp);
}

void InterpToDomain::putMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* i, domain::DomainObject* d)
{
    interp2dom_GLOBALSTMT[i] = d;
    dom2interp_GLOBALSTMT[d] = i;
}
void InterpToDomain::eraseMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* i, domain::DomainObject* d)
{
    interp2dom_GLOBALSTMT.erase(i);
    dom2interp_GLOBALSTMT.erase(d);
}
domain::DomainObject* InterpToDomain::getMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_GLOBALSTMT.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::MAIN_FUNC_DECL_STMT* InterpToDomain::getMAIN_FUNC_DECL_STMT(domain::DomainObject* d) const
{
    interp::GLOBALSTMT *interp = NULL;
    try {
        interp = dom2interp_GLOBALSTMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MAIN_FUNC_DECL_STMT*>(interp);
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

interp::REXPR *InterpToDomain::getREXPR(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getREXPR(interp::REXPR *i) const
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

interp::LEXPR *InterpToDomain::getLEXPR(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::LEXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getLEXPR(interp::LEXPR *i) const
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

interp::REAL3_EXPR *InterpToDomain::getREAL3_EXPR(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
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
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREF_REAL3_VAR(interp::REF_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseREF_REAL3_VAR(interp::REF_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getREF_REAL3_VAR(interp::REF_REAL3_VAR* i) const
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
interp::REF_REAL3_VAR* InterpToDomain::getREF_REAL3_VAR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL3_VAR*>(interp);
}

void InterpToDomain::putADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getADD_REAL3_EXPR_REAL3_EXPR(interp::ADD_REAL3_EXPR_REAL3_EXPR* i) const
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
interp::ADD_REAL3_EXPR_REAL3_EXPR* InterpToDomain::getADD_REAL3_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL3_EXPR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getLMUL_REAL1_EXPR_REAL3_EXPR(interp::LMUL_REAL1_EXPR_REAL3_EXPR* i) const
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
interp::LMUL_REAL1_EXPR_REAL3_EXPR* InterpToDomain::getLMUL_REAL1_EXPR_REAL3_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::LMUL_REAL1_EXPR_REAL3_EXPR*>(interp);
}

void InterpToDomain::putRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getRMUL_REAL3_EXPR_REAL1_EXPR(interp::RMUL_REAL3_EXPR_REAL1_EXPR* i) const
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
interp::RMUL_REAL3_EXPR_REAL1_EXPR* InterpToDomain::getRMUL_REAL3_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::RMUL_REAL3_EXPR_REAL1_EXPR*>(interp);
}

interp::REAL3_LEXPR *InterpToDomain::getREAL3_LEXPR(domain::DomainObject *d) const
    {
        interp::REAL3_LEXPR *interp = NULL;
        try {
            interp = dom2interp_REAL3_LEXPR.at(d);
        }
        catch (std::out_of_range &e) {
            interp = NULL;
        }
        return (interp::REAL3_LEXPR*)interp;
    }
domain::DomainObject *InterpToDomain::getREAL3_LEXPR(interp::REAL3_LEXPR *i) const
    {
        domain::DomainObject *dom = NULL;
        try {
            dom = interp2dom_REAL3_LEXPR.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putLREF_REAL3_VAR(interp::LREF_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_LEXPR[i] = d;
    dom2interp_REAL3_LEXPR[d] = i;
}
void InterpToDomain::eraseLREF_REAL3_VAR(interp::LREF_REAL3_VAR* i, domain::DomainObject* d)
{
    interp2dom_REAL3_LEXPR.erase(i);
    dom2interp_REAL3_LEXPR.erase(d);
}
domain::DomainObject* InterpToDomain::getLREF_REAL3_VAR(interp::LREF_REAL3_VAR* i) const
{
    domain::DomainObject* dom = NULL;
    try {
        dom = interp2dom_REAL3_LEXPR.at(i);
    }
    catch (std::out_of_range &e) {
        dom = NULL;
    }
    return static_cast<domain::DomainObject*>(dom);
}
interp::LREF_REAL3_VAR* InterpToDomain::getLREF_REAL3_VAR(domain::DomainObject* d) const
{
    interp::REAL3_LEXPR *interp = NULL;
    try {
        interp = dom2interp_REAL3_LEXPR.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::LREF_REAL3_VAR*>(interp);
}

interp::REAL1_EXPR *InterpToDomain::getREAL1_EXPR(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
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
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREF_REAL1_VAR(interp::REF_REAL1_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseREF_REAL1_VAR(interp::REF_REAL1_VAR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getREF_REAL1_VAR(interp::REF_REAL1_VAR* i) const
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
interp::REF_REAL1_VAR* InterpToDomain::getREF_REAL1_VAR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REF_REAL1_VAR*>(interp);
}

void InterpToDomain::putADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getADD_REAL1_EXPR_REAL1_EXPR(interp::ADD_REAL1_EXPR_REAL1_EXPR* i) const
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
interp::ADD_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getADD_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::ADD_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(interp::MUL_REAL1_EXPR_REAL1_EXPR* i) const
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
interp::MUL_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getMUL_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::MUL_REAL1_EXPR_REAL1_EXPR*>(interp);
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

interp::REAL3_LITERAL *InterpToDomain::getREAL3_LITERAL(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
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
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* i) const
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
interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR* InterpToDomain::getREAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR*>(interp);
}

void InterpToDomain::putREAL3_EMPTY(interp::REAL3_EMPTY* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseREAL3_EMPTY(interp::REAL3_EMPTY* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL3_EMPTY(interp::REAL3_EMPTY* i) const
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
interp::REAL3_EMPTY* InterpToDomain::getREAL3_EMPTY(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL3_EMPTY*>(interp);
}

interp::REAL1_LITERAL *InterpToDomain::getREAL1_LITERAL(domain::DomainObject *d) const
    {
        interp::STMT *interp = NULL;
        try {
            interp = dom2interp_STMT.at(d);
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
            dom = interp2dom_STMT.at(i);
        }
        catch (std::out_of_range &e) {
            dom = NULL;
        }
        return dom;
    }

void InterpToDomain::putREAL1_LIT(interp::REAL1_LIT* i, domain::DomainObject* d)
{
    interp2dom_STMT[i] = d;
    dom2interp_STMT[d] = i;
}
void InterpToDomain::eraseREAL1_LIT(interp::REAL1_LIT* i, domain::DomainObject* d)
{
    interp2dom_STMT.erase(i);
    dom2interp_STMT.erase(d);
}
domain::DomainObject* InterpToDomain::getREAL1_LIT(interp::REAL1_LIT* i) const
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
interp::REAL1_LIT* InterpToDomain::getREAL1_LIT(domain::DomainObject* d) const
{
    interp::STMT *interp = NULL;
    try {
        interp = dom2interp_STMT.at(d);
    }
    catch (std::out_of_range &e) {
        interp = NULL;
    }
    return static_cast<interp::REAL1_LIT*>(interp);
}
