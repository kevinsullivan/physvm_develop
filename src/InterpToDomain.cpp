
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
