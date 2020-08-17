#ifndef INTERPTODOMAIN_H
#define INTERPTODOMAIN_H

#include <iostream>
#include "Domain.h"
#include "Interp.h"

#include <unordered_map>

namespace interp2domain{

class InterpToDomain
{
    public:
	void putSpace(interp::Space* key, domain::Space* val);
	domain::Space* getSpace(interp::Space* c) const;
	interp::Space* getSpace(domain::Space* d) const;

	void putFrame(interp::Frame* key, domain::Frame* val);
	domain::Frame* getFrame(interp::Frame* c) const;
	interp::Frame* getFrame(domain::Frame* d) const;

	domain::DomainObject* getPROGRAM(interp::PROGRAM* c) const;
	interp::PROGRAM* getPROGRAM(domain::DomainObject* d) const;
	
	void putSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* key, domain::DomainObject* val);
	domain::DomainObject* getSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* c) const;
	interp::SEQ_GLOBALSTMT* getSEQ_GLOBALSTMT(domain::DomainObject* d) const;
void eraseSEQ_GLOBALSTMT(interp::SEQ_GLOBALSTMT* key, domain::DomainObject* val);

	domain::DomainObject* getGLOBALSTMT(interp::GLOBALSTMT* c) const;
	interp::GLOBALSTMT* getGLOBALSTMT(domain::DomainObject* d) const;
	
	domain::DomainObject* getSTMT(interp::STMT* c) const;
	interp::STMT* getSTMT(domain::DomainObject* d) const;
	
	void putCOMPOUND_STMT(interp::COMPOUND_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getCOMPOUND_STMT(interp::COMPOUND_STMT* c) const;
	interp::COMPOUND_STMT* getCOMPOUND_STMT(domain::DomainObject* d) const;
void eraseCOMPOUND_STMT(interp::COMPOUND_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getFUNC_DECL(interp::FUNC_DECL* c) const;
	interp::FUNC_DECL* getFUNC_DECL(domain::DomainObject* d) const;
	
	void putVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* c) const;
	interp::VOID_FUNC_DECL_STMT* getVOID_FUNC_DECL_STMT(domain::DomainObject* d) const;
void eraseVOID_FUNC_DECL_STMT(interp::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);

	void putMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* c) const;
	interp::MAIN_FUNC_DECL_STMT* getMAIN_FUNC_DECL_STMT(domain::DomainObject* d) const;
void eraseMAIN_FUNC_DECL_STMT(interp::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);

private:

std::unordered_map<interp::Space*, domain::Space*> interp2dom_Spaces;

std::unordered_map<domain::Space*, interp::Space*> dom2interp_Spaces;

std::unordered_map<interp::Frame*, domain::Frame*> interp2dom_Frames;

std::unordered_map<domain::Frame*, interp::Frame*> dom2interp_Frames;

	std::unordered_map <interp::PROGRAM*,	domain::DomainObject*	> 	interp2dom_PROGRAM;
	std::unordered_map <domain::DomainObject*,	interp::PROGRAM*	> 	dom2interp_PROGRAM;

	std::unordered_map <interp::GLOBALSTMT*,	domain::DomainObject*	> 	interp2dom_GLOBALSTMT;
	std::unordered_map <domain::DomainObject*,	interp::GLOBALSTMT*	> 	dom2interp_GLOBALSTMT;

	std::unordered_map <interp::STMT*,	domain::DomainObject*	> 	interp2dom_STMT;
	std::unordered_map <domain::DomainObject*,	interp::STMT*	> 	dom2interp_STMT;

	std::unordered_map <interp::FUNC_DECL*,	domain::DomainObject*	> 	interp2dom_FUNC_DECL;
	std::unordered_map <domain::DomainObject*,	interp::FUNC_DECL*	> 	dom2interp_FUNC_DECL;

	std::unordered_map <interp::VOID_FUNC_DECL_STMT*,	domain::DomainObject*	> 	interp2dom_VOID_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	interp::VOID_FUNC_DECL_STMT*	> 	dom2interp_VOID_FUNC_DECL_STMT;

	std::unordered_map <interp::MAIN_FUNC_DECL_STMT*,	domain::DomainObject*	> 	interp2dom_MAIN_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	interp::MAIN_FUNC_DECL_STMT*	> 	dom2interp_MAIN_FUNC_DECL_STMT;
};

} // namespace

#endif