
#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "Coords.h"
#include "Domain.h"

#include <unordered_map>

/*
	When putting, we know precise subclass, so we don't include
	putters for Expr and Vector super-classes. When getting, we 
	generally don't know, so we can return superclass pointers.
*/

/*
We currently require client to create domain nodes, which we 
then map to and from the given coordinates. From coordinates 
is currently implement as unordered map. From domain object is
currently implemented as domain object method. This enables us
to return precisely typed objects without having to maintain a
lot of separate mapping tables.
*/

namespace coords2domain{

class CoordsToDomain
{
public:


	domain::DomainObject* getPROGRAM(coords::PROGRAM* c) const;
	coords::PROGRAM* getPROGRAM(domain::DomainObject* d) const;

	void putSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* key, domain::DomainObject* val);
	domain::DomainObject* getSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* c) const;
	coords::SEQ_GLOBALSTMT* getSEQ_GLOBALSTMT(domain::DomainObject* d) const;
void eraseSEQ_GLOBALSTMT(coords::SEQ_GLOBALSTMT* key, domain::DomainObject* val);

	domain::DomainObject* getGLOBALSTMT(coords::GLOBALSTMT* c) const;
	coords::GLOBALSTMT* getGLOBALSTMT(domain::DomainObject* d) const;

	domain::DomainObject* getSTMT(coords::STMT* c) const;
	coords::STMT* getSTMT(domain::DomainObject* d) const;

	void putCOMPOUND_STMT(coords::COMPOUND_STMT* key, domain::DomainObject* val);
	domain::DomainObject* getCOMPOUND_STMT(coords::COMPOUND_STMT* c) const;
	coords::COMPOUND_STMT* getCOMPOUND_STMT(domain::DomainObject* d) const;
void eraseCOMPOUND_STMT(coords::COMPOUND_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getFUNC_DECL(coords::FUNC_DECL* c) const;
	coords::FUNC_DECL* getFUNC_DECL(domain::DomainObject* d) const;

	domain::DomainObject* getVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* c) const;
	coords::VOID_FUNC_DECL_STMT* getVOID_FUNC_DECL_STMT(domain::DomainObject* d) const;

	void putVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);
void eraseVOID_FUNC_DECL_STMT(coords::VOID_FUNC_DECL_STMT* key, domain::DomainObject* val);

	domain::DomainObject* getMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* c) const;
	coords::MAIN_FUNC_DECL_STMT* getMAIN_FUNC_DECL_STMT(domain::DomainObject* d) const;

	void putMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);
void eraseMAIN_FUNC_DECL_STMT(coords::MAIN_FUNC_DECL_STMT* key, domain::DomainObject* val);

private:

	std::unordered_map <coords::PROGRAM*,	domain::DomainObject*	> 	coords2dom_PROGRAM;
	std::unordered_map <domain::DomainObject*,	coords::PROGRAM*	> 	dom2coords_PROGRAM;

	std::unordered_map <coords::GLOBALSTMT*,	domain::DomainObject*	> 	coords2dom_GLOBALSTMT;
	std::unordered_map <domain::DomainObject*,	coords::GLOBALSTMT*	> 	dom2coords_GLOBALSTMT;

	std::unordered_map <coords::STMT*,	domain::DomainObject*	> 	coords2dom_STMT;
	std::unordered_map <domain::DomainObject*,	coords::STMT*	> 	dom2coords_STMT;

	std::unordered_map <coords::FUNC_DECL*,	domain::DomainObject*	> 	coords2dom_FUNC_DECL;
	std::unordered_map <domain::DomainObject*,	coords::FUNC_DECL*	> 	dom2coords_FUNC_DECL;

	std::unordered_map <coords::VOID_FUNC_DECL_STMT*,	domain::DomainObject*	> 	coords2dom_VOID_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	coords::VOID_FUNC_DECL_STMT*	> 	dom2coords_VOID_FUNC_DECL_STMT;

	std::unordered_map <coords::MAIN_FUNC_DECL_STMT*,	domain::DomainObject*	> 	coords2dom_MAIN_FUNC_DECL_STMT;
	std::unordered_map <domain::DomainObject*,	coords::MAIN_FUNC_DECL_STMT*	> 	dom2coords_MAIN_FUNC_DECL_STMT;
};

} // namespace

#endif