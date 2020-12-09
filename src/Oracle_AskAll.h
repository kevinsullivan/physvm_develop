
#ifndef ORACLE_ASKALL_H
#define ORACLE_ASKALL_H

#include "Oracle.h"
#include "Domain.h"

namespace oracle{

class Oracle_AskAll : public Oracle 
{
public:
	Oracle_AskAll(domain::Domain* d)  : domain_(d) { };

    
    //virtual domain::Frame* getFrameInterpretation();
    //virtual domain::Space* getSpaceInterpretation();

    domain::DomainObject* getInterpretation(coords::Coords* coords, domain::DomainObject* dom);

    domain::Frame* getFrameForInterpretation(domain::Space* space);

    //domain::Space &getSpace();
    //domain::MapSpace &getMapSpace();
    virtual domain::DomainObject* getInterpretationForREAL3_EXPR(coords::REAL3_EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL3_LEXPR(coords::REAL3_LEXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL1_EXPR(coords::REAL1_EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL3_LITERAL(coords::REAL3_LITERAL* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL1_LITERAL(coords::REAL1_LITERAL* coords, domain::DomainObject* dom);

protected:
	domain::Domain* domain_;
};

} // namespace

#endif
