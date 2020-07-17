
#ifndef ORACLE_ASKALL_H
#define ORACLE_ASKALL_H

#include "Oracle.h"
#include "Domain.h"

namespace oracle{

class Oracle_AskAll : public Oracle 
{
public:
	Oracle_AskAll(domain::Domain* d) : domain_(d) { };

    domain::DomainObject* getInterpretation(coords::Coords* coords, domain::DomainObject* dom);
    //domain::Space &getSpace();
    //domain::MapSpace &getMapSpace();
    virtual domain::DomainObject* getInterpretationForSTMT(coords::STMT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForIFCOND(coords::IFCOND* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForEXPR(coords::EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForASSIGNMENT(coords::ASSIGNMENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForDECLARE(coords::DECLARE* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL1_EXPR(coords::REAL1_EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL3_EXPR(coords::REAL3_EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL4_EXPR(coords::REAL4_EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREALMATRIX_EXPR(coords::REALMATRIX_EXPR* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL4_VAR_IDENT(coords::REAL4_VAR_IDENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREALMATRIX_VAR_IDENT(coords::REALMATRIX_VAR_IDENT* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL1_LITERAL(coords::REAL1_LITERAL* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL3_LITERAL(coords::REAL3_LITERAL* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREAL4_LITERAL(coords::REAL4_LITERAL* coords, domain::DomainObject* dom);

    virtual domain::DomainObject* getInterpretationForREALMATRIX_LITERAL(coords::REALMATRIX_LITERAL* coords, domain::DomainObject* dom);

private:
	domain::Domain* domain_;
};

} // namespace

#endif
