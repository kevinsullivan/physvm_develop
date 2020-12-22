
#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include <iostream>
#include "Coords.h"
#include "Domain.h"

namespace oracle {

class Oracle {
public:
   // virtual domain::Frame* getFrameInterpretation();
   // virtual domain::Space* getSpaceInterpretation();

    
    virtual domain::DomainObject* getInterpretationForREALMATRIX4_EXPR(coords::REALMATRIX4_EXPR* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL3_EXPR(coords::REAL3_EXPR* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL3_LEXPR(coords::REAL3_LEXPR* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL1_EXPR(coords::REAL1_EXPR* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL1_VAR_IDENT(coords::REAL1_VAR_IDENT* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL3_VAR_IDENT(coords::REAL3_VAR_IDENT* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREALMATRIX4_VAR_IDENT(coords::REALMATRIX4_VAR_IDENT* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL3_LITERAL(coords::REAL3_LITERAL* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREAL1_LITERAL(coords::REAL1_LITERAL* coords, domain::DomainObject* dom) = 0;

    virtual domain::DomainObject* getInterpretationForREALMATRIX4_LITERAL(coords::REALMATRIX4_LITERAL* coords, domain::DomainObject* dom) = 0;


};

} // namespace

#endif
