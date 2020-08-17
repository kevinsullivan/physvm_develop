
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

    domain::Frame* getFrame(domain::Space* space);

    //domain::Space &getSpace();
    //domain::MapSpace &getMapSpace();
private:
	domain::Domain* domain_;
};

} // namespace

#endif
