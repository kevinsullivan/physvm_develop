
#include "InterpToDomain.h"

#include <iostream>

//#include <g3log/g3log.hpp>

using namespace interp2domain;

/*
	domain::Domain getDomain(interp::Interp);
	interp::Interp getInterp(domain::Domain);
	bool put(domain::Domain,interp::Interp);
*/

domain::DomainContainer* InterpToDomain::getDomain(interp::Interp* interp_){
    return this->edges[interp_];
};

interp::Interp* InterpToDomain::getInterp(domain::DomainContainer* domain_){
    for(auto kp:edges){
        if(kp.second == domain_)
            return kp.first;
    }
    return nullptr;
    
    //return this->edges[domain_];
};

bool InterpToDomain::put(interp::Interp* interp_,domain::DomainContainer* domain_){
    this->edges[interp_] = domain_;
    return true;
};