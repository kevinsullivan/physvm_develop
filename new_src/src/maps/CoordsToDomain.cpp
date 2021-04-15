
#include "CoordsToDomain.h"

# include <iostream>

# include <g3log/g3log.hpp>



//using namespace std;
using namespace coords2domain;

/*
	coords::Coords getCoords(domain::Domain);
	domain::Domain getDomain(coords::Coords);
	bool put(coords::Coords,domain::Domain);
*/

coords::Coords* CoordsToDomain::getCoords(domain::DomainContainer* d){
    for(auto kp:edges){
        if(kp.second = d)
            return kp.first;
    }
};

domain::DomainContainer* CoordsToDomain::getDomain(coords::Coords* c){
    return this->edges[c];
};

bool CoordsToDomain::put(coords::Coords* c, domain::DomainContainer* d){
    this->edges[c] = d;

    return true;
};