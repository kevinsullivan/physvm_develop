
#include "CoordsToInterp.h"

#include <iostream>

//#include <g3log/g3log.hpp>

/*
	coords::Coords getCoords(interp::Interp);
	interp::Interp getInterp(coords::Coords);
	bool put (coords::Coords,interp::Interp);
*/
using namespace coords2interp;

coords::Coords* CoordsToInterp::getCoords(interp::Interp* interp_){
    for(auto kp:edges){
        if(kp.second == interp_)
            return kp.first;
    }
    return nullptr;
};

interp::Interp* CoordsToInterp::getInterp(coords::Coords* coords_){
    return this->edges[coords_];
};

bool CoordsToInterp::put(coords::Coords* coords_, interp::Interp* interp_){
    this->edges[coords_] = interp_;
    return true;
};