#ifndef INTERPTODOMAIN_H
#define INTERPTODOMAIN_H

#include <iostream>
#include "../Domain.h"

//namespace interp
//{
 
//} // namespace

//#ifndef INTERP_H
#include "../Interp.h"
//#endif

#include <unordered_map>

namespace interp2domain{

class InterpToDomain
{
public:
	domain::DomainContainer* getDomain(interp::Interp*);
	interp::Interp* getInterp(domain::DomainContainer*);
	bool put(interp::Interp*,domain::DomainContainer*);

private:
	//std::unordered_map<
	//	std::string,//Subclass of Coords
		std::unordered_map<interp::Interp*, domain::DomainContainer*>
	//> 
	edges;
};

} // namespace

#endif