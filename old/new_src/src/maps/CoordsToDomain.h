
#ifndef COORDSTODOMAIN_H
#define COORDSTODOMAIN_H

#include <iostream>
#include "../Coords.h"
#include "../Domain.h"

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
	coords::Coords* getCoords(domain::DomainContainer*);
	domain::DomainContainer* getDomain(coords::Coords*);
	bool put(coords::Coords*,domain::DomainContainer*);

private:
	//std::unordered_map<
	//	std::string,//Subclass of Coords
		std::unordered_map<coords::Coords*, domain::DomainContainer*>
	//> 
	edges;

};

} // namespace

#endif