#ifndef COORDSTOINTERP_H
#define COORDSTOINTERP_H

# include <iostream>
# include "../Coords.h"
# include "../Interp.h"

# include <unordered_map>

namespace coords2interp{

class CoordsToInterp
{
public:
	coords::Coords* getCoords(interp::Interp*);
	interp::Interp* getInterp(coords::Coords*);
	bool put (coords::Coords*,interp::Interp*);

private:
	//std::unordered_map<
	//	std::string,//Subclass of Coords
		std::unordered_map<coords::Coords*, interp::Interp*>
	//	> 
		edges;
};

} // namespace

#endif