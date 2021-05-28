
#ifndef ORACLE_H
#define ORACLE_H

#include <string>
#include <iostream>
#include "../Coords.h"
#include "../Domain.h"

namespace oracle {

class Oracle {
public:
   // virtual domain::Frame* getFrameInterpretation();
   // virtual domain::Space* getSpaceInterpretation();
    std::vector<string> *choice_buffer;
    domain::DomainObject* getInterpretation(coords::Coords* coords);

};

} // namespace

#endif
