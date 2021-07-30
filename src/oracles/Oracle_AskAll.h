
#ifndef ORACLE_ASKALL_H
#define ORACLE_ASKALL_H

#include "Oracle.h"
#include "../Domain.h"
#include <vector>

namespace oracle{

class Oracle_AskAll : public Oracle 
{
public:
	Oracle_AskAll(domain::Domain* d)  : domain_(d) { };

    
    //virtual domain::Frame* getFrameInterpretation();
    //virtual domain::Space* getSpaceInterpretation();

    domain::DomainObject* getInterpretation(coords::Coords* coords);

    std::string getName();
    template<int Dimension>
    float* getValueVector();/*not physical vector*/
    template<int Dimension>
    float** getValueMatrix();/*not physical vector*/
    template<typename SpaceType>
    domain::CoordinateSpace* selectSpace(std::vector<SpaceType*>);
    domain::TimeSeries* selectTimeSeries();
    domain::CoordinateSpace* getSpace();
    domain::DomainObject* selectExisting();
    domain::TimeSeries* buildTimeSeries(coords::Coords*);
    void addTimeStampedToTimeSeries();

    int getValidChoice(int lower, int upperExclusive, std::string menu);
    std::vector<std::string> getChoices(){
        return choices;
    }

protected:
	domain::Domain* domain_;
    std::vector<domain::DomainObject*> existing_interpretations; 
    std::vector<std::string> choices;
};

} // namespace

#endif
