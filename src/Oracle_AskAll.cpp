
// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

# include <string>
# include <iostream>
# include <g3log/g3log.hpp>
# include <vector>
#include <memory>

//using namespace std;
using namespace oracle;



domain::Frame* Oracle_AskAll::getFrame(domain::Space* space){

    auto frames = space->getFrames();
    auto sz = (int)frames.size();
            
    while(true){
        int i = 0;
        std::cout<<"Available Frames For : " << space->toString() << "\n";
        for(auto fr : frames){
            std::cout<<"("+std::to_string((i++))+") "<<fr->toString()<<"\n";
        }
        int choice = 0;
        std::cin>>choice;
        if(choice > 0 and choice <= sz){
            return frames[choice-1];
        }
    }
    return nullptr;
}

domain::DomainObject* Oracle_AskAll::getInterpretation(coords::Coords* coords, domain::DomainObject* dom){

	if(false){}
	return nullptr;
}