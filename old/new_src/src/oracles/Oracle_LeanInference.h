#ifndef ORACLE_LEANINFERENCE_H
#define ORACLE_LEANINFERENCE_H

#include "Oracle.h"
#include "../Domain.h"
#include "../Interp.h"
#include <vector>
#include <unordered_map>

namespace oracle{

class Oracle_LeanInference : public Oracle 
{
public:
	Oracle_LeanInference(std::vector<interp::Interp*> ordered_nodes_, domain::Domain* d)  
        : ordered_nodes(ordered_nodes_), domain_(d) { };
    Oracle_LeanInference(domain::Domain* d) :domain_(d) { };
    void buildInterpretations(std::string peirceOutputName);

    domain::DomainObject* getInterpretation(coords::Coords* coords);

    void setNodes(std::vector<interp::Interp*> ordered_nodes_){
        this->ordered_nodes = ordered_nodes_;
    }
private:
    void generateLeanChecker(std::string peirceOutputName);    
    domain::DomainObject* parseInterpretation(std::vector<std::string> check_,std::vector<std::string> eval_);
    std::vector<interp::Interp*> ordered_nodes;
    std::vector<domain::DomainObject*> ordered_interpretations;
    domain::Domain* domain_;
};

}

#endif