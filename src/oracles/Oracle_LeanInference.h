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
    domain::DomainObject* getAllInterpretation(coords::Coords* coords);
    std::string leanInferenceOutputStr(std::string peirceOutputName);
    void setNodes(std::vector<interp::Interp*> ordered_nodes_){
        this->ordered_nodes = ordered_nodes_;
    }
    void setAllNodes(std::vector<interp::Interp*> all_nodes_){
        this->all_nodes = all_nodes_;
    }
    void generateLeanChecker(std::string peirceOutputName);  
private:  
    domain::DomainObject* parseInterpretation(std::string type_,std::string error_);
    std::vector<interp::Interp*> ordered_nodes;
    std::vector<domain::DomainObject*> ordered_interpretations;
    std::vector<interp::Interp*> all_nodes;
    std::vector<domain::DomainObject*> all_interpretations;
    domain::Domain* domain_;
};

}

#endif