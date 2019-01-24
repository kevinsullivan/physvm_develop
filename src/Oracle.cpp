// oracle.cpp
// implement the member functions in oracle header file

#include "Oracle.h"
#include "Domain.h"
#include <string>
#include <iostream>
// using namespace std;

Space& Oracle::getSpaceForVector(const VectorASTNode& n) {
    /*
    TODO: Associate the same space with every vector.
    */

	std::cout<<"Available spaces:\t"<<std::endl;

    list<Space>& candidatespaces = dom_.getSpaces();
    for(list<Space>::iterator it = candidatespaces.begin();it != candidatespaces.end();++it){
    	std::cout<< it->getName()<<"\t";
	}

	std::cout<< "\nPlease annotate the space for "<< "VectorASTNode n"<<std::endl;
	string selected_space;
	std::cin>> selected_space;

	Space *annotated_space =new Space(selected_space);

    return *annotated_space;
}





