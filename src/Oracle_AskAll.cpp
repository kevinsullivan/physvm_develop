// Oracle_AskAll.cpp. An oracle that asks interactively for
// information on every vector-valued term.

#include "Oracle_AskAll.h"

#include <string>
#include <iostream>
#include <g3log/g3log.hpp>

//using namespace std;
using namespace oracle;

void printSpaces(std::vector<domain::Space*>& spaces);
int selectSpace(std::vector<domain::Space*>& spaces, std::string);
int selectSpace(std::vector<domain::Space*>& spaces);

domain::Space& Oracle_AskAll::getSpace() {
    std::vector<domain::Space*>& spaces = dom_->getSpaces();
	if (spaces.size() == 0) {
		LOG(FATAL) <<"Oracle_AskAll::getSpace:: No abstract spaces available for interpretation. Bye!\n";
		exit(1);
	}
	printSpaces(spaces);
	int whichSpace = selectSpace(spaces);
	domain::Space& result = *spaces[whichSpace];
    return result;
}


void printSpaces(std::vector<domain::Space*>& spaces) {
	std::cout <<"\nAvailable spaces:\t" << std::endl; 
	int size = spaces.size();
	for (int i = 0; i < size; i++) {
		std::cout <<i << ". " << spaces[i]->getName() << "\n";
	}
}

int selectSpace(std::vector<domain::Space*>& spaces) {
	int choice = -1;
	while (choice == -1) {
		std::cout << "Space? ";
		std::cin >> choice;
		if (choice < 0 || choice >= (int)spaces.size())
		{
			choice = -1;
			continue;
		}
	}
	return choice;
}





