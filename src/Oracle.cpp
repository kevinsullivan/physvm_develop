// oracle.cpp
// implement the member functions in oracle header file

#include "Oracle.h"
#include "Coords.h"
#include "Domain.h"

#include <string>
#include <iostream>

#include "easylogging++.h"


using namespace std;
using namespace oracle;

void printSpaces(vector<domain::Space*>& spaces);
int selectSpace(vector<domain::Space*>& spaces, std::string);
int selectSpace(vector<domain::Space*>& spaces);

/*
domain::Space& Oracle::getSpaceForVector(std::string where) {
	LOG(DEBUG) <<"getSpaceForVector should take AST argument\n";
	return this->getSpace();
}
*/

domain::Space& Oracle::getSpace() {
    vector<domain::Space*>& spaces = dom_->getSpaces();
	if (spaces.size() == 0) {
		LOG(ERROR) <<"Oracle::getSpace:: No abstract spaces available for interpretation. Bye!\n";
		exit(1);
	}
	printSpaces(spaces);
	int whichSpace = selectSpace(spaces);
	domain::Space& result = *spaces[whichSpace];
    return result;
}




void printSpaces(vector<domain::Space*>& spaces) {
	cout <<"Available spaces:\t" << std::endl;
	int size = spaces.size();
	for (int i = 0; i < size; i++) {
		cout <<i << ". " << spaces[i]->getName() << "\n";
	}
}

int selectSpace(vector<domain::Space*>& spaces) {
	int choice = -1;
	while (choice == -1) {
		std::cout << "Space? ";
		cin >> choice;
		if (choice < 0 || choice >= (int)spaces.size())
		{
			choice = -1;
			continue;
		}
	}
	return choice;
}





