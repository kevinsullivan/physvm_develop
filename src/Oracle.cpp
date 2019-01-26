// oracle.cpp
// implement the member functions in oracle header file

#include "Oracle.h"
#include "Domain.h"
#include "CodeCoordinate.h"

#include <string>
#include <iostream>

using namespace std;

void printSpaces(vector<Space>& spaces);
int selectSpace(vector<Space>& spaces);
int selectSpace(vector<Space>& spaces);

Space& Oracle::getSpaceForVector(const VectorASTNode& n) {
    vector<Space>& spaces = dom_.getAllSpaces();
	if (spaces.size() == 0) {
		cerr << "No abstract spaces available for interpretation. Bye!\n";
		exit(1);
	}
	printSpaces(spaces);
	int whichSpace = selectSpace(spaces);
	Space& result = spaces[whichSpace];
    return result;
}

void printSpaces(vector<Space>& spaces) {
	cout << "Available spaces:\t" << std::endl;
	int size = spaces.size();
	for (int i = 0; i < size; i++) {
		cout << i << ". " << spaces[i].getName() << "\n";
	}
/*
	for(vector<Space>::iterator it = spaces.begin();it != spaces.end();++it) {
		cout<< it->getName()<<"\t";
	}
*/
}

int selectSpace(vector<Space>& spaces) {
	int choice = -1;
	while (choice == -1) {
		cout<< "\nSelect space for " << "vector" << std::endl;
		cin >> choice;
		if (choice < 0 || choice >= spaces.size())
		{
			choice = -1;
			continue;
		}
		return choice;
	}
}





