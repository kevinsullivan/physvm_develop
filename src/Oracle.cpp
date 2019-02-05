// oracle.cpp
// implement the member functions in oracle header file

#include "Oracle.h"
#include "CodeCoordinate.h"
#include "Bridge.h"

#include <string>
#include <iostream>

using namespace std;
using namespace bridge;

void printSpaces(vector<Space>& spaces);
int selectSpace(vector<Space>& spaces, string);
int selectSpace(vector<Space>& spaces);

Space& Oracle::getSpaceForVector(string where) {
    vector<Space>& spaces = dom_.getAllSpaces();
	if (spaces.size() == 0) {
		cerr << "No abstract spaces available for interpretation. Bye!\n";
		exit(1);
	}

	printSpaces(spaces);
	int whichSpace = selectSpace(spaces, where);
	Space& result = spaces[whichSpace];
    return result;
	cerr << "End getSpacesForVector\n";
}

void printSpaces(vector<Space>& spaces) {
	cerr << "Available spaces:\t" << std::endl;
	int size = spaces.size();
	for (int i = 0; i < size; i++) {
		cerr << i << ". " << spaces[i].getName() << "\n";
	}
}

int selectSpace(vector<Space>& spaces, string where) {
	int choice = -1;
	while (choice == -1) {
		cerr<< "Space for vector at "<< where << "? ";
		cin >> choice;
		if (choice < 0 || choice >= (int)spaces.size())
		{
			choice = -1;
			continue;
		}
	}
	return choice;
}





