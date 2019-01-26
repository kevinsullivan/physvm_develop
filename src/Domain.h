#ifndef DOMAIN_H
#define DOMAIN_H

#include <vector>
#include <string>

using namespace std;

// Definition for Space class 
class Space {
public:
	Space() : name_("") {};
	Space(string name) : name_(name) {};
	string getName();

private:
	string name_;
};



// Definition for Vector class 

class Vector {
public:
	Vector() {}
	Vector(Space& space): space_(space){}
	Space& getVecSpace();
private:
	Space space_;
};


// Definition for Expression class 

class Expression {
public:
	Expression() : v1_(*new Vector()), v2_(* new Vector()){}
	Expression(Vector& v1, Vector& v2);

	Vector& getVecParam1();
	Vector& getVecParam2();
private:
	Vector& v1_;
	Vector& v2_;
};


// Definition for Domain class 
class Domain {

public:

	// Add new space,, s, to domain
	// Precondition: true
	// Postcondition: 
	//	spaces' = spaces + s and
	//  return value = reference to s
	Space& addSpace(const string& name);

	// Add new vector, v, in space s, to domain
	// Precondition: s is already in spaces
	// Postcondition: vectors' = vectors + v
	Vector& addVector(Space& s);

	// Add new plus expression, e, to domain
	// Precondition: v1 and v2 already in vectors
	// Postcondition: expressions' = expressions + e
	//	where e has v1 and v2 as its arguments
	Expression& addExpression(Vector& v1, Vector& v2);

	// Check domain for consistency
	// Precondition: true
	// Postcondition: return value true indicates presence of inconsistencies
	bool isConsistent();

	/*
	Methods by which clients can learn what's in this domain.
	*/

	Space& get_nth_Spaces();

	vector<Space>& getAllSpaces();
	
private:
	vector<Space> spaces;
	vector<Vector> vectors;
	vector<Expression> expressions;
};

#endif