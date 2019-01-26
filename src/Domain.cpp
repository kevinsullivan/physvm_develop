#include <iostream>
#include <vector>
#include "Domain.h"
#include "Checker.h"

using namespace std;
 
// Space class member function implementation
string Space::getName(){return name_;}


// Vector class member function implementation
Space& Vector::getVecSpace(){return space_;}


// Expression class member function implementation
Expression::Expression(Vector& v1, Vector& v2) : v1_(v1), v2_(v2) {}
Vector& Expression::getVecParam1(){return v1_;}
Vector& Expression::getVecParam2(){return v2_;}

// Domain class member function implementation

// Add new space,, s, to domain
// Precondition: true
// Postcondition: 
//	spaces' = spaces + s and
//  return value = reference to s
Space& Domain::addSpace(const string& name) {
    Space* s = new Space(name);
    spaces.push_back(*s);
    return *s;
}

// Add new vector, v, in space s, to domain
// Precondition: s is already in spaces
// Postcondition: vectors' = vectors + v
Vector& Domain::addVector(Space& s) {
    Vector *v = new Vector(s);
    vectors.push_back(*v);
    cout << "DOMAIN: Added vector!\n";
    return *v;
}

// Add new plus expression, e, to domain
// Precondition: v1 and v2 already in vectors
// Postcondition: expressions' = expressions + e
//	where e has v1 and v2 as its arguments
Expression& Domain::addExpression(Vector& v1, Vector& v2) {

	Expression* expr = new Expression(v1, v2);
	expressions.push_back(*expr);

	cout<< "DOMAIN: Added Expression!\n";
	return *expr;
	
}

vector<Space>& Domain::getAllSpaces() {
    return spaces;
}

// Check domain for consistency
// Precondition: true
// Postcondition: return value true indicates presence of inconsistencies
// Implementation: Call Lean-specific checking code below (make virtual)
bool Domain::isConsistent() {
    Checker* c = new Checker(*this);
    bool result = c->Check();
    delete c;
    return result;
}

