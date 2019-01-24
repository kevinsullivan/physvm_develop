#include <iostream>
#include "Domain.h"

using namespace std;

// Todo: make this work right; STUBBED out
Vector::Vector() { space_ = *new Space(); }

Vector::Vector(Space& space) { space_ = space; }

// Todo: make these work right; STUBBED out
Expression::Expression() : v1_(*new Vector()), v2_(*new Vector()) {}
Expression::Expression(Vector& v1, Vector& v2) : v1_(v1), v2_(v2) {}

// Add new space,, s, to domain
// Precondition: true
// Postcondition: 
//	spaces' = spaces + s and
//  return value = reference to s
Space& Domain::addSpace(const string& name) {
    Space* s = new Space(name);
    spaces.push_front(*s);
    return *s;
}

// Add new vector, v, in space s, to domain
// Precondition: s is already in spaces
// Postcondition: vectors' = vectors + v
Vector& Domain::addVector(Space& s) {
    Vector *v = new Vector(s);
    vectors.push_front(*v);
    cout << "DOMAIN: Added vector!\n";
    return *v;
}

// Add new plus expression, e, to domain
// Precondition: v1 and v2 already in vectors
// Postcondition: expressions' = expressions + e
//	where e has v1 and v2 as its arguments
Expression& Domain::addExpression(Vector& v1, Vector& v2) {}

// Check domain for consistency
// Precondition: true
// Postcondition: return value true indicates presence of inconsistencies
bool Domain::isInconsistent() {
    return false;
}

list<Space>& Domain::getSpaces() {
    return spaces;
}
