// CodeCoords class function implementation
#include <cstddef>
#include <string>

#include "clang/AST/AST.h"
#include "clang/AST/ODRHash.h"

#include "Coords.h"

using namespace coords;

const VecIdent *Coords::makeCoordsForVecIdent(const clang::VarDecl *ident) {
    VecIdent *vecCoords = new coords::VecIdent(ident);
    this->declCoords_.insert(std::make_pair(ident, vecCoords));
    cerr << "Coords::makeCoordsForVecIdent: Created coords object at " << std::hex << vecCoords << " for coords::ident at " << std::hex << ident 
    << " toString is : " << vecCoords->toString() << "\n";
}