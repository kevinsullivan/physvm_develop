#include "BaseMatcher.h"
#include "Interpretation.h"
/*
See BaseMatcher.h for method details
Starting point entry for matching Clang AST. Searches for main method
*/
class MainMatcher : public BaseMatcher {
public:
    MainMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}

    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};