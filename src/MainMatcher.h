#include "BaseMatcher.h"
#include "Interpretation.h"

class MainMatcher : public BaseMatcher {
public:
    MainMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) {}

    virtual void search();
    virtual void run(const MatchFinder::MatchResult &Result);

};