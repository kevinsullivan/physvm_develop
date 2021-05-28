
#ifndef rosstatement
#define rosstatement
#include "../BaseMatcher.h"
#include "../Interpretation.h"

/*
See BaseMatcher.h for method details
Searches for relevant statements including physical calculations, generally inside a "compound" statement in a code block
*/

class ROSStatementMatcher : public BaseMatcher {
public:
    ROSStatementMatcher(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif
