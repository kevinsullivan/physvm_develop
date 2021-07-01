
#ifndef ROSTFQuaternionguard
#define ROSTFQuaternionguard
#include "../BaseMatcher.h"
#include "../Interpretation.h"


class ROSTFQuaternion : public BaseMatcher {
public:
    ROSTFQuaternion(clang::ASTContext* context, interp::Interpretation* interp) : BaseMatcher(context, interp) { }
        virtual void setup();
        virtual void run(const MatchFinder::MatchResult &Result);

};

#endif