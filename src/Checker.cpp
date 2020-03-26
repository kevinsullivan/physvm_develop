/***********************************************
Lean-specific consistency-checking functionality
************************************************/

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <iostream>
#include "Checker.h"
#include "Domain.h"

//#include <g3log/g3log.hpp>

struct aFile {
    FILE* file;
    const char* name;
};

aFile* openFile();
void generateMath(aFile* f, interp::Interpretation* i);
bool checkMath(aFile*);
void cleanup(aFile*);

// return true if domain is consistent
bool Checker::Check() {
    aFile* f = openFile();
    generateMath(f, interp_); 
    bool status = checkMath(f);
    cleanup(f);
    return status;
}

/************************
 * Implementation Details
 * **********************/

void writeDomain(FILE*, domain::Domain& d);

aFile* openFile() {
    aFile* f = new aFile;
    std::string name = std::string(tmpnam(NULL)) + ".lean";
    char * name_cstr = new char [name.length()+1];
    strcpy (name_cstr, name.c_str());
    f->name = name_cstr;
    f->file = fopen(f->name,"w");
    return f;
}

void generateMath(aFile* f, interp::Interpretation* interp) {
    std::string math = "";
    math += "import vec\n\n";
    math += interp->toString_Spaces();
    math += interp->toString_Defs();
    math += interp->toString_FloatDefs();
    //LOG(DEBUG) << "Checker::generateMath generated this: \n"
    //           << math << "\n";
    fputs(math.c_str(), f->file);
    fclose(f->file);
}

void cleanup(aFile* f) {
    delete f->name;
    delete f;
}

/*
launch a domain output file type checking process
get the exit code to determine whether there was an error
return true if there was no error otherwise return false
*/
bool checkMath(aFile* f) {
    int status = system((std::string("lean ") + std::string(f->name)).c_str());
    return (status == 0); 
}

