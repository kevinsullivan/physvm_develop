/***********************************************
Lean-specific consistency-checking functionality
************************************************/

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <iostream>
#include <string>
#include "Checker.h"
#include "Domain.h"

//#include <g3log/g3log.hpp>
/*
struct aFile {
    FILE* file;
    const char* name;
};
*/
aFile* openFile();
aFile* openFile(std::string);
void generateMath(aFile* f, interp::Interpretation* i, bool typecheck_mode_ = true);
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

std::string outputfile = "/peirce/PeirceOutput.lean";
std::string checkfile = "/peirce/PeirceOutput_CHECK.lean";

bool Checker::RebuildOutput(bool typecheck_mode_){//std::string check_data_){
    
    aFile* f = openFile(outputfile);
    generateMath(f, interp_, typecheck_mode_); 
    bool status = true;//checkMath(f);
    cleanup(f);

    /*
    this is a hack. remove this fairly soon. why on earth did i have to do this?
    */
    //aFile* f2 = openFile(checkfile);
    //fputs(check_data_.c_str(), f2->file);
    //fclose(f2->file);
   // cleanup(f2);

    return status;
}

bool Checker::Setup(){
    return true;
    //this->to_check_ = openFile();
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
    std::cout<<"Generating file ... " << name_cstr << "\n";
    f->file = fopen(f->name,"w");
    return f;
}
aFile* openFile(std::string fname) {
    aFile* f = new aFile;
    std::string name = fname;
    char * name_cstr = new char [name.length()+1];
    strcpy (name_cstr, name.c_str());
    f->name = name_cstr;
    std::cout<<"Generating file ... " << name_cstr << "\n";
    f->file = fopen(f->name,"w");
    return f;
}

void generateMath(aFile* f, interp::Interpretation* interp, bool typecheck_mode_) {
    std::string math = interp->toStringAST(typecheck_mode_);
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

