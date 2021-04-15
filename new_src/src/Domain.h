
#ifndef BRIDGE_H
#define BRIDGE_H

#ifndef leanInferenceWildcard
#define leanInferenceWildcard "_"
#endif

#include <cstddef>  
#include "clang/AST/AST.h"
#include <vector>
#include <string>
#include <memory>
#include <typeinfo>

//#include "AST.h"
#include "Coords.h"

#include <g3log/g3log.hpp>


using namespace std;

/*
- Space
- Ident
- Expr
- Value
- Defn
*/

namespace domain{

class DomainObject;
class DomainContainer;
template<typename ValueType,int ValueCount>
class ValueObject;

class CoordinateSpace;
class StandardSpace;
template<int Dimension>
class DerivedSpace;
class TimeCoordinateSpace;
class StandardTimeCoordinateSpace;
class DerivedTimeCoordinateSpace;

class TimeCoordinateSpace;
class Duration;
class Time;
class Scalar;
class TimeTransform;

            
// Definition for Domain class 
using string = std::string;

class Domain {
public:
    DomainContainer* mkDefaultDomainContainer();
    DomainContainer* mkDefaultDomainContainer(std::initializer_list<DomainContainer*> operands);
    DomainContainer* mkDefaultDomainContainer(std::vector<DomainContainer*> operands);
    //DomainContainer* mkDefaultDomainContainer(std::initializer_list<DomainContainer*> operands);
    /*DomainContainer* mkDefaultDomainContainer(std::vector<DomainContainer*> operands){
        std::vector<DomainObject*> ops = {std::transform(operands.begin(), operands.end(), s.begin(),
                   [](DomainContainer* d) -> DomainObject* { return dynamic_cast<DomainObject*>(d) })};
        return mkDefaultDomainContainer(ops);
    }*/

    StandardTimeCoordinateSpace* mkStandardTimeCoordinateSpace(string name);
    DerivedTimeCoordinateSpace* mkDerivedTimeCoordinateSpace(string name, TimeCoordinateSpace* parent, float* originData, float** basisData);

    Duration* mkDuration(string name, TimeCoordinateSpace* parent, float* value);
    Time* mkTime(string name, TimeCoordinateSpace* parent, float* value);
    //Scalar* mkScalar();
    TimeTransform* mkTimeTransform(); 

    std::vector<TimeCoordinateSpace*> getTimeSpaces() const {return timeSpaces;};
    std::vector<CoordinateSpace*> getSpaces() const {return spaces;};
private:
    std::vector<TimeCoordinateSpace*> timeSpaces;
    std::vector<CoordinateSpace*> spaces;
};
class DomainObject {
public:
    DomainObject(std::initializer_list<DomainObject*> args);
    DomainObject(std::vector<DomainObject*> operands) : operands_(operands) {};
    DomainObject(){};
    DomainObject(string name_) : name(name_) {};
    virtual ~DomainObject(){};
    DomainObject* getOperand(int i);
    std::vector<DomainObject*> getOperands() const { return operands_; };
    void setOperands(std::vector<DomainObject*> operands);

    virtual std::string toString() const { return "Bad code if called!"; }
    friend class DomainObject; 

    std::string getName() const {
        return name;
    }
  
protected:
    std::vector<DomainObject*> operands_;
    int operand_count;
    std::string name;
};

class DomainContainer : public DomainObject{
public:
        DomainContainer() : DomainObject(), inner_(nullptr) {};
        DomainContainer(DomainObject* inner) : inner_(inner) {};
        DomainContainer(std::initializer_list<DomainObject*> operands);
        DomainContainer(std::vector<DomainObject*> operands);
        DomainContainer(std::initializer_list<DomainContainer*> operands);
        DomainContainer(std::vector<DomainContainer*> operands);
        virtual std::string toString() const override;// { this->hasValue() ? this->inner_->toString() : "No Provided Interpretation"; }
        DomainObject* getValue() const { return this->inner_; }
        void setValue(DomainObject* obj);
        bool hasValue() const;
        

private:
    DomainObject* inner_;
};

class CoordinateSpace : public DomainObject {
public:
    CoordinateSpace(){};
    virtual ~CoordinateSpace(){};
    CoordinateSpace(std::string name_) : name(name_) {};
    std::string getName() const { return name; };
private:
    std::string name;
};

class StandardSpace : public CoordinateSpace {
public:
    virtual ~StandardSpace(){};
    StandardSpace() {};
private:
};

template<int Dimension>
class DerivedSpace : public CoordinateSpace {
public:
    virtual ~DerivedSpace() {
        delete originData;
        delete basisData;
    };
    DerivedSpace(){
        originData = new float[Dimension];
        basisData = new float*[Dimension];
        for(int i = 0;i<Dimension;i++)
            basisData[i] = new float[Dimension];
    }
    DerivedSpace(CoordinateSpace* parentSpace_) : DerivedSpace() {
        parentSpace = parentSpace_;
    };
    DerivedSpace(CoordinateSpace* parentSpace_, float* originData_, float** basisData_) 
        : DerivedSpace(parentSpace_){
        originData = originData_;
        basisData = basisData_;
        //setOrigin(originData_);
        //setBasis(basisData_);
    };
    DerivedSpace(float* originData_, float** basisData_) : DerivedSpace() {
        originData = originData;
        basisData = basisData_;
        //setOrigin(originData_);
        //setBasis(basisData_);
    };

    float* getOrigin() const { return originData; };//work on this
    float** getBasis() const { return basisData; };
    void setOrigin(float* originData_){
        for(auto i = 0;i<Dimension;i++){
            originData[i] = originData_[i];
        }
    };
    void setBasis(float** basisData_){
        for(auto i = 0;i<Dimension;i++){
            for(auto j = 0;j<Dimension;j++){
                basisData[i][j] = basisData_[i][j];
            }
        }
    };

    CoordinateSpace* getParent() const { return parentSpace; }
protected:
    float* originData;
    float** basisData;
    CoordinateSpace* parentSpace;
};

class TimeCoordinateSpace : public CoordinateSpace {
public:
    TimeCoordinateSpace(std::string name) : CoordinateSpace(name) {};
private:
};

//it's a... diamond
class StandardTimeCoordinateSpace : public TimeCoordinateSpace, public StandardSpace {
public:
    StandardTimeCoordinateSpace(std::string name) : TimeCoordinateSpace(name) {};

    virtual std::string toString() const override{
        return TimeCoordinateSpace::getName() + " StandardTimeCoordinateSpace()";
    };
private:
};

class DerivedTimeCoordinateSpace : public TimeCoordinateSpace, public DerivedSpace<1> {
public:
    DerivedTimeCoordinateSpace(std::string name, 
        TimeCoordinateSpace* parentSpace_, float* originData, float** basisData)
        : TimeCoordinateSpace(name), DerivedSpace<1>(parentSpace_,originData, basisData){};//, parentSpace(parentSpace_) {};
    TimeCoordinateSpace* getParent() const {
        return dynamic_cast<TimeCoordinateSpace*>(DerivedSpace::getParent());
    }
    virtual std::string toString() const override{
        return TimeCoordinateSpace::getName() + " DerivedTimeCoordinateSpace(parent:" 
            + this->getParent()->getName() + ",origin:" + std::to_string(originData[0]) + ",basis:" + std::to_string(basisData[0][0]) + ")";
    };

private:
    //--TimeCoordinateSpace* parentSpace;
};

class Duration : public DomainObject {
public:
    Duration(std::string name_, TimeCoordinateSpace* sp, float* value_) 
        : DomainObject(name_), space(sp), value(value_) {};
    virtual std::string toString() const override {
        return this->getName() + " " + std::string("Duration(") + space->getName() + "," + std::to_string(value[0]) + ")"; 
    };
    virtual TimeCoordinateSpace* getSpace() const { return space; };
    virtual float* getValue() const { return value; };
private:
    TimeCoordinateSpace* space;
    float* value;
};

class Time : public DomainObject {
public:
    Time(std::string name_, TimeCoordinateSpace* sp, float* value_) 
        : DomainObject(name_), space(sp), value(value_) {};
    virtual std::string toString() const override {
        return this->getName() + " " + std::string("Time(") + space->getName() + "," + std::to_string(value[0]) + ")"; 
    };
    virtual TimeCoordinateSpace* getSpace() const { return space; };
    virtual float* getValue() const { return value; };
private:
    TimeCoordinateSpace* space;
    float* value;
};

class Scalar : public DomainObject {
public:
private:
    float value;
};

class TimeTransform : public DomainObject {
public:
private:
    TimeCoordinateSpace* domain;
    TimeCoordinateSpace* codomain;
};

} // end namespace

#endif