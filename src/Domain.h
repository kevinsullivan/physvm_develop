
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

#include "AST.h"
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



class Space;
class DerivedSpace;
class MapSpace;
class Frame;
class StandardFrame;
class AliasedFrame;
class DerivedFrame;
class DomainObject;
class DomainContainer;
template<typename ValueType,int ValueCount>
class ValueObject;

class EuclideanGeometry;

class EuclideanGeometryFrame;

class EuclideanGeometryStandardFrame;

class EuclideanGeometryAliasedFrame;

class EuclideanGeometryDerivedFrame;

class MeasurementSystem;

class SIMeasurementSystem;

class ImperialMeasurementSystem;

template<typename ValueType,int ValueCount>
class EuclideanGeometryRotation;

template<typename ValueType,int ValueCount>
class EuclideanGeometryOrientation;

template<typename ValueType,int ValueCount>
class EuclideanGeometryFrameChange;

template<typename ValueType,int ValueCount>
class EuclideanGeometryCoordinatePoint;

template<typename ValueType,int ValueCount>
class EuclideanGeometryCoordinateVector;

class ClassicalTime;

class ClassicalTimeFrame;

class ClassicalTimeStandardFrame;

class ClassicalTimeAliasedFrame;

class ClassicalTimeDerivedFrame;

class MeasurementSystem;

class SIMeasurementSystem;

class ImperialMeasurementSystem;

template<typename ValueType,int ValueCount>
class ClassicalTimeFrameChange;

template<typename ValueType,int ValueCount>
class ClassicalTimeCoordinatePoint;

template<typename ValueType,int ValueCount>
class ClassicalTimeCoordinateVector;

class ClassicalVelocity;

class ClassicalVelocityFrame;

class ClassicalVelocityStandardFrame;

class ClassicalVelocityAliasedFrame;

class ClassicalVelocityDerivedFrame;

class MeasurementSystem;

class SIMeasurementSystem;

class ImperialMeasurementSystem;

template<typename ValueType,int ValueCount>
class ClassicalVelocityCoordinateVector;

            
// Definition for Domain class 

class Domain {
public:
// Space
	std::vector<Space*>& getSpaces();


    Space* getSpace(std::string key);

    DomainObject* mkDefaultDomainContainer();
    DomainObject* mkDefaultDomainContainer(std::initializer_list<DomainObject*> operands);
    DomainObject* mkDefaultDomainContainer(std::vector<DomainObject*> operands);
    //Frame* mkFrame(std::string name, Space* space, Frame* parent);
    //Frame<sp>* mkAliasedFrame(std::string name, Frame* aliased);

    //Frame<sp>* mkDerivedFrame(std::string name, Frame* parent);


    MapSpace* mkMapSpace(Space* space, Frame* dom, Frame* cod);


    SIMeasurementSystem* mkSIMeasurementSystem(string name);

    ImperialMeasurementSystem* mkImperialMeasurementSystem(string name);


    std::vector<MeasurementSystem*> measurementSystems;
    std::vector<MeasurementSystem*> getMeasurementSystems() const{return measurementSystems;};


	EuclideanGeometry* mkEuclideanGeometry(std::string key ,std::string name_, int dimension_);
	std::vector<EuclideanGeometry*> &getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

	EuclideanGeometryAliasedFrame* mkEuclideanGeometryAliasedFrame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometryFrame* aliased, domain::MeasurementSystem* ms);
	EuclideanGeometryDerivedFrame* mkEuclideanGeometryDerivedFrame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometryFrame* parent);

template <class ValueType, int ValueCount>
EuclideanGeometryRotation<ValueType,ValueCount>* mkEuclideanGeometryRotation(EuclideanGeometry* sp, std::shared_ptr<ValueType> values[ValueCount]){
    EuclideanGeometryRotation<ValueType,ValueCount>* dom_ = new EuclideanGeometryRotation<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->EuclideanGeometryRotation_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
EuclideanGeometryRotation<ValueType,ValueCount>* mkEuclideanGeometryRotation(){
    EuclideanGeometryRotation<ValueType,ValueCount>* dom_ = new EuclideanGeometryRotation<ValueType,ValueCount>({});
    //this->EuclideanGeometryRotation_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}


template <class ValueType, int ValueCount>
EuclideanGeometryOrientation<ValueType,ValueCount>* mkEuclideanGeometryOrientation(EuclideanGeometry* sp, std::shared_ptr<ValueType> values[ValueCount]){
    EuclideanGeometryOrientation<ValueType,ValueCount>* dom_ = new EuclideanGeometryOrientation<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->EuclideanGeometryOrientation_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
EuclideanGeometryOrientation<ValueType,ValueCount>* mkEuclideanGeometryOrientation(){
    EuclideanGeometryOrientation<ValueType,ValueCount>* dom_ = new EuclideanGeometryOrientation<ValueType,ValueCount>({});
    //this->EuclideanGeometryOrientation_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}


template <class ValueType, int ValueCount>
EuclideanGeometryFrameChange<ValueType,ValueCount>* mkEuclideanGeometryFrameChange(MapSpace* sp, std::shared_ptr<ValueType> values[ValueCount]){
    EuclideanGeometryFrameChange<ValueType,ValueCount>* dom_ = new EuclideanGeometryFrameChange<ValueType,ValueCount>(sp, {});
    //((ValueObject<ValueType,ValueCount>)(dom_))->setValues(values);
    //this->EuclideanGeometryFrameChange_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }
    return dom_;
}
                

template <class ValueType, int ValueCount>
EuclideanGeometryFrameChange<ValueType,ValueCount>* mkEuclideanGeometryFrameChange(){
    EuclideanGeometryFrameChange<ValueType,ValueCount>* dom_ = new EuclideanGeometryFrameChange<ValueType,ValueCount>({});
    //this->EuclideanGeometryFrameChange_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}


template <class ValueType, int ValueCount>
EuclideanGeometryCoordinatePoint<ValueType,ValueCount>* mkEuclideanGeometryCoordinatePoint(EuclideanGeometry* sp, std::shared_ptr<ValueType> values[ValueCount]){
    EuclideanGeometryCoordinatePoint<ValueType,ValueCount>* dom_ = new EuclideanGeometryCoordinatePoint<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->EuclideanGeometryCoordinatePoint_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
EuclideanGeometryCoordinatePoint<ValueType,ValueCount>* mkEuclideanGeometryCoordinatePoint(){
    EuclideanGeometryCoordinatePoint<ValueType,ValueCount>* dom_ = new EuclideanGeometryCoordinatePoint<ValueType,ValueCount>({});
    //this->EuclideanGeometryCoordinatePoint_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}


template <class ValueType, int ValueCount>
EuclideanGeometryCoordinateVector<ValueType,ValueCount>* mkEuclideanGeometryCoordinateVector(EuclideanGeometry* sp, std::shared_ptr<ValueType> values[ValueCount]){
    EuclideanGeometryCoordinateVector<ValueType,ValueCount>* dom_ = new EuclideanGeometryCoordinateVector<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->EuclideanGeometryCoordinateVector_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
EuclideanGeometryCoordinateVector<ValueType,ValueCount>* mkEuclideanGeometryCoordinateVector(){
    EuclideanGeometryCoordinateVector<ValueType,ValueCount>* dom_ = new EuclideanGeometryCoordinateVector<ValueType,ValueCount>({});
    //this->EuclideanGeometryCoordinateVector_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}

	ClassicalTime* mkClassicalTime(std::string key ,std::string name_);
	std::vector<ClassicalTime*> &getClassicalTimeSpaces() { return ClassicalTime_vec; }

	ClassicalTimeAliasedFrame* mkClassicalTimeAliasedFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* aliased, domain::MeasurementSystem* ms);
	ClassicalTimeDerivedFrame* mkClassicalTimeDerivedFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* parent);

template <class ValueType, int ValueCount>
ClassicalTimeFrameChange<ValueType,ValueCount>* mkClassicalTimeFrameChange(MapSpace* sp, std::shared_ptr<ValueType> values[ValueCount]){
    ClassicalTimeFrameChange<ValueType,ValueCount>* dom_ = new ClassicalTimeFrameChange<ValueType,ValueCount>(sp, {});
    //((ValueObject<ValueType,ValueCount>)(dom_))->setValues(values);
    //this->ClassicalTimeFrameChange_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }
    return dom_;
}
                

template <class ValueType, int ValueCount>
ClassicalTimeFrameChange<ValueType,ValueCount>* mkClassicalTimeFrameChange(){
    ClassicalTimeFrameChange<ValueType,ValueCount>* dom_ = new ClassicalTimeFrameChange<ValueType,ValueCount>({});
    //this->ClassicalTimeFrameChange_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}


template <class ValueType, int ValueCount>
ClassicalTimeCoordinatePoint<ValueType,ValueCount>* mkClassicalTimeCoordinatePoint(ClassicalTime* sp, std::shared_ptr<ValueType> values[ValueCount]){
    ClassicalTimeCoordinatePoint<ValueType,ValueCount>* dom_ = new ClassicalTimeCoordinatePoint<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->ClassicalTimeCoordinatePoint_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
ClassicalTimeCoordinatePoint<ValueType,ValueCount>* mkClassicalTimeCoordinatePoint(){
    ClassicalTimeCoordinatePoint<ValueType,ValueCount>* dom_ = new ClassicalTimeCoordinatePoint<ValueType,ValueCount>({});
    //this->ClassicalTimeCoordinatePoint_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}


template <class ValueType, int ValueCount>
ClassicalTimeCoordinateVector<ValueType,ValueCount>* mkClassicalTimeCoordinateVector(ClassicalTime* sp, std::shared_ptr<ValueType> values[ValueCount]){
    ClassicalTimeCoordinateVector<ValueType,ValueCount>* dom_ = new ClassicalTimeCoordinateVector<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->ClassicalTimeCoordinateVector_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
ClassicalTimeCoordinateVector<ValueType,ValueCount>* mkClassicalTimeCoordinateVector(){
    ClassicalTimeCoordinateVector<ValueType,ValueCount>* dom_ = new ClassicalTimeCoordinateVector<ValueType,ValueCount>({});
    //this->ClassicalTimeCoordinateVector_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}

	ClassicalVelocity* mkClassicalVelocity(std::string key, std::string name_,Space* base1, Space* base2);
	std::vector<ClassicalVelocity*> &getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

	ClassicalVelocityAliasedFrame* mkClassicalVelocityAliasedFrame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocityFrame* aliased, domain::MeasurementSystem* ms);
	ClassicalVelocityDerivedFrame* mkClassicalVelocityDerivedFrame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocityFrame* parent);

template <class ValueType, int ValueCount>
ClassicalVelocityCoordinateVector<ValueType,ValueCount>* mkClassicalVelocityCoordinateVector(ClassicalVelocity* sp, std::shared_ptr<ValueType> values[ValueCount]){
    ClassicalVelocityCoordinateVector<ValueType,ValueCount>* dom_ = new ClassicalVelocityCoordinateVector<ValueType,ValueCount>(sp, {});
    //dom_->setValues(values);
    //this->ClassicalVelocityCoordinateVector_vec.push_back(dom_);
    for(int i = 0; i < ValueCount;i++){
        dom_->setValue(values[i],i);
    }

    return dom_;
}
                

template <class ValueType, int ValueCount>
ClassicalVelocityCoordinateVector<ValueType,ValueCount>* mkClassicalVelocityCoordinateVector(){
    ClassicalVelocityCoordinateVector<ValueType,ValueCount>* dom_ = new ClassicalVelocityCoordinateVector<ValueType,ValueCount>({});
    //this->ClassicalVelocityCoordinateVector_vec.push_back(dom_);
    /*int i = 0;
    for(auto val : values){
        dom_->setValue(values[i],i++);
    } */  
    return dom_;
}

private:

	std::unordered_map<std::string, Space*> Space_map;
	std::vector<Space*> Space_vec;
	std::vector<EuclideanGeometry*> EuclideanGeometry_vec;
	std::vector<ClassicalTime*> ClassicalTime_vec;
	std::vector<ClassicalVelocity*> ClassicalVelocity_vec;
};


class Space {
public:
	Space() {};
    Space(string name, int dimension) : name_(name), dimension_(dimension) {};
    virtual ~Space(){};
	virtual std::string toString() const {
		return "Not implemented"; 
	}
    virtual std::string getName() const {
        return this->name_;
    }
    int getDimension() const {
        return this->dimension_;
    }

    std::vector<Frame*> getFrames() const { return this->frames_; };
    void addFrame(Frame* frame);

protected:
    std::vector<Frame*> frames_;
    std::string name_;
    int dimension_;

};

class MeasurementSystem {
public :
    MeasurementSystem(std::string name) : name_(name) {};
    virtual ~MeasurementSystem() {};
    virtual std::string toString() = 0;

    virtual std::string getName() const { return this->name_; };

protected :
    std::string name_;
};

class SIMeasurementSystem : public MeasurementSystem {
public:
    SIMeasurementSystem(std::string name) : MeasurementSystem(name) {};
    //virtual ~SIMeasurementSystem() {};
    virtual std::string toString() override { return "@@SI " + this->name_; };
};

class ImperialMeasurementSystem : public MeasurementSystem {
public:
    ImperialMeasurementSystem(std::string name) : MeasurementSystem(name) {};
   // virtual ~SIMeasurementSystem() {};
    virtual std::string toString() override { return "@@Imperial " + this->name_; };
};

class Frame {
public:
    Frame(std::string name, Space* sp) : name_(name), sp_(sp) {};
    Frame() {};
    virtual ~Frame(){};
    virtual std::string toString() const {
        return std::string("@@") + typeid(sp_).name() + "Frame " + this->getName();
    }

    //Frame* getParent() const{ return parent_; };
    //void setParent(Frame* parent);

    virtual std::string getName() const { return name_; };

    Space* getSpace() const { return sp_; };

protected:
    std::string name_;
    Space* sp_;
};

class StandardFrame : public Frame {
public:
    StandardFrame(Space* sp) : Frame("Standard", sp) {};
    StandardFrame() {};
    virtual ~StandardFrame(){};

    virtual std::string toString() const override { return this->getName() + "(" + this->sp_->getName() + ")"; };

    virtual std::string getName() const override { return this->sp_->getName() + ".standardFrame"; };

    //Space* getSpace() const { return space_; };

protected:
    std::string alias_;
};

class AliasedFrame : public Frame {
public:
    AliasedFrame(std::string name, Space* sp, Frame* original, domain::MeasurementSystem* ms) : Frame(name, sp), original_(original), units_(ms) {};
    AliasedFrame() {};
    virtual ~AliasedFrame(){};
    virtual std::string toString() const {
        return this->getName() + std::string("(") + this->sp_->getName() + "," + original_->getName() + ")";
    }

    Frame* getAliased() const{ return original_; };
    MeasurementSystem* getUnits() const { return units_; };
    void setAliased(Frame* original);

    std::string getName() const { return name_; };

    //Space* getSpace() const { return this->sp_; };

protected:
    Frame* original_;
    MeasurementSystem* units_;
    //std::string name_;
};

class DerivedFrame : public Frame {
public:
    DerivedFrame(std::string name, domain::Space* sp, Frame* parent) : Frame(name, sp), parent_(parent) {};
    DerivedFrame() {};
    virtual ~DerivedFrame(){};
    virtual std::string toString() const override {
        return this->getName() + std::string("(") + this->sp_->getName() + "," + parent_->getName() + ")";
    }

    Frame* getParent() const{ return parent_; };
    MeasurementSystem* getUnits() const { return units_; };
    void setParent(Frame* parent);

    //std::string getName() const { return name_; };
protected:
    Frame* parent_;
    MeasurementSystem* units_;
};

class DerivedSpace : public Space {
public:
    DerivedSpace() {};
    DerivedSpace(string name, Space* base1, Space* base2) :  Space(name, base1->getDimension()*base2->getDimension()), base_1(base1), base_2(base2) {
        
    }

    Space* getBase1() const {
        return this->base_1;
    }

    Space* getBase2() const {
        return this->base_2;
    }

    virtual ~DerivedSpace(){};
	virtual std::string toString() const override {
		return "Not implemented"; 
	}

protected:
    Space* base_1;
    Space* base_2;
};



//pretend this is a union
class MapSpace : public Space {
public:
	MapSpace() {}
	MapSpace(domain::Space* domain, domain::Space* codomain) : domain_(domain), codomain_(codomain), change_space_{true}, change_frame_{true} {};

    MapSpace(domain::Space* domain, domain::Space* codomain, Frame* domain_frame, Frame* codomain_frame) 
        : domain_(domain), domain_frame_(domain_frame), codomain_(codomain), codomain_frame_(codomain_frame), change_space_{true}, change_frame_{true} {};

    MapSpace(domain::Space* domain, Frame* domain_frame, Frame* codomain_frame)
        : domain_(domain), domain_frame_(domain_frame), codomain_(nullptr), codomain_frame_(codomain_frame), change_space_{false}, change_frame_{true} {};
	std::string toString() const {
        return "@@Map(" + this->getName() + ")";
    };
    std::string getName() const{
        if(change_space_){
            if(change_frame_){
                return domain_->getName()+"."+domain_frame_->getName()+"->"+codomain_->getName()+"."+codomain_frame_->getName();
            }
            else{
                return domain_->getName()+"->"+codomain_->getName();
            }
        }
        else{
            if(change_frame_){
                return domain_->getName()+"."+domain_frame_->getName()+"->"+domain_->getName()+"."+codomain_frame_->getName();
            }
        }
        return "";
    }
        

	domain::Space* domain_;
	domain::Frame* domain_frame_;

    domain::Space* codomain_;
    domain::Frame* codomain_frame_;
    
    bool change_space_;
    bool change_frame_;
};
class DomainObject {
public:
    DomainObject(std::initializer_list<DomainObject*> args);
    DomainObject(std::vector<DomainObject*> operands) : operands_(operands) {};
    DomainObject(){};
    virtual ~DomainObject(){};
    DomainObject* getOperand(int i);
    std::vector<DomainObject*> getOperands() const { return operands_; };
    void setOperands(std::vector<DomainObject*> operands);

    virtual std::string toString();
    friend class DomainObject; 
  
protected:
    std::vector<DomainObject*> operands_;
    int operand_count;
};

class DomainContainer : public DomainObject{
public:
        DomainContainer() : DomainObject(), inner_(nullptr) {};
        DomainContainer(DomainObject* inner) : inner_(inner) {};
        DomainContainer(std::initializer_list<DomainObject*> operands);
        DomainContainer(std::vector<DomainObject*> operands);
        virtual std::string toString() override;// { this->hasValue() ? this->inner_->toString() : "No Provided Interpretation"; }
        DomainObject* getValue() const { return this->inner_; }
        void setValue(DomainObject* obj);
        bool hasValue();
        

private:
    DomainObject* inner_;
};


template <typename ValueType, int ValueCount>
class ValueObject : public DomainObject {
public:
    // ValueCoords() : DomainObject() {};

    ValueObject() : DomainObject(){
        for(int i = 0; i<ValueCount;i++){
            this->values_[i] = nullptr;
        }
    };

    ValueObject(std::initializer_list<DomainObject*> args) :  DomainObject(args) {
        for(int i = 0; i<ValueCount;i++){
            this->values_[i] = nullptr;
        }

    }
    ValueObject(std::vector<DomainObject*> operands) : DomainObject(operands) {
        for(int i = 0; i<ValueCount;i++){
            this->values_[i] = nullptr;
        }

    }

    ~ValueObject() {
        for(auto v : this->values_){
           // delete v;
        }
    }

    ValueObject(ValueType* values...) : DomainObject() {
        int i = 0;
        for(auto val : {values}){
            if(i == ValueCount)
                throw "Out of Range";
            this->values_[i++] = std::make_shared<ValueType>(*val);

        }
    }

    ValueObject(std::initializer_list<DomainObject*> args, ValueType* values...) : ValueObject(values), DomainObject(args)
    {
    }

    ValueObject(std::vector<DomainObject*> operands, ValueType* values...) : ValueObject(values), DomainObject(operands)
    {
        int i = 0;
        for (auto val : { values}){
            if (i == ValueCount)
                throw "Out of Range";
            this->values_[i++] = std::make_shared<ValueType>(*val);

        }
    }

    virtual std::string toString() override {
        std::string ret = "Value=<";
    int i = 1;
        for(auto val : this->values_){
        ret += (val ? std::to_string(*val) : "UNK") + (i++ == ValueCount ? "" : ",");
    }
        return ret + ">";
    }

    ValueObject(ValueType* values[ValueCount]) : DomainObject(), values_(values) { };

    std::shared_ptr<ValueType> getValue(int index) const {
        if(index< 0 or index >= ValueCount)
            throw "Invalid Index";
        return this->values_[index];
    };

    void setValue(ValueType value, int index)
    {
        if (index < 0 or index >= ValueCount)
            throw "Invalid Index";
        if (this->values_[index])
            *this->values_[index] = value;
        else
            this->values_[index] = std::make_shared<ValueType>(value);
        //this->values_[index] = new ValueType(value)
    };

    void setValue(std::shared_ptr<ValueType> value, int index)
    {
        if (index < 0 or index >= ValueCount)
            throw "Invalid Index";
        if (this->values_[index])
            if(value)
                *this->values_[index] = *value;
            else{
                this->values_[index] = std::make_shared<ValueType>(*value);
            }
        else
            this->values_[index] = value ? std::make_shared<ValueType>(*value) : nullptr;
        //this->values_[index] = value ? new ValueType(*value) : nullptr;
    };
    protected:
    std::shared_ptr<ValueType> values_[ValueCount];
};



class EuclideanGeometry : public Space {
    public:
	    EuclideanGeometry(std::string name, int dimension) : Space(name, dimension) {};
	    std::string getName() const override { return name_; }; 
	    
        void addFrame(EuclideanGeometryFrame* frame);
	    std::string toString() const override {
		    return "@@EuclideanGeometry  " + getName()   + "("+ std::to_string(getDimension()) + ")"; 
	    }

    private:
    };


class EuclideanGeometryFrame : public Frame {
public:
	EuclideanGeometryFrame(std::string name,  EuclideanGeometry* space) : Frame(name, space) {};
    EuclideanGeometryFrame(){};
	/*std::string toString() const override {
        std::string parentName = ((EuclideanGeometry*)this->space_)->getName();
		return "@@EuclideanGeometryFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/

private:
};



class EuclideanGeometryStandardFrame : public StandardFrame, public EuclideanGeometryFrame {
public:
	EuclideanGeometryStandardFrame(EuclideanGeometry* space) : StandardFrame(space) {};
	/*std::string toString() const override {
        std::string parentName = ((EuclideanGeometry*)this->space_)->getName();
		return "@@EuclideanGeometryFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/

    virtual std::string getName() const override {
        return StandardFrame::getName();
    };

    virtual std::string toString() const override {
        return std::string("EuclideanGeometryStandardFrame ") + StandardFrame::toString();
    };

private:
};



class EuclideanGeometryAliasedFrame : public AliasedFrame, public EuclideanGeometryFrame {
public:
	EuclideanGeometryAliasedFrame(std::string name,  EuclideanGeometry* space, EuclideanGeometryFrame* aliased, domain::MeasurementSystem* ms) : AliasedFrame(name, space, aliased,  ms) {};
	/*std::string toString() const override {
        std::string parentName = ((EuclideanGeometry*)this->space_)->getName();
		return "@@EuclideanGeometryFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/
    virtual std::string toString() const override {
        return std::string("EuclideanGeometryAliasedFrame ") + AliasedFrame::toString();
    };

private:
};



class EuclideanGeometryDerivedFrame : public DerivedFrame, public EuclideanGeometryFrame {
public:
	EuclideanGeometryDerivedFrame(std::string name,  EuclideanGeometry* space, EuclideanGeometryFrame* parent) : DerivedFrame(name, space, parent) {};
	/*std::string toString() const override {
        std::string parentName = ((EuclideanGeometry*)this->space_)->getName();
		return "@@EuclideanGeometryFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/
    virtual std::string toString() const override {
        return std::string("EuclideanGeometryDerivedFrame ") + DerivedFrame::toString();
    };

private:
};




template <class ValueType, int ValueCount>
class EuclideanGeometryRotation : public ValueObject<ValueType,ValueCount> {
public:
    EuclideanGeometryRotation(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    EuclideanGeometryRotation(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~EuclideanGeometryRotation(){}
    std::string toString() override {
        return "@@EuclideanGeometryRotation(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString() + ")";
    }

    EuclideanGeometry* getSpace() const {return this->space_;};
    
    
private:
    EuclideanGeometry* space_; 
    
    
};




template <class ValueType, int ValueCount>
class EuclideanGeometryOrientation : public ValueObject<ValueType,ValueCount> {
public:
    EuclideanGeometryOrientation(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    EuclideanGeometryOrientation(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~EuclideanGeometryOrientation(){}
    std::string toString() override {
        return "@@EuclideanGeometryOrientation(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString() + ")";
    }

    EuclideanGeometry* getSpace() const {return this->space_;};
    
    
private:
    EuclideanGeometry* space_; 
    
    
};




template <class ValueType, int ValueCount>
class EuclideanGeometryFrameChange : public ValueObject<ValueType,ValueCount> {
public:
    EuclideanGeometryFrameChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    EuclideanGeometryFrameChange(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~EuclideanGeometryFrameChange(){}
    std::string toString() override {
        return "@@EuclideanGeometryFrameChange(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString() + ")";
    }

    
    
    
private:
     
    
    MapSpace* space_;
};




template <class ValueType, int ValueCount>
class EuclideanGeometryCoordinatePoint : public ValueObject<ValueType,ValueCount> {
public:
    EuclideanGeometryCoordinatePoint(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    EuclideanGeometryCoordinatePoint(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~EuclideanGeometryCoordinatePoint(){}
    std::string toString() override {
        return "@@EuclideanGeometryCoordinatePoint(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString()+","+(frame_?frame_->getName():"") + ")";
    }

    EuclideanGeometry* getSpace() const {return this->space_;};
    EuclideanGeometryFrame* getFrame() const { return this->frame_; };
    void setFrame(EuclideanGeometryFrame* frame){
            this->frame_ = frame;
        };
private:
    EuclideanGeometry* space_; 
    EuclideanGeometryFrame* frame_;
    
};




template <class ValueType, int ValueCount>
class EuclideanGeometryCoordinateVector : public ValueObject<ValueType,ValueCount> {
public:
    EuclideanGeometryCoordinateVector(EuclideanGeometry* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    EuclideanGeometryCoordinateVector(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~EuclideanGeometryCoordinateVector(){}
    std::string toString() override {
        return "@@EuclideanGeometryCoordinateVector(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString()+","+(frame_?frame_->getName():"") + ")";
    }

    EuclideanGeometry* getSpace() const {return this->space_;};
    EuclideanGeometryFrame* getFrame() const { return this->frame_; };
    void setFrame(EuclideanGeometryFrame* frame){
            this->frame_ = frame;
        };
private:
    EuclideanGeometry* space_; 
    EuclideanGeometryFrame* frame_;
    
};


class ClassicalTime : public Space {
    public:
	    ClassicalTime(std::string name) : Space(name, 1) {};
	    std::string getName() const override { return name_; }; 
	    
        void addFrame(ClassicalTimeFrame* frame);
	    std::string toString() const override {
		    return "@@ClassicalTime  " + getName()   + "(" + ")"; 
	    }

    private:
    };


class ClassicalTimeFrame : public Frame {
public:
	ClassicalTimeFrame(std::string name,  ClassicalTime* space) : Frame(name, space) {};
    ClassicalTimeFrame(){};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalTime*)this->space_)->getName();
		return "@@ClassicalTimeFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/

private:
};



class ClassicalTimeStandardFrame : public StandardFrame, public ClassicalTimeFrame {
public:
	ClassicalTimeStandardFrame(ClassicalTime* space) : StandardFrame(space) {};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalTime*)this->space_)->getName();
		return "@@ClassicalTimeFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/

    virtual std::string getName() const override {
        return StandardFrame::getName();
    };

    virtual std::string toString() const override {
        return std::string("ClassicalTimeStandardFrame ") + StandardFrame::toString();
    };

private:
};



class ClassicalTimeAliasedFrame : public AliasedFrame, public ClassicalTimeFrame {
public:
	ClassicalTimeAliasedFrame(std::string name,  ClassicalTime* space, ClassicalTimeFrame* aliased, domain::MeasurementSystem* ms) : AliasedFrame(name, space, aliased,  ms) {};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalTime*)this->space_)->getName();
		return "@@ClassicalTimeFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/
    virtual std::string toString() const override {
        return std::string("ClassicalTimeAliasedFrame ") + AliasedFrame::toString();
    };

private:
};



class ClassicalTimeDerivedFrame : public DerivedFrame, public ClassicalTimeFrame {
public:
	ClassicalTimeDerivedFrame(std::string name,  ClassicalTime* space, ClassicalTimeFrame* parent) : DerivedFrame(name, space, parent) {};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalTime*)this->space_)->getName();
		return "@@ClassicalTimeFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/
    virtual std::string toString() const override {
        return std::string("ClassicalTimeDerivedFrame ") + DerivedFrame::toString();
    };

private:
};




template <class ValueType, int ValueCount>
class ClassicalTimeFrameChange : public ValueObject<ValueType,ValueCount> {
public:
    ClassicalTimeFrameChange(MapSpace* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    ClassicalTimeFrameChange(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~ClassicalTimeFrameChange(){}
    std::string toString() override {
        return "@@ClassicalTimeFrameChange(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString() + ")";
    }

    
    
    
private:
     
    
    MapSpace* space_;
};




template <class ValueType, int ValueCount>
class ClassicalTimeCoordinatePoint : public ValueObject<ValueType,ValueCount> {
public:
    ClassicalTimeCoordinatePoint(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    ClassicalTimeCoordinatePoint(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~ClassicalTimeCoordinatePoint(){}
    std::string toString() override {
        return "@@ClassicalTimeCoordinatePoint(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString()+","+(frame_?frame_->getName():"") + ")";
    }

    ClassicalTime* getSpace() const {return this->space_;};
    ClassicalTimeFrame* getFrame() const { return this->frame_; };
    void setFrame(ClassicalTimeFrame* frame){
            this->frame_ = frame;
        };
private:
    ClassicalTime* space_; 
    ClassicalTimeFrame* frame_;
    
};




template <class ValueType, int ValueCount>
class ClassicalTimeCoordinateVector : public ValueObject<ValueType,ValueCount> {
public:
    ClassicalTimeCoordinateVector(ClassicalTime* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    ClassicalTimeCoordinateVector(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~ClassicalTimeCoordinateVector(){}
    std::string toString() override {
        return "@@ClassicalTimeCoordinateVector(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString()+","+(frame_?frame_->getName():"") + ")";
    }

    ClassicalTime* getSpace() const {return this->space_;};
    ClassicalTimeFrame* getFrame() const { return this->frame_; };
    void setFrame(ClassicalTimeFrame* frame){
            this->frame_ = frame;
        };
private:
    ClassicalTime* space_; 
    ClassicalTimeFrame* frame_;
    
};


class ClassicalVelocity : public DerivedSpace {
    public:
	    
        ClassicalVelocity(std::string name, Space* base1, Space* base2) : DerivedSpace(name, base1, base2) {};
        void addFrame(ClassicalVelocityFrame* frame);
	    std::string toString() const override {
		    return "@@ClassicalVelocity  " + getName()   + "(" + this->base_1->getName() + "," + this->base_2->getName() + ")"; 
	    }

    private:
    };


class ClassicalVelocityFrame : public Frame {
public:
	ClassicalVelocityFrame(std::string name,  ClassicalVelocity* space) : Frame(name, space) {};
    ClassicalVelocityFrame(){};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalVelocity*)this->space_)->getName();
		return "@@ClassicalVelocityFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/

private:
};



class ClassicalVelocityStandardFrame : public StandardFrame, public ClassicalVelocityFrame {
public:
	ClassicalVelocityStandardFrame(ClassicalVelocity* space) : StandardFrame(space) {};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalVelocity*)this->space_)->getName();
		return "@@ClassicalVelocityFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/

    virtual std::string getName() const override {
        return StandardFrame::getName();
    };

    virtual std::string toString() const override {
        return std::string("ClassicalVelocityStandardFrame ") + StandardFrame::toString();
    };

private:
};



class ClassicalVelocityAliasedFrame : public AliasedFrame, public ClassicalVelocityFrame {
public:
	ClassicalVelocityAliasedFrame(std::string name,  ClassicalVelocity* space, ClassicalVelocityFrame* aliased, domain::MeasurementSystem* ms) : AliasedFrame(name, space, aliased,  ms) {};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalVelocity*)this->space_)->getName();
		return "@@ClassicalVelocityFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/
    virtual std::string toString() const override {
        return std::string("ClassicalVelocityAliasedFrame ") + AliasedFrame::toString();
    };

private:
};



class ClassicalVelocityDerivedFrame : public DerivedFrame, public ClassicalVelocityFrame {
public:
	ClassicalVelocityDerivedFrame(std::string name,  ClassicalVelocity* space, ClassicalVelocityFrame* parent) : DerivedFrame(name, space, parent) {};
	/*std::string toString() const override {
        std::string parentName = ((ClassicalVelocity*)this->space_)->getName();
		return "@@ClassicalVelocityFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}*/
    virtual std::string toString() const override {
        return std::string("ClassicalVelocityDerivedFrame ") + DerivedFrame::toString();
    };

private:
};




template <class ValueType, int ValueCount>
class ClassicalVelocityCoordinateVector : public ValueObject<ValueType,ValueCount> {
public:
    ClassicalVelocityCoordinateVector(ClassicalVelocity* s, std::initializer_list<DomainObject*> args) : 
			ValueObject<ValueType,ValueCount>::ValueObject(args), space_(s)  {}
    ClassicalVelocityCoordinateVector(std::initializer_list<DomainObject*> args ) :
	 		ValueObject<ValueType,ValueCount>::ValueObject(args) {}
	virtual ~ClassicalVelocityCoordinateVector(){}
    std::string toString() override {
        return "@@ClassicalVelocityCoordinateVector(" + (space_?space_->getName():"Missing Space")+","+ValueObject<ValueType,ValueCount>::toString()+","+(frame_?frame_->getName():"") + ")";
    }

    ClassicalVelocity* getSpace() const {return this->space_;};
    ClassicalVelocityFrame* getFrame() const { return this->frame_; };
    void setFrame(ClassicalVelocityFrame* frame){
            this->frame_ = frame;
        };
private:
    ClassicalVelocity* space_; 
    ClassicalVelocityFrame* frame_;
    
};

} // end namespace

#endif