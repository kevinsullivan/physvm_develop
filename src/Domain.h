
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
class DomainObject;
class DomainContainer;
template<typename ValueType,int ValueCount>
class ValueObject;

class EuclideanGeometry;

class EuclideanGeometryFrame;

class ClassicalTime;

class ClassicalTimeFrame;

class ClassicalVelocity;

class ClassicalVelocityFrame;

            
// Definition for Domain class 

class Domain {
public:
// Space
	std::vector<Space*>& getSpaces();


    Space* getSpace(std::string key);

    DomainObject* mkDefaultDomainContainer();
    DomainObject* mkDefaultDomainContainer(std::initializer_list<DomainObject*> operands);
    DomainObject* mkDefaultDomainContainer(std::vector<DomainObject*> operands);
    Frame* mkFrame(std::string name, Space* space, Frame* parent);


    MapSpace* mkMapSpace(Space* space, Frame* dom, Frame* cod);

	EuclideanGeometry* mkEuclideanGeometry(std::string key ,std::string name_, int dimension_);
	std::vector<EuclideanGeometry*> &getEuclideanGeometrySpaces() { return EuclideanGeometry_vec; }

	EuclideanGeometryFrame* mkEuclideanGeometryFrame(std::string name, domain::EuclideanGeometry* space, domain::EuclideanGeometryFrame* parent);
	ClassicalTime* mkClassicalTime(std::string key ,std::string name_);
	std::vector<ClassicalTime*> &getClassicalTimeSpaces() { return ClassicalTime_vec; }

	ClassicalTimeFrame* mkClassicalTimeFrame(std::string name, domain::ClassicalTime* space, domain::ClassicalTimeFrame* parent);
	ClassicalVelocity* mkClassicalVelocity(std::string key, std::string name_,Space* base1, Space* base2);
	std::vector<ClassicalVelocity*> &getClassicalVelocitySpaces() { return ClassicalVelocity_vec; }

	ClassicalVelocityFrame* mkClassicalVelocityFrame(std::string name, domain::ClassicalVelocity* space, domain::ClassicalVelocityFrame* parent);
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

class Frame {
public:
    Frame(std::string name, Space* space, Frame* parent) : parent_(parent), space_(space), name_(name) {};
    Frame() {};
    virtual ~Frame(){};
    virtual std::string toString() const {
        return "This is a mixin interface";
    }

    Frame* getParent() const{ return parent_; };
    void setParent(Frame* parent);

    std::string getName() const { return name_; };

    Space* getSpace() const { return space_; };

protected:
    Frame* parent_;
    Space* space_;
    std::string name_;

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
	EuclideanGeometryFrame(std::string name,  EuclideanGeometry* space, EuclideanGeometryFrame* parent) : Frame(name, space, parent) {};
	std::string toString() const override {
        std::string parentName = ((EuclideanGeometry*)this->space_)->getName();
		return "@@EuclideanGeometryFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}

private:
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
	ClassicalTimeFrame(std::string name,  ClassicalTime* space, ClassicalTimeFrame* parent) : Frame(name, space, parent) {};
	std::string toString() const override {
        std::string parentName = ((ClassicalTime*)this->space_)->getName();
		return "@@ClassicalTimeFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}

private:
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
	ClassicalVelocityFrame(std::string name,  ClassicalVelocity* space, ClassicalVelocityFrame* parent) : Frame(name, space, parent) {};
	std::string toString() const override {
        std::string parentName = ((ClassicalVelocity*)this->space_)->getName();
		return "@@ClassicalVelocityFrame  " + this->getName() + "(" + parentName + (this->parent_? "," + parentName + "." + this->parent_->getName() : "") + ")";
	}

private:
};

} // end namespace

#endif