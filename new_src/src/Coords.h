
#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include <string>
#include <memory>
#include <vector>

#include "AST.h"


/*
Code coordinate objects wrap AST 
objects to provide inherited behavior
necessary and appropriate for each
referenced code object. They give
AST objects types in our domain's
ontology. 

We maintain a bijection betwen AST and 
Coord objects: specifically between the
memory addresses of these objects. It is
thus critical not to map one AST node
address to more than one Coord object.

Code coordinates provide for ontology 
translation, between the Clang's AST 
types and our domain elements (id, 
var expr, function application expr, 
constructed vector, and definition).
*/

namespace coords
{

    // Ontology of Clang object types that can be 
    // coordinatized. We do not currently use 
    // clang::Decl but we include it here to 
    // establish a path togeneralizability
    //
    //enum ast_type { CLANG_AST_STMT, CLANG_AST_DECL }; 

    struct ASTState
    {
    public:
        ASTState(
        std::string file_id,
        std::string file_name,
        std::string file_path,
        std::string name,
        std::string code,
        int begin_line_no,
        int begin_col_no,
        int end_line_no,
        int end_col_no
        );

        std::string file_id_;
        std::string file_name_;
        std::string file_path_;

        std::string name_; //only used for Decl. possibly subclass this, or else this property is unused elsewhere
        std::string code_;

        int begin_line_no_;
        int begin_col_no_;
        int end_line_no_;
        int end_col_no_;

        bool operator ==(const ASTState& other) const {
return 
    file_id_ == other.file_id_ and
            file_name_ == other.file_name_ and
            file_path_ == other.file_path_ and
            begin_line_no_ == other.begin_line_no_ and
            begin_col_no_ == other.begin_col_no_ and
            end_line_no_ == other.end_line_no_ and
            end_col_no_ == other.end_col_no_;
}
};

class Coords
{
public:
    Coords(std::string nodeType_, std::vector<coords::Coords*> operands_) 
        : nodeType(nodeType_), operands(operands_), linked(nullptr) {};

    virtual bool operator ==(const Coords &other) const;
    virtual std::string toString() const;
    virtual std::string getSourceLoc() const;
    int getIndex() const { return index_; };
    void setIndex(int index);
    virtual bool codegen() const {
        return false;
    }

    std::string getNodeType() const{
        return this->nodeType;
    };

    void addLink(coords::Coords* coords_){
        this->links.push_back(coords_);
    }

    std::vector<coords::Coords*> getLinks(){
        return links;
    }

    bool hasLinked() const {
        return linked != nullptr;
    }

    coords::Coords* getLinked() const {
        return linked;
    }

    void setLinked(coords::Coords* link_) {
        this->linked = link_;
    }

    bool hasName() const{
        return this->state_->name_ != "";
    };

    std::string getName() const{
        return this->state_->name_;
    };

    ASTState* state_; //maybe  change this to a constructor argument 
protected:
    int index_;//4-11 don't remember what this is for...?
    std::vector<coords::Coords*> operands;
    std::vector<coords::Coords*> links;
    coords::Coords* linked;
    std::string nodeType;
    std::string name;
};
template <class ValueType, int ValueCount>
class ValueCoords
{
public: 
   // ValueCoords() {};
    ValueCoords() {
        for(int i = 0; i<ValueCount;i++){
            this->values_[i] = nullptr;
        }
    };//, value_len_(len) { this->values_ = new ValueType[value_len_]; };
    //ValueCoords(ValueType* values, int len) : values_(values), value_len_(len) {};
    ValueCoords(std::shared_ptr<ValueType> values...)  {
        
        int i = 0;
        for(auto val : {values}){
            if(i == ValueCount)
                throw "Out of Range";
            this->values_[i++] = val ? std::make_shared<ValueType>(*val) : nullptr;
            
        }
    }

    ValueCoords(std::initializer_list<std::shared_ptr<ValueType>> values){
        
        int i = 0;
        for(auto val : values){
            if(i == ValueCount)
                throw "Out of Range";
            this->values_[i++] = val ? std::make_shared<ValueType>(*val) : nullptr;
            
        }
    }

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

    std::shared_ptr<ValueType>* getValues() const {
        return const_cast<std::shared_ptr<ValueType>*>(this->values_);
    }

protected:
    std::shared_ptr<ValueType> values_[ValueCount];
    //int value_len_;
    //std::Vector<ValueType*> values_;

};

} // namespace coords

#endif