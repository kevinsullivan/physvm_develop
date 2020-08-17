
#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include <string>
#include <memory>

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
        int begin_line_no,
        int begin_col_no,
        int end_line_no,
        int end_col_no
        );

        std::string file_id_;
        std::string file_name_;
        std::string file_path_;

        std::string name_; //only used for Decl. possibly subclass this, or else this property is unused elsewhere

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
    Coords() {};

    virtual bool operator ==(const Coords &other) const;
    virtual std::string toString() const;
    virtual std::string getSourceLoc() const;
    int getIndex() const { return index_; };
    void setIndex(int index);
    
    virtual bool codegen() const {
        return false;
    }

    ASTState* state_; //maybe  change this to a constructor argument
protected:
    int index_;
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
        return (std::shared_ptr<ValueType>*)this->values_;
    }

protected:
    std::shared_ptr<ValueType> values_[ValueCount];
    //int value_len_;
    //std::Vector<ValueType*> values_;

};



class PROGRAM;
class SEQ_GLOBALSTMT;
class GLOBALSTMT;
class STMT;
class COMPOUND_STMT;
class FUNC_DECL;
class VOID_FUNC_DECL_STMT;
class MAIN_FUNC_DECL_STMT;

class PROGRAM : public Coords {
public:
    PROGRAM() : Coords() {};
    std::string virtual toString() const { return "Do not call this"; };
    bool operator==(const PROGRAM &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class SEQ_GLOBALSTMT : public PROGRAM {
public:
    SEQ_GLOBALSTMT(std::vector<GLOBALSTMT*> operands);
    virtual std::string toString() const;
    bool operator==(const PROGRAM &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };

    std::vector<GLOBALSTMT*> getOperands() const { return this->operands_; };

    coords::GLOBALSTMT* getOperand(int i) const {
        return this->operands_.size() >= i ? this->operands_[i-1] : nullptr;
    }
protected:
	
    std::vector<GLOBALSTMT*> operands_;

};



class GLOBALSTMT : public Coords {
public:
    GLOBALSTMT() : Coords() {};
    std::string virtual toString() const { return "Do not call this"; };
    bool operator==(const GLOBALSTMT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class STMT : public Coords {
public:
    STMT() : Coords() {};
    std::string virtual toString() const { return "Do not call this"; };
    bool operator==(const STMT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class COMPOUND_STMT : public STMT {
public:
    COMPOUND_STMT(std::vector<STMT*> operands);
    virtual std::string toString() const;
    bool operator==(const STMT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };

    std::vector<STMT*> getOperands() const { return this->operands_; };

    coords::STMT* getOperand(int i) const {
        return this->operands_.size() >= i ? this->operands_[i-1] : nullptr;
    }
protected:
	
    std::vector<STMT*> operands_;

};



class FUNC_DECL : public GLOBALSTMT {
public:
    FUNC_DECL() : GLOBALSTMT() {};
    std::string virtual toString() const { return "Do not call this"; };
    bool operator==(const FUNC_DECL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class VOID_FUNC_DECL_STMT : public FUNC_DECL {
public:
    VOID_FUNC_DECL_STMT(coords::STMT * operand0) : FUNC_DECL()
        , operand_0(operand0){};
    std::string virtual toString() const;
    coords::STMT * getOperand0(){ return this->operand_0;};
    bool operator==(const VOID_FUNC_DECL_STMT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
protected:
    coords::STMT * operand_0;
};

    

class MAIN_FUNC_DECL_STMT : public FUNC_DECL {
public:
    MAIN_FUNC_DECL_STMT(coords::STMT * operand0) : FUNC_DECL()
        , operand_0(operand0){};
    std::string virtual toString() const;
    coords::STMT * getOperand0(){ return this->operand_0;};
    bool operator==(const MAIN_FUNC_DECL_STMT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
protected:
    coords::STMT * operand_0;
};

    
} // namespace coords

#endif