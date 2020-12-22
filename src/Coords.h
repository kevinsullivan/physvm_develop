
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
        return const_cast<std::shared_ptr<ValueType>*>(this->values_);
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
class DECLARE;
class DECL_REAL1_VAR_REAL1_EXPR;
class DECL_REAL3_VAR_REAL3_EXPR;
class DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR;
class DECL_REAL1_VAR;
class DECL_REAL3_VAR;
class DECL_REALMATRIX4_VAR;
class REXPR;
class LEXPR;
class REALMATRIX4_EXPR;
class REF_REALMATRIX4_VAR;
class MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR;
class REAL3_EXPR;
class REF_REAL3_VAR;
class ADD_REAL3_EXPR_REAL3_EXPR;
class LMUL_REAL1_EXPR_REAL3_EXPR;
class RMUL_REAL3_EXPR_REAL1_EXPR;
class TMUL_REALMATRIX4_EXPR_REAL3_EXPR;
class REAL3_LEXPR;
class LREF_REAL3_VAR;
class REAL1_EXPR;
class REF_REAL1_VAR;
class ADD_REAL1_EXPR_REAL1_EXPR;
class MUL_REAL1_EXPR_REAL1_EXPR;
class REAL1_VAR_IDENT;
class REAL3_VAR_IDENT;
class REALMATRIX4_VAR_IDENT;
class REAL3_LITERAL;
class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL3_EMPTY;
class REAL1_LITERAL;
class REAL1_LIT;
class REALMATRIX4_LITERAL;
class REALMATRIX4_EMPTY;

class PROGRAM : public Coords {
public:
    PROGRAM() : Coords() {};
    std::string virtual toString() const override { return "Do not call this"; };
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
    virtual std::string toString() const override;
    bool operator==(const PROGRAM &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };

    std::vector<GLOBALSTMT*> getOperands() const { return this->operands_; };

    coords::GLOBALSTMT* getOperand(int i) const {
        return ((int)this->operands_.size()) >= i ? this->operands_[i-1] : nullptr;
    }
protected:
	
    std::vector<GLOBALSTMT*> operands_;

};



class GLOBALSTMT : public Coords {
public:
    GLOBALSTMT() : Coords() {};
    std::string virtual toString() const override { return "Do not call this"; };
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
    std::string virtual toString() const override { return "Do not call this"; };
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
    virtual std::string toString() const override;
    bool operator==(const STMT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };

    std::vector<STMT*> getOperands() const { return this->operands_; };

    coords::STMT* getOperand(int i) const {
        return ((int)this->operands_.size()) >= i ? this->operands_[i-1] : nullptr;
    }
protected:
	
    std::vector<STMT*> operands_;

};



class FUNC_DECL : public GLOBALSTMT {
public:
    FUNC_DECL() : GLOBALSTMT() {};
    std::string virtual toString() const override { return "Do not call this"; };
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
    std::string virtual toString() const override;
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
    std::string virtual toString() const override;
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

    

class DECLARE : public STMT {
public:
    DECLARE() : STMT() {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class DECL_REAL1_VAR_REAL1_EXPR : public DECLARE {
public:
    DECL_REAL1_VAR_REAL1_EXPR(coords::REAL1_VAR_IDENT * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const override;
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_VAR_IDENT *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_VAR_IDENT *operand1;
	coords::REAL1_EXPR *operand2;
};



class DECL_REAL3_VAR_REAL3_EXPR : public DECLARE {
public:
    DECL_REAL3_VAR_REAL3_EXPR(coords::REAL3_VAR_IDENT * operand_1, coords::REAL3_EXPR * operand_2);
    virtual std::string toString() const override;
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
	coords::REAL3_EXPR *operand2;
};



class DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR : public DECLARE {
public:
    DECL_REALMATRIX4_VAR_REALMATRIX4_EXPR(coords::REALMATRIX4_VAR_IDENT * operand_1, coords::REALMATRIX4_EXPR * operand_2);
    virtual std::string toString() const override;
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REALMATRIX4_VAR_IDENT *getOperand1(); 
	coords::REALMATRIX4_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX4_VAR_IDENT *operand1;
	coords::REALMATRIX4_EXPR *operand2;
};



class DECL_REAL1_VAR : public DECLARE {
public:
    DECL_REAL1_VAR(coords::REAL1_VAR_IDENT * operand_1);
    virtual std::string toString() const override;
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL1_VAR_IDENT *operand1;
};



class DECL_REAL3_VAR : public DECLARE {
public:
    DECL_REAL3_VAR(coords::REAL3_VAR_IDENT * operand_1);
    virtual std::string toString() const override;
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
};



class DECL_REALMATRIX4_VAR : public DECLARE {
public:
    DECL_REALMATRIX4_VAR(coords::REALMATRIX4_VAR_IDENT * operand_1);
    virtual std::string toString() const override;
    bool operator==(const DECLARE &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REALMATRIX4_VAR_IDENT *getOperand1(); 
protected:
	coords::REALMATRIX4_VAR_IDENT *operand1;
};



class REXPR : public STMT {
public:
    REXPR() : STMT() {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class LEXPR : public STMT {
public:
    LEXPR() : STMT() {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const LEXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REALMATRIX4_EXPR : public REXPR {
public:
    REALMATRIX4_EXPR() : REXPR() {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REALMATRIX4_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REF_REALMATRIX4_VAR : public REALMATRIX4_EXPR {
public:
    REF_REALMATRIX4_VAR(coords::REALMATRIX4_VAR_IDENT * operand_1);
    virtual std::string toString() const override;
    bool operator==(const REALMATRIX4_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REALMATRIX4_VAR_IDENT *getOperand1(); 
protected:
	coords::REALMATRIX4_VAR_IDENT *operand1;
};



class MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR : public REALMATRIX4_EXPR {
public:
    MUL_REALMATRIX4_EXPR_REALMATRIX4_EXPR(coords::REALMATRIX4_EXPR * operand_1, coords::REALMATRIX4_EXPR * operand_2);
    virtual std::string toString() const override;
    bool operator==(const REALMATRIX4_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REALMATRIX4_EXPR *getOperand1(); 
	coords::REALMATRIX4_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX4_EXPR *operand1;
	coords::REALMATRIX4_EXPR *operand2;
};



class REAL3_EXPR : public REXPR, public ValueCoords<float,3> {
public:
    REAL3_EXPR(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : ValueCoords < float, 3 >::ValueCoords({value0,value1,value2}) {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REAL3_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REF_REAL3_VAR : public REAL3_EXPR {
public:
    REF_REAL3_VAR(coords::REAL3_VAR_IDENT * operand_1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
};



class ADD_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    ADD_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL3_EXPR * operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
};



class LMUL_REAL1_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    LMUL_REAL1_EXPR_REAL3_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL3_EXPR * operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
};



class RMUL_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    RMUL_REAL3_EXPR_REAL1_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL1_EXPR * operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class TMUL_REALMATRIX4_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    TMUL_REALMATRIX4_EXPR_REAL3_EXPR(coords::REALMATRIX4_EXPR * operand_1, coords::REAL3_EXPR * operand_2,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REALMATRIX4_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX4_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
};



class REAL3_LEXPR : public LEXPR, public ValueCoords<float,3> {
public:
    REAL3_LEXPR(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : ValueCoords < float, 3 >::ValueCoords({value0,value1,value2}) {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REAL3_LEXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class LREF_REAL3_VAR : public REAL3_LEXPR {
public:
    LREF_REAL3_VAR(coords::REAL3_VAR_IDENT * operand_1,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_LEXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
};



class REAL1_EXPR : public REXPR, public ValueCoords<float,1> {
public:
    REAL1_EXPR(std::shared_ptr<float> value0) : ValueCoords < float, 1 >::ValueCoords({value0}) {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REAL1_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REF_REAL1_VAR : public REAL1_EXPR {
public:
    REF_REAL1_VAR(coords::REAL1_VAR_IDENT * operand_1,std::shared_ptr<float> value0);
    virtual std::string toString() const override;
    bool operator==(const REAL1_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL1_VAR_IDENT *operand1;
};



class ADD_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    ADD_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2,std::shared_ptr<float> value0);
    virtual std::string toString() const override;
    bool operator==(const REAL1_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class MUL_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    MUL_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2,std::shared_ptr<float> value0);
    virtual std::string toString() const override;
    bool operator==(const REAL1_EXPR &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class REAL1_VAR_IDENT : public Coords, public ValueCoords<float,1> {
public:
    REAL1_VAR_IDENT(std::shared_ptr<float> value0) : ValueCoords < float, 1 >::ValueCoords({value0})
        {};
    std::string virtual toString() const override;
    
    bool operator==(const REAL1_VAR_IDENT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
protected:
    
};

    

class REAL3_VAR_IDENT : public Coords, public ValueCoords<float,3> {
public:
    REAL3_VAR_IDENT(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : ValueCoords < float, 3 >::ValueCoords({value0,value1,value2})
        {};
    std::string virtual toString() const override;
    
    bool operator==(const REAL3_VAR_IDENT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
protected:
    
};

    

class REALMATRIX4_VAR_IDENT : public Coords {
public:
    REALMATRIX4_VAR_IDENT() : Coords()
        {};
    std::string virtual toString() const override;
    
    bool operator==(const REALMATRIX4_VAR_IDENT &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
protected:
    
};

    

class REAL3_LITERAL : public REAL3_EXPR {
public:
    REAL3_LITERAL(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2) : REAL3_EXPR({value0,value1,value2}) {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REAL3_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL3_LITERAL {
public:
    REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2, coords::REAL1_EXPR * operand_3,std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
	coords::REAL1_EXPR *getOperand3(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
	coords::REAL1_EXPR *operand3;
};



class REAL3_EMPTY : public REAL3_LITERAL {
public:
    REAL3_EMPTY(std::shared_ptr<float> value0,std::shared_ptr<float> value1,std::shared_ptr<float> value2);
    virtual std::string toString() const override;
    bool operator==(const REAL3_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	
protected:
	
};



class REAL1_LITERAL : public REAL1_EXPR {
public:
    REAL1_LITERAL(std::shared_ptr<float> value0) : REAL1_EXPR({value0}) {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REAL1_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REAL1_LIT : public REAL1_LITERAL {
public:
    REAL1_LIT(std::shared_ptr<float> value0);
    virtual std::string toString() const override;
    bool operator==(const REAL1_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	
protected:
	
};



class REALMATRIX4_LITERAL : public REALMATRIX4_EXPR {
public:
    REALMATRIX4_LITERAL() : REALMATRIX4_EXPR() {};
    std::string virtual toString() const override { return "Do not call this"; };
    bool operator==(const REALMATRIX4_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
    virtual bool codegen() const override {
        return true;
    }
};

    

class REALMATRIX4_EMPTY : public REALMATRIX4_LITERAL {
public:
    REALMATRIX4_EMPTY();
    virtual std::string toString() const override;
    bool operator==(const REALMATRIX4_LITERAL &other) const {
        return ((Coords*)this)->state_ == ((Coords)other).state_;
    };
	
protected:
	
};


} // namespace coords

#endif