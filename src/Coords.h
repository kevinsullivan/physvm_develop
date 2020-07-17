
#ifndef COORDS_H
#define COORDS_H

#include "clang/AST/AST.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include <cstddef>
#include <iostream> // for cheap logging only
#include <string>

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

    ASTState* state_; //maybe  change this to a constructor argument
    protected:
};

class STMT;
class COMPOUND_STMT;
class IFCOND;
class IFTHEN_EXPR_STMT;
class IFTHENELSEIF_EXPR_STMT_IFCOND;
class IFTHENELSE_EXPR_STMT_STMT;
class EXPR;
class ASSIGNMENT;
class ASSIGN_REAL1_VAR_REAL1_EXPR;
class ASSIGN_REAL3_VAR_REAL3_EXPR;
class ASSIGN_REAL4_VAR_REAL4_EXPR;
class ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR;
class DECLARE;
class DECL_REAL1_VAR_REAL1_EXPR;
class DECL_REAL3_VAR_REAL3_EXPR;
class DECL_REAL4_VAR_REAL4_EXPR;
class DECL_REALMATRIX_VAR_REALMATRIX_EXPR;
class DECL_REAL1_VAR;
class DECL_REAL3_VAR;
class DECL_REAL4_VAR;
class DECL_REALMATRIX_VAR;
class REAL1_EXPR;
class PAREN_REAL1_EXPR;
class INV_REAL1_EXPR;
class NEG_REAL1_EXPR;
class ADD_REAL1_EXPR_REAL1_EXPR;
class SUB_REAL1_EXPR_REAL1_EXPR;
class MUL_REAL1_EXPR_REAL1_EXPR;
class DIV_REAL1_EXPR_REAL1_EXPR;
class REF_REAL1_VAR;
class REAL3_EXPR;
class PAREN_REAL3_EXPR;
class ADD_REAL3_EXPR_REAL3_EXPR;
class SUB_REAL3_EXPR_REAL3_EXPR;
class INV_REAL3_EXPR;
class NEG_REAL3_EXPR;
class MUL_REAL3_EXPR_REAL1_EXPR;
class MUL_REALMATRIX_EXPR_REAL3_EXPR;
class DIV_REAL3_EXPR_REAL1_EXPR;
class REF_REAL3_VAR;
class REAL4_EXPR;
class PAREN_REAL4_EXPR;
class ADD_REAL4_EXPR_REAL4_EXPR;
class MUL_REAL4_EXPR_REAL1_EXPR;
class REF_REAL4_VAR;
class REALMATRIX_EXPR;
class PAREN_REALMATRIX_EXPR;
class MUL_REALMATRIX_EXPR_REALMATRIX_EXPR;
class REF_EXPR_REALMATRIX_VAR;
class REAL1_VAR_IDENT;
class REAL3_VAR_IDENT;
class REAL4_VAR_IDENT;
class REALMATRIX_VAR_IDENT;
class REAL1_LITERAL;
class REAL1_LITERAL1;
class REAL3_LITERAL;
class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL3_LITERAL3;
class REAL4_LITERAL;
class REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REAL4_LITERAL4;
class REALMATRIX_LITERAL;
class REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR;
class REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR;
class REALMATRIX_LITERAL9;

    class STMT : public Coords {
    public:
        STMT() : Coords() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const STMT &other) const {
        return this->state_ == other.state_;
        };
    };

    

class COMPOUND_STMT : public STMT {
public:
    COMPOUND_STMT(std::vector<STMT*> operands);
    virtual std::string toString() const;
    bool operator==(const STMT &other) const {
        return this->state_ == other.state_;
    };

    coords::STMT* getOperand(int i) const {
        return this->operands_.size() >= i ? this->operands_[i-1] : nullptr;
    }
protected:
	
    std::vector<STMT*> operands_;

};



    class IFCOND : public STMT {
    public:
        IFCOND() : STMT() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const IFCOND &other) const {
        return this->state_ == other.state_;
        };
    };

    

class IFTHEN_EXPR_STMT : public IFCOND {
public:
    IFTHEN_EXPR_STMT(coords::EXPR * operand_1, coords::STMT * operand_2);
    virtual std::string toString() const;
    bool operator==(const IFCOND &other) const {
        return this->state_ == other.state_;
    };
	coords::EXPR *getOperand1(); 
	coords::STMT *getOperand2(); 
protected:
	coords::EXPR *operand1;
	coords::STMT *operand2;
};



class IFTHENELSEIF_EXPR_STMT_IFCOND : public IFCOND {
public:
    IFTHENELSEIF_EXPR_STMT_IFCOND(coords::EXPR * operand_1, coords::STMT * operand_2, coords::IFCOND * operand_3);
    virtual std::string toString() const;
    bool operator==(const IFCOND &other) const {
        return this->state_ == other.state_;
    };
	coords::EXPR *getOperand1(); 
	coords::STMT *getOperand2(); 
	coords::IFCOND *getOperand3(); 
protected:
	coords::EXPR *operand1;
	coords::STMT *operand2;
	coords::IFCOND *operand3;
};



class IFTHENELSE_EXPR_STMT_STMT : public IFCOND {
public:
    IFTHENELSE_EXPR_STMT_STMT(coords::EXPR * operand_1, coords::STMT * operand_2, coords::STMT * operand_3);
    virtual std::string toString() const;
    bool operator==(const IFCOND &other) const {
        return this->state_ == other.state_;
    };
	coords::EXPR *getOperand1(); 
	coords::STMT *getOperand2(); 
	coords::STMT *getOperand3(); 
protected:
	coords::EXPR *operand1;
	coords::STMT *operand2;
	coords::STMT *operand3;
};



    class EXPR : public STMT {
    public:
        EXPR() : STMT() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const EXPR &other) const {
        return this->state_ == other.state_;
        };
    };

    

    class ASSIGNMENT : public STMT {
    public:
        ASSIGNMENT() : STMT() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const ASSIGNMENT &other) const {
        return this->state_ == other.state_;
        };
    };

    

class ASSIGN_REAL1_VAR_REAL1_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REAL1_VAR_REAL1_EXPR(coords::REAL1_VAR_IDENT * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const ASSIGNMENT &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_VAR_IDENT *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_VAR_IDENT *operand1;
	coords::REAL1_EXPR *operand2;
};



class ASSIGN_REAL3_VAR_REAL3_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REAL3_VAR_REAL3_EXPR(coords::REAL3_VAR_IDENT * operand_1, coords::REAL3_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const ASSIGNMENT &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
	coords::REAL3_EXPR *operand2;
};



class ASSIGN_REAL4_VAR_REAL4_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REAL4_VAR_REAL4_EXPR(coords::REAL4_VAR_IDENT * operand_1, coords::REAL4_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const ASSIGNMENT &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_VAR_IDENT *getOperand1(); 
	coords::REAL4_EXPR *getOperand2(); 
protected:
	coords::REAL4_VAR_IDENT *operand1;
	coords::REAL4_EXPR *operand2;
};



class ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR : public ASSIGNMENT {
public:
    ASSIGN_REALMATRIX_VAR_REALMATRIX_EXPR(coords::REALMATRIX_VAR_IDENT * operand_1, coords::REALMATRIX_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const ASSIGNMENT &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_VAR_IDENT *getOperand1(); 
	coords::REALMATRIX_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX_VAR_IDENT *operand1;
	coords::REALMATRIX_EXPR *operand2;
};



    class DECLARE : public STMT {
    public:
        DECLARE() : STMT() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
        };
    };

    

class DECL_REAL1_VAR_REAL1_EXPR : public DECLARE {
public:
    DECL_REAL1_VAR_REAL1_EXPR(coords::REAL1_VAR_IDENT * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
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
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
	coords::REAL3_EXPR *operand2;
};



class DECL_REAL4_VAR_REAL4_EXPR : public DECLARE {
public:
    DECL_REAL4_VAR_REAL4_EXPR(coords::REAL4_VAR_IDENT * operand_1, coords::REAL4_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_VAR_IDENT *getOperand1(); 
	coords::REAL4_EXPR *getOperand2(); 
protected:
	coords::REAL4_VAR_IDENT *operand1;
	coords::REAL4_EXPR *operand2;
};



class DECL_REALMATRIX_VAR_REALMATRIX_EXPR : public DECLARE {
public:
    DECL_REALMATRIX_VAR_REALMATRIX_EXPR(coords::REALMATRIX_VAR_IDENT * operand_1, coords::REALMATRIX_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_VAR_IDENT *getOperand1(); 
	coords::REALMATRIX_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX_VAR_IDENT *operand1;
	coords::REALMATRIX_EXPR *operand2;
};



class DECL_REAL1_VAR : public DECLARE {
public:
    DECL_REAL1_VAR(coords::REAL1_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL1_VAR_IDENT *operand1;
};



class DECL_REAL3_VAR : public DECLARE {
public:
    DECL_REAL3_VAR(coords::REAL3_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
};



class DECL_REAL4_VAR : public DECLARE {
public:
    DECL_REAL4_VAR(coords::REAL4_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL4_VAR_IDENT *operand1;
};



class DECL_REALMATRIX_VAR : public DECLARE {
public:
    DECL_REALMATRIX_VAR(coords::REALMATRIX_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const DECLARE &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_VAR_IDENT *getOperand1(); 
protected:
	coords::REALMATRIX_VAR_IDENT *operand1;
};



    class REAL1_EXPR : public EXPR {
    public:
        REAL1_EXPR() : EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
        };
    };

    

class PAREN_REAL1_EXPR : public REAL1_EXPR {
public:
    PAREN_REAL1_EXPR(coords::REAL1_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
protected:
	coords::REAL1_EXPR *operand1;
};



class INV_REAL1_EXPR : public REAL1_EXPR {
public:
    INV_REAL1_EXPR(coords::REAL1_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
protected:
	coords::REAL1_EXPR *operand1;
};



class NEG_REAL1_EXPR : public REAL1_EXPR {
public:
    NEG_REAL1_EXPR(coords::REAL1_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
protected:
	coords::REAL1_EXPR *operand1;
};



class ADD_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    ADD_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class SUB_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    SUB_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class MUL_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    MUL_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class DIV_REAL1_EXPR_REAL1_EXPR : public REAL1_EXPR {
public:
    DIV_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class REF_REAL1_VAR : public REAL1_EXPR {
public:
    REF_REAL1_VAR(coords::REAL1_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL1_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL1_VAR_IDENT *operand1;
};



    class REAL3_EXPR : public EXPR {
    public:
        REAL3_EXPR() : EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
        };
    };

    

class PAREN_REAL3_EXPR : public REAL3_EXPR {
public:
    PAREN_REAL3_EXPR(coords::REAL3_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
protected:
	coords::REAL3_EXPR *operand1;
};



class ADD_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    ADD_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL3_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
};



class SUB_REAL3_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    SUB_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL3_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
};



class INV_REAL3_EXPR : public REAL3_EXPR {
public:
    INV_REAL3_EXPR(coords::REAL3_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
protected:
	coords::REAL3_EXPR *operand1;
};



class NEG_REAL3_EXPR : public REAL3_EXPR {
public:
    NEG_REAL3_EXPR(coords::REAL3_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
protected:
	coords::REAL3_EXPR *operand1;
};



class MUL_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    MUL_REAL3_EXPR_REAL1_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class MUL_REALMATRIX_EXPR_REAL3_EXPR : public REAL3_EXPR {
public:
    MUL_REALMATRIX_EXPR_REAL3_EXPR(coords::REALMATRIX_EXPR * operand_1, coords::REAL3_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
};



class DIV_REAL3_EXPR_REAL1_EXPR : public REAL3_EXPR {
public:
    DIV_REAL3_EXPR_REAL1_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class REF_REAL3_VAR : public REAL3_EXPR {
public:
    REF_REAL3_VAR(coords::REAL3_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL3_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL3_VAR_IDENT *operand1;
};



    class REAL4_EXPR : public EXPR {
    public:
        REAL4_EXPR() : EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REAL4_EXPR &other) const {
        return this->state_ == other.state_;
        };
    };

    

class PAREN_REAL4_EXPR : public REAL4_EXPR {
public:
    PAREN_REAL4_EXPR(coords::REAL4_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL4_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_EXPR *getOperand1(); 
protected:
	coords::REAL4_EXPR *operand1;
};



class ADD_REAL4_EXPR_REAL4_EXPR : public REAL4_EXPR {
public:
    ADD_REAL4_EXPR_REAL4_EXPR(coords::REAL4_EXPR * operand_1, coords::REAL4_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL4_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_EXPR *getOperand1(); 
	coords::REAL4_EXPR *getOperand2(); 
protected:
	coords::REAL4_EXPR *operand1;
	coords::REAL4_EXPR *operand2;
};



class MUL_REAL4_EXPR_REAL1_EXPR : public REAL4_EXPR {
public:
    MUL_REAL4_EXPR_REAL1_EXPR(coords::REAL4_EXPR * operand_1, coords::REAL1_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REAL4_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
protected:
	coords::REAL4_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
};



class REF_REAL4_VAR : public REAL4_EXPR {
public:
    REF_REAL4_VAR(coords::REAL4_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const REAL4_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL4_VAR_IDENT *getOperand1(); 
protected:
	coords::REAL4_VAR_IDENT *operand1;
};



    class REALMATRIX_EXPR : public EXPR {
    public:
        REALMATRIX_EXPR() : EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REALMATRIX_EXPR &other) const {
        return this->state_ == other.state_;
        };
    };

    

class PAREN_REALMATRIX_EXPR : public REALMATRIX_EXPR {
public:
    PAREN_REALMATRIX_EXPR(coords::REALMATRIX_EXPR * operand_1);
    virtual std::string toString() const;
    bool operator==(const REALMATRIX_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_EXPR *getOperand1(); 
protected:
	coords::REALMATRIX_EXPR *operand1;
};



class MUL_REALMATRIX_EXPR_REALMATRIX_EXPR : public REALMATRIX_EXPR {
public:
    MUL_REALMATRIX_EXPR_REALMATRIX_EXPR(coords::REALMATRIX_EXPR * operand_1, coords::REALMATRIX_EXPR * operand_2);
    virtual std::string toString() const;
    bool operator==(const REALMATRIX_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_EXPR *getOperand1(); 
	coords::REALMATRIX_EXPR *getOperand2(); 
protected:
	coords::REALMATRIX_EXPR *operand1;
	coords::REALMATRIX_EXPR *operand2;
};



class REF_EXPR_REALMATRIX_VAR : public REALMATRIX_EXPR {
public:
    REF_EXPR_REALMATRIX_VAR(coords::REALMATRIX_VAR_IDENT * operand_1);
    virtual std::string toString() const;
    bool operator==(const REALMATRIX_EXPR &other) const {
        return this->state_ == other.state_;
    };
	coords::REALMATRIX_VAR_IDENT *getOperand1(); 
protected:
	coords::REALMATRIX_VAR_IDENT *operand1;
};



    class REAL1_VAR_IDENT : public Coords {
    public:
        REAL1_VAR_IDENT() : Coords() {};
        std::string virtual toString() const;
        bool operator==(const REAL1_VAR_IDENT &other) const {
        return this->state_ == other.state_;
        };
    };

    

    class REAL3_VAR_IDENT : public Coords {
    public:
        REAL3_VAR_IDENT() : Coords() {};
        std::string virtual toString() const;
        bool operator==(const REAL3_VAR_IDENT &other) const {
        return this->state_ == other.state_;
        };
    };

    

    class REAL4_VAR_IDENT : public Coords {
    public:
        REAL4_VAR_IDENT() : Coords() {};
        std::string virtual toString() const;
        bool operator==(const REAL4_VAR_IDENT &other) const {
        return this->state_ == other.state_;
        };
    };

    

    class REALMATRIX_VAR_IDENT : public Coords {
    public:
        REALMATRIX_VAR_IDENT() : Coords() {};
        std::string virtual toString() const;
        bool operator==(const REALMATRIX_VAR_IDENT &other) const {
        return this->state_ == other.state_;
        };
    };

    

    class REAL1_LITERAL : public REAL1_EXPR {
    public:
        REAL1_LITERAL() : REAL1_EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REAL1_LITERAL &other) const {
        return this->state_ == other.state_;
        };
    };

    

class REAL1_LITERAL1 : public REAL1_LITERAL {
public:
    REAL1_LITERAL1(double value_1);
    virtual std::string toString() const;
    bool operator==(const REAL1_LITERAL &other) const {
    return this->state_ == other.state_;
    }
	double getOperand1() const { return this->value1; }
protected:
	double value1;
};



    class REAL3_LITERAL : public REAL3_EXPR {
    public:
        REAL3_LITERAL() : REAL3_EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REAL3_LITERAL &other) const {
        return this->state_ == other.state_;
        };
    };

    

class REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL3_LITERAL {
public:
    REAL3_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2, coords::REAL1_EXPR * operand_3);
    virtual std::string toString() const;
    bool operator==(const REAL3_LITERAL &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
	coords::REAL1_EXPR *getOperand3(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
	coords::REAL1_EXPR *operand3;
};



class REAL3_LITERAL3 : public REAL3_LITERAL {
public:
    REAL3_LITERAL3(double value_1, double value_2, double value_3);
    virtual std::string toString() const;
    bool operator==(const REAL3_LITERAL &other) const {
    return this->state_ == other.state_;
    }
	double getOperand1() const { return this->value1; }
	double getOperand2() const { return this->value2; }
	double getOperand3() const { return this->value3; }
protected:
	double value1;
	double value2;
	double value3;
};



    class REAL4_LITERAL : public REAL4_EXPR {
    public:
        REAL4_LITERAL() : REAL4_EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REAL4_LITERAL &other) const {
        return this->state_ == other.state_;
        };
    };

    

class REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REAL4_LITERAL {
public:
    REAL4_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2, coords::REAL1_EXPR * operand_3, coords::REAL1_EXPR * operand_4);
    virtual std::string toString() const;
    bool operator==(const REAL4_LITERAL &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
	coords::REAL1_EXPR *getOperand3(); 
	coords::REAL1_EXPR *getOperand4(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
	coords::REAL1_EXPR *operand3;
	coords::REAL1_EXPR *operand4;
};



class REAL4_LITERAL4 : public REAL4_LITERAL {
public:
    REAL4_LITERAL4(double value_1, double value_2, double value_3, double value_4);
    virtual std::string toString() const;
    bool operator==(const REAL4_LITERAL &other) const {
    return this->state_ == other.state_;
    }
	double getOperand1() const { return this->value1; }
	double getOperand2() const { return this->value2; }
	double getOperand3() const { return this->value3; }
	double getOperand4() const { return this->value4; }
protected:
	double value1;
	double value2;
	double value3;
	double value4;
};



    class REALMATRIX_LITERAL : public REALMATRIX_EXPR {
    public:
        REALMATRIX_LITERAL() : REALMATRIX_EXPR() {};
        std::string virtual toString() const { return "Do not call this"; };
        bool operator==(const REALMATRIX_LITERAL &other) const {
        return this->state_ == other.state_;
        };
    };

    

class REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR : public REALMATRIX_LITERAL {
public:
    REALMATRIX_LIT_REAL3_EXPR_REAL3_EXPR_REAL3_EXPR(coords::REAL3_EXPR * operand_1, coords::REAL3_EXPR * operand_2, coords::REAL3_EXPR * operand_3);
    virtual std::string toString() const;
    bool operator==(const REALMATRIX_LITERAL &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL3_EXPR *getOperand1(); 
	coords::REAL3_EXPR *getOperand2(); 
	coords::REAL3_EXPR *getOperand3(); 
protected:
	coords::REAL3_EXPR *operand1;
	coords::REAL3_EXPR *operand2;
	coords::REAL3_EXPR *operand3;
};



class REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR : public REALMATRIX_LITERAL {
public:
    REALMATRIX_LIT_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR_REAL1_EXPR(coords::REAL1_EXPR * operand_1, coords::REAL1_EXPR * operand_2, coords::REAL1_EXPR * operand_3, coords::REAL1_EXPR * operand_4, coords::REAL1_EXPR * operand_5, coords::REAL1_EXPR * operand_6, coords::REAL1_EXPR * operand_7, coords::REAL1_EXPR * operand_8, coords::REAL1_EXPR * operand_9);
    virtual std::string toString() const;
    bool operator==(const REALMATRIX_LITERAL &other) const {
        return this->state_ == other.state_;
    };
	coords::REAL1_EXPR *getOperand1(); 
	coords::REAL1_EXPR *getOperand2(); 
	coords::REAL1_EXPR *getOperand3(); 
	coords::REAL1_EXPR *getOperand4(); 
	coords::REAL1_EXPR *getOperand5(); 
	coords::REAL1_EXPR *getOperand6(); 
	coords::REAL1_EXPR *getOperand7(); 
	coords::REAL1_EXPR *getOperand8(); 
	coords::REAL1_EXPR *getOperand9(); 
protected:
	coords::REAL1_EXPR *operand1;
	coords::REAL1_EXPR *operand2;
	coords::REAL1_EXPR *operand3;
	coords::REAL1_EXPR *operand4;
	coords::REAL1_EXPR *operand5;
	coords::REAL1_EXPR *operand6;
	coords::REAL1_EXPR *operand7;
	coords::REAL1_EXPR *operand8;
	coords::REAL1_EXPR *operand9;
};



class REALMATRIX_LITERAL9 : public REALMATRIX_LITERAL {
public:
    REALMATRIX_LITERAL9(double value_1, double value_2, double value_3, double value_4, double value_5, double value_6, double value_7, double value_8, double value_9);
    virtual std::string toString() const;
    bool operator==(const REALMATRIX_LITERAL &other) const {
    return this->state_ == other.state_;
    }
	double getOperand1() const { return this->value1; }
	double getOperand2() const { return this->value2; }
	double getOperand3() const { return this->value3; }
	double getOperand4() const { return this->value4; }
	double getOperand5() const { return this->value5; }
	double getOperand6() const { return this->value6; }
	double getOperand7() const { return this->value7; }
	double getOperand8() const { return this->value8; }
	double getOperand9() const { return this->value9; }
protected:
	double value1;
	double value2;
	double value3;
	double value4;
	double value5;
	double value6;
	double value7;
	double value8;
	double value9;
};


} // namespace coords

#endif