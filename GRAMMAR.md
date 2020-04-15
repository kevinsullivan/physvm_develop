# Supported Grammars

### CPP-Parsing Grammar

The following is a supported BNF grammar for parsing C++ programs into our virtual AST representation. Please see BaseMatcher.h, as well as any *Matcher.h class files.
Any *Matcher.h represents a grammar production commensurate with different cases that Peirce is capable of recognizing and parsing.

STMT := VEC_VAR = EXPR | SCALAR_VAR = SCALAR_EXPR  | VEC_EXPR | SCALAR_EXPR | DECL VEC_VAR = VEC_EXPR | DECL SCALAR_VAR = SCALAR_EXPR

VEC_EXPR := (VEC_EXPR) | VEC_EXPR + VEC_EXPR | VEC_EXPR * SCALAR_EXPR | VEC_VAR | VEC_LITERAL

SCALAR_EXPR := (SCALAR_EXPR) | SCALAR_EXPR + SCALAR_EXPR | SCALAR_EXPR * SCALAR_EXPR | SCALAR_VAR | SCALAR_LITERAL

...

SCALAR_VAR := IDENT

VEC_VAR := IDENT

SCALAR_LITERAL := Floating point value

VEC_LITERAL := Vector rvalue

### Domain-Lean Parsing Grammar

In progress over next few weeks.
