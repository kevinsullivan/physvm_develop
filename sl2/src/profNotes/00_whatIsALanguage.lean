inductive Syntax : Type
| I
| II
| III
| IV
| V

inductive SemanticDomain : Type
| one
| two
| three
| four
| five

open Syntax SemanticDomain

def semantics : Syntax → SemanticDomain
| I := one 
| II := two
| III := three
| IV := four
| V := five