namespace hidden

/-
The empty data type has no
values/constructors at all.
This fact becomes interesting
and useful when one performs
a case analysis on values of
this type, as there are no
cases to consider. 
-/
inductive empty : Type -- uninhabited

/-
Exercise: Show that you can
implement a function, e2n, that
takes (assumes it's given) an
argument, e, of type empty and
that then uses match/with/end
to "eliminate" e and to return
without returning any particular
value of type nat.
-/

def bool_not' : bool → bool
| tt := ff
| ff := tt 

def bool_not : bool → bool :=
λ b, 
  match b with
  | tt := ff
  | ff := tt
  end


def e2n (e : empty) : nat :=
match e with
end 

end hidden