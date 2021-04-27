inductive ST : Type
| empty
| salmon (e : ST)
| trout (e: ST)

open ST

def e1 := ST.empty
def e2 := ST.salmon ST.empty
def e3 := salmon 
            (trout
              (trout
                e1
              )
            )

/-salmon
  empty
salmon
  trout
    trout
      empty
-/

def fishEvalHelper : ST → prod nat nat → prod nat nat 
| ST.empty (prod.mk s t) := (prod.mk s t)
| (ST.salmon e) (prod.mk s t) := _

def fishEval : ST → prod nat nat 
| e := fishEvalHelper e (0,0)

#eval fishEval e1
#eval fishEval e2

def o1 : option nat := option.some 1
def o2 : option nat := option.none

def foo : option nat → string
| (option.none) := "no answer"
| (option.some n) := "the answer was " ++ repr n


#eval foo o1
#eval foo o2