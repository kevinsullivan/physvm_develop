import .space1

-- Now talk in terms of spaces. Here are some examples


/-
Duplicate code copied from point1.lean.
File-scoped, presumably. Fix if easy. 
-/
universes u --v w
variables 
{K : Type u} [ring K] [inhabited K] 
{α : Type u} [has_add α]

/-
Client API test
-/
def newPoint := mk_point std_spc (2:K) 
def newVectr := mk_vectr std_spc (2:K)

#check @newPoint 
#check @newVectr 
-- K ring
#reduce @newPoint 
#reduce @newVectr 

#check newPoint.pt.val.fst
#check newPoint.pt.val.snd

-- TODO: show proof parts, too, here

#check newVectr.vec.val.fst
#check newVectr.vec.val.snd

#reduce newVectr.vec.val.fst
#reduce newVectr.vec.val.snd

-- TODO: show proof parts, too, here

-- Make new frame from newPoint and newVector
def newFrame : @fm K _ _ := mk_frame newPoint newVectr  -- no infer K

-- On that frame design a space
def newSpace := mk_space (@newFrame K _ _)              -- space for newFrame

-- Make a point and a vector in this new space
def nextPoint := mk_point newSpace (3:K)
def nextVectr := mk_vectr newSpace (2:K)

-- And frome here we see that we can build trees

