import .affnKcoord_transforms

abbreviation K := ℚ 
def dim := 1
def first_id := 1
def std_fm : fm K dim (λi,first_id) := fm.base dim first_id
def std_sp := mk_space std_fm
#check std_fm

def p1 : point std_sp := 
  mk_point std_sp ⟨[1], rfl⟩

def prod2_point : point (mk_prod_spc std_sp std_sp) :=
  mk_point_prod p1 p1

example : (add_maps (λ (i : fin dim), first_id) (λ (i : fin dim), first_id))= (λ i : fin 2 , first_id)
  := begin
    intros,
    simp * ,
    refl,
  end

  #check eq.rec_on

@[reducible, simp]
def fmtest : fm K (2) (λi, first_id) :=--(add_maps (λ (i : fin dim), first_id) (λ (i : fin dim), first_id)) :=--(λ i, first_id) := 
  let pf:(add_maps (λ (i : fin dim), first_id) (λ (i : fin dim), first_id))=(λi, first_id)
    := begin
    intros,
    simp * ,
    end in
    (eq.rec_on pf prod2_point.space.fm)
  /-begin
    let h : fm K (2) (λi, first_id) :=
      eq.rec_on
  end-/
  /-
  (eq.rec_on begin 
    
  end prod2_point.space.fm : fm K (2) (λi, first_id))
-/
def prod3_point : point _ :=
  mk_point_prod prod2_point p1

def v1 : vectr std_sp :=
  mk_vectr std_sp ⟨[1],rfl⟩

def prod2_vectr :=
  mk_vectr_prod v1 v1

def prod3_vectr :=
  mk_vectr_prod prod2_vectr v1

def prod3_vectr_alt :=
  mk_vectr_prod v1 prod2_vectr


#check prod3_vectr +ᵥ prod3_point --works!
#check prod3_vectr +ᵥ prod3_vectr_alt -- same space, BUT NOT definitionally equal

--construct space directly
def prod3_spc := mk_prod_spc (mk_prod_spc std_sp std_sp) std_sp

def my_pt : point prod3_spc := mk_point prod3_spc ⟨[1,1,1],rfl⟩

def u1 : vectr prod3_spc := mk_vectr prod3_spc ⟨[2,0,0],rfl⟩
def u2 : vectr prod3_spc := mk_vectr prod3_spc ⟨[0,2,0],rfl⟩
def u3 : vectr prod3_spc := mk_vectr prod3_spc ⟨[0,0,2],rfl⟩

def prod3_der_fm : fm K (3) (add_maps (add_maps ↑first_id ↑first_id) ↑first_id) 
    := fm.deriv my_pt.coords (λi, match i.1 with
    | 0 := u1.coords
    | 1 := u2.coords
    | _ := u3.coords
    end) sorry sorry prod3_spc.fm 

def prod3_der_sp : spc K prod3_der_fm := mk_space prod3_der_fm

def der_pt : point prod3_der_sp :=  mk_point _ ⟨[1,1,1],rfl⟩

-- get coords of der_pt in the prod3_spc coordinate system?

def der_to_p3 := prod3_der_sp.fm_tr prod3_spc

#check der_to_p3.transform_point der_pt
#eval der_to_p3.transform_point der_pt

--error, noncomputable!
def der_pt_in_p3 : point prod3_spc := der_to_p3.transform_point der_pt
--OK
noncomputable def nc_der_pt_in_p3 : point prod3_spc := der_to_p3.transform_point der_pt


#check der_pt -ᵥ my_pt

--still works
#check prod3_point -ᵥ my_pt

