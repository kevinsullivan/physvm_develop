import .lang.imperative_DSL.physlang

noncomputable theory

/-
EXAMPLE 1 : VEC PLUS VEC ( FROM EMAIL DISCUSSION)

-/

#check decidable_eq 
/-

@[reducible]
def decidable_eq (α : Sort u) :=
decidable_rel (@eq α)

class inductive decidable (p : Prop)
| is_false (h : ¬p) : decidable
| is_true  (h : p) : decidable

@[reducible]
def decidable_rel {α : Sort u} (r : α → α → Prop) :=
Π (a b : α), decidable (r a b)


inductive eq {α : Sort u} (a : α) : α → Prop
| refl [] : eq a


-/
--lemma is_dec : decidable_eq 


def env1 := environment.init_env

--phys literals

#check {n: ℕ // n∈[0,1]}

def time : classicalTime := classicalTime.build 10
--def geom3 : euclideanGeometry 3 := euclideanGeometry.build 3 9
def si : measurementSystem.MeasurementSystem := measurementSystem.si_measurement_system
def base_link_frame := 
    classicalTimeFrame.build_derived_from_coords time.stdFrame ⟨[1],rfl⟩ ⟨[60],rfl⟩  si -- 
def left_leg_frame := 
    classicalTimeFrame.build_derived_from_coords time.stdFrame ⟨[3600],rfl⟩ ⟨[3600],rfl⟩  si 
--def left_leg := 
--    classicalTimeFrame.build_derived time.stdFrame (classicalTimePoint.build sp ⟨[3],rfl⟩) ⟨[2],rfl⟩  si 

/-
    tf::Vector3<stamped>(.frameid = ) vec_in_base_link = tf::Vector3(1,1,1);
    tf::Vector3 vec_in_left_leg = tf::Vector3(1,1,1);
    //No type error here
    tf::Vector3 vec_add_okay = vec_in_base_link + vec_in_base_link;
    //Type error here
    tf::Vector3 vec_add_bad = vec_in_base_link + vec_in_left_leg;
-/
def vec_in_base_link : classicalTimeCoordinateVector base_link_frame := 
      classicalTimeCoordinateVector.build base_link_frame ⟨[1],rfl⟩ --[3,3,3,3]
--def v2 : classicalTimeCoordinateVector baselink := classicalTimeCoordinateVector.build baselink ⟨[1],rfl⟩
def vec_in_left_leg : classicalTimeCoordinateVector left_leg_frame := 
      classicalTimeCoordinateVector.build left_leg_frame ⟨[1],rfl⟩

def vec_add_okay : classicalTimeCoordinateVector _ := 
    time_vec_plus_vec vec_in_base_link vec_in_base_link
--def v_p_v2 : classicalTimeCoordinateVector baselink := v1+v2-- notation not working

def vec_add_bad  : classicalTimeCoordinateVector _ := 
    time_vec_plus_vec vec_in_base_link vec_in_left_leg

--partially embedded