import PhysL

def time : peirce.vector_space := peirce.vector_space.mk 0
def geom : peirce.vector_space := peirce.vector_space.mk 1
def flt_var : peirce.scalar_variable := peirce.scalar_variable.mk  1
def flt : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def flt2_var : peirce.scalar_variable := peirce.scalar_variable.mk  2
def flt2 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt2_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def flt3_var : peirce.scalar_variable := peirce.scalar_variable.mk  3
def flt3 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt3_var ( ( peirce.scalar_expression.scalar_var flt2_var : peirce.scalar_expression  )  )

def flt4_var : peirce.scalar_variable := peirce.scalar_variable.mk  4
def flt4 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt4_var ( ( peirce.scalar_expression.scalar_mul ( peirce.scalar_expression.scalar_var flt3_var : peirce.scalar_expression  )  ( peirce.scalar_expression.scalar_var flt3_var : peirce.scalar_expression  )  : peirce.scalar_expression )  )

def r2o2_var : peirce.scalar_variable := peirce.scalar_variable.mk  5
def r2o2 : peirce.scalar_cmd := peirce.scalar_cmd.assmt r2o2_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def v1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 6
def v1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def v2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 7
def v2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v2_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def r11_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 8
def r11 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r11_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r12_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 9
def r12 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r12_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r13_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 10
def r13 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r13_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def res1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 11
def res1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res1_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def vvv_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 12
def vvv : peirce.vector_cmd := @peirce.vector_cmd.assmt geom vvv_var ( ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def v3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 13
def v3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v3_var ( ( @peirce.vector_expression.scalar_vector_mul geom ( peirce.scalar_expression.scalar_var flt2_var : peirce.scalar_expression  )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def v4_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 14
def v4 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v4_var ( ( @peirce.vector_expression.vector_paren geom ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v3_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) : peirce.vector_expression geom ) : peirce.vector_expression geom )  )

def r21_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 15
def r21 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r21_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r22_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 16
def r22 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r22_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def r23_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 17
def r23 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom r23_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def s11_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 18
def s11 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom s11_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def s12_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 19
def s12 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom s12_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def s13_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 20
def s13 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom s13_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def sh1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 21
def sh1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom sh1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def sh2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 22
def sh2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom sh2_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def sh3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 23
def sh3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom sh3_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def p1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 24
def p1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom p1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def p2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 25
def p2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom p2_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def p3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 26
def p3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom p3_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def c1_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 27
def c1 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom c1_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def c2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 28
def c2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom c2_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def c3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 29
def c3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom c3_var (  ( @peirce.vector_expression.vector_literal geom  ( @peirce.vector.mk geom  0 0 0  : peirce.vector geom ) : peirce.vector_expression geom )  )

def res2_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 30
def res2 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res2_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def res3_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 31
def res3 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res3_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom projection_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def res4_var : @peirce.vector_variable geom := @peirce.vector_variable.mk geom 32
def res4 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res4_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom rotate_and_scale_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def rotation1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 33
def rotation1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotation1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom r11_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r12_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r13_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def rotation2_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 34
def rotation2 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotation2_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom r21_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r22_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom r23_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def scale1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 35
def scale1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom scale1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom s11_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom s12_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom s13_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def sheer1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 36
def sheer1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom sheer1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom sh1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom sh2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom sh3_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def projection_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 37
def projection : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom projection_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom p1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom p2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom p3_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def double_rotate_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 38
def double_rotate : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom double_rotate_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom rotation1_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom rotation2_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def rotate_and_scale_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 39
def rotate_and_scale : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom double_rotate_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def cob1_var : @peirce.transform_variable geom geom := @peirce.transform_variable.mk geom geom 40
def cob1 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom cob1_var ( ( @peirce.transform_expression.transform_literal geom geom  ( @peirce.transform.mk geom geom  ( @peirce.vector_expression.vector_var geom c1_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom c2_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom c3_var : peirce.vector_expression geom )  : peirce.transform geom geom ) : peirce.transform_expression geom geom ) )

def v2_41 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v2_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def res1_42 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res1_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom rotation1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def v2_43 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v2_var ( ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  )

def v4_44 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom v4_var ( ( @peirce.vector_expression.scalar_vector_mul geom ( peirce.scalar_expression.scalar_var flt3_var : peirce.scalar_expression  )  ( @peirce.vector_expression.vector_add geom ( @peirce.vector_expression.vector_var geom v4_var : peirce.vector_expression geom )  ( @peirce.vector_expression.vector_var geom v4_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) : peirce.vector_expression geom ) )

def res4_45 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res4_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom rotation2_var : peirce.transform_expression geom geom )  ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom rotation1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) : peirce.vector_expression geom ) )

def res4_46 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res4_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom res4_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def res3_47 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res3_var ( ( peirce.transform_apply ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom rotation2_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom rotation1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def res2_48 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res2_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def res2_49 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res2_var ( ( peirce.transform_apply ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom projection_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v2_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def res2_50 : peirce.vector_cmd := @peirce.vector_cmd.assmt geom res2_var ( ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_paren geom ( peirce.transform_apply ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  ( @peirce.vector_expression.vector_var geom v1_var : peirce.vector_expression geom )  : peirce.vector_expression geom ) : peirce.vector_expression geom )  : peirce.vector_expression geom ) )

def flt_51 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt_var ( ( peirce.scalar_expression.scalar_lit 0 : peirce.scalar_expression ) )

def flt3_52 : peirce.scalar_cmd := peirce.scalar_cmd.assmt flt3_var ( ( peirce.scalar_expression.scalar_paren ( peirce.scalar_expression.scalar_var flt2_var : peirce.scalar_expression  )  : peirce.scalar_expression )   )

def rotate_and_scale_53 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom double_rotate_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def rotate_and_scale_54 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( peirce.transform_compose ( @peirce.transform_expression.transform_var geom geom double_rotate_var : peirce.transform_expression geom geom )  ( @peirce.transform_expression.transform_var geom geom scale1_var : peirce.transform_expression geom geom )  : peirce.transform_expression geom geom )  )

def rotate_and_scale_55 : peirce.transform_cmd := @peirce.transform_cmd.assmt geom geom rotate_and_scale_var ( ( @peirce.transform_expression.transform_var geom geom cob1_var : peirce.transform_expression geom geom )  )