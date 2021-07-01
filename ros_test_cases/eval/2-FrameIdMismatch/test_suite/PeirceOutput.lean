import .lang.expressions.time_expr
import .lang.expressions.geom1d_expr

import .lang.expressions.geom3d_expr

open lang.time
open lang.geom1d
open lang.geom3d
def World_fr : geom3d_frame_expr := |geom3d_std_frame|
def World : geom3d_space_expr World_fr := |geom3d_std_space|



