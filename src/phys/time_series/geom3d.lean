import .definitions
import ..geom.geom3d

variables
  {tf : time_frame} (ts : time_space tf)
  {gf : geom3d_frame} (gs : geom3d_space gf)
  {gf2 : geom3d_frame} (gs2 : geom3d_space gf2)
  (min_t max_t : time ts)
/-
impossible to write this definition, 
-/
definition geom3d_series :=
  time_series ts geom3d_space

abbreviation geom3d_frame_series := 
  time_series ts geom3d_frame

abbreviation displacement3d_series := 
  time_series ts (displacement3d gs)

abbreviation position3d_series :=
  time_series ts (position3d gs)

abbreviation orientation3d_series := 
  time_series ts (orientation3d gs)

abbreviation rotation3d_series :=
  time_series ts (rotation3d gs)

abbreviation pose3d_series :=
  time_series ts (pose3d gs)

noncomputable def mk_geom3d_frame_series_empty : geom3d_frame_series ts := 
  λt, inhabited.default geom3d_frame

noncomputable def mk_displacement3d_series_empty : displacement3d_series ts gs :=
  λt, inhabited.default (displacement3d gs)

noncomputable def mk_position3d_series_empty : position3d_series ts gs :=
  λt, inhabited.default (position3d gs)

noncomputable def mk_orientation3d_series_empty : orientation3d_series ts gs := 
  λt, inhabited.default (orientation3d gs)

noncomputable def mk_rotation3d_series_empty : rotation3d_series ts gs :=
  λt, inhabited.default (rotation3d gs)

noncomputable def mk_pose3d_series_empty : pose3d_series ts gs :=
  λt, inhabited.default (pose3d gs)

abbreviation geom3d_frame_discrete := 
  discrete_series ts geom3d_frame

abbreviation displacement3d_discrete := 
  discrete_series ts (displacement3d gs)

abbreviation position3d_discrete :=
  discrete_series ts (position3d gs)

abbreviation orientation3d_discrete := 
  discrete_series ts (orientation3d gs)

abbreviation rotation3d_discrete :=
  discrete_series ts (rotation3d gs)

abbreviation pose3d_discrete :=
  discrete_series ts (pose3d gs)

abbreviation geom3d_transform_discrete :=
  discrete_series ts (geom3d_transform gs gs2)

noncomputable def geom3d_transform_discrete.transform_pose3d
  {tf : time_frame} {ts : time_space tf}
  {gf : geom3d_frame} {gs : geom3d_space gf}
  {gf2 : geom3d_frame} {gs2 : geom3d_space gf}
  (tr : geom3d_transform_discrete ts gs gs2) :
  pose3d_discrete ts gs → pose3d_discrete ts gs2 → pose3d_discrete ts gs2
  := 
  λpd pd2, pd2.update ⟨tr.head.timestamp,(tr.head.value.transform_pose3d pd.head.value)⟩

noncomputable def geom3d_transform_discrete.transform_pose3d_latest
  {tf : time_frame} {ts : time_space tf}
  {gf : geom3d_frame} {gs : geom3d_space gf}
  {gf2 : geom3d_frame} {gs2 : geom3d_space gf}
  (tr : geom3d_transform_discrete ts gs gs2) :
  pose3d_discrete ts gs → pose3d_discrete ts gs2 → pose3d_discrete ts gs2
  := 
  λpd pd2, pd2.update ⟨tr.head.timestamp,(tr.latest.value.transform_pose3d pd.head.value)⟩ 

notation N`[`T`⬝`O`]` := geom3d_transform_discrete.transform_pose3d_latest

noncomputable def mk_geom3d_frame_discrete_empty : geom3d_frame_discrete ts := 
  discrete_series.mk_empty

noncomputable def mk_displacement3d_discrete_empty : displacement3d_discrete ts gs :=
  discrete_series.mk_empty

noncomputable def mk_position3d_discrete_empty : position3d_discrete ts gs :=
  discrete_series.mk_empty

noncomputable def mk_orientation3d_discrete_empty : orientation3d_discrete ts gs := 
  discrete_series.mk_empty

noncomputable def mk_rotation3d_discrete_empty : rotation3d_discrete ts gs :=
  discrete_series.mk_empty

noncomputable def mk_pose3d_discrete_empty : pose3d_discrete ts gs :=
  discrete_series.mk_empty

noncomputable def mk_geom3d_transform_discrete_empty : geom3d_transform_discrete ts gs gs2 :=
  discrete_series.mk_empty

abbreviation geom3d_frame_discrete_ici := 
  discrete_series.Ici ts geom3d_frame min_t

abbreviation displacement3d_discrete_ici := 
  discrete_series.Ici ts (displacement3d gs) min_t

abbreviation position3d_discrete_ici :=
  discrete_series.Ici ts (position3d gs) min_t

abbreviation orientation3d_discrete_ici := 
  discrete_series.Ici ts (orientation3d gs) min_t

abbreviation rotation3d_discrete_ici :=
  discrete_series.Ici ts (rotation3d gs) min_t

abbreviation pose3d_discrete_ici :=
  discrete_series.Ici ts (pose3d gs) min_t