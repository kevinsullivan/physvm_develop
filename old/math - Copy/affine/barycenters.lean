-- barycenters and barycentric coordinates: here for the future
-- TODO: move this stuff to a separate file barycenters.lean or something
def affine_combination (g_add : ∑ i in s, g i = 1) := ∑ i in s, g i • v i
def barycenter (g_add : ∑ i in s, g i = 1) := g -- TODO: want to coerce g to be a list?