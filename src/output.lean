import vec

def time : peirce.space := peirce.space.mk 0
def geom : peirce.space := peirce.space.mk 1
def flt : peirce.scalar  := ( 0 : peirce.scalar )
def flt2 : peirce.scalar  := ( 0 : peirce.scalar )
def flt3 : peirce.scalar  := ( flt2 : peirce.scalar  )
def flt4 : peirce.scalar  := ( peirce.smul ( flt3 : peirce.scalar  )  ( flt3 : peirce.scalar  )  : peirce.scalar )
def v1 : peirce.vec geom := ( peirce.vec.mkVector _ 0 0 0 )
def v2 : peirce.vec _ := ( v1 : peirce.vec _ )
def vvv : peirce.vec _ := ( peirce.vadd ( v1 : peirce.vec _ ) ( v2 : peirce.vec _ ) : peirce.vec _ )
def v3 : peirce.vec _ := ( peirce.vsmul ( flt2 : peirce.scalar  )  ( v2 : peirce.vec _ ) : peirce.vec _ )
def v4 : peirce.vec _ := ( ( ( peirce.vadd ( v3 : peirce.vec _ ) ( peirce.vsmul ( flt : peirce.scalar  )  ( v2 : peirce.vec _ ) : peirce.vec _ ) : peirce.vec _ ) ) : peirce.vec _ )
#check ( v2 : peirce.vec _ ) == ( v1 : peirce.vec _ )
#check ( v4 : peirce.vec _ ) == ( peirce.vsmul ( flt3 : peirce.scalar  )  ( peirce.vadd ( v4 : peirce.vec _ ) ( v4 : peirce.vec _ ) : peirce.vec _ ) : peirce.vec _ )
#check ( flt3 : peirce.scalar  )  == ( ( ( flt2 : peirce.scalar  )  ) : peirce.scalar  )

--OUTPUT

/--
root@39b34ed0eb59:/# lean /tmp/file71EmNW.lean
v2 == v1 : Prop
v4 == peirce.vsmul flt3 (peirce.vadd v4 v4) : Prop
flt3 == flt2 : Prop
--/