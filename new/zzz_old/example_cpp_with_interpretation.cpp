                        // annotations                        // code translated into Lean  
                        // t is time milliseconds
int foo () {
    float v = 5;        // vector/duration in space t           // v := vectr.mk t 5
    float w = 3;        // w another vector in space t                     // w := vectr.mk t 3
    float p = 3;        // p is point in space t                  // p := point.mk t 3
    float z = w + p;    // figure out what z is             // z := vectr.add {t} w v
    float p2 = p + p;   // does this type check?             // p2 := point_vector_add {t} p p **
    return z;
}