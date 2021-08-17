# Library design question: Phys. 

Do we want to enable user of library to instantiate multiple independent instances of, say, a time space? One argument is that there's only one timeline in Newtonian physics, and everything else is related to frames (origins, units, etc). A counter-argument is that in distributed systems you can have unsynchronized clocks, and maybe these have to be modeled by separate timelines. At a minimum, some kind of time synchronization will be needed to allow transforms between two such clocks, possibly with uncertainty bounds.

So our library will support instantiation of multiple physical spaces for the same physical dimension. If a user wants to model a single global space for a dimension they can certainly do that with a singleton object.

We also do want to impose a constraint that algebraic/physical operations can only be performed on objects within space. 

That said, we will want to be able to define transforms that take us from one space to another. This one of the places where bare coordinate matrices are too abstract -- they don't specify domain and co-domain spaces. 



In this directory, we define various spaces of physical quantities,
aka dimensions. We currently focus on classical versions of the following: 
- time
- geometry
- velocity

Original concept. Review how "on" it was, including where it was off.

- DSL defines term something like this: (Lit_Geom_Expr "world" 3 si_system ...)
- What are the semantics of this term? To what does the following evaluate?
**    eval(Lit_Geom_Expr "world" 3 si_system ...) ----> something in phys
- Intuition: It evaluates to a "space". Idea: Dimensions are spaces.
- A space (phys) in turn is a physical concept with an algebraic structure (affine space)
- For example, a 1D geometric space has the structure of an real affine 1 space. 
- Another intuition: Spaces (qua dimensions) can be multiplied
- For example, we can multiple 2 1-d geometric spaces to get a 2D space.
