# This *New* Directory

## Overview

This directory contains our most recent developments in abstract and physical algebra for temporal and spatial dimensions. The algebras are affine, each comprising a set of points, a set of vectors that act on them, and satisfying the laws of affine spaces. This library currectly defines a 1-D  K affine coordinate space algebra as a simple DSL shallowly embedded in Lean. These affine spaces can be over specified fields.

## Operations and notations

An affine space comprises a set of points and a set of displacements between points called vectors. The set of vectors is a vector space under given vector addition and scaling operations. Addition is denoted + and scalar multiplication by \bu (in Lean). The affine operations currently supported are point-point subtraction yielding vector, denoted -v, and vector point addition, denoted +v. Crucially, the type of an affine space point or vector includes the affine *coordinate* space to which it belongs. The vector and affine space operations are constraints to work only for points and vectors in/with the same coordinate space. 

I think we need at least to instantiate a different standard space for each physical dimension.

## Issues
1. No algebra of transformations
2. No derived dimension algebra 
3. No direct summing of spaces
4. No barycentric combinations
5. Can't have just one std_space for distinct physical dimensions
  
Proposed: Each affine-structured physical dimension is represented by a unique, dimension-specific standard affine space. The client attaches physical interpretation to the origin and basis vectors of the standard frame on this space, but every abstract point and vector in it is mean to represent a physical quantity in that specific dimension (geometry, time, etc). From the standard frame given with each such "physical dimension" space, again, you can build trees of affine coordinate systems, yielding a collection of isomorphic coordinatizations, but only of one specific physical dimension. So, for example, vectors mustn't be equal coming from the std_space elements representing different physical dimensions. 

We need distinct replicas of std_spce, one for each physical dimension.

So what is the 


