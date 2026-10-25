/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Roots

/-!
# Finite-degree Cayley transform

Algebraic and complex-root APIs for the homogeneous polynomial transform
`(1 - T)^n p(T / (1 - T))`.

This package generalizes theory first used in the OEIS proofs' Cayley
homogenization and unit-circle coefficient arguments.
-/

@[expose] public section
