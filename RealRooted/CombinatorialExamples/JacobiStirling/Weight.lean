import Mathlib.Algebra.Ring.Defs

/-!
# Jacobi--Stirling weights

The first- and second-kind Jacobi--Stirling triangles use the same weight
sequence.
-/

namespace RealRooted.JacobiStirling

variable {R : Type*} [CommSemiring R]

/-- The Jacobi--Stirling weight `i(i + z)`, indexed from `i = 1`. -/
def weight (z : R) (i : ℕ) : R :=
  (i + 1 : R) * ((i + 1 : R) + z)

end RealRooted.JacobiStirling
