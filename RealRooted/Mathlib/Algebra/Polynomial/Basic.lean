module

public import Mathlib.Algebra.Polynomial.Basic

public section

namespace Polynomial
variable {R : Type*} [Semiring R] {p : R[X]}

attribute [simp] X_ne_C

lemma natCast_def (n : ℕ) : (n : R[X]) = C (n : R) := rfl
lemma ofNat_def (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]) = C (ofNat(n) : R) := rfl

end Polynomial
