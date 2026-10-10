import RealRooted.Mathlib.Combinatorics.Enumerative.Separable
import RealRooted.SeparablePermutations.Gamma

/-!
# The descent enumerator of the separable permutations

A permutation is *separable* if it is built from the one-letter permutation by direct and skew
sums, equivalently if it avoids the patterns `2413` and `3142`
(`Equiv.Perm.mem_separablePermutations`).  Separability, descents and the enumerator are the
canonical `Equiv.Perm.IsSeparable`, `Equiv.Perm.descentCount` and
`Equiv.Perm.separableDescentEnumerator` of the staging modules
`RealRooted.Mathlib.Combinatorics.Enumerative`.  Here `descentEnumerator n` is that enumerator
for `n + 1` letters, which keeps the empty permutation out of the picture.

`RealRooted.SeparablePermutations.descentEnumerator_eq_descentPolynomial` identifies it with the
algebraic family `descentPolynomial` of `RealRooted/SeparablePermutations/Gamma.lean`.
-/

open Polynomial

noncomputable section

namespace RealRooted.SeparablePermutations

/-- The descent enumerator `∑ x ^ des σ` of the separable permutations of `n + 1` letters. -/
def descentEnumerator (n : ℕ) : ℝ[X] :=
  Equiv.Perm.separableDescentEnumerator ℝ (n + 1)

end RealRooted.SeparablePermutations
