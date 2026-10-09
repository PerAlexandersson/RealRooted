import RealRooted.BrandenLC

/-!
# Infinite log-concavity of Pólya-frequency polynomials

This packages the standard Boros–Moll/McNamara–Sagan iterate definition using
Brändén's transform. The cited result is P. Brändén, “Iterated sequences and
the geometry of zeros”, J. reine angew. Math. 658 (2011), 115–131. The proof
here is a different stability-functional / Laguerre argument found by
Aristotle.
-/

open Polynomial

namespace RealRooted.Branden

/-- A polynomial is infinitely log-concave when every transform iterate has
nonnegative coefficients. This is the standard Boros–Moll/McNamara–Sagan
definition, with the zeroth iterate included. -/
def IsInfinitelyLogConcave (p : ℝ[X]) : Prop :=
  ∀ k : ℕ, HasNonnegCoeffs ((RealRooted.Branden.logConcavityTransform^[k]) p)

/-- Every Pólya-frequency polynomial is infinitely log-concave. -/
theorem IsPFPolynomial.isInfinitelyLogConcave {p : ℝ[X]}
    (hp : IsPFPolynomial p) : IsInfinitelyLogConcave p := by
  intro k
  have hpf : ∀ j : ℕ,
      IsPFPolynomial ((RealRooted.Branden.logConcavityTransform^[j]) p) := by
    intro j
    induction j with
    | zero => simpa only [Function.iterate_zero_apply] using hp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact RealRooted.Branden.IsPFPolynomial.logConcavityTransform ih
  exact (hpf k).hasNonnegCoeffs

end RealRooted.Branden
