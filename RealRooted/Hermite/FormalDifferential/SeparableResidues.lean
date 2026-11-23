module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.Separable
import RealRooted.Hermite.FormalDifferential.SeparableNormalization
import RealRooted.Mathlib.RingTheory.PowerSeries.FirstDiscrepancy

/-!
# Degree classes with eventually simple complex roots

For every nonexponential real formal symbol with nonzero constant term,
one common discrepancy order selects two degree residue classes on which
all nonzero polynomial inputs eventually acquire simple complex roots.
This is the real-symbol case of Kim--Kim (2015), Section 4.
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- A nonexponential symbol determines an order `p >= 2` such that every
nonzero input of degree congruent to zero or one modulo `p` eventually has
simple complex roots. The iteration time can depend on the input. -/
theorem exists_eventually_separable_iterate
    {φ : PowerSeries ℝ} (h0 : PowerSeries.constantCoeff φ ≠ 0)
    (hne : φ ≠ PowerSeries.C (PowerSeries.constantCoeff φ) *
      PowerSeries.rescale (PowerSeries.coeff 1 φ / PowerSeries.constantCoeff φ)
        (PowerSeries.exp ℝ)) :
    ∃ p : ℕ, 2 ≤ p ∧ ∀ P : ℝ[X], P ≠ 0 → P.natDegree % p ≤ 1 →
      ∀ᶠ m : ℕ in atTop, ((formalDifferentialOperator φ)^[m] P).Separable := by
  obtain ⟨p, hp, hjet, hdiff⟩ :=
    PowerSeries.exists_first_scaled_exponential_discrepancy h0 hne
  refine ⟨p, hp, fun P hP hrem ↦ ?_⟩
  exact eventually_separable_iterate_of_scaled_exponential_jet h0
    (PowerSeries.coeff 1 φ / PowerSeries.constantCoeff φ) hp hjet
    (sub_ne_zero.mpr hdiff) hP hrem

end RealRooted.HermitePoulain
