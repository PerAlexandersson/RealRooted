import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Mathlib-version compatibility helpers

The following lemmas restate a handful of `Polynomial` facts about derivatives
using API that is stable across the Mathlib versions this file is built against.
-/

/-- Exact `natDegree` of a derivative over `ℝ` (a characteristic-zero field). -/
@[deprecated Polynomial.natDegree_derivative (since := "2026-10-05")]
lemma natDegree_derivative_eq (p : ℝ[X]) :
    p.derivative.natDegree = p.natDegree - 1 :=
  p.natDegree_derivative

/-- A polynomial of `natDegree` zero has vanishing derivative. -/
@[deprecated Polynomial.derivative_eq_zero (since := "2026-10-05")]
lemma derivative_eq_zero_of_natDegree_eq_zero {p : ℝ[X]} (h : p.natDegree = 0) :
    p.derivative = 0 :=
  Polynomial.derivative_eq_zero.mpr h

/-- A polynomial of positive `natDegree` has a nonzero derivative. -/
@[deprecated Polynomial.derivative_ne_zero (since := "2026-10-05")]
lemma derivative_ne_zero_of_natDegree_ne_zero {p : ℝ[X]} (h : p.natDegree ≠ 0) :
    p.derivative ≠ 0 :=
  Polynomial.derivative_ne_zero.mpr h

@[deprecated Polynomial.Splits.of_natDegree_eq_zero (since := "2026-10-06")]
alias splits_of_natDegree_eq_zero := Polynomial.Splits.of_natDegree_eq_zero

/-! ## Exact degree of derivative -/

protected lemma HasNonnegCoeffs.derivative {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.derivative := fun n => by
  simpa [coeff_derivative] using mul_nonneg (hp (n + 1)) (by positivity)

protected lemma HasPosLeadingCoeff.derivative {f : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : f.natDegree ≠ 0) :
    HasPosLeadingCoeff f.derivative := by
  unfold HasPosLeadingCoeff at hf_pos ⊢
  rw [leadingCoeff, f.natDegree_derivative, coeff_derivative]
  rw [Nat.sub_add_cancel (by lia), coeff_natDegree] at *
  positivity

lemma HasNonnegCoeffs.iterate_derivative {p : ℝ[X]} :
    ∀ n : ℕ, HasNonnegCoeffs p → HasNonnegCoeffs ((derivative^[n]) p)
  | 0, hp => hp
  | n + 1, hp => by
      simpa [Function.iterate_succ_apply'] using (hp.iterate_derivative n).derivative

lemma coeff_one_sub_X_mul_derivative (p : ℝ[X]) (m : Nat) :
    ((1 - X) * p.derivative).coeff m =
      ((m + 1 : ℝ) * p.coeff (m + 1)) - ((m : ℝ) * p.coeff m) := by
  cases m <;> simp [sub_mul, coeff_derivative]
  ring_nf

/-- The derivative does not vanish at a root of multiplicity one. -/
theorem eval_derivative_ne_zero_of_rootMultiplicity_eq_one
    {p : ℝ[X]} {r : ℝ} (hr : p.IsRoot r) (hmult : p.rootMultiplicity r = 1) :
    p.derivative.eval r ≠ 0 := by
  intro hder
  have hp₀ : p ≠ 0 := by rintro rfl; simp at hmult
  have hmultiple := (one_lt_rootMultiplicity_iff_isRoot hp₀).2 ⟨hr, hder⟩
  lia

/-- An exact double root has nonvanishing second derivative. -/
lemma eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
    {p : ℝ[X]} {x : ℝ} (hp0 : p ≠ 0) (hmult : p.rootMultiplicity x = 2) :
    p.derivative.derivative.eval x ≠ 0 := by
  have hp_root : p.IsRoot x :=
    (rootMultiplicity_pos hp0).mp (by lia)
  have hp_deg_ge2 : 2 ≤ p.natDegree := by
    calc
      2 = p.rootMultiplicity x := by lia
      _ = p.roots.count x := (count_roots p).symm
      _ ≤ p.roots.card := p.roots.count_le_card x
      _ ≤ p.natDegree := card_roots' p
  have hpd_ne : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hpd_rootmult : p.derivative.rootMultiplicity x = 1 := by
    rw [derivative_rootMultiplicity_of_root hp_root, hmult]
  apply eval_derivative_ne_zero_of_rootMultiplicity_eq_one
  · exact (rootMultiplicity_pos hpd_ne).mp (by lia)
  · exact hpd_rootmult

end RealRooted
