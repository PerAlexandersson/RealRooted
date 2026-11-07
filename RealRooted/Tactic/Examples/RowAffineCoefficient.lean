module

import RealRooted.Tactic.RowInterlacing
import RealRooted.Tactic.Row.AffineCoefficient
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineLogarithm
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
import RealRooted.BrandenLeite.PositivePowerFactors
import RealRooted.BrandenLeite.LogarithmicFactors
import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Generic canonical coefficient row tactic regressions -/

@[expose] public section

open Polynomial RealRooted

noncomputable section

namespace RealRooted.Tactic.Examples.RowAffineCoefficient

/-- Generic canonical negative-power rows, with no sequence-specific data. -/
def powerRows {ι ν : Type*} (s : Finset ι) (α : ι → ℝ) (t : Finset ν) (β : ν → ℝ)
    (c κ : ℝ) (r n : ℕ) : ℝ[X] :=
  PowerSeries.affineNegativePowerCoeff κ
    ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
    ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n

/-- Generic canonical logarithmic rows, with no sequence-specific data. -/
def logRows {ι ν : Type*} (s : Finset ι) (α : ι → ℝ) (t : Finset ν) (β : ν → ℝ)
    (c : ℝ) (r n : ℕ) : ℝ[X] :=
  PowerSeries.affineLogCoeff
    ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
    ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n

example {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (r n : ℕ) (hr : 0 < r) :
    (powerRows s α t β c κ r n).Splits := by
  rr_row_splits (via := affineCoefficient)

example {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) (c : ℝ) (hc : 0 < c)
    (r n : ℕ) (hr : 0 < r) (hn : n ≠ 0) :
    (logRows s α t β c r n).Splits := by
  rr_row_splits (via := affineCoefficient)

section

variable {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
  (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
  (hβ : ∀ j ∈ t, 0 ≤ β j) (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
  (r n : ℕ) (hr : 0 < r) (hn : n ≠ 0)

include hs hα hβ hc hκ hr in
example : (powerRows s α t β c κ r n).Splits := by
  rr_row_splits

include hs hα hβ hc hr hn in
example : (logRows s α t β c r n).Splits := by
  rr_row_splits?

-- The route must not invent a positive exponent or a nonzero logarithmic index.
include hs hα hβ hc hr in
example (h : (powerRows s α t β c κ r n).Splits) :
    (powerRows s α t β c κ r n).Splits := by
  fail_if_success (clear h hκ; rr_row_splits (via := affineCoefficient))
  exact h

include hs hα hβ hc hr in
example (h : (logRows s α t β c r n).Splits) :
    (logRows s α t β c r n).Splits := by
  fail_if_success (clear h hn; rr_row_splits (via := affineCoefficient))
  exact h

example (p : ℝ[X]) (h : p.Splits) : p.Splits := by
  fail_if_success (clear h; rr_row_splits (via := affineCoefficient))
  exact h

end

-- An arbitrary series presentation is rejected before formal-series elaboration.
example (κ : ℝ) (Q B : PowerSeries ℝ) (n : ℕ)
    (h : (PowerSeries.affineNegativePowerCoeff κ Q B n).Splits) :
    (PowerSeries.affineNegativePowerCoeff κ Q B n).Splits := by
  fail_if_success (clear h; rr_row_splits (via := affineCoefficient))
  exact h

-- Products of separately coerced factors require algebraic normalization first.
example {ι : Type*} (s : Finset ι) (α : ι → ℝ) (κ : ℝ) (B : PowerSeries ℝ)
    (n : ℕ)
    (h : (PowerSeries.affineNegativePowerCoeff κ
      (∏ i ∈ s, ((1 - C (α i) * X : ℝ[X]) : PowerSeries ℝ)) B n).Splits) :
    (PowerSeries.affineNegativePowerCoeff κ
      (∏ i ∈ s, ((1 - C (α i) * X : ℝ[X]) : PowerSeries ℝ)) B n).Splits := by
  fail_if_success (clear h; rr_row_splits (via := affineCoefficient))
  exact h

open RealRooted.BrandenLeite

/-- Nonintegral exponent and genuinely nonmonomial numerator, matching the
example in the source note. -/
example (n : ℕ) :
    let q := fun m => PowerSeries.affineNegativePowerCoeff (1 / 2 : ℝ)
      (((1 - X) * (1 - C 2 * X) : Polynomial ℝ) : PowerSeries ℝ)
      ((X * (1 + C 3 * X) : Polynomial ℝ) : PowerSeries ℝ) m
    (q n).Splits ∧ (q n).natDegree = n ∧ Interl (q n) (q (n + 1)) := by
  have hp := affineNegativePowerCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp)
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 2)
    (by intro i _; fin_cases i <;> norm_num)
    (Finset.univ : Finset (Fin 1)) (fun _ => (3 : ℝ))
    (by intro i _; norm_num) (c := 1) (κ := 1 / 2)
    (by norm_num) (by norm_num) 1 (by norm_num) n
  simpa [Fin.prod_univ_two, Fin.prod_univ_one] using
    And.intro hp.2.1 (And.intro hp.2.2.2.1 hp.2.2.2.2.2)

/-- Valuation three exercises degree loss and the equal-degree interlacing
steps of the regularization limit. -/
example (n : ℕ) :
    let q := fun m => PowerSeries.affineNegativePowerCoeff (1 / 2 : ℝ)
      (((1 - X) * (1 - C 2 * X) : Polynomial ℝ) : PowerSeries ℝ)
      ((C 2 * X ^ 3 * (1 + C 3 * X) : Polynomial ℝ) : PowerSeries ℝ) m
    (q n).natDegree = n / 3 ∧ Interl (q n) (q (n + 1)) := by
  have hp := affineNegativePowerCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp)
    (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 2)
    (by intro i _; fin_cases i <;> norm_num)
    (Finset.univ : Finset (Fin 1)) (fun _ => (3 : ℝ))
    (by intro i _; norm_num) (c := 2) (κ := 1 / 2)
    (by norm_num) (by norm_num) 3 (by norm_num) n
  simpa [Fin.prod_univ_two, Fin.prod_univ_one] using
    And.intro hp.2.2.2.1 hp.2.2.2.2.2

/-- Repeated denominator and numerator factors remain allowed. -/
example (n : ℕ) :
    let q := fun m => PowerSeries.affineNegativePowerCoeff (1 / 2 : ℝ)
      (((1 - X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ)
      ((X ^ 2 * (1 + X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ) m
    (q n).Splits ∧ (q n).natDegree = n / 2 ∧ Interl (q n) (q (n + 1)) := by
  have hp := affineNegativePowerCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp) (fun _ => (1 : ℝ))
    (by intro i _; norm_num)
    (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
    (by intro i _; norm_num) (c := 1) (κ := 1 / 2)
    (by norm_num) (by norm_num) 2 (by norm_num) n
  simpa [Fin.prod_univ_two, pow_two] using
    And.intro hp.2.1 (And.intro hp.2.2.2.1 hp.2.2.2.2.2)

/-- The logarithmic limit retains the same higher-valuation degree and
orientation, starting at positive row index. -/
example (n : ℕ) :
    let ℓ := fun m => PowerSeries.affineLogCoeff
      (((1 - X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ)
      ((X ^ 2 * (1 + X) ^ 2 : Polynomial ℝ) : PowerSeries ℝ) m
    (ℓ (n + 1)).Splits ∧ (ℓ (n + 1)).natDegree = (n + 1) / 2 ∧
      Interl (ℓ (n + 1)) (ℓ (n + 2)) := by
  have hp := affineLogCoeff_factor_properties
    (Finset.univ : Finset (Fin 2)) (by simp) (fun _ => (1 : ℝ))
    (by intro i _; norm_num)
    (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ))
    (by intro i _; norm_num) (c := 1) (by norm_num) 2 (by norm_num)
    (n + 1) (Nat.succ_ne_zero n)
  simpa [Fin.prod_univ_two, pow_two, Nat.add_assoc] using
    And.intro hp.2.1 (And.intro hp.2.2.2.1 hp.2.2.2.2.2)

/-- The linear/linear exceptional case is exactly a positive scalar times
a repeated linear factor. It provides an exact regression for the exceptional family. -/
private theorem affineNegativePowerCoeff_one_sub_X (κ : ℝ) (n : ℕ) :
    PowerSeries.affineNegativePowerCoeff κ (1 - PowerSeries.X) PowerSeries.X n =
      C (Ring.multichoose κ n) * (1 + X) ^ n := by
  unfold PowerSeries.affineNegativePowerCoeff
  have harg : PowerSeries.map Polynomial.C (1 - PowerSeries.X : PowerSeries ℝ) -
      PowerSeries.C Polynomial.X * PowerSeries.map Polynomial.C PowerSeries.X - 1 =
      PowerSeries.C (-(1 + Polynomial.X) : Polynomial ℝ) *
        (PowerSeries.X : PowerSeries (Polynomial ℝ)) := by
    simp only [map_sub, map_one, PowerSeries.map_X, map_neg, map_add]
    ring
  have hsmul := PowerSeries.smul_eq_C_mul (R := Polynomial ℝ)
    (PowerSeries.X : PowerSeries (Polynomial ℝ)) (-(1 + Polynomial.X))
  have hrescale :=
    (PowerSeries.rescale_eq_subst (R := Polynomial ℝ) (-(1 + Polynomial.X))
      (PowerSeries.binomialSeries (Polynomial ℝ) (-C κ))).trans
      (congrArg
        (fun g : PowerSeries (Polynomial ℝ) =>
          PowerSeries.subst g (PowerSeries.binomialSeries (Polynomial ℝ) (-C κ))) hsmul)
  rw [harg]
  calc
    _ = PowerSeries.coeff n (PowerSeries.rescale (-(1 + Polynomial.X))
        (PowerSeries.binomialSeries (Polynomial ℝ) (-C κ))) :=
      congrArg (PowerSeries.coeff n) hrescale.symm
    _ = (-(1 + X)) ^ n * Ring.choose (-C κ) n := by
      rw [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff]
      simp only [smul_eq_mul, mul_one]
    _ = (1 + X) ^ n * ((-1 : Polynomial ℝ) ^ n * Ring.choose (-C κ) n) := by
      rw [neg_pow]
      ring
    _ = C (Ring.multichoose κ n) * (1 + X) ^ n := by
      rw [Ring.neg_one_pow_mul_choose_neg,
        ← Ring.map_multichoose Polynomial.C κ n]
      ring

/-- A nonintegral exponent does not remove the repeated-root exception. -/
example (n : ℕ) :
    PowerSeries.affineNegativePowerCoeff (1 / 2 : ℝ)
      (1 - PowerSeries.X) PowerSeries.X (n + 2) =
        C (Ring.multichoose (1 / 2 : ℝ) (n + 2)) * (1 + X) ^ (n + 2) :=
  affineNegativePowerCoeff_one_sub_X (1 / 2) (n + 2)

/-- In the exceptional family, `-1` is simultaneously a root of every
row of degree at least two and of its derivative. -/
example (n : ℕ) :
    let p := PowerSeries.affineNegativePowerCoeff (1 / 2 : ℝ)
      (1 - PowerSeries.X) PowerSeries.X (n + 2)
    p.eval (-1) = 0 ∧ p.derivative.eval (-1) = 0 := by
  dsimp
  rw [affineNegativePowerCoeff_one_sub_X]
  constructor <;> simp [Polynomial.derivative_mul, Polynomial.derivative_pow]

end RealRooted.Tactic.Examples.RowAffineCoefficient
