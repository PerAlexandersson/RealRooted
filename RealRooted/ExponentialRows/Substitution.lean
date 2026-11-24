module

public import RealRooted.ExponentialRows.SubstitutionRows
public import RealRooted.PFPolynomial
import RealRooted.ExponentialRows.SubstitutionPreserver
import RealRooted.GarloffWagner.KreinExpansion
import Mathlib.Tactic

/-!
# Substitution closure of real-rooted exponential rows

If `Φ(0) = 0` and `Φ' = a + b z + λ Φ` for nonnegative `a`, `b`, and `λ`,
substitution of `Φ(B)` for the marked series preserves real-rootedness and
all directed weak interlacings of the rows of `exp(A + t B)`.

The proof uses the exponential-kernel operator, its single-deletion invariant,
and the existing Krein-expansion and coefficientwise closure theorems.
Zero outputs and vanishing parameter values are included.

The existing `insertionRow_isRealRooted_quartic_of_nonneg` supplies nonnegative
quadratic seeds for the polynomial degree-raising corollary. Related Bell theory
is `RealRooted.associatedBell_rows` in `DerivativeRecurrence/AssociatedBell.lean`,
which packages a normalized recurrence. Here the threshold-two corollary is
identified with its literal EGF using the same generic `insertionRow` definition.

Source: unpublished manuscript (RealRooted issue #2415), Theorem 1,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- An ODE substitution kernel preserves PF polynomials. -/
theorem isPFPolynomial_exponentialSubstitution {P : PowerSeries ℝ} {a b l : ℝ}
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (exponentialSubstitution P p) := by
  apply isPFPolynomial_map_of_substitution_rule (exponentialSubstitution P) ha hb hl
  · intro q hq
    exact hasNonnegCoeffs_exponentialSubstitution hP
      (coeff_nonneg_of_substitution_ode hP hode ha hb hl) hq
  · exact coeff_zero_exponentialSubstitution hP
  · exact exponentialSubstitution_one hP
  · exact exponentialSubstitution_linear_mul hP hode
  · exact hp

/-- ODE substitution kernels preserve directed weak PF interlacing, even when
one or both transformed polynomials vanish. -/
theorem interl_exponentialSubstitution {P : PowerSeries ℝ} {a b l : ℝ}
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hfg : Interl f g) :
    Interl (exponentialSubstitution P f) (exponentialSubstitution P g) := by
  apply interl_map_of_substitution_rule (exponentialSubstitution P) ha hb hl
  · intro q hq
    exact hasNonnegCoeffs_exponentialSubstitution hP
      (coeff_nonneg_of_substitution_ode hP hode ha hb hl) hq
  · exact coeff_zero_exponentialSubstitution hP
  · exact exponentialSubstitution_one hP
  · exact exponentialSubstitution_linear_mul hP hode
  · exact natDegree_exponentialSubstitution_le hP
  · exact hf
  · exact hg
  · exact hfg

/-- Substitution closure for an arbitrary unmarked series: every real-rooted
input row with nonnegative coefficients has a real-rooted substituted row.
The zero polynomial is included in the splitting conclusion. -/
theorem insertionRow_splits_subst {A B P : PowerSeries ℝ} {a b l : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A (P.subst B)) n).Splits := by
  rw [← exponentialSubstitution_insertionRow hA hB hP]
  exact (isPFPolynomial_exponentialSubstitution hP hode ha hb hl
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) hrow)).splits

/-- Every directed weak interlacing between exponential rows survives ODE
substitution of the marked series, with the same arbitrary unmarked series. -/
theorem insertionRow_interl_subst {A B P : PowerSeries ℝ} {a b l : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : PowerSeries.constantCoeff P = 0)
    (hode : PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * P)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (hrows : ∀ n, (insertionRow (affineBlockWeights A B) n).Splits)
    {m n : ℕ} (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) :
    Interl (insertionRow (affineBlockWeights A (P.subst B)) m)
      (insertionRow (affineBlockWeights A (P.subst B)) n) := by
  rw [← exponentialSubstitution_insertionRow hA hB hP,
    ← exponentialSubstitution_insertionRow hA hB hP]
  exact interl_exponentialSubstitution hP hode ha hb hl
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn m) (hrows m))
    (IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) (hrows n)) hinterl

/-- Quadratic marked substitution preserves splitting for every unmarked
series. This is the `λ = 0` specialization, including `a = 0` and `b = 0`. -/
theorem insertionRow_splits_quadratic_subst {A B : PowerSeries ℝ} {a b : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A
      (PowerSeries.C a * B + PowerSeries.C (b / 2) * B ^ 2)) n).Splits := by
  let P : PowerSeries ℝ :=
    PowerSeries.C a * PowerSeries.X + PowerSeries.C (b / 2) * PowerSeries.X ^ 2
  have hP : PowerSeries.constantCoeff P = 0 := by simp [P]
  have hode : PowerSeries.derivative P =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C 0 * P := by
    have hc : PowerSeries.C (b / 2) * (2 : PowerSeries ℝ) = PowerSeries.C b := by
      rw [← map_ofNat (PowerSeries.C : ℝ →+* PowerSeries ℝ) 2, ← map_mul]
      congr 1
      ring
    simp [P, PowerSeries.derivative.leibniz, smul_eq_mul]
    linear_combination hc * PowerSeries.X
  have hsub : P.subst B = PowerSeries.C a * B + PowerSeries.C (b / 2) * B ^ 2 := by
    have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hB
    simp only [P, PowerSeries.subst_add hs, PowerSeries.subst_mul hs,
      PowerSeries.subst_pow hs, PowerSeries.subst_X hs, PowerSeries.subst_C]
    rfl
  simpa only [hsub] using insertionRow_splits_subst hA hB hP hode ha hb le_rfl
    hAnn hBnn n hrow

/-- The degree-raising operation on `q`, with marked series `B = z² q`.
The unmarked formal series is arbitrary and fixed. -/
theorem insertionRow_splits_degree_raising {A q : PowerSeries ℝ} {a b : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hq : ∀ r, 0 ≤ PowerSeries.coeff r q)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A (PowerSeries.X ^ 2 * q)) n).Splits) :
    (insertionRow (affineBlockWeights A (PowerSeries.X ^ 2 *
      (PowerSeries.C a * q + PowerSeries.C (b / 2) * PowerSeries.X ^ 2 * q ^ 2))) n).Splits := by
  have hB : PowerSeries.constantCoeff (PowerSeries.X ^ 2 * q) = 0 := by simp
  have hBnn (r : ℕ) : 0 ≤ PowerSeries.coeff r (PowerSeries.X ^ 2 * q) := by
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs
    · exact hq _
    · exact le_rfl
  have H := insertionRow_splits_quadratic_subst hA hB ha hb hAnn hBnn n hrow
  convert H using 2; ring

/-- Polynomial marked-block form of the degree-raising closure. In particular,
the already formalized nonnegative quadratic seeds can be used directly. -/
theorem insertionRow_splits_marked_degree_raising {q : ℝ[X]} {a b : ℝ}
    (hq : HasNonnegCoeffs q) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (hrow : (insertionRow (markedBlockWeights (X ^ 2 * q)) n).Splits) :
    (insertionRow (markedBlockWeights
      (X ^ 2 * (C a * q + C (b / 2) * X ^ 2 * q ^ 2))) n).Splits := by
  have hweights (Q : ℝ[X]) :
      affineBlockWeights PowerSeries.X (PowerSeries.X ^ 2 * (Q : PowerSeries ℝ)) =
        markedBlockWeights (X ^ 2 * Q) := by
    have h1 : (X ^ 2 * Q).coeff 1 = 0 := by simp [Polynomial.coeff_X_pow_mul']
    simpa using affineBlockWeights_X_eq_markedBlockWeights h1
  have hAnn (r : ℕ) : 0 ≤ PowerSeries.coeff r (PowerSeries.X : PowerSeries ℝ) := by
    simp only [PowerSeries.coeff_X]
    split_ifs <;> positivity
  have hqnn (r : ℕ) : 0 ≤ PowerSeries.coeff r (q : PowerSeries ℝ) := by
    simpa using hq r
  have hin : (insertionRow (affineBlockWeights PowerSeries.X
      (PowerSeries.X ^ 2 * (q : PowerSeries ℝ))) n).Splits := by
    simpa only [hweights] using hrow
  have H := insertionRow_splits_degree_raising (by simp) ha hb hAnn hqnn n hin
  have hQ : (PowerSeries.C a * (q : PowerSeries ℝ) +
      PowerSeries.C (b / 2) * PowerSeries.X ^ 2 * (q : PowerSeries ℝ) ^ 2) =
        ((C a * q + C (b / 2) * X ^ 2 * q ^ 2 : ℝ[X]) : PowerSeries ℝ) := by simp
  simpa only [hQ, hweights] using H

/-- Equal singleton weights in the unmarked and marked series give binomial rows. -/
theorem insertionRow_affine_X_X (n : ℕ) :
    insertionRow (affineBlockWeights PowerSeries.X PowerSeries.X) n = (1 + X) ^ n := by
  rw [insertionRow_affineBlockWeights_eq_exponential (by simp) (by simp)]
  have harg : PowerSeries.map C (PowerSeries.X : PowerSeries ℝ) +
      PowerSeries.C X * PowerSeries.map C (PowerSeries.X : PowerSeries ℝ) =
        PowerSeries.C (1 + X : ℝ[X]) * (PowerSeries.X : PowerSeries ℝ[X]) := by
    simp only [PowerSeries.map_X, map_add, map_one]
    ring
  have hs : PowerSeries.rescale (1 + X) (PowerSeries.exp ℝ[X]) =
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C (1 + X) * PowerSeries.X) := by
    rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]
  rw [harg, ← hs, factorialCoeff_rescale_exp]

private theorem coeff_X_nonneg (r : ℕ) :
    0 ≤ PowerSeries.coeff r (PowerSeries.X : PowerSeries ℝ) := by
  rw [PowerSeries.coeff_X]
  split_ifs <;> positivity

private theorem thresholdTwo_ode :
    PowerSeries.derivative (PowerSeries.exp ℝ - 1 - PowerSeries.X) =
      PowerSeries.C 0 + PowerSeries.C 1 * PowerSeries.X +
        PowerSeries.C 1 * (PowerSeries.exp ℝ - 1 - PowerSeries.X) := by
  simp only [map_sub, PowerSeries.derivative_exp, PowerSeries.derivative_one,
    PowerSeries.derivative_X, map_zero, map_one]
  ring

/-- Threshold-two big-block rows are nonzero and real-rooted in every rank.
The EGF is exactly `exp(z + t (exp(z) - 1 - z))`; singletons are unmarked
and each block of size at least two contributes `t`. -/
theorem insertionRow_isRealRooted_threshold_two (n : ℕ) :
    let w := affineBlockWeights PowerSeries.X (PowerSeries.exp ℝ - 1 - PowerSeries.X)
    insertionRow w n ≠ 0 ∧ (insertionRow w n).Splits := by
  dsimp only
  have hP : PowerSeries.constantCoeff (PowerSeries.exp ℝ - 1 - PowerSeries.X) = 0 := by simp
  have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℝ) = 0 := by simp
  have hid := exponentialSubstitution_insertionRow (A := PowerSeries.X) (B := PowerSeries.X)
    hX0 hX0 hP n
  rw [PowerSeries.X_subst] at hid
  have hseed : IsPFPolynomial (insertionRow
      (affineBlockWeights PowerSeries.X PowerSeries.X) n) := by
    rw [insertionRow_affine_X_X]
    simpa [add_comm] using (isPFPolynomial_X_add_C (a := 1) zero_le_one).pow n
  have hpf := isPFPolynomial_exponentialSubstitution hP thresholdTwo_ode
    le_rfl zero_le_one zero_le_one hseed
  rw [hid] at hpf
  refine ⟨?_, hpf.splits⟩
  have hc := coeff_zero_exponentialSubstitution hP
    (insertionRow (affineBlockWeights PowerSeries.X PowerSeries.X) n)
  rw [hid, insertionRow_affine_X_X] at hc
  have hc1 : (insertionRow
      (affineBlockWeights PowerSeries.X (PowerSeries.exp ℝ - 1 - PowerSeries.X)) n).coeff 0 =
        1 := by
    simpa only [coeff_zero_eq_eval_zero, eval_pow, eval_add, eval_one, eval_X,
      add_zero, one_pow] using hc
  intro hzero
  simp [hzero] at hc1

/-- Threshold-two big-block rows have directed consecutive weak interlacing.
Both rows are nonzero, so this is the library's `StrictInterl` relation,
which allows repeated and shared roots. -/
theorem insertionRow_strictInterl_threshold_two (n : ℕ) :
    let w := affineBlockWeights PowerSeries.X (PowerSeries.exp ℝ - 1 - PowerSeries.X)
    StrictInterl (insertionRow w n) (insertionRow w (n + 1)) := by
  have hP : PowerSeries.constantCoeff (PowerSeries.exp ℝ - 1 - PowerSeries.X) = 0 := by simp
  have hrows (k : ℕ) :
      (insertionRow (affineBlockWeights PowerSeries.X PowerSeries.X) k).Splits := by
    rw [insertionRow_affine_X_X]
    simpa [add_comm] using (Polynomial.Splits.X_add_C (1 : ℝ)).pow k
  have hseed : Interl (insertionRow (affineBlockWeights PowerSeries.X PowerSeries.X) n)
      (insertionRow (affineBlockWeights PowerSeries.X PowerSeries.X) (n + 1)) := by
    rw [insertionRow_affine_X_X, insertionRow_affine_X_X]
    have h := strictInterl_self_X_sub_C_mul (pow_ne_zero n (by
      simpa only [C_1, add_comm] using Polynomial.X_add_C_ne_zero (1 : ℝ)))
      (by simpa only [insertionRow_affine_X_X] using hrows n) (-1)
    simpa [pow_succ, sub_eq_add_neg, mul_comm, add_comm] using h.toInterl
  have H := insertionRow_interl_subst (A := PowerSeries.X) (B := PowerSeries.X)
    (P := PowerSeries.exp ℝ - 1 - PowerSeries.X)
    (by simp) (by simp) hP thresholdTwo_ode le_rfl zero_le_one zero_le_one
    coeff_X_nonneg coeff_X_nonneg hrows hseed
  rw [PowerSeries.X_subst] at H
  exact H.toStrictInterl_of_ne (insertionRow_isRealRooted_threshold_two n).1
    (insertionRow_isRealRooted_threshold_two (n + 1)).1

end RealRooted.ExponentialRows
