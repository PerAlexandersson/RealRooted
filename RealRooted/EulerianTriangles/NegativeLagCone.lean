module

public import RealRooted.RootLocation.Basic
public import RealRooted.Basic.Coefficients
import RealRooted.BernsteinCone.Preserver
import RealRooted.Mathlib.Algebra.Order.BigOperators.Alternating
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.BernsteinBasisTransform
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import RealRooted.Recurrence.Uniqueness
import RealRooted.RootLocation.CommonInterlacer
import RealRooted.Transforms.BrandenE.IntervalPreserver

/-!
# Negative-lag Euler recurrences

This module proves the Bernstein-cone theorem for the negative-lag recurrence
from RealRooted issue #2511.  The recurrence first collapses to a positive
one-step construction.  After dividing out the positive row scale, that
construction is Brändén's `E` transform of a polynomial whose Cayley
coefficients are nonnegative alternating sums.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The Euler operator `X + X (1 + X) d/dX` occurring in the negative-lag
recurrence. -/
def negativeLagEulerOperator (p : ℝ[X]) : ℝ[X] :=
  X * p + X * (1 + X) * p.derivative

/-- Polynomial rows of the negative-lag Euler recurrence. -/
def negativeLagEulerRow (r s : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => C (r 1) + C (s 1) * X
  | n + 2 =>
      C (r (n + 2)) * negativeLagEulerRow r s (n + 1) +
        C (s (n + 2)) * negativeLagEulerOperator (negativeLagEulerRow r s (n + 1)) -
          C (r (n + 2) * s (n + 1)) *
            negativeLagEulerOperator (negativeLagEulerRow r s n)

@[simp] theorem negativeLagEulerRow_zero (r s : ℕ → ℝ) :
    negativeLagEulerRow r s 0 = 1 := rfl

@[simp] theorem negativeLagEulerRow_one (r s : ℕ → ℝ) :
    negativeLagEulerRow r s 1 = C (r 1) + C (s 1) * X := rfl

theorem negativeLagEulerRow_succ_succ (r s : ℕ → ℝ) (n : ℕ) :
    negativeLagEulerRow r s (n + 2) =
      C (r (n + 2)) * negativeLagEulerRow r s (n + 1) +
        C (s (n + 2)) * negativeLagEulerOperator (negativeLagEulerRow r s (n + 1)) -
          C (r (n + 2) * s (n + 1)) *
            negativeLagEulerOperator (negativeLagEulerRow r s n) := rfl

/-- Any polynomial sequence with the two seeds and the negative-lag
recurrence is the canonical recursive sequence. -/
theorem eq_negativeLagEulerRow_of_recurrence (Q : ℕ → ℝ[X]) (r s : ℕ → ℝ)
    (hzero : Q 0 = 1)
    (hone : Q 1 = C (r 1) + C (s 1) * X)
    (hrec : ∀ n, Q (n + 2) =
      C (r (n + 2)) * Q (n + 1) +
        C (s (n + 2)) * negativeLagEulerOperator (Q (n + 1)) -
          C (r (n + 2) * s (n + 1)) * negativeLagEulerOperator (Q n)) :
    ∀ n, Q n = negativeLagEulerRow r s n := by
  exact sequence_eq_of_same_lag_two_recurrence
    (fun n p q ↦
      C (r (n + 2)) * p + C (s (n + 2)) * negativeLagEulerOperator p -
        C (r (n + 2) * s (n + 1)) * negativeLagEulerOperator q)
    hzero hone hrec (negativeLagEulerRow_succ_succ r s)

private def negativeLagProduct (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, a (i + 1)

private def negativeLagRatioProduct (r s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, r (i + 1) / s (i + 1)

private def negativeLagInput (r s : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (negativeLagRatioProduct r s k) * X ^ (n - k)

private lemma negativeLagEulerOperator_C_mul (a : ℝ) (p : ℝ[X]) :
    negativeLagEulerOperator (C a * p) = C a * negativeLagEulerOperator p := by
  simp [negativeLagEulerOperator, Polynomial.derivative_mul]
  ring

private theorem negativeLagEulerRow_succ (r s : ℕ → ℝ) : ∀ n,
    negativeLagEulerRow r s (n + 1) =
      C (s (n + 1)) * negativeLagEulerOperator (negativeLagEulerRow r s n) +
        C (negativeLagProduct r (n + 1)) := by
  intro n
  induction n with
  | zero =>
      simp [negativeLagEulerOperator, negativeLagProduct]
      ring
  | succ n ih =>
      rw [negativeLagEulerRow_succ_succ, ih]
      simp only [map_mul]
      simp [negativeLagProduct, Finset.prod_range_succ]
      ring

private theorem negativeLagProduct_mul_ratioProduct (r s : ℕ → ℝ)
    (hs : ∀ n, 1 ≤ n → 0 < s n) (n : ℕ) :
    negativeLagProduct s n * negativeLagRatioProduct r s n =
      negativeLagProduct r n := by
  rw [negativeLagProduct, negativeLagRatioProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hsi : s (i + 1) ≠ 0 := (hs (i + 1) (by lia)).ne'
  simpa only [mul_comm] using div_mul_cancel₀ (r (i + 1)) hsi

private theorem negativeLagRatioProduct_succ (r s : ℕ → ℝ) (n : ℕ) :
    negativeLagRatioProduct r s (n + 1) =
      negativeLagRatioProduct r s n * (r (n + 1) / s (n + 1)) := by
  unfold negativeLagRatioProduct
  rw [Finset.prod_range_succ]

private theorem coeff_negativeLagInput (r s : ℕ → ℝ) (n j : ℕ) :
    (negativeLagInput r s n).coeff j =
      if j ≤ n then negativeLagRatioProduct r s (n - j) else 0 := by
  rw [negativeLagInput, Polynomial.coeff_sum_range_C_mul_X_pow_sub]

private theorem negativeLagInput_succ (r s : ℕ → ℝ) (n : ℕ) :
    negativeLagInput r s (n + 1) =
      X * negativeLagInput r s n + C (negativeLagRatioProduct r s (n + 1)) := by
  apply Polynomial.ext
  intro j
  rw [coeff_negativeLagInput, Polynomial.coeff_add]
  by_cases hj : j = 0
  · subst j
    simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [Polynomial.coeff_X_mul, coeff_negativeLagInput]
    simp only [coeff_C, Nat.succ_ne_zero, ite_false, add_zero]
    by_cases h : j ≤ n
    · have hsucc : j.succ ≤ n + 1 := by lia
      simp only [hsucc, h, ite_true]
      congr 1
      lia
    · have hsucc : ¬j.succ ≤ n + 1 := by lia
      simp only [hsucc, h, ite_false]

private theorem negativeLagInput_degree_pos (r s : ℕ → ℝ) (n : ℕ) :
    (negativeLagInput r s n).natDegree = n ∧
      HasPosLeadingCoeff (negativeLagInput r s n) := by
  have hle : (negativeLagInput r s n).natDegree ≤ n := by
    exact Polynomial.natDegree_sum_range_C_mul_X_pow_sub_le _ _
  have hcoeff : (negativeLagInput r s n).coeff n = 1 := by
    rw [negativeLagInput, Polynomial.coeff_sum_range_C_mul_X_pow_sub]
    simp [negativeLagRatioProduct]
  have hdeg : (negativeLagInput r s n).natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcoeff])
  refine ⟨hdeg, ?_⟩
  rw [HasPosLeadingCoeff, leadingCoeff, hdeg, hcoeff]
  norm_num

private theorem negativeLagRatioProduct_nonneg (r s : ℕ → ℝ)
    (hr : ∀ n, 1 ≤ n → 0 ≤ r n) (hs : ∀ n, 1 ≤ n → 0 < s n) (n : ℕ) :
    0 ≤ negativeLagRatioProduct r s n := by
  apply Finset.prod_nonneg
  intro i hi
  exact div_nonneg (hr (i + 1) (by lia)) (hs (i + 1) (by lia)).le

private theorem negativeLagRatioProduct_scaled_succ_le (r s : ℕ → ℝ)
    (hr : ∀ n, 1 ≤ n → 0 ≤ r n) (hs : ∀ n, 1 ≤ n → 0 < s n)
    (hrs : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * r n ≤ s n) (n : ℕ) :
    (n + 1 : ℕ) * negativeLagRatioProduct r s (n + 1) ≤
      negativeLagRatioProduct r s n := by
  rw [negativeLagRatioProduct_succ]
  have hs' := hs (n + 1) (by lia)
  have hratio : ((n : ℝ) + 1) * (r (n + 1) / s (n + 1)) ≤ 1 := by
    rw [show ((n : ℝ) + 1) * (r (n + 1) / s (n + 1)) =
      (((n : ℝ) + 1) * r (n + 1)) / s (n + 1) by ring, div_le_one hs']
    simpa using hrs (n + 1) (by lia)
  have hnonneg := negativeLagRatioProduct_nonneg r s hr hs n
  push_cast
  nlinarith

private theorem coeff_cayleyTransform_negativeLagInput (r s : ℕ → ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    (Polynomial.cayleyTransform n (negativeLagInput r s n)).coeff k =
      ∑ l ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ l * (Nat.choose (n - k + l) l : ℝ) *
          negativeLagRatioProduct r s (n - k + l) := by
  have hdeg : (negativeLagInput r s n).natDegree ≤ n :=
    (negativeLagInput_degree_pos r s n).1.le
  rw [Polynomial.cayleyTransform_eq_sum hdeg, Polynomial.finsetSum_coeff]
  have hrestrict :
      ∑ j ∈ Finset.range (n + 1),
          (C ((negativeLagInput r s n).coeff j) * X ^ j * (1 - X) ^ (n - j)).coeff k =
        ∑ j ∈ Finset.range (k + 1),
          (C ((negativeLagInput r s n).coeff j) * X ^ j * (1 - X) ^ (n - j)).coeff k := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      lia
    · intro j hjn hjk
      rw [show C ((negativeLagInput r s n).coeff j) * X ^ j * (1 - X) ^ (n - j) =
          C ((negativeLagInput r s n).coeff j) * (X ^ j * (1 - X) ^ (n - j)) by ring,
        coeff_C_mul, coeff_X_pow_mul']
      have hnot : ¬j ≤ k := fun hjle ↦ hjk (Finset.mem_range.mpr (by lia))
      simp only [hnot, ite_false, mul_zero]
  rw [hrestrict]
  have href :
      ∑ j ∈ Finset.range (k + 1),
          (C ((negativeLagInput r s n).coeff j) * X ^ j * (1 - X) ^ (n - j)).coeff k =
        ∑ l ∈ Finset.range (k + 1),
          (C ((negativeLagInput r s n).coeff (k - l)) * X ^ (k - l) *
            (1 - X) ^ (n - (k - l))).coeff k := by
    let f := fun j ↦ (C ((negativeLagInput r s n).coeff j) * X ^ j *
      (1 - X) ^ (n - j)).coeff k
    calc
      ∑ j ∈ Finset.range (k + 1), f j =
          ∑ l ∈ Finset.range (k + 1), f (k + 1 - 1 - l) :=
        (Finset.sum_range_reflect f (k + 1)).symm
      _ = ∑ l ∈ Finset.range (k + 1), f (k - l) := by
        apply Finset.sum_congr rfl
        intro l hl
        congr 1
  rw [href]
  apply Finset.sum_congr rfl
  intro l hl
  have hlk : l ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
  rw [show C ((negativeLagInput r s n).coeff (k - l)) * X ^ (k - l) *
      (1 - X) ^ (n - (k - l)) =
        C ((negativeLagInput r s n).coeff (k - l)) *
          (X ^ (k - l) * (1 - X) ^ (n - (k - l))) by ring,
    coeff_C_mul, coeff_X_pow_mul']
  simp only [show k - l ≤ k by lia, ite_true]
  rw [Polynomial.coeff_one_sub_X_pow, coeff_negativeLagInput]
  simp only [show k - l ≤ n by lia, ite_true]
  have h₁ : k - (k - l) = l := by lia
  have h₂ : n - (k - l) = n - k + l := by lia
  rw [h₁, h₂]
  ring

private theorem hasNonnegCoeffs_cayleyTransform_negativeLagInput (r s : ℕ → ℝ)
    (hr : ∀ n, 1 ≤ n → 0 ≤ r n) (hs : ∀ n, 1 ≤ n → 0 < s n)
    (hrs : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * r n ≤ s n) (n : ℕ) :
    HasNonnegCoeffs (Polynomial.cayleyTransform n (negativeLagInput r s n)) := by
  intro k
  by_cases hk : k ≤ n
  · rw [coeff_cayleyTransform_negativeLagInput r s n k hk]
    simpa only [mul_assoc] using Finset.alternating_sum_range_nonneg (k + 1)
      (fun l ↦ (Nat.choose (n - k + l) l : ℝ) *
        negativeLagRatioProduct r s (n - k + l)) (by
      intro l
      let a := n - k
      have hscaled := negativeLagRatioProduct_scaled_succ_le r s hr hs hrs (a + l)
      have hchoose :
          ((l : ℝ) + 1) * (Nat.choose (a + l + 1) (l + 1) : ℝ) =
            ((a : ℝ) + l + 1) * (Nat.choose (a + l) l : ℝ) := by
        have hnat : Nat.choose (a + l + 1) (l + 1) * (l + 1) =
            Nat.choose (a + l) l * (a + l + 1) :=
          (Nat.choose_succ_right_eq (a + l + 1) l).trans
            (Nat.choose_mul_succ_eq (a + l) l).symm
        have hnatR : (Nat.choose (a + l + 1) (l + 1) : ℝ) * (l + 1) =
            (Nat.choose (a + l) l : ℝ) * (a + l + 1) := by
          exact_mod_cast hnat
        linear_combination hnatR
      have hnext := negativeLagRatioProduct_nonneg r s hr hs (a + l + 1)
      have hchoose_nonneg : 0 ≤ (Nat.choose (a + l) l : ℝ) := by positivity
      dsimp [a] at hscaled hchoose hnext ⊢
      push_cast at hscaled hchoose ⊢
      have hscaledmul := mul_le_mul_of_nonneg_left hscaled hchoose_nonneg
      have hnextTerm : 0 ≤ (Nat.choose (n - k + l + 1) (l + 1) : ℝ) *
          negativeLagRatioProduct r s (n - k + l + 1) := mul_nonneg (by positivity) hnext
      have hlreal : 1 ≤ (l : ℝ) + 1 := by norm_num
      calc
        (Nat.choose (n - k + (l + 1)) (l + 1) : ℝ) *
              negativeLagRatioProduct r s (n - k + (l + 1)) ≤
            ((l : ℝ) + 1) *
              ((Nat.choose (n - k + l + 1) (l + 1) : ℝ) *
                negativeLagRatioProduct r s (n - k + l + 1)) := by
                  simpa only [Nat.add_assoc] using
                    le_mul_of_one_le_left hnextTerm hlreal
        _ = (Nat.choose (n - k + l) l : ℝ) *
              (((n - k : ℕ) : ℝ) + l + 1) *
                negativeLagRatioProduct r s (n - k + l + 1) := by
                  calc
                    ((l : ℝ) + 1) *
                        ((Nat.choose (n - k + l + 1) (l + 1) : ℝ) *
                          negativeLagRatioProduct r s (n - k + l + 1)) =
                      (((l : ℝ) + 1) *
                        (Nat.choose (n - k + l + 1) (l + 1) : ℝ)) *
                          negativeLagRatioProduct r s (n - k + l + 1) := by ring
                    _ = (((n - k : ℕ) : ℝ) + l + 1) *
                        (Nat.choose (n - k + l) l : ℝ) *
                          negativeLagRatioProduct r s (n - k + l + 1) := by rw [hchoose]
                    _ = _ := by ring
        _ ≤ (Nat.choose (n - k + l) l : ℝ) *
              negativeLagRatioProduct r s (n - k + l) := by
                simpa only [mul_assoc] using hscaledmul) (by
      intro l
      exact mul_nonneg (by positivity)
        (negativeLagRatioProduct_nonneg r s hr hs (n - k + l)))
  · have hdeg : (Polynomial.cayleyTransform n (negativeLagInput r s n)).natDegree ≤ n := by
      rw [Polynomial.cayleyTransform_eq_mobiusTransform]
      exact Polynomial.natDegree_mobiusTransform_le (n := n) (a := 1) (b := 0)
        (c := -1) (d := 1)
        (negativeLagInput_degree_pos r s n).1.le
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_not_ge hk))]

private def negativeLagClosedRow (r s : ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  C (negativeLagProduct s n) * brandenE (negativeLagInput r s n)

private theorem negativeLagClosedRow_succ (r s : ℕ → ℝ)
    (hs : ∀ n, 1 ≤ n → 0 < s n) (n : ℕ) :
    negativeLagClosedRow r s (n + 1) =
      C (s (n + 1)) * negativeLagEulerOperator (negativeLagClosedRow r s n) +
        C (negativeLagProduct r (n + 1)) := by
  change C (negativeLagProduct s (n + 1)) *
      brandenE (negativeLagInput r s (n + 1)) =
    C (s (n + 1)) * negativeLagEulerOperator
      (C (negativeLagProduct s n) * brandenE (negativeLagInput r s n)) +
        C (negativeLagProduct r (n + 1))
  rw [negativeLagInput_succ, brandenE_add, brandenE_X_mul,
    negativeLagEulerOperator_C_mul]
  have hconstant : brandenE (C (negativeLagRatioProduct r s (n + 1))) =
      C (negativeLagRatioProduct r s (n + 1)) := by
    rw [show C (negativeLagRatioProduct r s (n + 1)) =
      C (negativeLagRatioProduct r s (n + 1)) * (1 : ℝ[X]) by simp,
      brandenE_C_mul]
    change C (negativeLagRatioProduct r s (n + 1)) * brandenE (X ^ 0) = _
    rw [brandenE_X_pow]
    rfl
  rw [hconstant]
  have hprod := negativeLagProduct_mul_ratioProduct r s hs (n + 1)
  rw [negativeLagProduct, Finset.prod_range_succ] at hprod ⊢
  have hprodC := congrArg C hprod
  simp only [negativeLagProduct] at hprodC ⊢
  simp only [map_mul, negativeLagEulerOperator] at hprodC ⊢
  linear_combination hprodC

private theorem negativeLagEulerRow_eq_closed (r s : ℕ → ℝ)
    (hs : ∀ n, 1 ≤ n → 0 < s n) (n : ℕ) :
    negativeLagEulerRow r s n = negativeLagClosedRow r s n := by
  apply sequence_eq_of_same_lag_one_recurrence
    (fun n p ↦ C (s (n + 1)) * negativeLagEulerOperator p +
      C (negativeLagProduct r (n + 1)))
  · rw [negativeLagEulerRow_zero, negativeLagClosedRow]
    simp only [negativeLagProduct, negativeLagInput, negativeLagRatioProduct,
      Finset.range_zero, Finset.prod_empty,
      Finset.sum_range_succ, Finset.sum_empty, zero_add,
      Nat.zero_sub, pow_zero, C_1, one_mul]
    change (1 : ℝ[X]) = brandenE (X ^ 0 : ℝ[X])
    rw [brandenE_X_pow]
    rfl
  · exact negativeLagEulerRow_succ r s
  · exact negativeLagClosedRow_succ r s hs

private def negativeLagWeights (r s : ℕ → ℝ) (n : ℕ) : List (ℝ × ℝ[X]) :=
  let q := Polynomial.cayleyTransform n (negativeLagInput r s n)
  List.ofFn fun k : Fin (n + 1) ↦ (q.coeff k, brandenBasisImage n k)

private theorem negativeLagInput_eq_bernsteinExpansion (r s : ℕ → ℝ) (n : ℕ) :
    negativeLagInput r s n = Polynomial.bernsteinExpansion n
      (Polynomial.cayleyTransform n (negativeLagInput r s n)) := by
  let q := Polynomial.cayleyTransform n (negativeLagInput r s n)
  have hinput : (negativeLagInput r s n).natDegree ≤ n :=
    (negativeLagInput_degree_pos r s n).1.le
  have hq : q.natDegree ≤ n := by
    simp only [q]
    rw [Polynomial.cayleyTransform_eq_mobiusTransform]
    exact Polynomial.natDegree_mobiusTransform_le (n := n) (a := 1) (b := 0)
      (c := -1) (d := 1) hinput
  rw [Polynomial.bernsteinExpansion_eq_mobiusTransform hq]
  exact (Polynomial.mobiusTransform_one_zero_one_one_cayleyTransform
    (n := n) hinput).symm

private theorem weightedSum_negativeLagWeights (r s : ℕ → ℝ) (n : ℕ) :
    weightedSum (negativeLagWeights r s n) = brandenE (negativeLagInput r s n) := by
  let q := Polynomial.cayleyTransform n (negativeLagInput r s n)
  rw [negativeLagInput_eq_bernsteinExpansion r s n]
  change weightedSum (List.ofFn fun k : Fin (n + 1) ↦
      (q.coeff k, brandenBasisImage n k)) = brandenE (Polynomial.bernsteinExpansion n q)
  rw [weightedSum_ofFn]
  calc
    ∑ k : Fin (n + 1), C (q.coeff k) * brandenBasisImage n k =
        ∑ k ∈ Finset.range (n + 1), C (q.coeff k) * brandenBasisImage n k := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun k ↦ C (q.coeff k) * brandenBasisImage n k) (n + 1)
    _ = brandenE (Polynomial.bernsteinExpansion n q) := by
      simpa [brandenE, brandenBasisImage, brandenBinomialBasis, add_comm] using
        (Polynomial.basisTransform_bernsteinExpansion
          (orderedBellPolynomial (R := ℝ)) n q).symm

private theorem negativeLagProduct_pos (s : ℕ → ℝ)
    (hs : ∀ n, 1 ≤ n → 0 < s n) (n : ℕ) : 0 < negativeLagProduct s n := by
  apply Finset.prod_pos
  intro i hi
  exact hs (i + 1) (by lia)

private theorem brandenE_negativeLagInput_certificate (r s : ℕ → ℝ)
    (hr : ∀ n, 1 ≤ n → 0 ≤ r n) (hs : ∀ n, 1 ≤ n → 0 < s n)
    (hrs : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * r n ≤ s n) (n : ℕ) :
    (brandenE (negativeLagInput r s n)).natDegree = n ∧
      HasPosLeadingCoeff (brandenE (negativeLagInput r s n)) ∧
        IsRealRootedIn (Set.Icc (-1) 0) (brandenE (negativeLagInput r s n)) := by
  let q := Polynomial.cayleyTransform n (negativeLagInput r s n)
  let ws := negativeLagWeights r s n
  have hqnonneg : HasNonnegCoeffs q :=
    hasNonnegCoeffs_cayleyTransform_negativeLagInput r s hr hs hrs n
  have hinput : (negativeLagInput r s n).natDegree ≤ n :=
    (negativeLagInput_degree_pos r s n).1.le
  have hqdeg : q.natDegree ≤ n := by
    simp only [q]
    rw [Polynomial.cayleyTransform_eq_mobiusTransform]
    exact Polynomial.natDegree_mobiusTransform_le (n := n) (a := 1) (b := 0)
      (c := -1) (d := 1) hinput
  have hqne : q ≠ 0 := by
    simp only [q]
    rw [Polynomial.cayleyTransform_eq_mobiusTransform]
    exact Polynomial.mobiusTransform_ne_zero
      (n := n) (a := 1) (b := 0) (c := -1) (d := 1)
      (negativeLagInput_degree_pos r s n).2.ne_zero hinput (by norm_num)
  have hweights : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws] at hap
    rw [negativeLagWeights, List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    exact hqnonneg k
  have hdeg : ∀ ap ∈ ws, ap.2.natDegree = n := by
    intro ap hap
    simp only [ws] at hap
    rw [negativeLagWeights, List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    exact (brandenBasisImage_degree_pos n k (by lia)).1
  have hpos : ∀ ap ∈ ws, HasPosLeadingCoeff ap.2 := by
    intro ap hap
    simp only [ws] at hap
    rw [negativeLagWeights, List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    exact (brandenBasisImage_degree_pos n k (by lia)).2
  have hroot : ∀ ap ∈ ws, IsRealRootedIn (Set.Icc (-1) 0) ap.2 := by
    intro ap hap
    simp only [ws] at hap
    rw [negativeLagWeights, List.mem_ofFn] at hap
    rcases hap with ⟨k, rfl⟩
    have hk : k.val ≤ n := by lia
    exact ⟨(brandenBasisImage_degree_pos n k hk).2.ne_zero,
      brandenBasisImage_splits n k hk, fun x hx ↦
        ⟨brandenBasisImage_roots_ge_neg_one n k hk x hx,
          brandenBasisImage_roots_nonpos n k x hx⟩⟩
  have hex : ∃ ap ∈ ws, 0 < ap.1 := by
    let k : Fin (n + 1) := ⟨q.natDegree, by lia⟩
    refine ⟨(q.coeff k, brandenBasisImage n k), ?_, ?_⟩
    · simp only [ws]
      rw [negativeLagWeights, List.mem_ofFn]
      exact ⟨k, rfl⟩
    · change 0 < q.leadingCoeff
      exact hqnonneg.pos_leadingCoeff hqne
  have hsum := weightedSum_negativeLagWeights r s n
  have hpf : IsPFPolynomial (brandenE (negativeLagInput r s n)) := by
    rw [negativeLagInput_eq_bernsteinExpansion r s n]
    change IsPFPolynomial (Polynomial.basisTransform (orderedBellPolynomial (R := ℝ))
      (Polynomial.bernsteinExpansion n q))
    have hrow : IsInterlacingSeqNonneg
        (bernsteinBasisImageRow (orderedBellPolynomial (R := ℝ)) n) := by
      rw [← brandenBasisImageRow_eq_bernsteinBasisImageRow]
      exact brandenBasisImageRow_isInterlacingSeqNonneg n
    exact hrow.basisTransform_bernsteinExpansion_isPF hqnonneg
  have hsumdeg := natDegree_weightedSum_eq_of_nonneg_of_sameDegree hweights hdeg hpos hex
  have hsumpos := hasPosLeadingCoeff_weightedSum ws hweights hpos hex
  have hsumroot := isRealRootedIn_weightedSum_of_splits Set.ordConnected_Icc
    hroot hdeg hpos hweights hex (hsum.symm ▸ hpf.splits)
  rw [hsum] at hsumdeg hsumpos hsumroot
  exact ⟨hsumdeg, hsumpos, hsumroot⟩

/-- Theorem A: under the sharp ratio bound, every negative-lag Euler row has
its index as degree, positive leading coefficient, and all roots in
`[-1, 0]`. -/
theorem negativeLagEulerRow_degree_pos_rooted
    (r s : ℕ → ℝ)
    (hr : ∀ n, 1 ≤ n → 0 ≤ r n) (hs : ∀ n, 1 ≤ n → 0 < s n)
    (hrs : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * r n ≤ s n) (n : ℕ) :
    (negativeLagEulerRow r s n).natDegree = n ∧
      HasPosLeadingCoeff (negativeLagEulerRow r s n) ∧
        IsRealRootedIn (Set.Icc (-1) 0) (negativeLagEulerRow r s n) := by
  have hcore := brandenE_negativeLagInput_certificate r s hr hs hrs n
  have hscale := negativeLagProduct_pos s hs n
  rw [negativeLagEulerRow_eq_closed r s hs n, negativeLagClosedRow]
  refine ⟨?_, hasPosLeadingCoeff_C_mul hscale hcore.2.1,
    IsRealRootedIn.C_mul hscale.ne' hcore.2.2⟩
  rw [Polynomial.natDegree_C_mul hscale.ne', hcore.1]

/-- The A371898 specialization of the negative-lag Euler rows. -/
abbrev a371898Row : ℕ → ℝ[X] :=
  negativeLagEulerRow (fun _ ↦ 1) (fun n ↦ n)

theorem a371898Row_degree_pos_rooted (n : ℕ) :
    (a371898Row n).natDegree = n ∧ HasPosLeadingCoeff (a371898Row n) ∧
      IsRealRootedIn (Set.Icc (-1) 0) (a371898Row n) := by
  apply negativeLagEulerRow_degree_pos_rooted
  · intro k hk
    norm_num
  · intro k hk
    positivity
  · intro k hk
    norm_num

end RealRooted
