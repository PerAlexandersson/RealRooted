module

import RealRooted.Derivative.Interlacing
import RealRooted.DerivativeRecurrence.SecondOrderDegree
import RealRooted.DerivativeRecurrence.QuadraticLagStrict
public import RealRooted.LiuWang.FiniteFamily
public import RealRooted.SimpleRoots
public import RealRooted.WagnerRightSum
import RealRooted.WagnerRightSum.Sign
import RealRooted.Derivative.Algebra
import RealRooted.Linear

/-!
# Interlacing for affine-lagged second-order derivative recurrences

Coefficient positivity, strict root negativity, and interlacing for the
second-order recurrence shared by several OEIS polynomial families.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

variable {P : ℕ → ℝ[X]} {a c : ℝ}

/-- Every polynomial in the recurrence has constant coefficient one. -/
theorem coeff_zero_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) :
    ∀ n : ℕ, coeff (P n) 0 = 1
  | 0 => by rw [h0]; simp
  | 1 => by rw [h1]; simp
  | n + 2 => by
      have ih := coeff_zero_affine_lag_second_order_derivative h0 h1 hrec (n + 1)
      rw [hrec n]
      rw [show (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative =
          C a * (X * (P (n + 1)).derivative) +
            C (-a) * (X ^ 2 * (P (n + 1)).derivative) by ring]
      rw [show (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) =
          P (n + 1) + C ((a + 1) + a * (n : ℝ)) * (X * P (n + 1)) by
            rw [map_one]
            ring]
      rw [show (C c * X) * P n = C c * (X * P n) by ring]
      simp only [coeff_add, coeff_C_mul]
      norm_num
      exact ih

private theorem nonneg_coeffs_affine_lag_second_order_derivative_aux
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n)
    (habove : ∀ n k, n < k → coeff (P n) k = 0) :
    ∀ n k, 0 ≤ coeff (P n) k
  | 0, k => by
      rw [h0, coeff_one]
      split_ifs <;> norm_num
  | 1, k => by
      rw [h1, coeff_add, coeff_one, coeff_X]
      split_ifs <;> norm_num
  | n + 2, k => by
      have hnn1 := nonneg_coeffs_affine_lag_second_order_derivative_aux
        ha hc h0 h1 hrec habove (n + 1)
      have hnn0 := nonneg_coeffs_affine_lag_second_order_derivative_aux
        ha hc h0 h1 hrec habove n
      have hcoeff : ∀ j : ℕ, coeff (P (n + 2)) (j + 1) =
          (a * ((j : ℝ) + 1) + 1) * coeff (P (n + 1)) (j + 1) +
            (((a + 1) + a * (n : ℝ)) - a * (j : ℝ)) * coeff (P (n + 1)) j +
              c * coeff (P n) j := fun j =>
        second_order_derivative_coeff_succ_succ P a c
          (fun m => (a + 1) + a * (m : ℝ)) hrec n j
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [coeff_zero_affine_lag_second_order_derivative h0 h1 hrec (n + 2)]
        norm_num
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
        rw [hcoeff j]
        have hfirst :
            0 ≤ (a * ((j : ℝ) + 1) + 1) * coeff (P (n + 1)) (j + 1) :=
          mul_nonneg (by positivity) (hnn1 (j + 1))
        have hlast : 0 ≤ c * coeff (P n) j := mul_nonneg hc (hnn0 j)
        have hmiddle :
            0 ≤ (((a + 1) + a * (n : ℝ)) - a * (j : ℝ)) *
              coeff (P (n + 1)) j := by
          by_cases hj : n + 1 < j
          · rw [habove (n + 1) j hj]
            simp
          · have hjle : (j : ℝ) ≤ (n : ℝ) + 1 := by
              exact_mod_cast (by lia : j ≤ n + 1)
            exact mul_nonneg (by nlinarith) (hnn1 j)
        linarith

private theorem top_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) (n : ℕ) :
    0 < coeff (P n) n ∧ ∀ m > n, coeff (P n) m = 0 :=
  second_order_derivative_top_and_above P a c
    (fun m => (a + 1) + a * (m : ℝ)) h0 h1 hrec (by intro m; ring) n

/-- Every polynomial in the recurrence has nonnegative coefficients when both
the derivative and lag parameters are nonnegative. -/
theorem hasNonnegCoeffs_of_affine_lag_second_order_derivative_of_nonneg_lag
    (P : ℕ → ℝ[X]) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) :
    ∀ n, HasNonnegCoeffs (P n) := fun n =>
  nonneg_coeffs_affine_lag_second_order_derivative_aux ha hc h0 h1 hrec
    (fun m k hmk => (top_affine_lag_second_order_derivative h0 h1 hrec m).2 k hmk) n

private theorem natDegree_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) (n : ℕ) :
    (P n).natDegree = n :=
  natDegree_of_second_order_derivative P a c
    (fun m => (a + 1) + a * (m : ℝ)) h0 h1 hrec (by intro m; ring) n

private theorem pos_leading_affine_lag_second_order_derivative
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) (n : ℕ) :
    HasPosLeadingCoeff (P n) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff, natDegree_affine_lag_second_order_derivative h0 h1 hrec n]
  exact (top_affine_lag_second_order_derivative h0 h1 hrec n).1

/-- Every real root is strictly negative for a positive derivative parameter
and an independent nonnegative lag. -/
theorem root_neg_affine_lag_second_order_derivative_of_nonneg_lag
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) (n : ℕ) {r : ℝ} (hr : (P n).IsRoot r) :
    r < 0 := by
  have hpos := pos_leading_affine_lag_second_order_derivative h0 h1 hrec n
  have hnonneg : HasNonnegCoeffs (P n) :=
    hasNonnegCoeffs_of_affine_lag_second_order_derivative_of_nonneg_lag
      P a c ha hc h0 h1 hrec n
  have hmem : r ∈ (P n).roots := by
    rw [mem_roots hpos.ne_zero]
    exact hr
  have hle : r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hnonneg r hmem
  rcases lt_or_eq_of_le hle with hlt | rfl
  · exact hlt
  · exfalso
    have heval : eval 0 (P n) = 1 := by
      rw [← coeff_zero_eq_eval_zero,
        coeff_zero_affine_lag_second_order_derivative h0 h1 hrec]
    rw [Polynomial.IsRoot.def, heval] at hr
    norm_num at hr

/-- Adjacent members of an affine-lagged second-order derivative recurrence
with an independent nonnegative lag strictly interlace and have no common
real root.  This is the case `b = a` of
`strictInterl_and_noCommonRoot_of_quadratic_lag`. -/
theorem strictInterl_and_noCommonRoot_of_affine_lag_second_order_derivative_of_nonneg_lag
    (P : ℕ → ℝ[X]) (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) :
    ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r :=
  strictInterl_and_noCommonRoot_of_quadratic_lag P a a c
    (fun n ↦ C 1 + C ((a + 1) + a * (n : ℝ)) * X) ha ha.le hc
    (natDegree_affine_lag_second_order_derivative h0 h1 hrec)
    (pos_leading_affine_lag_second_order_derivative h0 h1 hrec)
    (fun n _ hr ↦ root_neg_affine_lag_second_order_derivative_of_nonneg_lag
      ha.le hc h0 h1 hrec n hr)
    (by
      rw [h0]
      exact (interlaces_one_linear (by
        rw [natDegree_affine_lag_second_order_derivative h0 h1 hrec])).toStrictInterl)
    (fun r _ hr0 ↦ by
      rw [Polynomial.IsRoot.def, h0] at hr0
      simp at hr0)
    hrec

/-- The rankwise invariants supplied by the independent-lag recurrence
theorem. -/
structure AffineLagSecondOrderCertificate (P : ℕ → ℝ[X]) (n : ℕ) : Prop where
  nonnegCoeffs : HasNonnegCoeffs (P n)
  coeff_zero : coeff (P n) 0 = 1
  natDegree : (P n).natDegree = n
  posLeadingCoeff : HasPosLeadingCoeff (P n)
  roots_neg : ∀ r : ℝ, (P n).IsRoot r → r < 0
  interlaces_succ : Interlaces (P n) (P (n + 1))
  noCommonRoot_succ : ∀ r : ℝ, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r
  simpleRoots : HasSimpleRoots (P n)

/-- Consecutive members of a certified rankwise recurrence are in proper
position. -/
theorem AffineLagSecondOrderCertificate.strictInterl_succ {P : ℕ → ℝ[X]} {n : ℕ}
    (h : AffineLagSecondOrderCertificate P n) : StrictInterl (P n) (P (n + 1)) :=
  h.interlaces_succ.toStrictInterl

/-- The current member of a certified rankwise recurrence splits over the
reals. -/
theorem AffineLagSecondOrderCertificate.splits {P : ℕ → ℝ[X]} {n : ℕ}
    (h : AffineLagSecondOrderCertificate P n) : (P n).Splits :=
  h.strictInterl_succ.1.2

/-- The reusable rankwise package for an independent nonnegative lag. -/
theorem affine_lag_second_order_derivative_certificate_of_nonneg_lag
    (P : ℕ → ℝ[X]) (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) :
    ∀ n, AffineLagSecondOrderCertificate P n := by
  intro n
  have hpair :=
    strictInterl_and_noCommonRoot_of_affine_lag_second_order_derivative_of_nonneg_lag
      P a c ha hc h0 h1 hrec n
  have hinter : Interlaces (P n) (P (n + 1)) :=
    hpair.1.toInterlaces (by
      rw [natDegree_affine_lag_second_order_derivative h0 h1 hrec,
        natDegree_affine_lag_second_order_derivative h0 h1 hrec])
  have hsimple : HasSimpleRoots (P n) :=
    (hpair.1.hasSimpleRoots_of_no_common_root fun r hr =>
      hpair.2 r hr.2 hr.1).1
  exact
    ⟨hasNonnegCoeffs_of_affine_lag_second_order_derivative_of_nonneg_lag
        P a c ha.le hc h0 h1 hrec n,
      coeff_zero_affine_lag_second_order_derivative h0 h1 hrec n,
      natDegree_affine_lag_second_order_derivative h0 h1 hrec n,
      pos_leading_affine_lag_second_order_derivative h0 h1 hrec n,
      fun _ hr => root_neg_affine_lag_second_order_derivative_of_nonneg_lag
        ha.le hc h0 h1 hrec n hr,
      hinter, hpair.2, hsimple⟩

/-- Reversed finite prefixes of an independent-lag family are Sturm
sequences. -/
theorem isSturmSeq_affine_lag_second_order_derivative_of_nonneg_lag
    (P : ℕ → ℝ[X]) (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (h0 : P 0 = 1) (h1 : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) =
      (C a * X + C (-a) * X ^ 2) * (P (n + 1)).derivative +
        (C 1 + C ((a + 1) + a * (n : ℝ)) * X) * P (n + 1) +
        (C c * X) * P n) (n : ℕ) :
    IsSturmSeq ((List.range (n + 1)).reverse.map P) := by
  induction n with
  | zero => simp [IsSturmSeq]
  | succ n ih =>
      have hinter := (affine_lag_second_order_derivative_certificate_of_nonneg_lag
        P a c ha hc h0 h1 hrec n).interlaces_succ
      simpa [IsSturmSeq, List.range_succ] using And.intro hinter ih

end RealRooted
