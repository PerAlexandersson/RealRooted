import RealRooted.DerivativeRecurrence.LagWeak
import RealRooted.EulerOperator
import RealRooted.FiniteFreeRootCount
import RealRooted.Hadamard
import RealRooted.Interlacing.ReversalCommonFactor
import RealRooted.LinearPowerFamily
import RealRooted.NarayanaTransformation
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
import RealRooted.ReciprocalShift.ProperPosition

/-!
# The A079508 reflected Schur--Szego model

The original rows carry parity-dependent powers of `X`; removing them gives a
strictly interlacing reflected model.
-/

open RealRooted Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A079508

/-- The downstream lag-three update for A079508. -/
def nextRow (n : ℕ) (p q r : ℝ[X]) : ℝ[X] :=
  (C ((1 / (3 + (1 / 2) * (n : ℝ))) * (-3 + (-1 / 2) * n)) +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((9 / 2) + n)) * X) * p +
    (C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((21 / 2) + 3 * n)) * X +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + (-1 / 2) * n)) *
        X ^ 2) * q +
    (C ((1 / (3 + (1 / 2) * (n : ℝ))) * (6 + 2 * n)) * X +
      C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + (-1 / 2) * n)) *
        X ^ 2) * r

/-- The recurrence presentation of A079508 used for its model identification. -/
def recurrencePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | 2 => 2 * X + X ^ 2
  | n + 3 => nextRow n (recurrencePolynomial (n + 2))
      (recurrencePolynomial (n + 1)) (recurrencePolynomial n)

private theorem A079508_denom_pos (n : ℕ) : (0 : ℝ) < 3 + (1 / 2) * (n : ℝ) := by
  positivity

private def recurrencePolynomialα (n : ℕ) : ℝ :=
  (1 / (3 + (1 / 2) * (n : ℝ))) * ((9 / 2) + (n : ℝ))

private def recurrencePolynomialβ (n : ℕ) : ℝ :=
  (1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + (-1 / 2) * (n : ℝ))

private theorem recurrencePolynomialα_pos (n : ℕ) : 0 < recurrencePolynomialα n := by
  unfold recurrencePolynomialα; have := A079508_denom_pos n; positivity

private theorem recurrencePolynomialβ_neg (n : ℕ) : recurrencePolynomialβ n < 0 := by
  unfold recurrencePolynomialβ
  exact mul_neg_of_pos_of_neg (by have := A079508_denom_pos n; positivity) (by grind)

private theorem recurrencePolynomialαβ (n : ℕ) :
    recurrencePolynomialα n + recurrencePolynomialβ n = 1 := by
  unfold recurrencePolynomialα recurrencePolynomialβ
  grind

private def A079508c1 (n : ℕ) : ℝ[X] :=
  C ((1 / (3 + (1 / 2) * (n : ℝ))) * (-3 + (-1 / 2) * (n : ℝ))) +
    C (recurrencePolynomialα n) * X

private def A079508c2 (n : ℕ) : ℝ[X] :=
  C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((21 / 2) + 3 * (n : ℝ))) * X +
    C (recurrencePolynomialβ n) * X ^ 2

private def A079508c3 (n : ℕ) : ℝ[X] :=
  C ((1 / (3 + (1 / 2) * (n : ℝ))) * (6 + (2 * (n : ℝ)))) * X
    + C ((1 / (3 + (1 / 2) * (n : ℝ))) * ((-3 / 2) + ((-1 / 2) * (n : ℝ)))) * X ^ 2

private theorem A079508_rec (n : ℕ) :
    recurrencePolynomial (n + 3) =
      A079508c1 n * recurrencePolynomial (n + 2) +
        A079508c2 n * recurrencePolynomial (n + 1) +
          A079508c3 n * recurrencePolynomial n := by
  unfold A079508c1 A079508c2 A079508c3 recurrencePolynomialα recurrencePolynomialβ
  rfl

private theorem recurrencePolynomial_recurrence (n : ℕ) :
    recurrencePolynomial (n + 3) =
      nextRow n (recurrencePolynomial (n + 2))
        (recurrencePolynomial (n + 1)) (recurrencePolynomial n) := by
  rw [nextRow]
  exact A079508_rec n

private theorem A079508_c1_natDegree (n : ℕ) : (A079508c1 n).natDegree = 1 := by
  unfold A079508c1
  rw [natDegree_add_eq_right_of_natDegree_lt]
  · rw [natDegree_C_mul (ne_of_gt (recurrencePolynomialα_pos n)), natDegree_X]
  · rw [natDegree_C_mul (ne_of_gt (recurrencePolynomialα_pos n)), natDegree_X, natDegree_C]
    norm_num

private theorem A079508_c1_leadingCoeff (n : ℕ) :
    (A079508c1 n).leadingCoeff = recurrencePolynomialα n := by
  rw [leadingCoeff, A079508_c1_natDegree]
  unfold A079508c1
  simp

private theorem A079508_c2_natDegree (n : ℕ) : (A079508c2 n).natDegree = 2 := by
  unfold A079508c2
  rw [natDegree_add_eq_right_of_natDegree_lt]
  · rw [natDegree_C_mul (ne_of_lt (recurrencePolynomialβ_neg n))]
    simp
  · rw [natDegree_C_mul (ne_of_lt (recurrencePolynomialβ_neg n)), natDegree_X_pow]
    grind

private theorem A079508_c2_leadingCoeff (n : ℕ) :
    (A079508c2 n).leadingCoeff = recurrencePolynomialβ n := by
  rw [leadingCoeff, A079508_c2_natDegree]
  unfold A079508c2
  simp

private theorem A079508_c3_natDegree_le (n : ℕ) : (A079508c3 n).natDegree ≤ 2 := by
  unfold A079508c3
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · grind
  · grind

private theorem A079508_c1_ne (n : ℕ) : A079508c1 n ≠ 0 :=
  leadingCoeff_ne_zero.mp (by
    rw [A079508_c1_leadingCoeff]
    exact ne_of_gt (recurrencePolynomialα_pos n))

private theorem A079508_c2_ne (n : ℕ) : A079508c2 n ≠ 0 :=
  leadingCoeff_ne_zero.mp (by
    rw [A079508_c2_leadingCoeff]
    exact ne_of_lt (recurrencePolynomialβ_neg n))

private theorem A079508_key (n : ℕ) :
    (recurrencePolynomial n).natDegree = n ∧ (recurrencePolynomial n).leadingCoeff = 1 := by
  have main : ∀ m : ℕ,
      ((recurrencePolynomial m).natDegree = m ∧ (recurrencePolynomial m).leadingCoeff = 1) ∧
      ((recurrencePolynomial (m + 1)).natDegree = m + 1 ∧
        (recurrencePolynomial (m + 1)).leadingCoeff = 1) ∧
      ((recurrencePolynomial (m + 2)).natDegree = m + 2 ∧
        (recurrencePolynomial (m + 2)).leadingCoeff = 1) := by
    intro m
    induction m with
    | zero =>
        refine ⟨⟨by simp [recurrencePolynomial], by simp [recurrencePolynomial]⟩,
          ⟨by simp [recurrencePolynomial], by simp [recurrencePolynomial]⟩, ⟨?_, ?_⟩⟩
        · change (2 * X + X ^ 2 : ℝ[X]).natDegree = 2
          compute_degree!
        · change (2 * X + X ^ 2 : ℝ[X]).leadingCoeff = 1
          rw [leadingCoeff, show (2 * X + X ^ 2 : ℝ[X]).natDegree = 2 from by compute_degree!]
          simp only [coeff_add, coeff_ofNat_mul, coeff_X_pow, coeff_X]
          norm_num
    | succ k ih =>
        obtain ⟨hk, hk1, hk2⟩ := ih
        refine ⟨hk1, hk2, ?_⟩
        have hk_ne : recurrencePolynomial k ≠ 0 := leadingCoeff_ne_zero.mp (by simp_all)
        have hk1_ne : recurrencePolynomial (k + 1) ≠ 0 := leadingCoeff_ne_zero.mp (by simp_all)
        have hk2_ne : recurrencePolynomial (k + 2) ≠ 0 := leadingCoeff_ne_zero.mp (by simp_all)
        have hd1 : (A079508c1 k * recurrencePolynomial (k + 2)).natDegree = k + 3 := by
          rw [natDegree_mul (A079508_c1_ne k) hk2_ne, A079508_c1_natDegree, hk2.1]
          lia
        have hd2 : (A079508c2 k * recurrencePolynomial (k + 1)).natDegree = k + 3 := by
          rw [natDegree_mul (A079508_c2_ne k) hk1_ne, A079508_c2_natDegree, hk1.1]
          lia
        have hd3 : (A079508c3 k * recurrencePolynomial k).natDegree ≤ k + 2 := by
          refine le_trans (natDegree_mul_le) ?_
          rw [hk.1]
          have := A079508_c3_natDegree_le k
          lia
        have hc1 :
            (A079508c1 k * recurrencePolynomial (k + 2)).coeff (k + 3) =
              recurrencePolynomialα k * 1 := by
          have := coeff_mul_degree_add_degree (A079508c1 k) (recurrencePolynomial (k + 2))
          rw [A079508_c1_natDegree, hk2.1, show 1 + (k + 2) = k + 3 from by lia] at this
          rw [this, A079508_c1_leadingCoeff, hk2.2]
        have hc2 :
            (A079508c2 k * recurrencePolynomial (k + 1)).coeff (k + 3) =
              recurrencePolynomialβ k * 1 := by
          have := coeff_mul_degree_add_degree (A079508c2 k) (recurrencePolynomial (k + 1))
          rw [A079508_c2_natDegree, hk1.1, show 2 + (k + 1) = k + 3 from by lia] at this
          rw [this, A079508_c2_leadingCoeff, hk1.2]
        have hc3 : (A079508c3 k * recurrencePolynomial k).coeff (k + 3) = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd3 (by lia))
        have hcoeff_top : (recurrencePolynomial (k + 3)).coeff (k + 3) = 1 := by
          rw [A079508_rec, coeff_add, coeff_add, hc1, hc2, hc3, mul_one, mul_one, add_zero,
              recurrencePolynomialαβ]
        have hcoeff_ne : (recurrencePolynomial (k + 3)).coeff (k + 3) ≠ 0 := by simp_all
        have hub : (recurrencePolynomial (k + 3)).natDegree ≤ k + 3 := by
          rw [A079508_rec]
          refine le_trans (natDegree_add_le _ _)
            (max_le (le_trans (natDegree_add_le _ _) (max_le ?_ ?_)) ?_)
          · simp_all
          · simp_all
          · grind
        have hdeg : (recurrencePolynomial (k + 3)).natDegree = k + 3 :=
          le_antisymm hub (le_natDegree_of_ne_zero hcoeff_ne)
        refine ⟨by assumption, ?_⟩
        rw [leadingCoeff, hdeg, hcoeff_top]
  simp_all
private def fibPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => fibPolynomial (n + 1) + X * fibPolynomial n

private theorem A011973_rec (n : ℕ) :
    fibPolynomial (n + 2) = fibPolynomial (n + 1) + X * fibPolynomial n := by
  rfl

private lemma A011973_coeff_choose :
    ∀ n k : ℕ, (fibPolynomial n).coeff k = (Nat.choose (n - k) k : ℝ)
  | 0, k => by
      rw [show fibPolynomial 0 = 1 from rfl, coeff_one]
      cases k <;> simp
  | 1, k => by
      rw [show fibPolynomial 1 = 1 from rfl, coeff_one]
      cases k <;> simp
  | n + 2, 0 => by
      rw [A011973_rec]
      simp [A011973_coeff_choose]
  | n + 2, k + 1 => by
      rw [A011973_rec, coeff_add, coeff_X_mul,
        A011973_coeff_choose, A011973_coeff_choose]
      rw [show n + 2 - (k + 1) = n + 1 - k by lia]
      by_cases hk : k ≤ n
      · rw [show n + 1 - (k + 1) = n - k by lia,
          show n + 1 - k = (n - k) + 1 by lia,
          Nat.choose_succ_succ]
        grind
      · have hnk : n - k = 0 := by lia
        have hkpos : 0 < k := by lia
        have hsub1 : n + 1 - (k + 1) = 0 := by lia
        have hsub2 : n + 1 - k = 0 := by lia
        have hz : Nat.choose 0 k = 0 :=
          Nat.choose_eq_zero_of_lt hkpos
        simp_all

/-- The A079508 row after removing its forced zero roots and reflecting. -/
def A079508ReflectedModel (n : ℕ) : ℝ[X] :=
  schurSzegoComp (n + 1) (fibPolynomial n) (narayanaPolynomial 1 (n + 1))

private lemma A079508ReflectedModel_coeff_of_le (n k : ℕ) (hk : k ≤ n) :
    (A079508ReflectedModel n).coeff k =
      (Nat.choose (n - k) k : ℝ) * (Nat.choose (n + 2) k : ℝ) /
        (k + 1 : ℝ) := by
  unfold A079508ReflectedModel
  rw [coeff_schurSzegoComp_of_le (by lia),
    A011973_coeff_choose,
    coeff_narayanaPolynomial_of_le (by lia)]
  unfold narayanaTransformCoeff
  have hden :
      (Nat.choose (1 + k) k : ℝ) = (k + 1 : ℝ) := by
    norm_num [Nat.add_comm]
  rw [hden]
  have hchoose : (Nat.choose (n + 1) k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by lia : k ≤ n + 1)).ne'
  grind

private lemma A079508ReflectedModel_coeff_eq_zero_of_lt (n k : ℕ) (hnk : n < k) :
    (A079508ReflectedModel n).coeff k = 0 := by
  unfold A079508ReflectedModel
  by_cases hk : k ≤ n + 1
  · have hkeq : k = n + 1 := by lia
    rw [coeff_schurSzegoComp_of_le hk, A011973_coeff_choose, hkeq]
    simp
  · exact coeff_schurSzegoComp_eq_zero_of_lt (by lia)
      (fibPolynomial n) (narayanaPolynomial 1 (n + 1))

private lemma A079508_reflected_coeff_identity (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose (n - k + 1) (k + 1) : ℝ) *
          (Nat.choose (n + 2) (n - k + 2) : ℝ) /
          ((n - k + 1 : ℕ) : ℝ) =
      (Nat.choose (n - k) k : ℝ) *
          (Nat.choose (n + 2) k : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  have hsym :
      Nat.choose (n + 2) (n - k + 2) = Nat.choose (n + 2) k := by
    have h := Nat.choose_symm (n := n + 2) (k := k) (by lia)
    grind
  rw [hsym]
  have hrelNat := Nat.add_one_mul_choose_eq (n - k) k
  have hrel :
      ((n - k + 1 : ℕ) : ℝ) * (Nat.choose (n - k) k : ℝ) =
        (Nat.choose (n - k + 1) (k + 1) : ℝ) * (k + 1 : ℝ) := by
    exact_mod_cast hrelNat
  grind

/-!
## Coefficient model to formalize

The OEIS entry identifies the underlying table as Raney numbers.  The local
coefficient of `X^k` is the OEIS entry in row `n + 2`, column `k + 1`, so its
formula is

`T(n+2,k+1) =
  binomial(k+1,n+1-k) * binomial(n+2,k+2) / (k+1)`.

This agrees with the generated examples (including their leading zero
coefficients).  The Lean definition above is nevertheless authoritative:
before using the formula, prove

```lean
(recurrencePolynomial n).coeff k =
  (Nat.choose (k+1) (n+1-k) : ℝ) *
    (Nat.choose (n+2) (k+2) : ℝ) / (k+1)
```
After removing the forced power of `X`,
the remaining coefficients are products of two finite binomial strings.
This makes a fixed-degree Schur--Szegő composition the preferred route:
`finiteSchurSzegoComposition` is assumption-free, unlike
the assumption-valued generic Hadamard wrapper.  The remaining formal work is
to choose the even/odd normalizations, prove their two factor polynomials are
PF, and identify their Schur--Szegő composition coefficientwise.
-/

private def A079508SchurLeft (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k (Nat.choose (k + 1) (n + 1 - k) : ℝ)

private def A079508SchurRight (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k
      ((Nat.choose n k : ℝ) * (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1))

private def A079508Closed (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k
      ((Nat.choose (k + 1) (n + 1 - k) : ℝ) *
        (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1))

@[simp] private lemma A079508SchurLeft_coeff (n k : ℕ) :
    (A079508SchurLeft n).coeff k =
      if k ≤ n then (Nat.choose (k + 1) (n + 1 - k) : ℝ) else 0 := by
  simp [A079508SchurLeft, Polynomial.finsetSum_coeff, coeff_monomial]

@[simp] private lemma A079508SchurRight_coeff (n k : ℕ) :
    (A079508SchurRight n).coeff k =
      if k ≤ n then
        (Nat.choose n k : ℝ) * (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1)
      else 0 := by
  simp [A079508SchurRight, Polynomial.finsetSum_coeff, coeff_monomial]

@[simp] private lemma A079508Closed_coeff (n k : ℕ) :
    (A079508Closed n).coeff k =
      if k ≤ n then
        (Nat.choose (k + 1) (n + 1 - k) : ℝ) *
          (Nat.choose (n + 2) (k + 2) : ℝ) / (k + 1)
      else 0 := by
  simp [A079508Closed, Polynomial.finsetSum_coeff, coeff_monomial]

private lemma A079508ReflectedModel_eq_reflect_closed (n : ℕ) :
    A079508ReflectedModel n = Polynomial.reflect n (A079508Closed n) := by
  ext k
  rw [Polynomial.coeff_reflect]
  by_cases hk : k ≤ n
  · rw [Polynomial.revAt_le hk,
      A079508ReflectedModel_coeff_of_le n k hk,
      A079508Closed_coeff, ite_eq_left (by lia : n - k ≤ n)]
    rw [show n + 1 - (n - k) = k + 1 by lia]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (A079508_reflected_coeff_identity n k hk).symm
  · have hkn : n < k := by lia
    rw [Polynomial.revAt_eq_self_of_lt hkn,
      A079508ReflectedModel_coeff_eq_zero_of_lt n k hkn,
      A079508Closed_coeff, ite_eq_right hk]

private def A079508CR (n k : ℕ) : ℝ :=
  (Nat.choose (n - k) k : ℝ) * (Nat.choose (n + 2) k : ℝ) / (k + 1 : ℝ)

private lemma A079508_cast_choose_fact {N K : ℕ} (h : K ≤ N) :
    (Nat.choose N K : ℝ) =
      (Nat.factorial N : ℝ) /
        ((Nat.factorial K : ℝ) * (Nat.factorial (N - K) : ℝ)) := by
  apply (eq_div_iff (by positivity :
    (Nat.factorial K : ℝ) * (Nat.factorial (N - K) : ℝ) ≠ 0)).2
  norm_cast
  simpa [mul_assoc] using Nat.choose_mul_factorial_mul_factorial h

private lemma A079508_CR_fact (n k : ℕ) (h : 2 * k ≤ n) :
    A079508CR n k =
      (Nat.factorial (n - k) : ℝ) * (Nat.factorial (n + 2) : ℝ) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (n - 2 * k) : ℝ) *
       ((Nat.factorial k : ℝ) * (Nat.factorial (n + 2 - k) : ℝ)) * (k + 1 : ℝ)) := by
  rw [A079508CR, A079508_cast_choose_fact (by lia : k ≤ n - k),
    A079508_cast_choose_fact (by lia : k ≤ n + 2)]
  grind

private lemma A079508_CR_shift_fact (n k a b : ℕ) (hb : b ≤ k) (hs : 2 * k ≤ n) :
    A079508CR (n + a) (k - b) =
      (Nat.factorial (n - k + a + b) : ℝ) * (Nat.factorial (n + a + 2) : ℝ) /
      ((Nat.factorial (k - b) : ℝ) * (Nat.factorial (n - 2 * k + a + 2 * b) : ℝ) *
        ((Nat.factorial (k - b) : ℝ) * (Nat.factorial (n - k + a + b + 2) : ℝ)) *
       (((k - b : ℕ) : ℝ) + 1)) := by
  rw [A079508_CR_fact _ _ (by lia)]
  grind

private lemma A079508_factorial_add_one_cast (m : ℕ) :
    (Nat.factorial (m + 1) : ℝ) = (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
  norm_num [Nat.factorial_succ]

private lemma A079508_factorial_add_two_cast (m : ℕ) :
    (Nat.factorial (m + 2) : ℝ) =
      (m + 2 : ℝ) * (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
  norm_num [Nat.factorial_succ]; ring

private lemma A079508_factorial_add_three_cast (m : ℕ) :
    (Nat.factorial (m + 3) : ℝ) =
      (m + 3 : ℝ) * (m + 2 : ℝ) * (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
  norm_num [Nat.factorial_succ]; ring

private lemma A079508_factorial_add_four_cast (m : ℕ) :
    (Nat.factorial (m + 4) : ℝ) =
      (m + 4 : ℝ) * (m + 3 : ℝ) * (m + 2 : ℝ) * (m + 1 : ℝ) *
        (Nat.factorial m : ℝ) := by
  norm_num [Nat.factorial_succ]; ring

private lemma A079508_factorial_add_five_cast (m : ℕ) :
    (Nat.factorial (m + 5) : ℝ) =
      (m + 5 : ℝ) * (m + 4 : ℝ) * (m + 3 : ℝ) * (m + 2 : ℝ) *
        (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
  norm_num [Nat.factorial_succ]; ring

private lemma A079508_CR_rec_interior (n k : ℕ) (hk : 2 ≤ k) (hs : 2 * k ≤ n) :
    A079508CR (n + 3) k =
      ((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ) * A079508CR (n + 2) k - A079508CR (n + 2) (k - 1)
      + (-(n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR (n + 1) k
      + (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * A079508CR (n + 1) (k - 1)
      + (-(n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR n (k - 1)
      + (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR n (k - 2) := by
  have h30 := A079508_CR_shift_fact n k 3 0 (by lia) hs
  have h20 := A079508_CR_shift_fact n k 2 0 (by lia) hs
  have h10 := A079508_CR_shift_fact n k 1 0 (by lia) hs
  have h01 := A079508_CR_shift_fact n k 0 1 (by lia) hs
  have h02 := A079508_CR_shift_fact n k 0 2 (by assumption) hs
  simp only [Nat.sub_zero, Nat.add_zero, mul_zero] at h30 h20 h10
  simp only [Nat.add_zero] at h01 h02
  rw [h30, h20, A079508_CR_shift_fact n k 2 1 (by lia) hs, h10,
    A079508_CR_shift_fact n k 1 1 (by lia) hs, h01, h02]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  simp only [show 2 + q = q + 2 by lia,
      show 2 * (q + 2) + t - (q + 2) = q + 2 + t by lia,
      show 2 * (q + 2) + t - 2 * (q + 2) = t by lia,
      show q + 2 - 1 = q + 1 by lia, show q + 2 - 2 = q by lia]
  norm_num only [Nat.mul_one, Nat.one_mul, Nat.add_zero]
  rw [A079508_factorial_add_one_cast (q + 2 + t),
      A079508_factorial_add_two_cast (q + 2 + t),
      A079508_factorial_add_three_cast (q + 2 + t),
      A079508_factorial_add_four_cast (q + 2 + t),
      A079508_factorial_add_five_cast (q + 2 + t),
      A079508_factorial_add_one_cast (2 * (q + 2) +t + 2),
      A079508_factorial_add_two_cast (2 * (q + 2) +t + 2),
      A079508_factorial_add_three_cast (2 * (q + 2) +t + 2),
      A079508_factorial_add_one_cast q, A079508_factorial_add_two_cast q,
      A079508_factorial_add_one_cast t, A079508_factorial_add_two_cast t,
      A079508_factorial_add_three_cast t, A079508_factorial_add_four_cast t]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

private lemma A079508_CR_zero (n k : ℕ) (h : n < 2 * k) : A079508CR n k = 0 := by
  unfold A079508CR
  rw [Nat.choose_eq_zero_of_lt (by lia : n - k < k)]
  simp

private lemma A079508_CR_boundary_fact (q d a b : ℕ) (hd4 : d ≤ 4) (hb2 : b ≤ 2)
    (hsupp : d ≤ a + 2 * b) :
    A079508CR (2 * q + (4 - d) + a) (q + (2 - b)) =
      (Nat.factorial (q + (2 + a + b - d)) : ℝ) *
        (Nat.factorial (2 * q + (6 + a - d)) : ℝ) /
      ((Nat.factorial (q + (2 - b)) : ℝ) *
        (Nat.factorial (a + 2 * b - d) : ℝ) *
        ((Nat.factorial (q + (2 - b)) : ℝ) *
        (Nat.factorial (q + (4 + a + b - d)) : ℝ)) *
       (((q + (3 - b) : ℕ) : ℝ))) := by
  rw [A079508_CR_fact _ _ (by lia)]
  rw [show 2 * q + (4 - d) +a - (q + (2 - b)) = q + (2 + a + b - d) by lia,
      show 2 * q + (4 - d) +a + 2 = 2 * q + (6 + a - d) by lia,
      show 2 * q + (4 - d) +a - 2 * (q + (2 - b)) = a + 2 * b - d by lia,
      show 2 * q + (6 + a - d)-(q + (2 - b)) = q + (4 + a + b - d) by lia,
      show ((q + (2 - b) : ℕ) : ℝ) + 1 = ((q + (3 - b) : ℕ) : ℝ) by
        have hb3 : b ≤ 3 := by lia
        norm_num only [Nat.cast_add, Nat.cast_sub hb2, Nat.cast_sub hb3,
          Nat.cast_ofNat]
        ring]

private lemma A079508_CR_rec_boundary (n k d : ℕ) (hk : 2 ≤ k) (hd1 : 1 ≤ d)
    (hd4 : d ≤ 4) (hd : n + d = 2 * k) :
    A079508CR (n + 3) k =
      ((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ) * A079508CR (n + 2) k - A079508CR (n + 2) (k - 1)
      + (-(n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR (n + 1) k
      + (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * A079508CR (n + 1) (k - 1)
      + (-(n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR n (k - 1)
      + (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR n (k - 2) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  interval_cases d
  · have hn : n = 2 * q + 3 := by lia
    subst n
    simp only [show 2 + q = q + 2 by lia, show q + 2 - 1 = q + 1 by lia,
      show q + 2 - 2 = q by lia]
    have h30 := A079508_CR_boundary_fact q 1 3 0 (by assumption) (by lia) (by lia)
    have h20 := A079508_CR_boundary_fact q 1 2 0 (by assumption) (by lia) (by lia)
    have h21 := A079508_CR_boundary_fact q 1 2 1 (by assumption) (by lia) (by assumption)
    have h10 := A079508_CR_boundary_fact q 1 1 0 (by assumption) (by lia) (by assumption)
    have h11 := A079508_CR_boundary_fact q 1 1 1 (by assumption) (by lia) (by lia)
    have h01 := A079508_CR_boundary_fact q 1 0 1 (by assumption) (by lia) (by lia)
    have h02 := A079508_CR_boundary_fact q 1 0 2 (by assumption) (by lia) (by assumption)
    norm_num at h30 h20 h21 h10 h11 h01 h02
    rw [h30, h20, h21, h10, h11, h01, h02]
    norm_num [Nat.factorial_succ]
    field_simp
    ring
  · have hn : n = 2 * q + 2 := by lia
    subst n
    simp only [show 2 + q = q + 2 by lia, show q + 2 - 1 = q + 1 by lia,
      show q + 2 - 2 = q by lia]
    have h30 := A079508_CR_boundary_fact q 2 3 0 (by assumption) (by lia) (by lia)
    have h20 := A079508_CR_boundary_fact q 2 2 0 (by assumption) (by lia) (by lia)
    have h21 := A079508_CR_boundary_fact q 2 2 1 (by assumption) (by assumption) (by assumption)
    have h10 := A079508_CR_zero (2 * q + 3) (q + 2) (by lia)
    have h11 := A079508_CR_boundary_fact q 2 1 1 (by assumption) (by assumption) (by lia)
    have h01 := A079508_CR_boundary_fact q 2 0 1 (by assumption) (by assumption) (by lia)
    have h02 := A079508_CR_boundary_fact q 2 0 2 (by assumption) (by lia) (by assumption)
    norm_num at h30 h20 h21 h10 h11 h01 h02
    rw [h30, h20, h21, h10, h11, h01, h02]
    norm_num [Nat.factorial_succ]
    field_simp
    ring
  · have hn : n = 2 * q + 1 := by lia
    subst n
    simp only [show 2 + q = q + 2 by lia, show q + 2 - 1 = q + 1 by lia,
      show q + 2 - 2 = q by lia]
    have h30 := A079508_CR_boundary_fact q 3 3 0 (by assumption) (by lia) (by lia)
    have h20 := A079508_CR_zero (2 * q + 3) (q + 2) (by lia)
    have h21 := A079508_CR_boundary_fact q 3 2 1 (by assumption) (by lia) (by assumption)
    have h10 := A079508_CR_zero (2 * q + 2) (q + 2) (by lia)
    have h11 := A079508_CR_boundary_fact q 3 1 1 (by assumption) (by lia) (by lia)
    have h01 := A079508_CR_zero (2 * q + 1) (q + 1) (by lia)
    have h02 := A079508_CR_boundary_fact q 3 0 2 (by assumption) (by lia) (by assumption)
    norm_num at h30 h20 h21 h10 h11 h01 h02
    rw [h30, h20, h21, h10, h11, h01, h02]
    norm_num [Nat.factorial_succ]
    field_simp
    ring
  · have hn : n = 2 * q := by lia
    subst n
    simp only [show 2 + q = q + 2 by lia, show q + 2 - 1 = q + 1 by lia,
      show q + 2 - 2 = q by lia]
    have h30 := A079508_CR_zero (2 * q + 3) (q + 2) (by lia)
    have h20 := A079508_CR_zero (2 * q + 2) (q + 2) (by lia)
    have h21 := A079508_CR_boundary_fact q 4 2 1 (by assumption) (by lia) (by assumption)
    have h10 := A079508_CR_zero (2 * q + 1) (q + 2) (by lia)
    have h11 := A079508_CR_zero (2 * q + 1) (q + 1) (by lia)
    have h01 := A079508_CR_zero (2 * q) (q + 1) (by lia)
    have h02 := A079508_CR_boundary_fact q 4 0 2 (by assumption) (by lia) (by assumption)
    norm_num at h30 h20 h21 h10 h11 h01 h02
    rw [h30, h20, h21, h10, h11, h01, h02]
    norm_num [Nat.factorial_succ]
    field_simp
    ring

private lemma A079508_CR_rec (n k : ℕ) (hk : 2 ≤ k) :
    A079508CR (n + 3) k =
      ((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ) * A079508CR (n + 2) k - A079508CR (n + 2) (k - 1)
      + (-(n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR (n + 1) k
      + (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * A079508CR (n + 1) (k - 1)
      + (-(n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR n (k - 1)
      + (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * A079508CR n (k - 2) := by
  by_cases hs : 2 * k ≤ n
  · exact A079508_CR_rec_interior n k hk hs
  by_cases hfar : n + 5 ≤ 2 * k
  · rw [A079508_CR_zero _ _ (by lia), A079508_CR_zero _ _ (by lia),
      A079508_CR_zero _ _ (by lia), A079508_CR_zero _ _ (by lia),
      A079508_CR_zero _ _ (by lia), A079508_CR_zero _ _ (by lia),
      A079508_CR_zero _ _ (by lia)]
    ring
  · let d := 2 * k - n
    apply A079508_CR_rec_boundary n k d hk
    · grind
    · grind
    · grind

private lemma A079508_model_coeff_CR (n k : ℕ) :
    (A079508ReflectedModel n).coeff k = A079508CR n k := by
  by_cases hk : k ≤ n
  · rw [A079508ReflectedModel_coeff_of_le n k hk]
    rfl
  · rw [A079508ReflectedModel_coeff_eq_zero_of_lt n k (by lia),
      A079508_CR_zero n k (by lia)]

private lemma A079508_CR_derivative_rec_interior
    (n k : ℕ) (h : 2 * k < n) :
    (n + 5 : ℝ) * A079508CR (n + 2) (k + 1) =
      (n + 7 + 2 * k : ℝ) * A079508CR (n + 1) (k + 1) +
        ((n : ℝ) + 1 - 2 * (k : ℝ)) * A079508CR (n + 1) k +
          (3 * (n + 3) : ℝ) * A079508CR n k := by
  rw [A079508_CR_fact _ _ (by lia), A079508_CR_fact _ _ (by lia),
    A079508_CR_fact _ _ (by lia), A079508_CR_fact _ _ (by lia)]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (by lia : 2 * k + 1 ≤ n)
  simp only [show 2 * k + 1 + t + 2 = 2 * k + t + 3 by lia,
    show 2 * k + 1 + t + 1 + 2 = 2 * k + t + 3 + 1 by lia]
  simp only [show 2 * k + t + 3 - (k + 1) = k + t + 2 by lia,
    show 2 * k + 1 + t + 1 - (k + 1) = k + t + 1 by lia,
    show 2 * k + 1 + t + 1 - k = k + t + 2 by lia,
    show 2 * k + 1 + t - k = k + t + 1 by lia,
    show 2 * k + t + 3 - 2 * (k + 1) = t + 1 by lia,
    show 2 * k + 1 + t + 1 - 2 * (k + 1) = t by lia,
    show 2 * k + 1 + t + 1 - 2 * k = t + 2 by lia,
    show 2 * k + 1 + t - 2 * k = t + 1 by lia,
    show 2 * k + t + 3 + 2 - (k + 1) = k + t + 4 by lia,
    show 2 * k + t + 3 + 1 - (k + 1) = k + t + 3 by lia,
    show 2 * k + t + 3 + 1 - k = k + t + 4 by lia,
    show 2 * k + t + 3 - k = k + t + 3 by lia]
  rw [A079508_factorial_add_one_cast (k + t + 1),
    A079508_factorial_add_two_cast (k + t + 1),
    A079508_factorial_add_three_cast (k + t + 1),
    A079508_factorial_add_one_cast (2 * k + t + 3),
    A079508_factorial_add_two_cast (2 * k + t + 3),
    A079508_factorial_add_one_cast k, A079508_factorial_add_one_cast t,
    A079508_factorial_add_two_cast t]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

private lemma A079508_CR_derivative_rec (n k : ℕ) :
    (n + 5 : ℝ) * A079508CR (n + 2) (k + 1) =
      (n + 7 + 2 * k : ℝ) * A079508CR (n + 1) (k + 1) +
        ((n : ℝ) + 1 - 2 * (k : ℝ)) * A079508CR (n + 1) k +
          (3 * (n + 3) : ℝ) * A079508CR n k := by
  by_cases h : 2 * k < n
  · exact A079508_CR_derivative_rec_interior n k h
  by_cases hboundary : n = 2 * k
  · subst n
    rw [A079508_CR_zero (2 * k + 1) (k + 1) (by lia),
      A079508_CR_fact _ _ (by lia), A079508_CR_fact _ _ (by lia),
      A079508_CR_fact _ _ (by lia)]
    simp only [show 2 * k + 2 - (k + 1) = k + 1 by lia,
      show 2 * k + 2 + 2 - (k + 1) = k + 3 by lia,
      show 2 * k + 2 - 2 * (k + 1) = 0 by lia,
      show 2 * k + 1 - k = k + 1 by lia,
      show 2 * k + 1 + 2 - k = k + 3 by lia,
      show 2 * k + 1 - 2 * k = 1 by lia,
      show 2 * k - k = k by lia, show 2 * k + 2 - k = k + 2 by lia,
      show 2 * k - 2 * k = 0 by lia]
    rw [A079508_factorial_add_one_cast k,
      A079508_factorial_add_two_cast k,
      A079508_factorial_add_three_cast k,
      A079508_factorial_add_one_cast (2 * k + 2),
      A079508_factorial_add_two_cast (2 * k + 2)]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
    field_simp
    ring
  by_cases heq : n + 1 = 2 * k
  · rw [A079508_CR_zero (n + 2) (k + 1) (by lia),
      A079508_CR_zero (n + 1) (k + 1) (by lia),
      A079508_CR_zero n k (by lia)]
    have heq' : (n : ℝ) + 1 = 2 * (k : ℝ) := by exact_mod_cast heq
    rw [heq']
    ring
  · rw [A079508_CR_zero (n + 2) (k + 1) (by lia),
      A079508_CR_zero (n + 1) (k + 1) (by lia),
      A079508_CR_zero (n + 1) k (by lia), A079508_CR_zero n k (by lia)]
    ring

private def reflectedU (n : ℕ) : ℝ[X] :=
  1 + C ((n + 1 : ℝ) / (n + 5 : ℝ)) * X

private def reflectedV (n : ℕ) : ℝ[X] :=
  C (2 / (n + 5 : ℝ)) * X * (1 - X)

private def reflectedW (n : ℕ) : ℝ[X] :=
  C (3 * (n + 3 : ℝ) / (n + 5 : ℝ)) * X

private lemma reflectedModel_derivative_recurrence (n : ℕ) :
    A079508ReflectedModel (n + 2) =
      reflectedU n * A079508ReflectedModel (n + 1) +
        reflectedV n * (A079508ReflectedModel (n + 1)).derivative +
        reflectedW n * A079508ReflectedModel n := by
  apply Polynomial.ext
  intro q
  rw [show reflectedU n * A079508ReflectedModel (n + 1) +
      reflectedV n * (A079508ReflectedModel (n + 1)).derivative +
      reflectedW n * A079508ReflectedModel n =
        A079508ReflectedModel (n + 1) +
          C ((n + 1 : ℝ) / (n + 5 : ℝ)) *
            (X * A079508ReflectedModel (n + 1)) +
          C (2 / (n + 5 : ℝ)) * theta (A079508ReflectedModel (n + 1)) -
          C (2 / (n + 5 : ℝ)) *
            (X * theta (A079508ReflectedModel (n + 1))) +
          C (3 * (n + 3 : ℝ) / (n + 5 : ℝ)) *
            (X * A079508ReflectedModel n) by
    simp only [reflectedU, reflectedV, reflectedW, theta]
    ring]
  rcases q with _ | k
  · simp only [A079508_model_coeff_CR, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_mul_zero, coeff_theta, Nat.cast_zero, zero_mul, A079508CR]
    norm_num
  · simp only [A079508_model_coeff_CR, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_mul, coeff_theta, Nat.cast_add, Nat.cast_one]
    have h := A079508_CR_derivative_rec n k
    have hden : (n + 5 : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    linarith

private lemma reflectedModel_natDegree (n : ℕ) :
    (A079508ReflectedModel n).natDegree = n / 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [A079508_model_coeff_CR, A079508_CR_zero n k (by lia)]
  · rw [A079508_model_coeff_CR]
    unfold A079508CR
    have hleft : 0 < (n - n / 2).choose (n / 2) :=
      Nat.choose_pos (by lia)
    have hright : 0 < (n + 2).choose (n / 2) :=
      Nat.choose_pos (by lia)
    positivity

private lemma reflectedModel_hasPosLeadingCoeff (n : ℕ) :
    HasPosLeadingCoeff (A079508ReflectedModel n) := by
  rw [HasPosLeadingCoeff, leadingCoeff, reflectedModel_natDegree,
    A079508_model_coeff_CR]
  unfold A079508CR
  have hleft : 0 < (n - n / 2).choose (n / 2) :=
    Nat.choose_pos (by lia)
  have hright : 0 < (n + 2).choose (n / 2) :=
    Nat.choose_pos (by lia)
  positivity

private lemma reflectedModel_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (A079508ReflectedModel n) := by
  intro k
  rw [A079508_model_coeff_CR]
  unfold A079508CR
  positivity

private lemma reflectedModel_degree_step (n : ℕ) :
    (A079508ReflectedModel (n + 1)).natDegree =
        (A079508ReflectedModel n).natDegree ∨
      (A079508ReflectedModel (n + 1)).natDegree =
        (A079508ReflectedModel n).natDegree + 1 := by
  rw [reflectedModel_natDegree, reflectedModel_natDegree]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · left
    rw [show 2 * m + 1 = 1 + m * 2 by lia,
      Nat.add_mul_div_right _ _ (by norm_num)]
    norm_num
  · right
    rw [show 2 * m + 1 + 1 = 0 + (m + 1) * 2 by lia,
      show 2 * m + 1 = 1 + m * 2 by lia,
      Nat.add_mul_div_right _ _ (by norm_num),
      Nat.add_mul_div_right _ _ (by norm_num)]
    norm_num

private lemma reflectedV_eval_nonpos (n : ℕ) (x : ℝ) (hx : x ≤ 0) :
    (reflectedV n).eval x ≤ 0 := by
  simp only [reflectedV, eval_mul, eval_C, eval_X, eval_sub, eval_one]
  have hden : 0 < (n + 5 : ℝ) := by positivity
  have hone : 0 ≤ 1 - x := by linarith
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) hden.le) hx)
    hone

private lemma reflectedW_eval_nonpos (n : ℕ) (x : ℝ) (hx : x ≤ 0) :
    (reflectedW n).eval x ≤ 0 := by
  simp only [reflectedW, eval_mul, eval_C, eval_X]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hx

private lemma reflectedModel_zero : A079508ReflectedModel 0 = 1 := by
  ext k
  rw [A079508_model_coeff_CR]
  rcases k with _ | k
  · norm_num [A079508CR, coeff_one]
  · rw [A079508_CR_zero 0 (k + 1) (by lia)]
    simp only [coeff_one, Nat.succ_ne_zero, ↓reduceIte]

private lemma reflectedModel_one : A079508ReflectedModel 1 = 1 := by
  ext k
  rw [A079508_model_coeff_CR]
  rcases k with _ | k
  · norm_num [A079508CR, coeff_one]
  · rw [A079508_CR_zero 1 (k + 1) (by lia)]
    simp only [coeff_one, Nat.succ_ne_zero, ↓reduceIte]

/-- Consecutive nonzero-root factors of A079508 strictly interlace. -/
theorem reflectedModel_strictInterl_succ (n : ℕ) :
    StrictInterl (A079508ReflectedModel n) (A079508ReflectedModel (n + 1)) := by
  apply derivativeLag_strictInterl_of_nonnegCoeffs_of_step
    reflectedModel_derivative_recurrence reflectedModel_degree_step
    reflectedModel_hasPosLeadingCoeff reflectedModel_hasNonnegCoeffs
    reflectedV_eval_nonpos reflectedW_eval_nonpos
  rw [reflectedModel_zero, reflectedModel_one]
  exact StrictInterl.refl (one_ne_zero : (1 : ℝ[X]) ≠ 0) (Splits.C 1)

private lemma A079508_model_rec (n : ℕ) :
    A079508ReflectedModel (n + 3) =
      (C (((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ)) - X) * A079508ReflectedModel (n + 2) +
      (C (-(n + 3 : ℝ) / (n + 6 : ℝ)) + C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X) *
        A079508ReflectedModel (n + 1) +
      (C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X + C (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2) *
        A079508ReflectedModel n := by
  ext k
  rw [A079508_model_coeff_CR]
  simp only [sub_mul, add_mul, mul_assoc, coeff_add, coeff_sub, coeff_C_mul]
  rcases k with _ | k
  · simp [A079508_model_coeff_CR, A079508CR, Nat.choose_zero_right]
    grind
  · rcases k with _ | k
    · simp [coeff_X_mul, coeff_X_pow_mul', A079508_model_coeff_CR, A079508CR,
        Nat.choose_zero_right, Nat.choose_one_right]
      grind
    · simp only [coeff_X_mul, coeff_X_pow_mul', ite_eq_left (by lia : 2 ≤ k + 2),
        show k + 2 - 2 = k by lia, A079508_model_coeff_CR]
      rw [A079508_CR_rec n (k + 2) (by lia)]
      grind

private lemma A079508_model_natDegree_le (n : ℕ) :
    (A079508ReflectedModel n).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact A079508ReflectedModel_coeff_eq_zero_of_lt n k hk

private lemma A079508_closed_eq_reflect_model (n : ℕ) :
    A079508Closed n = Polynomial.reflect n (A079508ReflectedModel n) := by
  rw [A079508ReflectedModel_eq_reflect_closed]
  simp

private lemma A079508_reflect_sub_poly (N : ℕ) (p q : ℝ[X]) :
    Polynomial.reflect N (p - q) = Polynomial.reflect N p - Polynomial.reflect N q := by simp

private lemma A079508_reflect_factor1 (n : ℕ) :
    Polynomial.reflect 1 (C (((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ)) - X) =
      C (-1) + C (((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ)) * X := by
  rw [A079508_reflect_sub_poly]
  rw [show (X : ℝ[X]) = X ^ 1 by ring, Polynomial.reflect_monomial]
  simp
  ring

private lemma A079508_reflect_factor2 (n : ℕ) :
    Polynomial.reflect 2
      (C (-(n + 3 : ℝ) / (n + 6 : ℝ)) + C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X) =
      C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X +
        C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2 := by
  rw [Polynomial.reflect_add]
  rw [show C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X =
      C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X ^ 1 by ring,
    Polynomial.reflect_C_mul_X_pow]
  simp
  ring

private lemma A079508_reflect_factor3 (n : ℕ) :
    Polynomial.reflect 3
      (C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X + C (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2) =
      C (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * X + C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2 := by
  rw [Polynomial.reflect_add]
  rw [show C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X =
      C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 1 by ring,
    Polynomial.reflect_C_mul_X_pow, Polynomial.reflect_C_mul_X_pow]
  simp
  ring

private lemma A079508_closed_rec (n : ℕ) :
    A079508Closed (n + 3) =
      (C (-1) + C (((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ)) * X) * A079508Closed (n + 2) +
      (C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X + C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2) *
        A079508Closed (n + 1) +
      (C (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * X + C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2) *
        A079508Closed n := by
  have h := congrArg (Polynomial.reflect (n + 3)) (A079508_model_rec n)
  simp only [Polynomial.reflect_add] at h
  rw [show n + 3 = 1 + (n + 2) by lia,
      Polynomial.reflect_mul _ _ (F := 1) (G := n + 2) (by compute_degree!)
        (A079508_model_natDegree_le (n + 2))] at h
  rw [show 1 + (n + 2) = 2 + (n + 1) by lia,
      Polynomial.reflect_mul _ _ (F := 2) (G := n + 1) (by compute_degree!)
        (A079508_model_natDegree_le (n + 1))] at h
  rw [show 2 + (n + 1) = 3 + n by lia,
      Polynomial.reflect_mul _ _ (F := 3) (G := n) (by compute_degree!)
        (A079508_model_natDegree_le n)] at h
  rw [← A079508_closed_eq_reflect_model, ← A079508_closed_eq_reflect_model,
      ← A079508_closed_eq_reflect_model, ← A079508_closed_eq_reflect_model,
      A079508_reflect_factor1, A079508_reflect_factor2,
      A079508_reflect_factor3] at h
  grind

private lemma A079508_c1_eq (n : ℕ) : A079508c1 n =
    C (-1) + C (((2 * n + 9 : ℕ) : ℝ) / (n + 6 : ℝ)) * X := by
  apply Polynomial.funext
  intro r
  simp only [A079508c1, recurrencePolynomialα, eval_add, eval_mul, eval_C, eval_X]
  grind

private lemma A079508_c2_eq (n : ℕ) : A079508c2 n =
    C (3 * (2 * n + 7 : ℝ) / (n + 6 : ℝ)) * X + C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2 := by
  apply Polynomial.funext
  intro r
  simp only [A079508c2, recurrencePolynomialβ, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  grind

private lemma A079508_c3_eq (n : ℕ) : A079508c3 n =
    C (4 * (n + 3 : ℝ) / (n + 6 : ℝ)) * X + C (-(n + 3 : ℝ) / (n + 6 : ℝ)) * X ^ 2 := by
  apply Polynomial.funext
  intro r
  simp only [A079508c3, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  grind

private lemma A079508_generated_eq_closed (n : ℕ) : recurrencePolynomial n = A079508Closed n := by
  have main : ∀ m : ℕ,
      recurrencePolynomial m = A079508Closed m ∧
      recurrencePolynomial (m + 1) = A079508Closed (m + 1) ∧
      recurrencePolynomial (m + 2) = A079508Closed (m + 2) := by
    intro m
    induction m with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · norm_num [recurrencePolynomial, A079508Closed, Finset.sum_range_succ]
        · rw [show recurrencePolynomial 1 = X from rfl]
          norm_num [A079508Closed, Finset.sum_range_succ]
          rw [← C_mul_X_pow_eq_monomial]
          simp
        · rw [show recurrencePolynomial 2 = 2 * X + X ^ 2 from rfl]
          norm_num [A079508Closed, Finset.sum_range_succ]
          simp only [← C_mul_X_pow_eq_monomial]
          norm_num
          ring_nf
          rw [Nat.choose_eq_zero_of_lt (by norm_num : 1 < 3)]
          simp [map_ofNat]
    | succ m ih =>
        refine ⟨ih.2.1, ih.2.2, ?_⟩
        rw [show m + 1 + 2 = m + 3 by lia, A079508_rec, A079508_closed_rec,
          ih.1, ih.2.1, ih.2.2, A079508_c1_eq, A079508_c2_eq, A079508_c3_eq]
  simp_all

private lemma reflectedModel_coeff_zero (n : ℕ) :
    (A079508ReflectedModel n).coeff 0 = 1 := by
  rw [A079508_model_coeff_CR]
  norm_num [A079508CR]

private lemma reflectedModel_isPF (n : ℕ) :
    IsPFPolynomial (A079508ReflectedModel n) :=
  IsPFPolynomial.of_realRooted_nonneg (reflectedModel_hasNonnegCoeffs n)
    (reflectedModel_strictInterl_succ n).1.2

private lemma reflectedModel_roots_neg (n : ℕ) :
    ∀ x ∈ (A079508ReflectedModel n).roots, x < 0 :=
  (reflectedModel_isPF n).roots_neg_of_coeff_zero_ne (by
    rw [reflectedModel_coeff_zero]
    norm_num)

private lemma reverse_reflectedModel_hasNonnegCoeffs (n : ℕ) :
    HasNonnegCoeffs (A079508ReflectedModel n).reverse := by
  intro k
  rw [coeff_reverse]
  exact reflectedModel_hasNonnegCoeffs n _

private lemma reverse_reflectedModel_natDegree (n : ℕ) :
    (A079508ReflectedModel n).reverse.natDegree = n / 2 := by
  rw [Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (.inr (by
      rw [reflectedModel_coeff_zero]
      norm_num)), Nat.sub_zero, reflectedModel_natDegree]

/-- The A079508 coefficient model, including its forced powers of `X`. -/
def polynomial (n : ℕ) : ℝ[X] := A079508Closed n

/-- Consecutive A079508 model rows weakly interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) := by
  rw [polynomial, polynomial, A079508_closed_eq_reflect_model,
    A079508_closed_eq_reflect_model]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hdeg0 : (A079508ReflectedModel (2 * m)).natDegree = m := by
      rw [reflectedModel_natDegree, show 2 * m = 0 + m * 2 by lia,
        Nat.add_mul_div_right _ _ (by norm_num)]
      norm_num
    have hdeg1 : (A079508ReflectedModel (2 * m + 1)).natDegree = m := by
      rw [reflectedModel_natDegree, show 2 * m + 1 = 1 + m * 2 by lia,
        Nat.add_mul_div_right _ _ (by norm_num)]
      norm_num
    have hreverse :
        StrictInterl (A079508ReflectedModel (2 * m + 1)).reverse
          (A079508ReflectedModel (2 * m)).reverse := by
      have h := reciprocalShift_reverses_strictInterl (D := m)
        (reflectedModel_isPF (2 * m)) (reflectedModel_isPF (2 * m + 1))
        hdeg0.le hdeg1.le (reflectedModel_strictInterl_succ (2 * m))
      rw [reciprocalShift_eq_X_pow_mul_reverse hdeg1.le,
        reciprocalShift_eq_X_pow_mul_reverse hdeg0.le, hdeg0, hdeg1,
        Nat.sub_self, pow_zero, one_mul] at h
      simpa only [one_mul] using h
    have hout := strictInterl_X_pow_mul_X_pow_succ_of_reverse_strictInterl_nonneg
      hreverse (reverse_reflectedModel_hasNonnegCoeffs (2 * m))
      (reverse_reflectedModel_hasNonnegCoeffs (2 * m + 1)) m
    rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse
        (N := 2 * m) _ (by rw [hdeg0]; lia),
      DegreeDropReversal.reflect_eq_X_pow_mul_reverse
        (N := 2 * m + 1) _ (by rw [hdeg1]; lia), hdeg0, hdeg1]
    simp only [show 2 * m - m = m by lia,
      show 2 * m + 1 - m = m + 1 by lia]
    exact hout.toInterlaces (by
      rw [natDegree_X_pow_mul m hreverse.2.1.1,
        natDegree_X_pow_mul (m + 1) hreverse.1.1,
        reverse_reflectedModel_natDegree, reverse_reflectedModel_natDegree]
      lia)
  · have hdeg0 : (A079508ReflectedModel (2 * m + 1)).natDegree = m := by
      rw [reflectedModel_natDegree, show 2 * m + 1 = 1 + m * 2 by lia,
        Nat.add_mul_div_right _ _ (by norm_num)]
      norm_num
    have hdeg1 :
        (A079508ReflectedModel (2 * m + 1 + 1)).natDegree = m + 1 := by
      rw [reflectedModel_natDegree,
        show 2 * m + 1 + 1 = 0 + (m + 1) * 2 by lia,
        Nat.add_mul_div_right _ _ (by norm_num)]
      norm_num
    rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse
        (N := 2 * m + 1) _ (by rw [hdeg0]; lia),
      DegreeDropReversal.reflect_eq_X_pow_mul_reverse
        (N := 2 * m + 1 + 1) _ (by rw [hdeg1]; lia), hdeg0, hdeg1]
    simp only [show 2 * m + 1 - m = m + 1 by lia,
      show 2 * m + 1 + 1 - (m + 1) = m + 1 by lia]
    exact interlaces_X_pow_mul_reverse_of_roots_neg
      ((reflectedModel_strictInterl_succ (2 * m + 1)).toInterlaces (by
        rw [hdeg0, hdeg1]))
      (reflectedModel_roots_neg (2 * m + 1 + 1))
      (reflectedModel_roots_neg (2 * m + 1)) (m + 1)

/-- Every A079508 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits :=
  (polynomial_interlaces n).2.1.2

/-- The A079508 model satisfies the downstream lag-three recurrence. -/
theorem polynomial_recurrence (n : ℕ) :
    polynomial (n + 3) =
      nextRow n (polynomial (n + 2)) (polynomial (n + 1)) (polynomial n) := by
  rw [polynomial, polynomial, polynomial, polynomial,
    ← A079508_generated_eq_closed, ← A079508_generated_eq_closed,
    ← A079508_generated_eq_closed, ← A079508_generated_eq_closed]
  exact recurrencePolynomial_recurrence n

private theorem polynomial_zero : polynomial 0 = 1 := by
  simpa only [polynomial, recurrencePolynomial] using
    (A079508_generated_eq_closed 0).symm

private theorem polynomial_one : polynomial 1 = X := by
  simpa only [polynomial, recurrencePolynomial] using
    (A079508_generated_eq_closed 1).symm

private theorem polynomial_two : polynomial 2 = 2 * X + X ^ 2 := by
  simpa only [polynomial, recurrencePolynomial] using
    (A079508_generated_eq_closed 2).symm

/-- A sequence with the A079508 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (htwo : P 2 = 2 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    (htwo.trans polynomial_two.symm) hrec polynomial_recurrence
  rw [heq n]
  exact polynomial_splits n

/-- Consecutive rows with the A079508 initial rows and update interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (htwo : P 2 = 2 * X + X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_three_recurrence nextRow
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    (htwo.trans polynomial_two.symm) hrec polynomial_recurrence
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n
/-- The downstream A079508 recurrence rows weakly interlace. -/
theorem A079508_interlaces (n : ℕ) :
    RealRooted.Interlaces (recurrencePolynomial n) (recurrencePolynomial (n + 1)) := by
  rw [A079508_generated_eq_closed, A079508_generated_eq_closed]
  exact polynomial_interlaces n

/-- Every downstream A079508 recurrence row splits over the reals. -/
theorem A079508_splits (n : ℕ) : (recurrencePolynomial n).Splits := by
  rw [A079508_generated_eq_closed]
  exact polynomial_splits n

/-- Every downstream A079508 recurrence row is nonzero. -/
theorem A079508_ne_zero (n : ℕ) : (recurrencePolynomial n) ≠ 0 :=
  leadingCoeff_ne_zero.mp (by rw [(A079508_key n).2]; norm_num)

/-- Consecutive downstream A079508 recurrence rows are in directed proper position. -/
theorem A079508_prec (n : ℕ) :
    RealRooted.StrictInterl (recurrencePolynomial n) (recurrencePolynomial (n + 1)) := by
  exact (A079508_interlaces n).toStrictInterl

end RealRooted.Applications.OEIS.A079508
