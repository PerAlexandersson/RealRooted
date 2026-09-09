import RealRooted.ObreschkoffConverse
import RealRooted.SequenceClosure
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# Generalized Eulerian polynomials

The parameterized Eulerian differential recurrence and its real-rootedness,
degree, and coefficient-positivity invariants.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Eulerian differential polynomials with a real dilation parameter. -/
def generalizedEulerian (c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      (1 + C (c * (n : ℝ) + 1) * X) * generalizedEulerian c n
        + C c * X * (1 - X) * (generalizedEulerian c n).derivative

lemma generalizedEulerian_succ (c : ℝ) (n : ℕ) :
    generalizedEulerian c (n + 1) =
      (1 + C (c * (n : ℝ) + 1) * X) * generalizedEulerian c n
        + C c * X * (1 - X) * (generalizedEulerian c n).derivative :=
  rfl

/-- Generalized Eulerian polynomials have their expected degree and are monic
for every real parameter. -/
theorem generalizedEulerian_degree_and_monic (c : ℝ) (n : ℕ) :
    (generalizedEulerian c n).natDegree = n ∧
      (generalizedEulerian c n).Monic := by
  have hrec : ∀ k, generalizedEulerian c (k + 1) =
      (C c * X + C (-c) * X ^ 2) * (generalizedEulerian c k).derivative +
        (C 1 + C (c * (k : ℝ) + 1) * X) * generalizedEulerian c k + 0 := by
    intro k
    rw [generalizedEulerian_succ]
    simp only [map_neg, map_one]
    ring
  have hseed : generalizedEulerian c 0 ≠ 0 := by
    simp [generalizedEulerian]
  have hrem : ∀ k, (0 : ℝ[X]).natDegree ≤
      (generalizedEulerian c 0).natDegree + k := by
    intro k
    simp
  have hfactor : ∀ k,
      (-c) * (((generalizedEulerian c 0).natDegree + k : ℕ) : ℝ) +
          (c * (k : ℝ) + 1) ≠ 0 := by
    intro k
    simp [generalizedEulerian]
  have hresult :=
    Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_recurrence_of_ne_zero
      (generalizedEulerian c) (fun _ => 0) (fun _ => c) (fun _ => -c)
        (fun _ => 1) (fun k => c * (k : ℝ) + 1) hrec hseed hrem hfactor n
  constructor
  · simpa [generalizedEulerian] using hresult.1
  · change (generalizedEulerian c n).leadingCoeff = 1
    simpa [generalizedEulerian] using hresult.2

/-- Degree of a generalized Eulerian polynomial, for every real parameter. -/
theorem generalizedEulerian_natDegree (c : ℝ) (n : ℕ) :
    (generalizedEulerian c n).natDegree = n :=
  (generalizedEulerian_degree_and_monic c n).1

/-- Monicity of a generalized Eulerian polynomial, for every real parameter. -/
theorem generalizedEulerian_monic (c : ℝ) (n : ℕ) :
    (generalizedEulerian c n).Monic :=
  (generalizedEulerian_degree_and_monic c n).2

@[simp] lemma coeff_zero_generalizedEulerian (c : ℝ) (n : ℕ) :
    (generalizedEulerian c n).coeff 0 = 1 := by
  induction n with
  | zero => simp [generalizedEulerian]
  | succ n ih =>
      rw [generalizedEulerian_succ]
      simpa using ih

lemma coeff_generalizedEulerian_succ (c : ℝ) (n k : ℕ) :
    (generalizedEulerian c (n + 1)).coeff (k + 1) =
      (1 + c * ((k : ℝ) + 1)) * (generalizedEulerian c n).coeff (k + 1)
        + (1 + c * ((n : ℝ) - (k : ℝ))) *
          (generalizedEulerian c n).coeff k := by
  rw [generalizedEulerian_succ]
  rw [show (1 + C (c * (n : ℝ) + 1) * X) * generalizedEulerian c n =
      generalizedEulerian c n +
        C (c * (n : ℝ) + 1) * (X * generalizedEulerian c n) by ring]
  rw [show C c * X * (1 - X) * (generalizedEulerian c n).derivative =
      C c * (X * (generalizedEulerian c n).derivative)
        - C c * (X ^ 2 * (generalizedEulerian c n).derivative) by ring]
  simp only [coeff_add, coeff_sub, coeff_C_mul]
  rw [coeff_X_mul, coeff_X_mul, coeff_X_pow_mul']
  by_cases hk : k = 0
  · subst k
    norm_num [coeff_derivative]
    ring
  · rw [if_pos (by lia : 2 ≤ k + 1), coeff_derivative]
    rw [coeff_derivative]
    have hidx : k + 1 - 2 + 1 = k := by lia
    rw [hidx]
    have hcast : ((k + 1 - 2 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      exact_mod_cast hidx
    grind

/-- Positive-parameter generalized Eulerian polynomials have the expected
degree, nonnegative coefficients, and only real roots. -/
lemma generalizedEulerian_invariants (hc : 0 < c) :
    ∀ n : ℕ,
      (generalizedEulerian c n).natDegree = n ∧
        HasNonnegCoeffs (generalizedEulerian c n) ∧
          (generalizedEulerian c n).Splits := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp [generalizedEulerian]
      · constructor
        · exact hasNonnegCoeffs_one
        · change (1 : ℝ[X]).Splits
          simp
  | succ n ih =>
      rcases ih with ⟨hdeg, hnn, hsplits⟩
      have htop : 0 < (generalizedEulerian c n).coeff n := by
        rw [show (generalizedEulerian c n).coeff n =
          (generalizedEulerian c n).leadingCoeff by rw [leadingCoeff, hdeg]]
        exact hnn.pos_leadingCoeff (by
          intro hz
          have hz0 := coeff_zero_generalizedEulerian c n
          simp_all)
      have hdeg_next : (generalizedEulerian c (n + 1)).natDegree = n + 1 :=
        generalizedEulerian_natDegree c (n + 1)
      have hnn_next : HasNonnegCoeffs (generalizedEulerian c (n + 1)) := by
        intro k
        cases k with
        | zero =>
            simp
        | succ k =>
            rw [coeff_generalizedEulerian_succ]
            have hk := hnn (k + 1)
            have hk' := hnn k
            by_cases hkn : k ≤ n
            · have hfactor : 0 ≤ 1 + c * ((n : ℝ) - (k : ℝ)) := by
                have hle : (k : ℝ) ≤ (n : ℝ) := by simp_all
                have hdiff : 0 ≤ (n : ℝ) - (k : ℝ) := sub_nonneg.mpr hle
                nlinarith [mul_nonneg hc.le hdiff]
              exact add_nonneg (mul_nonneg (by positivity) hk) (mul_nonneg hfactor hk')
            · have hkzero : (generalizedEulerian c n).coeff (k + 1) = 0 :=
                coeff_eq_zero_of_natDegree_lt (by lia)
              have hkzero' : (generalizedEulerian c n).coeff k = 0 :=
                coeff_eq_zero_of_natDegree_lt (by lia)
              simp_all
      have hsplits_next : (generalizedEulerian c (n + 1)).Splits := by
        cases n with
        | zero =>
            have heq : generalizedEulerian c 1 = (1 + X : ℝ[X]) := by
              simp [generalizedEulerian]
            rw [heq]
            exact Polynomial.Splits.of_natDegree_le_one (by simp_all)
        | succ n =>
            let f := generalizedEulerian c (n + 1)
            let a : ℝ := (n + 1 : ℝ) + 1 / c
            let g := C a * f + (1 - X) * f.derivative
            have hfdeg : f.natDegree = n + 1 := hdeg
            have hf0 : f ≠ 0 := by
              intro hf
              simp_all
            have ha : (f.natDegree : ℝ) < a := by
              dsimp only [a]
              simp_all
            have hgf : Prec g f := by
              exact prec_affine_derivative_of_nonnegCoeffs hsplits
                (by lia) hnn ha
            have hgroots : ∀ r ∈ g.roots, r ≤ 0 :=
              roots_le_of_prec_right hgf
                (roots_nonpos_of_nonneg_coeffs hsplits hnn)
            have hgpos : HasPosLeadingCoeff g := by
              unfold HasPosLeadingCoeff
              dsimp only [g]
              rw [leadingCoeff_affineDeriv hf0 (by lia) (ne_of_gt ha)]
              exact mul_pos (sub_pos.mpr ha) (hnn.pos_leadingCoeff hf0)
            have hgnn : HasNonnegCoeffs g :=
              ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos
                (left_splits_of_prec hgf)).mpr ⟨hgpos, hgroots⟩).1
            have hshift : Prec f (X * g) :=
              prec_mul_X_of_prec_of_nonneg hgf hgnn hnn
            have hcombo := allComboRealRooted_of_prec hshift (1 : ℝ) c
            have hrewrite :
                generalizedEulerian c (n + 2) = C 1 * f + C c * (X * g) := by
              rw [generalizedEulerian_succ]
              grind
            simp_all
      simp_all

theorem generalizedEulerian_splits (hc : 0 < c) (n : ℕ) :
    (generalizedEulerian c n).Splits :=
  (generalizedEulerian_invariants hc n).2.2

/-- The leading coefficient of an ordinary Eulerian polynomial is one. -/
theorem coeff_top_generalizedEulerian_one : ∀ n : ℕ,
    (generalizedEulerian 1 n).coeff n = 1 := by
  intro n
  have hdeg := generalizedEulerian_natDegree 1 n
  rw [show (generalizedEulerian 1 n).coeff n =
    (generalizedEulerian 1 n).leadingCoeff by
      rw [leadingCoeff, hdeg]]
  exact generalizedEulerian_monic 1 n

/-- The coefficients of an ordinary Eulerian polynomial are palindromic. -/
theorem coeff_symm_generalizedEulerian_one : ∀ n i j : ℕ, i + j = n →
    (generalizedEulerian 1 n).coeff i = (generalizedEulerian 1 n).coeff j := by
  intro n
  induction n with
  | zero =>
      intro i j hij
      have hi : i = 0 := by lia
      have hj : j = 0 := by lia
      rw [hi, hj]
  | succ n ih =>
      intro i j hij
      match i, j with
      | 0, j =>
          have hj : j = n + 1 := by lia
          rw [hj, coeff_zero_generalizedEulerian, coeff_top_generalizedEulerian_one]
      | i, 0 =>
          have hi : i = n + 1 := by lia
          rw [hi, coeff_zero_generalizedEulerian, coeff_top_generalizedEulerian_one]
      | i' + 1, j' + 1 =>
          have hn : 1 ≤ n := by lia
          have hsum : i' + j' = n - 1 := by lia
          have hleft := coeff_generalizedEulerian_succ 1 n i'
          have hright := coeff_generalizedEulerian_succ 1 n j'
          have hcross_left :
              (generalizedEulerian 1 n).coeff (i' + 1) =
                (generalizedEulerian 1 n).coeff j' :=
            ih (i' + 1) j' (by lia)
          have hcross_right :
              (generalizedEulerian 1 n).coeff i' =
                (generalizedEulerian 1 n).coeff (j' + 1) :=
            ih i' (j' + 1) (by lia)
          rw [hleft, hright, hcross_left, hcross_right]
          have hcast : (i' : ℝ) + (j' : ℝ) = (n : ℝ) - 1 := by
            have hcast' : ((i' + j' : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) := by
              exact_mod_cast hsum
            push_cast [Nat.cast_sub hn] at hcast'
            linarith
          have hfactor_left :
              (1 : ℝ) + 1 * ((i' : ℝ) + 1) = 1 + 1 * ((n : ℝ) - (j' : ℝ)) := by
            linarith
          have hfactor_right :
              (1 : ℝ) + 1 * ((n : ℝ) - (i' : ℝ)) = 1 + 1 * ((j' : ℝ) + 1) := by
            linarith
          rw [hfactor_left, hfactor_right]
          ring

/-- Reflection through the degree fixes every ordinary Eulerian polynomial. -/
theorem generalizedEulerian_one_reflect (n : ℕ) :
    Polynomial.reflect n (generalizedEulerian 1 n) = generalizedEulerian 1 n := by
  ext i
  rw [coeff_reflect]
  by_cases hi : i ≤ n
  · rw [revAt_le hi]
    exact coeff_symm_generalizedEulerian_one n (n - i) i (Nat.sub_add_cancel hi)
  · rw [revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]

/-- Reciprocal evaluation identity for ordinary Eulerian polynomials. -/
theorem eval_recip_generalizedEulerian_one (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (generalizedEulerian 1 n).eval x =
      x ^ n * (generalizedEulerian 1 n).eval (1 / x) := by
  letI : Invertible x := invertibleOfNonzero hx
  have hdeg : (generalizedEulerian 1 n).natDegree ≤ n :=
    (generalizedEulerian_natDegree 1 n).le
  have heval := Polynomial.eval₂_reflect_mul_pow
    (i := RingHom.id ℝ) (x := x) n (generalizedEulerian 1 n) hdeg
  rw [generalizedEulerian_one_reflect] at heval
  simpa [Polynomial.eval₂_id, invOf_eq_inv, one_div, mul_comm] using heval.symm

end RealRooted
