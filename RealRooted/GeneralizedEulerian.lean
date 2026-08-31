import RealRooted.ObreschkoffConverse
import RealRooted.SequenceClosure
import RealRooted.WagnerX.NonnegativeRoots
import Mathlib.Tactic

/-!
# Generalized Eulerian polynomials

The parameterized Eulerian differential recurrence and its real-rootedness,
degree, and coefficient-positivity invariants.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Eulerian differential polynomials with a positive real dilation parameter. -/
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
      have hdeg_next : (generalizedEulerian c (n + 1)).natDegree = n + 1 := by
        apply natDegree_eq_of_le_of_coeff_ne_zero
        · rw [natDegree_le_iff_coeff_eq_zero]
          intro k hk
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
          rw [coeff_generalizedEulerian_succ]
          have hzero : (generalizedEulerian c n).coeff (j + 1) = 0 :=
            coeff_eq_zero_of_natDegree_lt (by lia)
          have hzero' : (generalizedEulerian c n).coeff j = 0 :=
            coeff_eq_zero_of_natDegree_lt (by lia)
          simp_all
        · rw [coeff_generalizedEulerian_succ]
          have hzero : (generalizedEulerian c n).coeff (n + 1) = 0 :=
            coeff_eq_zero_of_natDegree_lt (by lia)
          grind
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

end RealRooted
