import RealRooted.Basic
import RealRooted.Derivative
import RealRooted.Wagner
import RealRooted.AffineDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic
import RealRooted.Mathlib.Algebra.Polynomial.Basic

/-!
# Derangement Excedance Polynomials

Sturm-sequence and real-rootedness facts for derangement excedance polynomials,
using `X` for the polynomial variable.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The derangement excedance recurrence, viewed as a candidate Sturm sequence. -/
def sturmDerangementsExc : Nat → ℝ[X]
  | 0 => 0
  | 1 => 0
  | 2 => X
  | n + 3 =>
      X * (((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1) +
        ((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2) +
        (1 - X) * (sturmDerangementsExc (n + 2)).derivative)

@[simp] lemma sturmDerangementsExc_zero : sturmDerangementsExc 0 = 0 := rfl

@[simp] lemma sturmDerangementsExc_one : sturmDerangementsExc 1 = 0 := rfl

@[simp] lemma sturmDerangementsExc_two : sturmDerangementsExc 2 = X := rfl

lemma sturmDerangementsExc_recurrence (n : Nat) :
    sturmDerangementsExc (n + 3) =
      X * (((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1) +
        ((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2) +
        (1 - X) * (sturmDerangementsExc (n + 2)).derivative) := rfl

/-- The affine derivative block appearing in the derangement recurrence. -/
def affineSturmDerangementsExc (n : Nat) : ℝ[X] :=
  C (n : ℝ) * sturmDerangementsExc n + (1 - X) * (sturmDerangementsExc n).derivative

/-- The full recurrence core before the outer `X` factor:
`n * P_{n-1} + (n * P_n + (1 - X) P'_n)`. -/
def recurrenceCoreSturmDerangementsExc (n : Nat) : ℝ[X] :=
  C (n : ℝ) * sturmDerangementsExc (n - 1) + affineSturmDerangementsExc n

lemma sturmDerangementsExc_succ_eq_X_mul_recurrenceCore (n : Nat) (hn : 2 ≤ n) :
    sturmDerangementsExc (n + 1) = X * recurrenceCoreSturmDerangementsExc n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [recurrenceCoreSturmDerangementsExc, affineSturmDerangementsExc,
    add_assoc, add_left_comm, add_comm, ofNat_def] using sturmDerangementsExc_recurrence k

/-- If `f` is real-rooted with nonnegative coefficients, then the derivative term
`(1 - X) * f'` sits on the "right" of `f` in the oriented `Prec` relation. -/
lemma prec_one_sub_X_derivative_right {f : ℝ[X]} (hf : f.Splits) (hdeg : 2 ≤ f.natDegree)
    (hnn : HasNonnegCoeffs f) :
    Prec f ((1 - X) * f.derivative) := by
  have hder : Prec f.derivative f := (derivative_interlaces hf hdeg).toPrec
  have hnn' : HasNonnegCoeffs f.derivative := hnn.derivative
  have hf'_pos : HasPosLeadingCoeff f.derivative := hnn'.pos_leadingCoeff hder.1.1
  have hf_pos : HasPosLeadingCoeff f := hnn.pos_leadingCoeff <| by rintro rfl; simp at hdeg
  have hf_le1 : ∀ s ∈ f.roots, s ≤ 1 := by
    intro s hs
    linarith [roots_nonpos_of_nonneg_coeffs hf hnn s hs]
  have hf'_le1 : ∀ s ∈ f.derivative.roots, s ≤ 1 := by
    intro s hs
    linarith [roots_nonpos_of_nonneg_coeffs hder.1.2 hnn' s hs]
  have hdeg' : f.derivative.natDegree + 1 = f.natDegree := by grind [f.natDegree_derivative]
  have hmain : Prec f ((X - C 1) * f.derivative) :=
    (prec_iff_prec_mul_X_sub_C_of_roots_le 1 hder.1.2 hf hf'_pos hf_pos hf'_le1 hf_le1 hdeg').mp
      hder
  have hscaled : Prec f (C (-1) * ((X - C 1) * f.derivative)) :=
    prec_C_mul_right hmain (by simp)
  grind

/-- Every derangement excedance polynomial has `X` as a factor. In the original variable,
this says every `P_n` is divisible by `t`. -/
lemma X_dvd_sturmDerangementsExc : ∀ n : Nat, X ∣ sturmDerangementsExc n
  | 0 => ⟨0, by simp [sturmDerangementsExc]⟩
  | 1 => ⟨0, by simp [sturmDerangementsExc]⟩
  | 2 => ⟨1, by simp [sturmDerangementsExc]⟩
  | n + 3 =>
      ⟨((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1) +
        ((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2) +
        (1 - X) * (sturmDerangementsExc (n + 2)).derivative, by
        simp [sturmDerangementsExc]⟩

/-- Equivalently, `0` is a root of every derangement excedance polynomial. -/
lemma sturmDerangementsExc_isRoot_zero (n : Nat) : (sturmDerangementsExc n).IsRoot 0 := by
  rcases X_dvd_sturmDerangementsExc n with ⟨q, hq⟩
  simp_all

lemma sturmDerangementsExc_three :
    sturmDerangementsExc 3 = X ^ 2 + X := by
  rw [sturmDerangementsExc_recurrence 0]
  simp
  grind

lemma sturmDerangementsExc_four :
    sturmDerangementsExc 4 = X ^ 3 + 7 * X ^ 2 + X := by
  rw [sturmDerangementsExc_recurrence 1, sturmDerangementsExc_three]
  simp
  grind

lemma sturmDerangementsExc_five :
    sturmDerangementsExc 5 = X ^ 4 + 21 * X ^ 3 + 21 * X ^ 2 + X := by
  have hC2 : (C (2 : ℝ) : ℝ[X]) = 2 := (ofNat_def 2).symm
  rw [sturmDerangementsExc_recurrence 2, sturmDerangementsExc_three, sturmDerangementsExc_four]
  simp only [Nat.cast_ofNat, derivative_X_pow_succ, map_add, map_one,
    derivative_mul, derivative_ofNat, zero_mul, Nat.cast_one, pow_one, zero_add, derivative_X]
  grind

lemma coeff_sturmDerangementsExc_succ (n m : Nat) :
    coeff (sturmDerangementsExc (n + 3)) (m + 1) =
      (n + 2 : ℝ) * coeff (sturmDerangementsExc (n + 1)) m +
      ((n + 2 : ℝ) - m) * coeff (sturmDerangementsExc (n + 2)) m +
      (m + 1 : ℝ) * coeff (sturmDerangementsExc (n + 2)) (m + 1) := by
  rw [sturmDerangementsExc_recurrence, coeff_X_mul]
  simp only [coeff_add, coeff_one_sub_X_mul_derivative]
  have h₁ :
      (((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 1)).coeff m =
        (n + 2 : ℝ) * (sturmDerangementsExc (n + 1)).coeff m := by
    simpa [ofNat_def] using
      (coeff_C_mul (n := m) (a := (n + 2 : ℝ)) (p := sturmDerangementsExc (n + 1)))
  have h₂ :
      (((n + 2 : ℝ[X])) * sturmDerangementsExc (n + 2)).coeff m =
        (n + 2 : ℝ) * (sturmDerangementsExc (n + 2)).coeff m := by
    simpa [ofNat_def] using
      (coeff_C_mul (n := m) (a := (n + 2 : ℝ)) (p := sturmDerangementsExc (n + 2)))
  grind

lemma coeff_sturmDerangementsExc_top_and_above :
    ∀ n : Nat, 2 ≤ n →
      coeff (sturmDerangementsExc n) (n - 1) = 1 ∧
      ∀ m > n - 1, coeff (sturmDerangementsExc n) m = 0
  | 0, h => by lia
  | 1, h => by lia
  | 2, _ => by
      constructor
      · simp [sturmDerangementsExc_two]
      · intro m hm
        have hm' : 1 < m := by lia
        rw [sturmDerangementsExc_two]
        simp [coeff_X, Nat.ne_of_lt hm']
  | 3, _ => by
      constructor
      · rw [sturmDerangementsExc_three]
        norm_num [coeff_X_pow, coeff_X]
      · intro m hm
        have hm' : 2 < m := by lia
        rw [sturmDerangementsExc_three]
        have hX2 : coeff (X ^ 2 : ℝ[X]) m = 0 := by
          grind
        have hX : coeff (X : ℝ[X]) m = 0 := by
          have hm1 : m ≠ 1 := by lia
          have hm1' : ¬1 = m := by lia
          simp [coeff_X, hm1']
        simp [hX2, hX]
  | n + 4, _ => by
      rcases coeff_sturmDerangementsExc_top_and_above (n + 2) (by lia) with
        ⟨hsmall_top, hsmall_hi⟩
      rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨hbig_top, hbig_hi⟩
      constructor
      · have hsmall_zero : coeff (sturmDerangementsExc (n + 2)) (n + 2) = 0 :=
          hsmall_hi (n + 2) (by lia)
        have hbig_zero : coeff (sturmDerangementsExc (n + 3)) (n + 3) = 0 :=
          hbig_hi (n + 3) (by lia)
        have hbig_top' : coeff (sturmDerangementsExc (n + 3)) (n + 2) = 1 := by
          lia
        have htop :
            coeff (sturmDerangementsExc (n + 4)) (n + 3) = 1 := by
          rw [coeff_sturmDerangementsExc_succ (n + 1) (n + 2)]
          simp [hsmall_zero, hbig_top', hbig_zero]
        lia
      · intro m hm
        cases m with
        | zero =>
            lia
        | succ m =>
            have hsmall_zero : coeff (sturmDerangementsExc (n + 2)) m = 0 := by
              grind
            have hbig_zero₁ : coeff (sturmDerangementsExc (n + 3)) m = 0 := by
              grind
            have hbig_zero₂ : coeff (sturmDerangementsExc (n + 3)) (m + 1) = 0 := by
              grind
            rw [coeff_sturmDerangementsExc_succ (n + 1) m]
            simp [hsmall_zero, hbig_zero₁, hbig_zero₂]

lemma coeff_sturmDerangementsExc_symm :
    ∀ n : Nat, ∀ m ≤ n, coeff (sturmDerangementsExc n) m = coeff (sturmDerangementsExc n) (n - m)
  | 0, m, hm => by
      lia
  | 1, m, hm => by
      simp
  | 2, m, hm => by
      have hm0 : m = 0 ∨ m = 1 ∨ m = 2 := by lia
      rcases hm0 with rfl | rfl | rfl <;> simp [sturmDerangementsExc_two, coeff_X]
  | n + 3, 0, hm => by
      have hcoeff0 : coeff (sturmDerangementsExc (n + 3)) 0 = 0 := by
        rcases X_dvd_sturmDerangementsExc (n + 3) with ⟨q, hq⟩
        simp [hq]
      have hcoeff_hi : coeff (sturmDerangementsExc (n + 3)) (n + 3) = 0 := by
        rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨_, habove⟩
        simp_all
      lia
  | n + 3, m + 1, hm => by
      by_cases htop : m + 1 = n + 3
      · have hcoeff_hi : coeff (sturmDerangementsExc (n + 3)) (m + 1) = 0 := by
          rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨_, habove⟩
          simp_all
        have hcoeff0 : coeff (sturmDerangementsExc (n + 3)) 0 = 0 := by
          rcases X_dvd_sturmDerangementsExc (n + 3) with ⟨q, hq⟩
          simp [hq]
        simp_all
      · have hm_le : m ≤ n + 1 := by lia
        have hm_succ_le : m + 1 ≤ n + 2 := by lia
        have hsub : n + 2 - (m + 1) = n + 1 - m := by lia
        have hidx : (n + 1 - m) + 1 = n + 2 - m := by lia
        have hgoal : n + 3 - (m + 1) = n + 2 - m := by lia
        have hs1 :=
          coeff_sturmDerangementsExc_symm (n + 1) m hm_le
        have hs2m :=
          coeff_sturmDerangementsExc_symm (n + 2) m (by lia)
        have hs2m1 :
            coeff (sturmDerangementsExc (n + 2)) (m + 1) =
              coeff (sturmDerangementsExc (n + 2)) (n + 1 - m) := by
          simpa [hsub] using
            coeff_sturmDerangementsExc_symm (n + 2) (m + 1) hm_succ_le
        have hrec1 := coeff_sturmDerangementsExc_succ n m
        have hrec2 :
            coeff (sturmDerangementsExc (n + 3)) (n + 2 - m) =
              (n + 2 : ℝ) * coeff (sturmDerangementsExc (n + 1)) (n + 1 - m) +
              ((n + 2 : ℝ) - ↑(n + 1 - m)) * coeff (sturmDerangementsExc (n + 2)) (n + 1 - m) +
              (((n + 1 - m : Nat) : ℝ) + 1) * coeff (sturmDerangementsExc (n + 2)) (n + 2 - m) := by
          simpa [hidx] using coeff_sturmDerangementsExc_succ n (n + 1 - m)
        rw [hgoal, hrec1, hrec2, hs1, hs2m, hs2m1]
        have hcast1 : (((n + 1 - m : Nat) : ℝ)) = (n + 1 : ℝ) - m := by
          simp_all
        grind

lemma natDegree_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (sturmDerangementsExc n).natDegree = n - 1 := by
  rcases coeff_sturmDerangementsExc_top_and_above n hn with ⟨htop, habove⟩
  exact natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr (fun m hm => habove m hm))
    (by simp_all)

lemma monic_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (sturmDerangementsExc n).Monic := by
  rcases coeff_sturmDerangementsExc_top_and_above n hn with ⟨htop, _⟩
  rw [Monic.def, leadingCoeff, natDegree_sturmDerangementsExc hn]
  lia

lemma sturmDerangementsExc_ne_zero {n : Nat} (hn : 2 ≤ n) :
    sturmDerangementsExc n ≠ 0 :=
  (monic_sturmDerangementsExc hn).ne_zero

lemma sturmDerangementsExc_posLeadingCoeff {n : Nat} (hn : 2 ≤ n) :
    HasPosLeadingCoeff (sturmDerangementsExc n) := by
  simp [HasPosLeadingCoeff, (monic_sturmDerangementsExc hn).leadingCoeff]

lemma natDegree_le_sturmDerangementsExc (n : Nat) :
    (sturmDerangementsExc n).natDegree ≤ n := by
  cases n with
  | zero =>
      simp [sturmDerangementsExc_zero]
  | succ n =>
      cases n with
      | zero =>
          simp [sturmDerangementsExc_one]
      | succ n =>
          rw [natDegree_sturmDerangementsExc (by lia)]
          lia

lemma reflect_sturmDerangementsExc (n : Nat) :
    Polynomial.reflect n (sturmDerangementsExc n) = sturmDerangementsExc n := by
  ext m
  rw [Polynomial.coeff_reflect]
  by_cases hm : m ≤ n
  · rw [Polynomial.revAt_le hm, coeff_sturmDerangementsExc_symm n m hm]
  · rw [Polynomial.revAt_eq_self_of_lt (lt_of_not_ge hm)]

lemma eval_neg_one_mul_neg_one_pow_sturmDerangementsExc (n : Nat) :
    (sturmDerangementsExc n).eval (-1) * (-1 : ℝ) ^ n = (sturmDerangementsExc n).eval (-1) := by
  letI : Invertible (-1 : ℝ) := invertibleOfNonzero (by simp)
  simpa [reflect_sturmDerangementsExc n] using
    (Polynomial.eval₂_reflect_mul_pow (i := RingHom.id ℝ) (x := (-1 : ℝ)) n
      (sturmDerangementsExc n) (natDegree_le_sturmDerangementsExc n))

lemma sturmDerangementsExc_isRoot_neg_one_of_odd {n : Nat} (hn : Odd n) :
    (sturmDerangementsExc n).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def]
  have h := eval_neg_one_mul_neg_one_pow_sturmDerangementsExc n
  rw [hn.neg_one_pow] at h
  linarith

lemma X_add_one_dvd_sturmDerangementsExc_of_odd {n : Nat} (hn : Odd n) :
    X + 1 ∣ sturmDerangementsExc n :=
  by simpa [sub_eq_add_neg, add_comm] using
    (dvd_iff_isRoot).2 (sturmDerangementsExc_isRoot_neg_one_of_odd hn)

lemma sturmDerangementsExc_nonnegCoeffs : ∀ n : Nat, HasNonnegCoeffs (sturmDerangementsExc n)
  | 0 => by
      intro m
      simp [sturmDerangementsExc]
  | 1 => by
      intro m
      simp [sturmDerangementsExc]
  | 2 => by
      intro m
      by_cases hm : m = 1
      · simp_all
      · have hm' : 1 ≠ m := by lia
        simp [sturmDerangementsExc_two, coeff_X, hm']
  | 3 => by
      intro m
      by_cases hm2 : m = 2
      · subst hm2
        norm_num [sturmDerangementsExc_three, coeff_X_pow, coeff_X]
      · by_cases hm1 : m = 1
        · subst hm1
          norm_num [sturmDerangementsExc_three, coeff_X_pow, coeff_X, hm2]
        · have hm2' : 2 ≠ m := by lia
          have hm1' : 1 ≠ m := by lia
          simp [sturmDerangementsExc_three, coeff_X_pow, coeff_X, hm2, hm1']
  | n + 4 => by
      rintro (_ | m)
      · rw [sturmDerangementsExc_recurrence (n + 1)]
        simp
      · have hcoeff :
            coeff (sturmDerangementsExc (n + 4)) (m + 1) =
              (n + 1 : ℝ) * coeff (sturmDerangementsExc (n + 2)) m +
              (n + 1 : ℝ) * coeff (sturmDerangementsExc (n + 3)) m +
              (coeff (sturmDerangementsExc (n + 2)) m * 2 -
                (m : ℝ) * coeff (sturmDerangementsExc (n + 3)) m) +
              (m : ℝ) * coeff (sturmDerangementsExc (n + 3)) (m + 1) +
              coeff (sturmDerangementsExc (n + 3)) m * 2 +
              coeff (sturmDerangementsExc (n + 3)) (m + 1) := by
          have h := coeff_sturmDerangementsExc_succ (n + 1) m
          grind
        rw [hcoeff]
        by_cases hm : m ≤ n + 2
        · have h₁ : 0 ≤ coeff (sturmDerangementsExc (n + 2)) m :=
            sturmDerangementsExc_nonnegCoeffs (n + 2) m
          have h₂ : 0 ≤ coeff (sturmDerangementsExc (n + 3)) m :=
            sturmDerangementsExc_nonnegCoeffs (n + 3) m
          have h₃ : 0 ≤ coeff (sturmDerangementsExc (n + 3)) (m + 1) :=
            sturmDerangementsExc_nonnegCoeffs (n + 3) (m + 1)
          have hm' : (m : ℝ) ≤ n + 3 := by
            have hmNat : m ≤ n + 3 := le_trans hm (Nat.le_succ _)
            exact_mod_cast hmNat
          have hcoef : 0 ≤ ((n + 3 : ℝ) - m) := by
            linarith
          nlinarith
        · have hm' : n + 2 < m := lt_of_not_ge hm
          rcases coeff_sturmDerangementsExc_top_and_above (n + 2) (by lia) with ⟨_, hsmall_hi⟩
          rcases coeff_sturmDerangementsExc_top_and_above (n + 3) (by lia) with ⟨_, hbig_hi⟩
          grind

lemma roots_nonpos_sturmDerangementsExc_of_isRealRooted {n : Nat}
    (hrr : (sturmDerangementsExc n).Splits) :
    ∀ r ∈ (sturmDerangementsExc n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hrr (sturmDerangementsExc_nonnegCoeffs n)

lemma prec_lowerTerm_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n)
    (hprec : Prec (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    Prec (C (n : ℝ) * sturmDerangementsExc (n - 1)) (sturmDerangementsExc n) :=
  prec_C_mul_left hprec (by exact_mod_cast (show n ≠ 0 by lia))

lemma prec_affine_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n)
    (hrr : (sturmDerangementsExc n).Splits) :
    Prec (affineSturmDerangementsExc n) (sturmDerangementsExc n) := by
  apply prec_affine_derivative'
  · lia
  · rw [natDegree_sturmDerangementsExc hn]
    lia
  · exact sturmDerangementsExc_posLeadingCoeff hn
  · exact roots_nonpos_sturmDerangementsExc_of_isRealRooted hrr
  · rw [natDegree_sturmDerangementsExc hn]
    exact_mod_cast (Nat.sub_lt (by lia) (by lia))

lemma natDegree_affine_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (affineSturmDerangementsExc n).natDegree = (sturmDerangementsExc n).natDegree := by
  refine natDegree_affineDeriv (sturmDerangementsExc_ne_zero hn) ?_ ?_
  · rw [natDegree_sturmDerangementsExc hn]
    lia
  · rw [natDegree_sturmDerangementsExc hn]
    have hn0 : 0 < n := by lia
    have hlt : ((n - 1 : Nat) : ℝ) < n := by
      simp_all
    linarith

lemma affine_sturmDerangementsExc_nonnegCoeffs {n : Nat} (hn : 2 ≤ n) :
    HasNonnegCoeffs (affineSturmDerangementsExc n) := by
  intro m
  rw [affineSturmDerangementsExc]
  rw [coeff_add]
  rw [show coeff (C (n : ℝ) * sturmDerangementsExc n) m =
      (n : ℝ) * coeff (sturmDerangementsExc n) m by
      simp]
  rw [coeff_one_sub_X_mul_derivative]
  by_cases hm : m ≤ n
  · have hcoeff_m : 0 ≤ coeff (sturmDerangementsExc n) m :=
      sturmDerangementsExc_nonnegCoeffs n m
    have hcoeff_succ : 0 ≤ coeff (sturmDerangementsExc n) (m + 1) :=
      sturmDerangementsExc_nonnegCoeffs n (m + 1)
    have hnm : 0 ≤ (n : ℝ) - m := by
      simp_all
    nlinarith
  · have hm' : n < m := lt_of_not_ge hm
    rcases coeff_sturmDerangementsExc_top_and_above n hn with ⟨_, habove⟩
    have hcoeff_m : coeff (sturmDerangementsExc n) m = 0 := by
      grind
    have hcoeff_succ : coeff (sturmDerangementsExc n) (m + 1) = 0 := by
      grind
    simp [hcoeff_m, hcoeff_succ]

lemma affine_sturmDerangementsExc_isRoot_neg_one_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    (affineSturmDerangementsExc n).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def]
  rcases hn with ⟨k, rfl⟩
  have hk : 1 ≤ k := by lia
  set A : ℝ[X] := affineSturmDerangementsExc (k + k)
  change A.eval (-1) = 0
  have hprev_odd : Odd ((k + k) - 1) := ⟨k - 1, by lia⟩
  have hnext_odd : Odd (k + k + 1) := ⟨k, by lia⟩
  have hprev0 : (sturmDerangementsExc (k + k - 1)).eval (-1) = 0 :=
    Polynomial.IsRoot.def.mp (sturmDerangementsExc_isRoot_neg_one_of_odd hprev_odd)
  have hnext0 : (sturmDerangementsExc (k + k + 1)).eval (-1) = 0 :=
    Polynomial.IsRoot.def.mp (sturmDerangementsExc_isRoot_neg_one_of_odd hnext_odd)
  have hk1 : k + k - 2 + 1 = k + k - 1 := by lia
  have hk2 : k + k - 2 + 2 = k + k := by lia
  have hk3 : k + k - 2 + 3 = k + k + 1 := by lia
  have hrec_eval :
      0 =
        -(((↑(k + k - 2) : ℝ) + 2) * (sturmDerangementsExc (k + k)).eval (-1) +
          (1 + 1 : ℝ) * (sturmDerangementsExc (k + k)).derivative.eval (-1)) := by
    simpa [hk1, hk2, hk3, Polynomial.eval_add, Polynomial.eval_mul, hprev0, hnext0]
      using congrArg (fun p : ℝ[X] => p.eval (-1))
        (sturmDerangementsExc_recurrence (k + k - 2))
  have hcoef : ((↑(k + k - 2) : ℝ) + 2) = (k + k : ℝ) := by
    simp_all
  rw [hcoef] at hrec_eval
  have hA_eval :
      A.eval (-1) =
        (k + k : ℝ) * (sturmDerangementsExc (k + k)).eval (-1) +
          (1 + 1 : ℝ) * (sturmDerangementsExc (k + k)).derivative.eval (-1) := by
    simp [A, affineSturmDerangementsExc]
  grind

lemma X_add_one_dvd_affine_sturmDerangementsExc_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    X + 1 ∣ affineSturmDerangementsExc n :=
  by simpa [sub_eq_add_neg, add_comm] using
    (dvd_iff_isRoot).2 (affine_sturmDerangementsExc_isRoot_neg_one_of_even hn h2)

lemma X_add_one_dvd_recurrenceCoreSturmDerangementsExc_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    X + 1 ∣ recurrenceCoreSturmDerangementsExc n := by
  rw [recurrenceCoreSturmDerangementsExc]
  apply dvd_add
  · have hodd : Odd (n - 1) := by
      grind
    exact dvd_mul_of_dvd_right (X_add_one_dvd_sturmDerangementsExc_of_odd hodd) (C (n : ℝ))
  · exact X_add_one_dvd_affine_sturmDerangementsExc_of_even hn h2

lemma exists_recurrenceCoreSturmDerangementsExc_eq_X_add_one_mul_of_even {n : Nat}
    (hn : Even n) (h2 : 2 ≤ n) :
    ∃ q : ℝ[X], recurrenceCoreSturmDerangementsExc n = (X + 1) * q := by
  rcases X_add_one_dvd_recurrenceCoreSturmDerangementsExc_of_even hn h2 with ⟨q, hq⟩
  simp_all

lemma recurrenceCoreSturmDerangementsExc_nonnegCoeffs {n : Nat} (hn : 2 ≤ n) :
    HasNonnegCoeffs (recurrenceCoreSturmDerangementsExc n) := by
  rw [recurrenceCoreSturmDerangementsExc]
  intro m
  have hscalar :
      0 ≤ (C (n : ℝ) * sturmDerangementsExc (n - 1)).coeff m := by
    rw [coeff_C_mul]
    exact mul_nonneg (by simp) (sturmDerangementsExc_nonnegCoeffs (n - 1) m)
  exact add_nonneg hscalar (affine_sturmDerangementsExc_nonnegCoeffs hn m)

lemma recurrenceCoreSturmDerangementsExc_ne_zero {n : Nat} (hn : 2 ≤ n) :
    recurrenceCoreSturmDerangementsExc n ≠ 0 := by
  have hsucc_ne : sturmDerangementsExc (n + 1) ≠ 0 :=
    sturmDerangementsExc_ne_zero (by lia)
  rw [sturmDerangementsExc_succ_eq_X_mul_recurrenceCore n hn] at hsucc_ne
  simp_all

lemma natDegree_recurrenceCoreSturmDerangementsExc {n : Nat} (hn : 2 ≤ n) :
    (recurrenceCoreSturmDerangementsExc n).natDegree = n - 1 := by
  have hcore_ne : recurrenceCoreSturmDerangementsExc n ≠ 0 :=
    recurrenceCoreSturmDerangementsExc_ne_zero hn
  have hdeg :=
    congrArg Polynomial.natDegree (sturmDerangementsExc_succ_eq_X_mul_recurrenceCore n hn)
  rw [natDegree_sturmDerangementsExc (by lia), natDegree_X_mul hcore_ne] at hdeg
  lia

lemma roots_nonpos_affine_sturmDerangementsExc_of_isRealRooted {n : Nat} (hn : 2 ≤ n)
    (hrr : (sturmDerangementsExc n).Splits) :
    ∀ r ∈ (affineSturmDerangementsExc n).roots, r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs (prec_affine_sturmDerangementsExc hn hrr).1.2
    (affine_sturmDerangementsExc_nonnegCoeffs hn)

lemma roots_nonpos_lowerTerm_sturmDerangementsExc {n : Nat} (hn : 3 ≤ n)
    (hprec : Prec (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    ∀ r ∈ (C (n : ℝ) * sturmDerangementsExc (n - 1)).roots, r ≤ 0 := by
  have hn_cast : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
  intro r hr
  rw [roots_C_mul _ hn_cast] at hr
  exact roots_nonpos_of_nonneg_coeffs hprec.1.2
    (sturmDerangementsExc_nonnegCoeffs (n - 1)) r hr

lemma prec_sturmDerangementsExc_affine_mul_X {n : Nat} (hn : 2 ≤ n)
    (hrr : (sturmDerangementsExc n).Splits) :
    Prec (sturmDerangementsExc n)
      (X * affineSturmDerangementsExc n) :=
  prec_sameDegree_to_prec_mul_X_of_roots_nonpos
    (prec_affine_sturmDerangementsExc hn hrr)
    (natDegree_affine_sturmDerangementsExc hn)
    (roots_nonpos_affine_sturmDerangementsExc_of_isRealRooted hn hrr)
    (roots_nonpos_sturmDerangementsExc_of_isRealRooted hrr)

lemma prec_X_mul_affine_sturmDerangementsExc {n : Nat} (hn : 2 ≤ n)
    (hrr : (sturmDerangementsExc n).Splits) :
    Prec (X * affineSturmDerangementsExc n) (X * sturmDerangementsExc n) :=
  prec_mul_X_both_of_roots_nonpos
    (prec_affine_sturmDerangementsExc hn hrr)
    (roots_nonpos_affine_sturmDerangementsExc_of_isRealRooted hn hrr)
    (roots_nonpos_sturmDerangementsExc_of_isRealRooted hrr)

lemma prec_X_mul_lowerTerm_sturmDerangementsExc {n : Nat} (hn : 3 ≤ n)
    (hprec : Prec (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    Prec (X * (C (n : ℝ) * sturmDerangementsExc (n - 1)))
      (X * sturmDerangementsExc n) := by
  have hlower : Prec (C (n : ℝ) * sturmDerangementsExc (n - 1))
      (sturmDerangementsExc n) :=
    prec_lowerTerm_sturmDerangementsExc (by lia) hprec
  exact prec_mul_X_both_of_roots_nonpos hlower
    (roots_nonpos_lowerTerm_sturmDerangementsExc hn hprec)
    (roots_nonpos_sturmDerangementsExc_of_isRealRooted hprec.2.1.2)

/-- The two inner summands in the derangement recurrence both precede `X * P_n`.
This matches the main induction-step input in the human proof. -/
lemma prec_X_mul_recurrenceSummands_sturmDerangementsExc {n : Nat} (hn : 3 ≤ n)
    (hprec : Prec (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    Prec (X * (C (n : ℝ) * sturmDerangementsExc (n - 1))) (X * sturmDerangementsExc n) ∧
      Prec (X * affineSturmDerangementsExc n) (X * sturmDerangementsExc n) :=
  ⟨prec_X_mul_lowerTerm_sturmDerangementsExc hn hprec,
    prec_X_mul_affine_sturmDerangementsExc (by lia) hprec.2.1.2⟩

/-- The recurrence core
`n * P_{n-1} + (n * P_n + (1 - X) P'_n)` precedes `P_n` once `P_{n-1} ≪ P_n`.
This is the inner addition step in the human proof of Sturm interlacing. -/
lemma prec_recurrenceCoreSturmDerangementsExc {n : Nat} (hn : 3 ≤ n)
    (hprec : Prec (sturmDerangementsExc (n - 1)) (sturmDerangementsExc n)) :
    Prec (recurrenceCoreSturmDerangementsExc n) (sturmDerangementsExc n) := by
  rw [recurrenceCoreSturmDerangementsExc]
  have hlower : Prec (C (n : ℝ) * sturmDerangementsExc (n - 1)) (sturmDerangementsExc n) :=
    prec_lowerTerm_sturmDerangementsExc (by lia) hprec
  have haff : Prec (affineSturmDerangementsExc n) (sturmDerangementsExc n) :=
    prec_affine_sturmDerangementsExc (by lia) hprec.2.1.2
  have hlower_pos : HasPosLeadingCoeff (C (n : ℝ) * sturmDerangementsExc (n - 1)) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hn0)]
    exact mul_pos (by grind) (sturmDerangementsExc_posLeadingCoeff (by lia))
  have haff_pos : HasPosLeadingCoeff (affineSturmDerangementsExc n) :=
    (affine_sturmDerangementsExc_nonnegCoeffs (by lia)).pos_leadingCoeff haff.1.1
  exact prec_add_of_prec_right_of_posLeadingCoeff hlower haff hlower_pos haff_pos

/-- Once the recurrence core is known to precede `P_n`, the actual Sturm step
`P_n ≪ P_{n+1}` follows immediately from the outer `X` factor in the recurrence. -/
lemma prec_sturmDerangementsExc_succ_of_prec_recurrenceCore {n : Nat} (hn : 2 ≤ n)
    (hcore : Prec (recurrenceCoreSturmDerangementsExc n) (sturmDerangementsExc n)) :
    Prec (sturmDerangementsExc n) (sturmDerangementsExc (n + 1)) := by
  have hsame :
      (recurrenceCoreSturmDerangementsExc n).natDegree = (sturmDerangementsExc n).natDegree := by
    rw [natDegree_recurrenceCoreSturmDerangementsExc hn, natDegree_sturmDerangementsExc hn]
  have hcore_nonpos :
      ∀ r ∈ (recurrenceCoreSturmDerangementsExc n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hcore.1.2 (recurrenceCoreSturmDerangementsExc_nonnegCoeffs hn)
  have hpn_nonpos :
      ∀ r ∈ (sturmDerangementsExc n).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hcore.2.1.2 (sturmDerangementsExc_nonnegCoeffs n)
  have hmain :
      Prec (sturmDerangementsExc n) (X * recurrenceCoreSturmDerangementsExc n) :=
    prec_sameDegree_to_prec_mul_X_of_roots_nonpos hcore hsame hcore_nonpos hpn_nonpos
  simpa [sturmDerangementsExc_succ_eq_X_mul_recurrenceCore n hn] using hmain

/-- Consecutive derangement excedance polynomials interlace in the oriented
`Prec` sense: `P_n ≪ P_{n+1}` for every `n ≥ 2`. -/
theorem prec_sturmDerangementsExc_succ : ∀ n : Nat, 2 ≤ n →
    Prec (sturmDerangementsExc n) (sturmDerangementsExc (n + 1))
  | 0, hn => by lia
  | 1, hn => by lia
  | 2, _ => by
      have hcore : Prec (recurrenceCoreSturmDerangementsExc 2) (sturmDerangementsExc 2) := by
        simpa [recurrenceCoreSturmDerangementsExc, affineSturmDerangementsExc]
          using prec_affine_sturmDerangementsExc (n := 2) (by lia) (by simp)
      exact prec_sturmDerangementsExc_succ_of_prec_recurrenceCore (n := 2) (by lia) hcore
  | n + 3, _ => by
      have hprev : Prec (sturmDerangementsExc (n + 2)) (sturmDerangementsExc (n + 3)) :=
        prec_sturmDerangementsExc_succ (n + 2) (by lia)
      have hcore : Prec (recurrenceCoreSturmDerangementsExc (n + 3))
          (sturmDerangementsExc (n + 3)) :=
        prec_recurrenceCoreSturmDerangementsExc (n := n + 3) (by lia) hprev
      exact prec_sturmDerangementsExc_succ_of_prec_recurrenceCore (n := n + 3) (by lia) hcore

/-- In particular, every nontrivial derangement excedance polynomial is real-rooted. -/
theorem isRealRooted_sturmDerangementsExc : ∀ n : Nat, 2 ≤ n →
    ((sturmDerangementsExc n) ≠ 0 ∧ (sturmDerangementsExc n).Splits)
  | 0, hn => by lia
  | 1, hn => by lia
  | 2, _ => by
      simp
  | n + 3, _ => (prec_sturmDerangementsExc_succ (n + 2) (by lia)).2.1

/-- Consecutive derangement excedance polynomials form a genuine differ-by-1
interlacing pair, not just an abstract `Prec` pair. -/
theorem interlaces_sturmDerangementsExc_succ {n : Nat} (hn : 2 ≤ n) :
    Interlaces (sturmDerangementsExc n) (sturmDerangementsExc (n + 1)) :=
  (prec_sturmDerangementsExc_succ n hn).toInterlaces <| by
    rw [natDegree_sturmDerangementsExc hn, natDegree_sturmDerangementsExc (by lia)]
    lia

/-- The descending prefix `[P_{n+1}, P_n, ..., P_2]` of the derangement
excedance sequence. This is the natural finite list for `IsSturmSeq`. -/
def sturmDerangementsExcPrefix : Nat → List ℝ[X]
  | 0 => []
  | n + 1 => sturmDerangementsExc (n + 2) :: sturmDerangementsExcPrefix n

@[simp] lemma sturmDerangementsExcPrefix_zero :
    sturmDerangementsExcPrefix 0 = [] := rfl

@[simp] lemma sturmDerangementsExcPrefix_succ (n : Nat) :
    sturmDerangementsExcPrefix (n + 1) =
      sturmDerangementsExc (n + 2) :: sturmDerangementsExcPrefix n := rfl

/-- Every finite descending prefix of the nonzero derangement excedance sequence
is a Sturm sequence. -/
theorem isSturmSeq_sturmDerangementsExcPrefix :
    ∀ n : Nat, IsSturmSeq (sturmDerangementsExcPrefix n) := by
  intro n
  induction n with
  | zero =>
      simp [sturmDerangementsExcPrefix, IsSturmSeq]
  | succ n ih =>
      cases n with
      | zero =>
          simp [sturmDerangementsExcPrefix, IsSturmSeq]
      | succ n =>
          simpa [sturmDerangementsExcPrefix, IsSturmSeq] using
            And.intro (interlaces_sturmDerangementsExc_succ (n := n + 2) (by lia)) ih

/-- Backward-compatible alias while the project transitions away from the old name. -/
abbrev warmupP := sturmDerangementsExc

@[simp] lemma warmupP_zero : warmupP 0 = 0 := sturmDerangementsExc_zero

@[simp] lemma warmupP_one : warmupP 1 = 0 := sturmDerangementsExc_one

@[simp] lemma warmupP_two : warmupP 2 = X := sturmDerangementsExc_two

lemma warmupP_recurrence (n : Nat) : warmupP (n + 3) =
    X * (((n + 2 : ℝ[X])) * warmupP (n + 1) +
      ((n + 2 : ℝ[X])) * warmupP (n + 2) +
      (1 - X) * (warmupP (n + 2)).derivative) :=
  sturmDerangementsExc_recurrence n

lemma X_dvd_warmupP (n : Nat) : X ∣ warmupP n :=
  X_dvd_sturmDerangementsExc n

lemma warmupP_isRoot_zero (n : Nat) : (warmupP n).IsRoot 0 :=
  sturmDerangementsExc_isRoot_zero n

lemma warmupP_three : warmupP 3 = X ^ 2 + X := sturmDerangementsExc_three

lemma warmupP_four : warmupP 4 = X ^ 3 + 7 * X ^ 2 + X := sturmDerangementsExc_four

lemma warmupP_five : warmupP 5 = X ^ 4 + 21 * X ^ 3 + 21 * X ^ 2 + X := sturmDerangementsExc_five

end RealRooted
