module

public import RealRooted.PosCombo
public import Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Derivative.Algebra
import RealRooted.Derivative.Interlacing
import RealRooted.Linear

/-!
# A parameter-shifted derivative-lag family

This module defines a two-parameter family of real polynomials and proves the
parameter-shift and scalar recurrences that make its interlacing induction
close.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The positive-construction family for the derivative-lag recurrence. -/
@[expose] def derivativeLagFamily (beta : ℝ) : ℕ → ℝ → ℝ[X]
  | 0, _ => 1
  | n + 1, a =>
      X * derivativeLagFamily beta n (a + 2) +
        C beta * (X * (derivativeLagFamily beta n (a + 1)).derivative) +
          C a * derivativeLagFamily beta n (a + 1)

/-- The degree-zero member of the derivative-lag family is one. -/
@[simp] theorem derivativeLagFamily_zero (beta a : ℝ) :
    derivativeLagFamily beta 0 a = 1 := rfl

/-- The defining positive recurrence for the derivative-lag family. -/
theorem derivativeLagFamily_succ (beta a : ℝ) (n : ℕ) :
    derivativeLagFamily beta (n + 1) a =
      X * derivativeLagFamily beta n (a + 2) +
        C beta * (X * (derivativeLagFamily beta n (a + 1)).derivative) +
          C a * derivativeLagFamily beta n (a + 1) := rfl

/-- Increasing the parameter by one changes row `n + 1` by `n + 1` times the
preceding row. -/
theorem derivativeLagFamily_add_one_sub (beta : ℝ) : ∀ (n : ℕ) (a : ℝ),
    derivativeLagFamily beta (n + 1) (a + 1) - derivativeLagFamily beta (n + 1) a =
      C (n + 1 : ℝ) * derivativeLagFamily beta n (a + 1)
  | 0, a => by
      simp [derivativeLagFamily_succ]
  | n + 1, a => by
      rw [derivativeLagFamily_succ beta (a + 1) (n + 1),
        derivativeLagFamily_succ beta a (n + 1)]
      have hleft := derivativeLagFamily_add_one_sub beta n (a + 2)
      have hmiddle := derivativeLagFamily_add_one_sub beta n (a + 1)
      have hderivative := congrArg derivative hmiddle
      simp only [derivative_sub, derivative_C_mul] at hderivative
      norm_num [add_assoc] at hleft hmiddle hderivative
      have hdefinition := derivativeLagFamily_succ beta (a + 1) n
      simp only [Nat.cast_add, Nat.cast_one] at hleft hmiddle hderivative ⊢
      norm_num [add_assoc] at hdefinition ⊢
      simp only [C_ofNat] at ⊢
      linear_combination X * hleft + C beta * X * hderivative +
        (C a + 1) * hmiddle - ((n : ℝ[X]) + 1) * hdefinition

/-- The positive recurrence can be rewritten using only rows at parameters
`a` and `a + 1`. -/
theorem derivativeLagFamily_succ_eq (beta : ℝ) : ∀ (n : ℕ) (a : ℝ),
    derivativeLagFamily beta (n + 1) a =
      X * derivativeLagFamily beta n (a + 1) +
        C beta * (X * (derivativeLagFamily beta n a).derivative) +
          C (a + n) * derivativeLagFamily beta n a
  | 0, a => by
      simp [derivativeLagFamily_succ]
  | n + 1, a => by
      rw [derivativeLagFamily_succ beta a (n + 1)]
      have hleft := derivativeLagFamily_add_one_sub beta n (a + 1)
      have hmiddle := derivativeLagFamily_add_one_sub beta n a
      have hderivative := congrArg derivative hmiddle
      simp only [derivative_sub, derivative_C_mul] at hderivative
      norm_num [add_assoc] at hleft hmiddle hderivative
      have hdefinition := derivativeLagFamily_succ beta a n
      simp only [Nat.cast_add, Nat.cast_one] at hleft hmiddle hderivative ⊢
      norm_num [add_assoc] at hdefinition ⊢
      linear_combination X * hleft + C beta * X * hderivative +
        C a * hmiddle - ((n : ℝ[X]) + 1) * hdefinition

/-- The derivative-lag family satisfies the scalar lag-two recurrence. -/
theorem derivativeLagFamily_add_two (beta a : ℝ) (n : ℕ) :
    derivativeLagFamily beta (n + 2) a =
      (X + C (a + 2 * n + 2)) * derivativeLagFamily beta (n + 1) a +
        C beta * (X * (derivativeLagFamily beta (n + 1) a).derivative) -
          C (n + 1 : ℝ) *
            (C (a + n) * derivativeLagFamily beta n a +
              C beta * (X * (derivativeLagFamily beta n a).derivative)) := by
  have hnext := derivativeLagFamily_succ_eq beta (n + 1) a
  have hshift := derivativeLagFamily_add_one_sub beta n a
  have hprevious := derivativeLagFamily_succ_eq beta n a
  norm_num [add_assoc] at hnext hshift
  norm_num [add_assoc] at hnext hshift hprevious ⊢
  simp only [C_ofNat] at ⊢
  linear_combination hnext + X * hshift - ((n : ℝ[X]) + 1) * hprevious

/-- A polynomial sequence with the same seeds and scalar recurrence is the
derivative-lag family. -/
theorem eq_derivativeLagFamily_of_recurrence (P : ℕ → ℝ[X]) (beta a : ℝ)
    (hzero : P 0 = 1) (hone : P 1 = X + C a)
    (hrec : ∀ n, P (n + 2) =
      (X + C (a + 2 * n + 2)) * P (n + 1) + C beta * (X * (P (n + 1)).derivative) -
        C (n + 1 : ℝ) * (C (a + n) * P n + C beta * (X * (P n).derivative))) :
    ∀ n, P n = derivativeLagFamily beta n a := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one =>
      rw [hone, derivativeLagFamily_succ]
      simp
  | more n ih ih_succ =>
      rw [hrec n, derivativeLagFamily_add_two, ih, ih_succ]

/-- The positive construction is monic and has its index as its degree. -/
private theorem derivativeLagFamily_monic_natDegree (beta : ℝ) : ∀ (n : ℕ) (a : ℝ),
    (derivativeLagFamily beta n a).Monic ∧
      (derivativeLagFamily beta n a).natDegree = n
  | 0, a => by simp
  | 1, a => by
      constructor
      · simpa [derivativeLagFamily_succ] using monic_X_add_C a
      · simp [derivativeLagFamily_succ]
  | n + 2, a => by
      rw [derivativeLagFamily_succ, add_assoc]
      have hmain := derivativeLagFamily_monic_natDegree beta (n + 1) (a + 2)
      have hderivative := derivativeLagFamily_monic_natDegree beta (n + 1) (a + 1)
      have hlast := derivativeLagFamily_monic_natDegree beta (n + 1) (a + 1)
      have hderivative_ne :
          (derivativeLagFamily beta (n + 1) (a + 1)).derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr (by rw [hderivative.2]; lia)
      have hfirst_le :
          (C beta *
              (X * (derivativeLagFamily beta (n + 1) (a + 1)).derivative)).natDegree ≤
            n + 1 := by
        calc
          _ ≤ (X * (derivativeLagFamily beta (n + 1) (a + 1)).derivative).natDegree :=
            natDegree_C_mul_le _ _
          _ = n + 1 := by
            rw [natDegree_mul X_ne_zero hderivative_ne, natDegree_X,
              (derivativeLagFamily beta (n + 1) (a + 1)).natDegree_derivative,
              hderivative.2]
            lia
      have hlast_le :
          (C a * derivativeLagFamily beta (n + 1) (a + 1)).natDegree ≤ n + 1 :=
        (natDegree_C_mul_le _ _).trans hlast.2.le
      have hlower_le :
          (C beta * (X * (derivativeLagFamily beta (n + 1) (a + 1)).derivative) +
              C a * derivativeLagFamily beta (n + 1) (a + 1)).natDegree ≤ n + 1 :=
        (natDegree_add_le _ _).trans (max_le hfirst_le hlast_le)
      have hmain_degree :
          (X * derivativeLagFamily beta (n + 1) (a + 2)).natDegree = n + 2 := by
        rw [monic_X.natDegree_mul hmain.1, natDegree_X, hmain.2]
        lia
      have hlower_lt :
          (C beta * (X * (derivativeLagFamily beta (n + 1) (a + 1)).derivative) +
              C a * derivativeLagFamily beta (n + 1) (a + 1)).natDegree <
            (X * derivativeLagFamily beta (n + 1) (a + 2)).natDegree := by
        rw [hmain_degree]
        lia
      exact ⟨(monic_X.mul hmain.1).add_of_left (degree_lt_degree hlower_lt),
        natDegree_add_eq_left_of_natDegree_lt hlower_lt |>.trans hmain_degree⟩

/-- Every derivative-lag row is monic. -/
theorem monic_derivativeLagFamily (beta a : ℝ) (n : ℕ) :
    (derivativeLagFamily beta n a).Monic :=
  (derivativeLagFamily_monic_natDegree beta n a).1

/-- The degree of a derivative-lag row is its index. -/
theorem natDegree_derivativeLagFamily (beta a : ℝ) (n : ℕ) :
    (derivativeLagFamily beta n a).natDegree = n :=
  (derivativeLagFamily_monic_natDegree beta n a).2

/-- Nonnegative parameters give every row nonnegative coefficients. -/
theorem hasNonnegCoeffs_derivativeLagFamily {beta a : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 ≤ a) :
    ∀ n, HasNonnegCoeffs (derivativeLagFamily beta n a) := by
  intro n
  induction n generalizing a with
  | zero => simpa using hasNonnegCoeffs_one
  | succ n ih =>
      rw [derivativeLagFamily_succ]
      have htwo : 0 ≤ a + 2 := by positivity
      have hone : 0 ≤ a + 1 := by positivity
      exact ((ih htwo).X_mul.add
        (hasNonnegCoeffs_C_mul hbeta (ih hone).derivative.X_mul)).add
          (hasNonnegCoeffs_C_mul ha (ih hone))

/-- The shift identity transports degree-raising interlacing to same-degree
parameter interlacing. -/
private theorem strictInterl_derivativeLagFamily_add_one_of_succ
    (beta u : ℝ) (n : ℕ)
    (hprevious : StrictInterl (derivativeLagFamily beta n (u + 1))
      (derivativeLagFamily beta (n + 1) u)) :
    StrictInterl (derivativeLagFamily beta (n + 1) (u + 1))
      (derivativeLagFamily beta (n + 1) u) := by
  have hprevious_pos :=
    hasPosLeadingCoeff_of_monic (monic_derivativeLagFamily beta (u + 1) n)
  have hcurrent_pos :=
    hasPosLeadingCoeff_of_monic (monic_derivativeLagFamily beta u (n + 1))
  have hcombo := hprevious.nonneg_combo_right hprevious_pos hcurrent_pos
    (by positivity : 0 ≤ (n + 1 : ℝ)) zero_le_one (Or.inr one_pos)
  have hshift := derivativeLagFamily_add_one_sub beta n u
  rw [sub_eq_iff_eq_add] at hshift
  rw [hshift]
  simpa [add_comm] using hcombo

/-- A same-degree parameter interlacing step closes the next degree-raising
step by the weighted Wagner cone. -/
private theorem strictInterl_derivativeLagFamily_succ_of_add_one
    {beta a : ℝ} (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (m : ℕ) (hm : m ≠ 0)
    (hsame : StrictInterl (derivativeLagFamily beta m (a + 2))
      (derivativeLagFamily beta m (a + 1))) :
    StrictInterl (derivativeLagFamily beta m (a + 1))
      (derivativeLagFamily beta (m + 1) a) := by
  let f := derivativeLagFamily beta m (a + 1)
  let shifted := derivativeLagFamily beta m (a + 2)
  have hf_nonneg : HasNonnegCoeffs f :=
    hasNonnegCoeffs_derivativeLagFamily hbeta (by positivity) m
  have hshifted_nonneg : HasNonnegCoeffs shifted :=
    hasNonnegCoeffs_derivativeLagFamily hbeta (by positivity) m
  have hfirst : StrictInterl f (X * shifted) := by
    apply strictInterl_mul_X_of_strictInterl_of_nonneg
    · simpa [f, shifted] using hsame
    · exact hshifted_nonneg
    · exact hf_nonneg
  have hf_degree : f.natDegree = m := by
    simp [f, natDegree_derivativeLagFamily]
  have hderivative : StrictInterl f.derivative f :=
    (derivative_interlaces_of_natDegree_ne_zero hsame.2.1.2 (by
      rwa [hf_degree])).toStrictInterl
  have hsecond : StrictInterl f (X * f.derivative) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hderivative
      hf_nonneg.derivative hf_nonneg
  have hf_pos : HasPosLeadingCoeff f :=
    hasPosLeadingCoeff_of_monic (monic_derivativeLagFamily beta (a + 1) m)
  have hshifted_pos : HasPosLeadingCoeff (X * shifted) :=
    hasPosLeadingCoeff_of_monic
      (monic_X.mul (monic_derivativeLagFamily beta (a + 2) m))
  have hderivative_pos : HasPosLeadingCoeff (X * f.derivative) :=
    (hf_pos.derivative (by rwa [hf_degree])).X_mul
  have hweighted : StrictInterl f
      (weightedSum [(1, X * shifted), (beta, X * f.derivative), (a, f)]) := by
    apply StrictInterl.weightedSum_left_of_common_left
    · simp [hbeta, ha]
    · intro ap hap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
      rcases hap with rfl | rfl | rfl
      exacts [hfirst, hsecond, StrictInterl.refl hsame.2.1.1 hsame.2.1.2]
    · exact hf_pos
    · intro ap hap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
      rcases hap with rfl | rfl | rfl
      exacts [hshifted_pos, hderivative_pos, hf_pos]
    · exact ⟨(1, X * shifted), by simp⟩
  simpa [f, shifted, weightedSum, derivativeLagFamily_succ, add_assoc] using hweighted

/-- The simultaneous parameter-shift and degree-raising interlacing induction. -/
private theorem derivativeLagFamily_interlacing (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ (n : ℕ) (a : ℝ), 0 ≤ a →
      StrictInterl (derivativeLagFamily beta n (a + 1))
        (derivativeLagFamily beta n a) ∧
      StrictInterl (derivativeLagFamily beta n (a + 1))
        (derivativeLagFamily beta (n + 1) a)
  | 0, a, _ => by
      constructor
      · simpa using StrictInterl.refl (one_ne_zero : (1 : ℝ[X]) ≠ 0) (Splits.C 1)
      · rw [derivativeLagFamily_zero]
        have hone : derivativeLagFamily beta 1 a = X + C a := by
          simp [derivativeLagFamily_succ]
        rw [hone]
        exact (interlaces_one_linear (p := X + C a) (by simp)).toStrictInterl
  | n + 1, a, ha => by
      have hsame_a := strictInterl_derivativeLagFamily_add_one_of_succ beta a n
        (derivativeLagFamily_interlacing beta hbeta n a ha).2
      have ha_one : 0 ≤ a + 1 := by positivity
      have hsame_next := strictInterl_derivativeLagFamily_add_one_of_succ beta (a + 1) n
        (derivativeLagFamily_interlacing beta hbeta n (a + 1) ha_one).2
      have hsame_next' :
          StrictInterl (derivativeLagFamily beta (n + 1) (a + 2))
            (derivativeLagFamily beta (n + 1) (a + 1)) := by
        convert hsame_next using 1
        ring_nf
      exact ⟨hsame_a,
        strictInterl_derivativeLagFamily_succ_of_add_one hbeta ha (n + 1) (by lia)
          hsame_next'⟩

/-- A unit parameter increase interlaces each derivative-lag row from the left. -/
theorem strictInterl_derivativeLagFamily_add_one {beta a : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (n : ℕ) :
    StrictInterl (derivativeLagFamily beta n (a + 1))
      (derivativeLagFamily beta n a) :=
  (derivativeLagFamily_interlacing beta hbeta n a ha).1

/-- A unit parameter increase in row `n` interlaces row `n + 1` at the
original parameter. -/
theorem strictInterl_derivativeLagFamily_succ {beta a : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (n : ℕ) :
    StrictInterl (derivativeLagFamily beta n (a + 1))
      (derivativeLagFamily beta (n + 1) a) :=
  (derivativeLagFamily_interlacing beta hbeta n a ha).2

/-- Every derivative-lag row with nonnegative parameters splits over the reals. -/
theorem splits_derivativeLagFamily {beta a : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (n : ℕ) :
    (derivativeLagFamily beta n a).Splits :=
  (strictInterl_derivativeLagFamily_add_one hbeta ha n).2.1.2

/-- Every root of a derivative-lag row with nonnegative parameters is nonpositive. -/
theorem roots_derivativeLagFamily_nonpos {beta a : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 ≤ a) (n : ℕ) :
    ∀ r ∈ (derivativeLagFamily beta n a).roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (hasNonnegCoeffs_derivativeLagFamily hbeta ha n)

/-- The constant coefficient is the rising factorial of the row parameter. -/
theorem eval_zero_derivativeLagFamily (beta : ℝ) : ∀ (n : ℕ) (a : ℝ),
    (derivativeLagFamily beta n a).eval 0 = (ascPochhammer ℝ n).eval a
  | 0, a => by simp
  | n + 1, a => by
      rw [derivativeLagFamily_succ]
      simp [eval_zero_derivativeLagFamily beta n (a + 1), ascPochhammer_succ_left]

/-- Positive row parameter forces every root to be strictly negative. -/
theorem roots_derivativeLagFamily_neg {beta a : ℝ}
    (hbeta : 0 ≤ beta) (ha : 0 < a) (n : ℕ) :
    ∀ r ∈ (derivativeLagFamily beta n a).roots, r < 0 := by
  intro r hr
  have hr_le := roots_derivativeLagFamily_nonpos hbeta ha.le n r hr
  have hzero : (derivativeLagFamily beta n a).eval 0 ≠ 0 := by
    rw [eval_zero_derivativeLagFamily]
    exact (ascPochhammer_pos n a ha).ne'
  have hr_ne : r ≠ 0 := by
    rintro rfl
    have hroot := (mem_roots (monic_derivativeLagFamily beta a n).ne_zero).mp hr
    rw [Polynomial.IsRoot.def] at hroot
    exact hzero hroot
  exact lt_of_le_of_ne hr_le hr_ne

/-- Every positive-degree row at parameter zero has zero as a root. -/
theorem isRoot_zero_derivativeLagFamily (beta : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (derivativeLagFamily beta n 0).IsRoot 0 := by
  rw [Polynomial.IsRoot.def, eval_zero_derivativeLagFamily, ascPochhammer_eval_zero]
  simp [hn]

end RealRooted
