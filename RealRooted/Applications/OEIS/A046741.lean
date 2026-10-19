/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import Mathlib
import RealRooted.Basic.ProperPosition
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex
import RealRooted.ObreschkoffConverse.Converse
import RealRooted.Recurrence.RowModel

/-!
# OEIS A046741

The row polynomials of [OEIS A046741](https://oeis.org/A046741) count matchings in the
ladder graph `P₂ × Pₙ` by size. They satisfy

`P (n + 3) = (1 + 2X) P (n + 2) + X P (n + 1) - X³ P n`,

with `P 0 = 1`, `P 1 = 1 + X` and `P 2 = 1 + 4X + 2X²`.

## Main statements

* `im_eq_zero_of_aeval_pencil_eq_zero`: every nontrivial real combination of two consecutive
  rows has only real roots.
* `natDegree_polynomial`: `P n` has degree `n`; its top coefficient is the Fibonacci number
  `F (n + 1)` (`coeff_polynomial_self`).
* `strictInterl_polynomial_succ`: consecutive rows strictly interlace.
* `interlaces_of_recurrence`, `strictInterl_of_recurrence`: the same for any sequence with the
  A046741 initial rows and recurrence (`@[rr_row_model]` transfers).

## Proof

For `x` in the open upper half-plane, the values `a, b, c` of three consecutive terms of the
shifted sequence `0, P 0, P 1, …` satisfy six inequalities of the form `0 ≤ Im (conj u * v)`
(`Inv`), and the recurrence preserves them; each step is a polynomial identity plus sign
reasoning. In particular `Im (conj (P n x) * P (n + 1) x) > 0`, so no nontrivial real
combination of `P n` and `P (n + 1)` vanishes off the real axis. This proof was found by
Aristotle (Harmonic).
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A046741

/-- The row polynomial of [OEIS A046741](https://oeis.org/A046741). -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 1 + 4 * X + 2 * X ^ 2
  | n + 3 => (1 + 2 * X) * polynomial (n + 2) + X * polynomial (n + 1) +
      (-1 * X ^ 3) * polynomial n

section Pencil

open Complex

open Complex

/-- The cross product `Im (conj u * v)`; `0 ≤ br u v` means that `v` is obtained from `u`
by a counterclockwise rotation of angle in `[0, π]`. -/
private def br (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- The invariant satisfied by three consecutive values `a, b, c` of a solution of the
recurrence `f (n+3) = (1 + 2x) f (n+2) + x f (n+1) - x³ f n` (at a point `x` of the upper
half-plane), for the sequence `0, polynomial 0, polynomial 1, …`. -/
private structure Inv (x a b c : ℂ) : Prop where
  j1 : 0 ≤ br b (x * a)
  j2 : 0 ≤ br c (x * b)
  j3 : 0 ≤ br (b + x * a) (c - x * b)
  j4 : 0 ≤ br a (b - x * a)
  j5 : 0 ≤ br (x ^ 2 * a) (b - c)
  j6 : 0 ≤ br b (c - x * b)
  hb : b ≠ 0
  hc : c ≠ 0

/-- An auxiliary consequence of the invariant, proved by a two-case Grassmann–Plücker argument. -/
private lemma K_nonneg {x a b c : ℂ} (hx : 0 < x.im) (h : Inv x a b c) :
    0 ≤ br (b - x ^ 2 * a) c := by
  have hb2 : 0 < normSq b := normSq_pos.mpr h.hb
  have ha2 := normSq_nonneg a
  have hx2 := normSq_nonneg x
  have j1 := h.j1; have j2 := h.j2; have j3 := h.j3; have j4 := h.j4; have j5 := h.j5
  by_cases hs : 0 ≤ br (b - x ^ 2 * a) (b + x * a)
  · have hid : (x.im * normSq b + normSq x * (br a (b - x * a) + x.im * normSq a)) *
          br (b - x ^ 2 * a) c
        = br (b - x ^ 2 * a) (b + x * a) * br c (x * b) +
          (x.im * normSq b + normSq x * br b (x * a)) *
            (br (b + x * a) (c - x * b) + x.im * normSq b +
              normSq x * (br a (b - x * a) + x.im * normSq a)) := by
      simp only [br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
        pow_zero, one_re, one_im]
      ring
    have hpos : 0 < x.im * normSq b + normSq x * (br a (b - x * a) + x.im * normSq a) := by
      have h1 : 0 < x.im * normSq b := mul_pos hx hb2
      have h2 : 0 ≤ normSq x * (br a (b - x * a) + x.im * normSq a) :=
        mul_nonneg hx2 (add_nonneg j4 (mul_nonneg hx.le ha2))
      linarith
    have hR : 0 ≤ (x.im * normSq b + normSq x * (br a (b - x * a) + x.im * normSq a)) *
          br (b - x ^ 2 * a) c := by
      rw [hid]
      refine add_nonneg (mul_nonneg hs j2) (mul_nonneg ?_ ?_)
      · exact add_nonneg (mul_nonneg hx.le hb2.le) (mul_nonneg hx2 j1)
      · exact add_nonneg (add_nonneg j3 (mul_nonneg hx.le hb2.le))
          (mul_nonneg hx2 (add_nonneg j4 (mul_nonneg hx.le ha2)))
    exact (mul_nonneg_iff_of_pos_left hpos).mp hR
  · push Not at hs
    have hid : (br b (x * a) - br (b - x ^ 2 * a) (b + x * a)) * br (b - x ^ 2 * a) c
        = (-br b (x ^ 2 * a)) * br (b + x * a) (c - x * b) +
          (-br (b - x ^ 2 * a) (b + x * a)) * br (x ^ 2 * a) (b - c) +
          (-br b (x ^ 2 * a)) * (x.im * normSq (b + x * a) + br b (x * a)) := by
      simp only [br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
        pow_zero, one_re, one_im]
      ring
    have hsid : br (b - x ^ 2 * a) (b + x * a)
        = br b (x * a) + br b (x ^ 2 * a) + x.im * normSq x * normSq a := by
      simp only [br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
        pow_zero, one_re, one_im]
      ring
    have hxa : 0 ≤ x.im * normSq x * normSq a := mul_nonneg (mul_nonneg hx.le hx2) ha2
    have hbb : 0 ≤ -br b (x ^ 2 * a) := by linarith
    have hpos : 0 < br b (x * a) - br (b - x ^ 2 * a) (b + x * a) := by linarith
    have hR : 0 ≤ (br b (x * a) - br (b - x ^ 2 * a) (b + x * a)) * br (b - x ^ 2 * a) c := by
      rw [hid]
      refine add_nonneg (add_nonneg (mul_nonneg hbb j3) (mul_nonneg (by linarith) j5))
        (mul_nonneg hbb (add_nonneg (mul_nonneg hx.le (normSq_nonneg _)) j1))
    exact (mul_nonneg_iff_of_pos_left hpos).mp hR

/-- The invariant propagates along the recurrence. -/
private lemma Inv.step {x a b c : ℂ} (hx : 0 < x.im) (h : Inv x a b c) :
    Inv x b c ((1 + 2 * x) * c + x * b - x ^ 3 * a) := by
  set d := (1 + 2 * x) * c + x * b - x ^ 3 * a with hd
  have hc2 : 0 < normSq c := normSq_pos.mpr h.hc
  have hb2 := normSq_nonneg b
  have hx2 := normSq_nonneg x
  have hK := K_nonneg hx h
  have j1 := h.j1; have j2 := h.j2; have j3 := h.j3; have j4 := h.j4; have j6 := h.j6
  -- the new second inequality
  have T2id : br d (x * c) = x.im * normSq c + normSq x * br (b - x ^ 2 * a) c := by
    simp only [hd, br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
      pow_zero, one_re, one_im, re_ofNat, im_ofNat]
    ring
  have T2 : 0 ≤ br d (x * c) := by
    rw [T2id]; exact add_nonneg (mul_nonneg hx.le hc2.le) (mul_nonneg hx2 hK)
  -- the new third inequality
  have T3id : br (c + x * b) (d - x * c) = normSq x * br (b + x * a) (c - x * b) +
      2 * normSq x ^ 2 * br a (b - x * a) + x.im * normSq (c - x ^ 2 * a) +
      x.im * normSq x * normSq (b - x * a) := by
    simp only [hd, br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
      pow_zero, one_re, one_im, re_ofNat, im_ofNat]
    ring
  have T3 : 0 ≤ br (c + x * b) (d - x * c) := by
    rw [T3id]
    refine add_nonneg (add_nonneg (add_nonneg (mul_nonneg hx2 j3) ?_) ?_) ?_
    · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx2 2)) j4
    · exact mul_nonneg hx.le (normSq_nonneg _)
    · exact mul_nonneg (mul_nonneg hx.le hx2) (normSq_nonneg _)
  -- the new fifth inequality
  have T5id : br (x ^ 2 * b) (c - d) = 2 * normSq x * br c (x * b) +
      x.im * normSq x * normSq b + normSq x ^ 2 * br b (x * a) := by
    simp only [hd, br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
      pow_zero, one_re, one_im, re_ofNat, im_ofNat]
    ring
  have T5 : 0 ≤ br (x ^ 2 * b) (c - d) := by
    rw [T5id]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg (mul_nonneg (by norm_num) hx2) j2
    · exact mul_nonneg (mul_nonneg hx.le hx2) hb2
    · exact mul_nonneg (pow_nonneg hx2 2) j1
  -- the new sixth inequality, by a Plücker relation
  have T6id : br c (d - x * c) * br (c + x * b) (x * c) =
      br c (x * b) * br d (x * c) + x.im * normSq c * br (c + x * b) (d - x * c) := by
    simp only [hd, br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, pow_succ,
      pow_zero, one_re, one_im, re_ofNat, im_ofNat]
    ring
  have Wid : br (c + x * b) (x * c) =
      x.im * normSq c + normSq x * (br b (c - x * b) + x.im * normSq b) := by
    simp only [br, normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im]
    ring
  have Wpos : 0 < br (c + x * b) (x * c) := by
    rw [Wid]
    have : 0 ≤ normSq x * (br b (c - x * b) + x.im * normSq b) :=
      mul_nonneg hx2 (add_nonneg j6 (mul_nonneg hx.le hb2))
    have : 0 < x.im * normSq c := mul_pos hx hc2
    linarith
  have T6 : 0 ≤ br c (d - x * c) := by
    have : 0 ≤ br c (d - x * c) * br (c + x * b) (x * c) := by
      rw [T6id]
      exact add_nonneg (mul_nonneg j2 T2) (mul_nonneg (mul_nonneg hx.le hc2.le) T3)
    exact (mul_nonneg_iff_of_pos_right Wpos).mp this
  -- the new value does not vanish
  have hd0 : d ≠ 0 := by
    intro h0
    have : br c (d - x * c) = -(x.im * normSq c) := by
      rw [h0]; simp only [br, normSq_apply, sub_re, sub_im, mul_re, mul_im, zero_re, zero_im]
      ring
    have : 0 < x.im * normSq c := mul_pos hx hc2
    linarith
  exact ⟨j2, T2, T3, j6, T5, T6, h.hc, hd0⟩

/-- An auxiliary shifted sequence: `Q (n + 1) = polynomial n` and `Q 0 = 0`. -/
private def Q : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 1
  | 2 => 1 + X
  | n + 3 => (1 + 2 * X) * Q (n + 2) + X * Q (n + 1) - X ^ 3 * Q n

private lemma Q_succ (n : ℕ) : Q (n + 1) = polynomial n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [Q, polynomial]
    | 1 => simp [Q, polynomial]
    | 2 => simp only [Q, polynomial]; ring
    | n + 3 =>
      rw [show n + 3 + 1 = (n + 1) + 3 from rfl, Q, ih (n + 2) (by lia), ih (n + 1) (by lia),
        ih n (by lia)]
      simp only [polynomial]
      ring

private lemma Inv_Q {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    Inv z (aeval z (Q n)) (aeval z (Q (n + 1))) (aeval z (Q (n + 2))) := by
  induction n with
  | zero =>
    have h1 : (1 + z) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    have h2 : z.im * z.re ≤ (1 + z.re) * z.im := by nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Q, br, h1, h2]
  | succ n ih =>
    have hrec : aeval z (Q (n + 3)) = (1 + 2 * z) * aeval z (Q (n + 2)) +
        z * aeval z (Q (n + 1)) - z ^ 3 * aeval z (Q n) := by
      simp only [Q, map_add, map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
    have := ih.step hz
    rw [← hrec] at this
    exact this

/-- Key fact: for `Im z > 0`, `polynomial n` does not vanish at `z` and
`Im (conj (polynomial n z) * polynomial (n+1) z) > 0`. -/
private lemma key {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    aeval z (polynomial n) ≠ 0 ∧
      0 < br (aeval z (polynomial n)) (aeval z (polynomial (n + 1))) := by
  have h := Inv_Q hz n
  rw [Q_succ, show n + 2 = (n + 1) + 1 from rfl, Q_succ] at h
  refine ⟨h.hb, ?_⟩
  have hb2 : 0 < normSq (aeval z (polynomial n)) := normSq_pos.mpr h.hb
  have hid : br (aeval z (polynomial n)) (aeval z (polynomial (n + 1))) =
      br (aeval z (polynomial n)) (aeval z (polynomial (n + 1)) - z * aeval z (polynomial n)) +
        z.im * normSq (aeval z (polynomial n)) := by
    simp only [br, normSq_apply, sub_re, sub_im, mul_re, mul_im]
    ring
  rw [hid]
  have := h.j6
  have : 0 < z.im * normSq (aeval z (polynomial n)) := mul_pos hz hb2
  linarith

/-- The upper half-plane case of the theorem. -/
private lemma upper {n : ℕ} {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0) {z : ℂ} (hz : 0 < z.im)
    (h : aeval z (C a * polynomial n + C b * polynomial (n + 1)) = 0) : False := by
  obtain ⟨hne, hpos⟩ := key hz n
  set p := aeval z (polynomial n)
  set q := aeval z (polynomial (n + 1))
  have h' : (a : ℂ) * p + (b : ℂ) * q = 0 := by
    simpa [p, q] using h
  have hlin : br p ((a : ℂ) * p + (b : ℂ) * q) = b * br p q := by
    simp only [br, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
    ring
  rw [h'] at hlin
  have hb0 : b = 0 := by
    have : b * br p q = 0 := by rw [← hlin]; simp [br]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · linarith
  have ha0 : a = 0 := by
    rw [hb0] at h'
    simp only [ofReal_zero, zero_mul, add_zero, mul_eq_zero, ofReal_eq_zero] at h'
    rcases h' with h0 | h0
    · exact h0
    · exact absurd h0 hne
  rcases hab with h0 | h0
  · exact h0 ha0
  · exact h0 hb0

end Pencil

/-- Every nontrivial real combination of consecutive polynomial rows has only real roots. -/
theorem im_eq_zero_of_aeval_pencil_eq_zero (n : ℕ) (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) (z : ℂ)
    (hz : aeval z (C a * polynomial n + C b * polynomial (n + 1)) = 0) : z.im = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine upper (n := n) hab (z := (starRingEnd ℂ) z) (by simpa using hneg) ?_
    have := congrArg (starRingEnd ℂ) hz
    rw [map_zero] at this
    rw [← this]
    exact (Polynomial.aeval_algHom_apply (Complex.conjAe.toAlgHom) z _)
  · exact upper hab hpos hz

/-- The degree bound and top coefficient of the rows: `P n` has degree at most `n`, and its
coefficient of `X ^ n` is the Fibonacci number `F (n + 1)`. -/
private theorem natDegree_le_and_coeff (n : ℕ) :
    (polynomial n).natDegree ≤ n ∧ (polynomial n).coeff n = Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [polynomial]
    | 1 =>
      refine ⟨by rw [polynomial]; compute_degree!, ?_⟩
      simp [polynomial, coeff_X, coeff_one]
    | 2 =>
      refine ⟨by rw [polynomial]; compute_degree!, ?_⟩
      simp [polynomial, coeff_X, coeff_one, coeff_X_pow]
      norm_num [Nat.fib_add_two]
    | n + 3 =>
      obtain ⟨h0d, h0c⟩ := ih n (by lia)
      obtain ⟨h1d, -⟩ := ih (n + 1) (by lia)
      obtain ⟨h2d, h2c⟩ := ih (n + 2) (by lia)
      have hlin : (1 + 2 * X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
      have hcub : (-1 * X ^ 3 : ℝ[X]).natDegree ≤ 3 := by compute_degree!
      have hX : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
      constructor
      · rw [polynomial]
        refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
          (max_le ?_ ?_)) ?_)
        · exact natDegree_mul_le.trans (by lia)
        · exact natDegree_mul_le.trans (by lia)
        · exact natDegree_mul_le.trans (by lia)
      · have e : polynomial (n + 3) = polynomial (n + 2) + 2 * (X * polynomial (n + 2)) +
            X * polynomial (n + 1) - X ^ 3 * polynomial n := by
          rw [polynomial]
          ring
        have c1 : (polynomial (n + 2)).coeff (n + 3) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by lia)
        have c2 : (X * polynomial (n + 2)).coeff (n + 3) = (Nat.fib (n + 3) : ℝ) := by
          rw [coeff_X_mul, h2c]
        have c3 : (X * polynomial (n + 1)).coeff (n + 3) = 0 := by
          rw [coeff_X_mul]
          exact coeff_eq_zero_of_natDegree_lt (by lia)
        have c4 : (X ^ 3 * polynomial n).coeff (n + 3) = (Nat.fib (n + 1) : ℝ) := by
          rw [coeff_X_pow_mul, h0c]
        rw [e, coeff_sub, coeff_add, coeff_add, coeff_ofNat_mul, c1, c2, c3, c4,
          show n + 3 + 1 = n + 4 by lia, Nat.fib_add_two (n := n + 2),
          Nat.fib_add_two (n := n + 1)]
        push_cast
        ring

/-- The coefficient of `X ^ n` in `P n` is the Fibonacci number `F (n + 1)`. -/
theorem coeff_polynomial_self (n : ℕ) : (polynomial n).coeff n = Nat.fib (n + 1) :=
  (natDegree_le_and_coeff n).2

/-- `P n` has degree `n`. -/
theorem natDegree_polynomial (n : ℕ) : (polynomial n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_and_coeff n).1 (by
    rw [coeff_polynomial_self]
    exact_mod_cast (Nat.fib_pos.mpr (by lia)).ne')

/-- The rows have positive leading coefficient. -/
theorem leadingCoeff_polynomial_pos (n : ℕ) : 0 < (polynomial n).leadingCoeff := by
  rw [leadingCoeff, natDegree_polynomial, coeff_polynomial_self]
  exact_mod_cast Nat.fib_pos.mpr (by lia)

/-- The rows are nonzero. -/
theorem polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 :=
  leadingCoeff_ne_zero.mp (leadingCoeff_polynomial_pos n).ne'

/-- Every real combination of two consecutive rows splits. -/
theorem allComboRealRooted_polynomial_succ (n : ℕ) :
    AllComboRealRooted (polynomial n) (polynomial (n + 1)) := by
  intro α β
  by_cases h : α = 0 ∧ β = 0
  · simp [h.1, h.2]
  refine Polynomial.splits_of_all_roots_real fun z hz => ?_
  refine im_eq_zero_of_aeval_pencil_eq_zero n α β (by tauto) z ?_
  rwa [aeval_def, eval₂_eq_eval_map]

/-- The rows are real-rooted. -/
theorem splits_polynomial (n : ℕ) : (polynomial n).Splits := by
  simpa using allComboRealRooted_polynomial_succ n 1 0

/-- Consecutive A046741 rows strictly interlace. -/
theorem strictInterl_polynomial_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  have hdegree : (polynomial (n + 1)).natDegree = (polynomial n).natDegree + 1 := by
    rw [natDegree_polynomial, natDegree_polynomial]
  have horientation := strictInterl_of_allComboRealRooted
    (polynomial_ne_zero n) (splits_polynomial n)
    (polynomial_ne_zero (n + 1)) (splits_polynomial (n + 1))
    (allComboRealRooted_polynomial_succ n) (Or.inl hdegree.symm)
  exact StrictInterl.forward_of_orientation_of_succDegree hdegree horientation

/-- A sequence with the A046741 initial rows and recurrence is the A046741 sequence. -/
private theorem eq_polynomial_of_recurrence {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1) (hone : P 1 = 1 + X) (htwo : P 2 = 1 + 4 * X + 2 * X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      (1 + 2 * X) * P (n + 2) + X * P (n + 1) + (-1 * X ^ 3) * P n) :
    ∀ n, P n = polynomial n
  | 0 => hzero
  | 1 => hone
  | 2 => htwo
  | n + 3 => by
    rw [hrec, eq_polynomial_of_recurrence hzero hone htwo hrec n,
      eq_polynomial_of_recurrence hzero hone htwo hrec (n + 1),
      eq_polynomial_of_recurrence hzero hone htwo hrec (n + 2), polynomial]

/-- Any sequence with the A046741 initial rows and recurrence has strictly interlacing
consecutive rows. -/
@[rr_row_model]
theorem strictInterl_of_recurrence {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1) (hone : P 1 = 1 + X) (htwo : P 2 = 1 + 4 * X + 2 * X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      (1 + 2 * X) * P (n + 2) + X * P (n + 1) + (-1 * X ^ 3) * P n)
    (n : ℕ) : StrictInterl (P n) (P (n + 1)) := by
  rw [eq_polynomial_of_recurrence hzero hone htwo hrec n,
    eq_polynomial_of_recurrence hzero hone htwo hrec (n + 1)]
  exact strictInterl_polynomial_succ n

/-- Any sequence with the A046741 initial rows and recurrence has interlacing consecutive
rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1) (hone : P 1 = 1 + X) (htwo : P 2 = 1 + 4 * X + 2 * X ^ 2)
    (hrec : ∀ n, P (n + 3) =
      (1 + 2 * X) * P (n + 2) + X * P (n + 1) + (-1 * X ^ 3) * P n)
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  rw [eq_polynomial_of_recurrence hzero hone htwo hrec n,
    eq_polynomial_of_recurrence hzero hone htwo hrec (n + 1)]
  exact (strictInterl_polynomial_succ n).toInterlaces (by
    rw [natDegree_polynomial, natDegree_polynomial])

end RealRooted.Applications.OEIS.A046741
