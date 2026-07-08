import Mathlib
import RealRooted.PosCombo

/-!
# Degree-two same-degree obstruction

This module isolates the algebraic obstruction behind the degree-two base case
of the same-degree root-count route for the Chudnovsky--Seymour common
interleaver machinery (issue #41).  It is not part of the direct #42 route
unless that route later names this exact low-degree base case as a gap.

If two monic quadratics have separated roots `c <= d < a <= b`, then some
strictly positive combination
`(X - a)(X - b) + t * (X - c)(X - d)` has negative discriminant.  Thus a
positive-combination real-rooted pair of quadratics cannot have this separated
root configuration, which is the only way the degree-two same-degree threshold
root counts can differ by two.
-/

open Polynomial

namespace RealRooted

/-- Discriminant identity for the linear pencil of two monic quadratics given
by their roots. -/
theorem discrim_pencil_quadratics (a b c d t : ℝ) :
    discrim (1 + t) (-((a + b) + t * (c + d))) (a * b + t * (c * d)) =
      (a - b) ^ 2 +
        (2 * (a + b) * (c + d) - 4 * a * b - 4 * c * d) * t +
          (c - d) ^ 2 * t ^ 2 := by
  rw [discrim]
  ring

/-- Under separation `c <= d < a <= b`, the key linear coefficient of the
discriminant pencil is negative. -/
theorem neg_pencil_linear_coeff_pos_of_separated
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    0 < (b - c) * (a - d) + (b - d) * (a - c) := by
  have h1 : 0 < a - d := by linarith
  have h2 : 0 < a - c := by linarith
  have h3 : 0 ≤ b - c := by linarith
  have h4 : 0 ≤ b - d := by linarith
  nlinarith [mul_nonneg h3 h1.le, mul_nonneg h4 h2.le, mul_pos h1 h2]

/-- Analytic crux of the degree-two same-degree obstruction.

If two real quadratics have separated roots `c <= d < a <= b`, then some
strictly positive combination
`(X - a)(X - b) + t * (X - c)(X - d)` has negative discriminant. -/
theorem discrim_neg_of_quadratic_roots_separated
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    ∃ t : ℝ, 0 < t ∧
      discrim (1 + t) (-((a + b) + t * (c + d))) (a * b + t * (c * d)) < 0 := by
  have hS : 0 < (b - c) * (a - d) + (b - d) * (a - c) :=
    neg_pencil_linear_coeff_pos_of_separated hab hcd hsep
  have hbc : 0 < b - c := by linarith
  have had : 0 < a - d := by linarith
  by_cases hcd0 : c = d
  · subst hcd0
    have hden : 0 < (b - c) * (a - c) := by nlinarith
    refine ⟨((a - b) ^ 2 + 1) / (2 * ((b - c) * (a - c))), ?_, ?_⟩
    · exact div_pos (by positivity) (by linarith)
    · rw [discrim_pencil_quadratics]
      have hval :
          (a - b) ^ 2 +
                (2 * (a + b) * (c + c) - 4 * a * b - 4 * c * c) *
                  (((a - b) ^ 2 + 1) / (2 * ((b - c) * (a - c)))) +
              (c - c) ^ 2 *
                (((a - b) ^ 2 + 1) / (2 * ((b - c) * (a - c)))) ^ 2 =
            -(a - b) ^ 2 - 2 := by
        field_simp
        ring
      rw [hval]
      nlinarith [sq_nonneg (a - b)]
  · have hcd' : c < d := lt_of_le_of_ne hcd hcd0
    have hq : 0 < (c - d) ^ 2 := by
      have : c - d ≠ 0 := by
        intro h
        apply hcd0
        linarith
      positivity
    have hnonneg : 0 ≤ (b - a) * (d - c) :=
      mul_nonneg (by linarith) (by linarith)
    have hlin :
        (b - a) * (d - c) <
          (b - c) * (a - d) + (b - d) * (a - c) := by
      nlinarith [mul_pos had hbc]
    have hSsq :
        (a - b) ^ 2 * (c - d) ^ 2 <
          ((b - c) * (a - d) + (b - d) * (a - c)) ^ 2 := by
      nlinarith
        [mul_pos
          (show
            (0 : ℝ) <
              ((b - c) * (a - d) + (b - d) * (a - c)) -
                (b - a) * (d - c) by linarith)
          (show
            (0 : ℝ) <
              ((b - c) * (a - d) + (b - d) * (a - c)) +
                (b - a) * (d - c) by nlinarith [hS, hnonneg])]
    refine
      ⟨((b - c) * (a - d) + (b - d) * (a - c)) / ((c - d) ^ 2), ?_, ?_⟩
    · positivity
    · rw [discrim_pencil_quadratics]
      set S := (b - c) * (a - d) + (b - d) * (a - c) with hSdef
      have hKeq :
          2 * (a + b) * (c + d) - 4 * a * b - 4 * c * d = -(2 * S) := by
        rw [hSdef]
        ring
      rw [hKeq]
      have hval :
          (a - b) ^ 2 + -(2 * S) * (S / (c - d) ^ 2) +
              (c - d) ^ 2 * (S / (c - d) ^ 2) ^ 2 =
            (a - b) ^ 2 - S ^ 2 / (c - d) ^ 2 := by
        field_simp
        ring
      rw [hval, sub_neg, lt_div_iff₀ hq]
      nlinarith [hSsq]

/-- Reusable quadratic obstruction: a real quadratic
`C a * X ^ 2 + C b * X + C c` with nonzero leading coefficient and negative
discriminant does not split over `ℝ`.

This packages the "negative discriminant forbids a real root, hence a
nonconstant polynomial cannot split" step as a standalone lemma. -/
theorem not_splits_quadratic_of_discrim_neg {a b c : ℝ} (ha : a ≠ 0)
    (hdisc : discrim a b c < 0) :
    ¬ ((C a * X ^ 2 + C b * X + C c) : ℝ[X]).Splits := by
  set p : ℝ[X] := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  have hne : ∀ s : ℝ, discrim a b c ≠ s ^ 2 := by
    intro s h
    have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    rw [h] at hdisc
    linarith
  have hnoroot : ∀ x : ℝ, ¬ p.IsRoot x := by
    intro x hx
    have hpx : p.eval x = 0 := by
      simpa [Polynomial.IsRoot.def] using hx
    have hxeval : a * (x * x) + b * x + c = 0 := by
      rw [hp] at hpx
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at hpx
      nlinarith [hpx]
    exact quadratic_ne_zero_of_discrim_ne_sq hne x hxeval
  intro hsplit
  have hcard : p.roots.card = p.natDegree :=
    Polynomial.splits_iff_card_roots.1 hsplit
  rw [hdeg] at hcard
  have hpos : 0 < p.roots.card := by
    rw [hcard]
    norm_num
  obtain ⟨x, hxmem⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  exact hnoroot x ((mem_roots hp0).1 hxmem)

/-- Polynomial form of the degree-two same-degree obstruction.

If the roots of two real quadratics are separated, then some strictly positive
combination fails to split over `ℝ`. -/
theorem exists_pos_combo_not_splits_of_quadratic_roots_separated
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    ∃ t : ℝ, 0 < t ∧
      ¬ (((X - C a) * (X - C b) + C t * ((X - C c) * (X - C d))) :
          ℝ[X]).Splits := by
  obtain ⟨t, ht, hdisc⟩ := discrim_neg_of_quadratic_roots_separated hab hcd hsep
  refine ⟨t, ht, ?_⟩
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hpexp :
      ((X - C a) * (X - C b) + C t * ((X - C c) * (X - C d)) : ℝ[X]) =
        C (1 + t) * X ^ 2 + C (-((a + b) + t * (c + d))) * X +
          C (a * b + t * (c * d)) := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow]
    ring
  rw [hpexp]
  exact not_splits_quadratic_of_discrim_neg h1t.ne' hdisc

/-- Separated monic quadratic root pairs cannot satisfy the
`PosComboRealRooted` hypothesis. -/
theorem not_posComboRealRooted_quadratic_roots_separated
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    ¬ PosComboRealRooted ((X - C a) * (X - C b)) ((X - C c) * (X - C d)) := by
  intro hfg
  obtain ⟨t, ht, hnot⟩ :=
    exists_pos_combo_not_splits_of_quadratic_roots_separated hab hcd hsep
  exact hnot (hfg.isRealRooted_add_right ht).2

/-- Positive scalar multiples of separated monic quadratic root pairs cannot
satisfy the `PosComboRealRooted` hypothesis. -/
theorem not_posComboRealRooted_pos_scaled_quadratic_roots_separated
    {A B a b c d : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hab : a ≤ b) (hcd : c ≤ d) (hsep : d < a) :
    ¬ PosComboRealRooted
      (C A * ((X - C a) * (X - C b)))
      (C B * ((X - C c) * (X - C d))) := by
  intro hscaled
  have hmonic :
      PosComboRealRooted ((X - C a) * (X - C b)) ((X - C c) * (X - C d)) := by
    intro lam μ hlam hμ
    have hbase := hscaled (lam := lam / A) (μ := μ / B)
      (div_pos hlam hA) (div_pos hμ hB)
    have hEq :
        C (lam / A) * (C A * ((X - C a) * (X - C b))) +
            C (μ / B) * (C B * ((X - C c) * (X - C d))) =
          C lam * ((X - C a) * (X - C b)) +
            C μ * ((X - C c) * (X - C d)) := by
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X]
      field_simp [hA.ne', hB.ne']
    simpa [hEq] using hbase
  exact not_posComboRealRooted_quadratic_roots_separated hab hcd hsep hmonic

/-- Gap form of the separated-root obstruction. -/
theorem not_posComboRealRooted_pos_scaled_quadratic_roots_gap
    {A B a b c d z1 z2 : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hz : z1 < z2) (hdz1 : d ≤ z1) (hz2a : z2 ≤ a) :
    ¬ PosComboRealRooted
      (C A * ((X - C a) * (X - C b)))
      (C B * ((X - C c) * (X - C d))) :=
  not_posComboRealRooted_pos_scaled_quadratic_roots_separated hA hB hab hcd
    (lt_of_le_of_lt hdz1 (lt_of_lt_of_le hz hz2a))

/-- Monic gap form of the separated-root obstruction. -/
theorem not_posComboRealRooted_quadratic_roots_gap
    {a b c d z1 z2 : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hz : z1 < z2) (hdz1 : d ≤ z1) (hz2a : z2 ≤ a) :
    ¬ PosComboRealRooted ((X - C a) * (X - C b)) ((X - C c) * (X - C d)) :=
  not_posComboRealRooted_quadratic_roots_separated hab hcd
    (lt_of_le_of_lt hdz1 (lt_of_lt_of_le hz hz2a))

/-- Symmetric scaled gap form of the separated-root obstruction. -/
theorem not_posComboRealRooted_pos_scaled_quadratic_roots_gap_symm
    {A B a b c d z1 z2 : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hz : z1 < z2) (hbz1 : b ≤ z1) (hz2c : z2 ≤ c) :
    ¬ PosComboRealRooted
      (C A * ((X - C a) * (X - C b)))
      (C B * ((X - C c) * (X - C d))) := by
  intro hpc
  exact not_posComboRealRooted_pos_scaled_quadratic_roots_gap hB hA hcd hab
    hz hbz1 hz2c hpc.comm

/-- Symmetric monic gap form of the separated-root obstruction. -/
theorem not_posComboRealRooted_quadratic_roots_gap_symm
    {a b c d z1 z2 : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hz : z1 < z2) (hbz1 : b ≤ z1) (hz2c : z2 ≤ c) :
    ¬ PosComboRealRooted ((X - C a) * (X - C b)) ((X - C c) * (X - C d)) := by
  intro hpc
  exact not_posComboRealRooted_quadratic_roots_gap hcd hab hz hbz1 hz2c hpc.comm

end RealRooted
