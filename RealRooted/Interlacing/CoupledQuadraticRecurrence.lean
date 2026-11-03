module

public import RealRooted.SimpleRoots
public import RealRooted.Basic.Coefficients
import RealRooted.MaWang.Strong

/-!
# A coupled quadratic recurrence with varying coefficients

Let `ℓₙ = aₙ t + bₙ` with `aₙ > 0`.  Assume `u₀ > 0`, `uₙ ≥ 0`, and `vₙ > 0` for `n ≥ 1`.
The coupled polynomial sequences `Aₙ`, `Bₙ` are given by `A₀ = 1`, `B₁ = ℓ₀`, `A₁ = ℓ₀² - u₀` and,
for `n ≥ 1`,
`Bₙ₊₁ = ℓₙ Aₙ - vₙ Bₙ` and `Aₙ₊₁ = (ℓₙ² - uₙ) Aₙ - 2 vₙ ℓₙ Bₙ + vₙ² Aₙ₋₁`.

We prove that, for `n ≥ 1`, `Aₙ` and `Bₙ` have degrees `2n` and `2n - 1`, positive leading
coefficients and simple real roots, and that `Bₙ ≺ Aₙ ≺ Bₙ₊₁` strictly interlace.  The key
identity is `Δₙ₊₁ = vₙ² Δₙ - uₙ Aₙ²` for `Δₙ = Aₙ Aₙ₋₁ - Bₙ²`, which shows that `Δₙ < 0` on all
of `ℝ`.  The interlacing follows from two applications of the root-sign criterion
`strictInterl_of_interlaces_eval_mul_neg_succ`.

In the statements below all indices of the `n ≥ 1` range are written as `n + 1`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The data of the coupled quadratic recurrence: coefficient sequences `a b u v` with
`ℓₙ = aₙ X + bₙ`, the seeds and the two recurrences for polynomial sequences `A B`, and the sign
conditions `aₙ > 0`, `u₀ > 0`, `uₙ ≥ 0` and `vₙ > 0` for `n ≥ 1`. -/
structure CoupledQuadraticRecurrence (a b u v : ℕ → ℝ) (A B : ℕ → ℝ[X]) : Prop where
  /-- `a n > 0`. -/
  a_pos : ∀ n, 0 < a n
  /-- `u 0 > 0`. -/
  u_zero_pos : 0 < u 0
  /-- `u n ≥ 0`. -/
  u_nonneg : ∀ n, 0 ≤ u n
  /-- `v (n + 1) > 0`. -/
  v_pos : ∀ n, 0 < v (n + 1)
  /-- `A₀ = 1`. -/
  A_zero : A 0 = 1
  /-- `B₁ = ℓ₀`. -/
  B_one : B 1 = C (a 0) * X + C (b 0)
  /-- `A₁ = ℓ₀² - u₀`. -/
  A_one : A 1 = (C (a 0) * X + C (b 0)) ^ 2 - C (u 0)
  /-- `Bₙ₊₁ = ℓₙ Aₙ - vₙ Bₙ` for `n ≥ 1`. -/
  B_succ : ∀ n, B (n + 2) =
    (C (a (n + 1)) * X + C (b (n + 1))) * A (n + 1) - C (v (n + 1)) * B (n + 1)
  /-- `Aₙ₊₁ = (ℓₙ² - uₙ) Aₙ - 2 vₙ ℓₙ Bₙ + vₙ² Aₙ₋₁` for `n ≥ 1`. -/
  A_succ : ∀ n, A (n + 2) =
    ((C (a (n + 1)) * X + C (b (n + 1))) ^ 2 - C (u (n + 1))) * A (n + 1)
      - 2 * C (v (n + 1)) * (C (a (n + 1)) * X + C (b (n + 1))) * B (n + 1)
      + C (v (n + 1)) ^ 2 * A n

namespace CoupledQuadraticRecurrence

variable {a b u v : ℕ → ℝ} {A B : ℕ → ℝ[X]}

/-! ### The identity for `Δ` and its sign -/

/-- `Δ₁ = -u₀`, where `Δₙ = Aₙ Aₙ₋₁ - Bₙ²`. -/
theorem A_one_mul_A_zero_sub_sq (h : CoupledQuadraticRecurrence a b u v A B) :
    A 1 * A 0 - B 1 ^ 2 = -C (u 0) := by
  rw [h.A_one, h.B_one, h.A_zero]
  ring

/-- The identity `Δₙ₊₁ = vₙ² Δₙ - uₙ Aₙ²` for `Δₙ = Aₙ Aₙ₋₁ - Bₙ²`. -/
theorem A_succ_mul_A_sub_sq (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    A (n + 2) * A (n + 1) - B (n + 2) ^ 2 =
      C (v (n + 1)) ^ 2 * (A (n + 1) * A n - B (n + 1) ^ 2) - C (u (n + 1)) * A (n + 1) ^ 2 := by
  rw [h.A_succ n, h.B_succ n]
  ring

/-- `Δₙ(t) < 0` for every real `t` and `n ≥ 1`, where `Δₙ = Aₙ Aₙ₋₁ - Bₙ²`. -/
theorem eval_A_succ_mul_A_sub_sq_neg (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ)
    (t : ℝ) : (A (n + 1)).eval t * (A n).eval t - ((B (n + 1)).eval t) ^ 2 < 0 := by
  induction n with
  | zero =>
    have := congrArg (eval t) h.A_one_mul_A_zero_sub_sq
    simp only [eval_sub, eval_mul, eval_pow, eval_neg, eval_C] at this
    linarith [h.u_zero_pos]
  | succ n ih =>
    have := congrArg (eval t) (h.A_succ_mul_A_sub_sq n)
    simp only [eval_sub, eval_mul, eval_pow, eval_C] at this
    have hv := h.v_pos n
    have hu := h.u_nonneg (n + 1)
    nlinarith [sq_nonneg ((A (n + 1)).eval t), mul_nonneg hu (sq_nonneg ((A (n + 1)).eval t)),
      mul_pos (pow_pos hv 2) (neg_pos.mpr ih)]

/-! ### Degrees and leading coefficients -/

private lemma natDegree_add_and_hasPosLeadingCoeff {p q : ℝ[X]} {d : ℕ} (hp : p.natDegree = d)
    (hpos : HasPosLeadingCoeff p) (hq : q.natDegree < d) :
    (p + q).natDegree = d ∧ HasPosLeadingCoeff (p + q) := by
  have hdeg : q.degree < p.degree := degree_lt_degree (by lia)
  exact ⟨by rw [natDegree_add_eq_left_of_degree_lt hdeg, hp],
    by unfold HasPosLeadingCoeff; rwa [leadingCoeff_add_of_degree_lt' hdeg]⟩

private lemma natDegree_linear_mul {a b : ℝ} (ha : 0 < a) {p : ℝ[X]} {d : ℕ}
    (hp : p.natDegree = d) (hpos : HasPosLeadingCoeff p) :
    (((C a * X + C b) * p).natDegree = d + 1) ∧ HasPosLeadingCoeff ((C a * X + C b) * p) := by
  have hne : p ≠ 0 := hpos.ne_zero
  have hl : C a * X + C b ≠ 0 := fun h0 => by
    simpa [natDegree_linear ha.ne'] using congrArg natDegree h0
  refine ⟨?_, ?_⟩
  · rw [natDegree_mul hl hne, natDegree_linear ha.ne', hp]
    lia
  · unfold HasPosLeadingCoeff
    rw [leadingCoeff_mul, leadingCoeff_linear ha.ne']
    exact mul_pos ha hpos

private lemma natDegree_sq_sub_and_hasPosLeadingCoeff {a b u : ℝ} (ha : 0 < a) :
    ((C a * X + C b) ^ 2 - C u).natDegree = 2 ∧
      HasPosLeadingCoeff ((C a * X + C b) ^ 2 - C u) := by
  have hsq := natDegree_linear (b := b) ha.ne'
  have hlead := leadingCoeff_linear (b := b) ha.ne'
  have h2 : ((C a * X + C b) ^ 2).natDegree = 2 := by rw [natDegree_pow, hsq]
  have hpos : HasPosLeadingCoeff ((C a * X + C b) ^ 2) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_pow, hlead]
    positivity
  simpa [sub_eq_add_neg] using natDegree_add_and_hasPosLeadingCoeff (q := -C u) h2 hpos
    (by simp)

/-- The degrees and leading coefficients of `A` and `B`, proved by induction. -/
private lemma natDegree_and_hasPosLeadingCoeff (h : CoupledQuadraticRecurrence a b u v A B)
    (n : ℕ) :
    (A n).natDegree ≤ 2 * n ∧ (A (n + 1)).natDegree = 2 * n + 2 ∧ HasPosLeadingCoeff (A (n + 1)) ∧
      (B (n + 1)).natDegree = 2 * n + 1 ∧ HasPosLeadingCoeff (B (n + 1)) := by
  induction n with
  | zero =>
    have hB := natDegree_linear (b := b 0) (h.a_pos 0).ne'
    have hsq := natDegree_sq_sub_and_hasPosLeadingCoeff (b := b 0) (u := u 0) (h.a_pos 0)
    refine ⟨by simp [h.A_zero], by rw [h.A_one]; exact hsq.1, by rw [h.A_one]; exact hsq.2,
      by rwa [h.B_one], ?_⟩
    unfold HasPosLeadingCoeff
    rw [h.B_one, leadingCoeff_linear (h.a_pos 0).ne']
    exact h.a_pos 0
  | succ n ih =>
    obtain ⟨hAn, hA, hApos, hB, hBpos⟩ := ih
    have ha := h.a_pos (n + 1)
    obtain ⟨hdB, hposB⟩ := natDegree_linear_mul (b := b (n + 1)) ha hA hApos
    have hq : (C (v (n + 1)) * B (n + 1)).natDegree < 2 * n + 2 + 1 :=
      lt_of_le_of_lt (natDegree_C_mul_le _ _) (by lia)
    obtain ⟨hdB', hposB'⟩ := natDegree_add_and_hasPosLeadingCoeff
      (q := -(C (v (n + 1)) * B (n + 1))) hdB hposB (by rwa [natDegree_neg])
    obtain ⟨hdsq, hpossq⟩ := natDegree_sq_sub_and_hasPosLeadingCoeff (b := b (n + 1))
      (u := u (n + 1)) ha
    have hmul : (((C (a (n + 1)) * X + C (b (n + 1))) ^ 2 - C (u (n + 1))) *
        A (n + 1)).natDegree = 2 * n + 4 := by
      rw [natDegree_mul hpossq.ne_zero hApos.ne_zero, hdsq, hA]
      lia
    have hmulpos : HasPosLeadingCoeff (((C (a (n + 1)) * X + C (b (n + 1))) ^ 2 -
        C (u (n + 1))) * A (n + 1)) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul]
      exact mul_pos hpossq hApos
    have hq1 : (2 * C (v (n + 1)) * (C (a (n + 1)) * X + C (b (n + 1))) *
        B (n + 1)).natDegree ≤ 2 * n + 2 := by
      have e : (2 * C (v (n + 1)) * (C (a (n + 1)) * X + C (b (n + 1))) * B (n + 1) : ℝ[X]) =
          C (2 * v (n + 1)) * ((C (a (n + 1)) * X + C (b (n + 1))) * B (n + 1)) := by
        simp only [map_mul, map_ofNat]
        ring
      have hl := natDegree_linear_le (a := a (n + 1)) (b := b (n + 1))
      rw [e]
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      lia
    have hq2 : (C (v (n + 1)) ^ 2 * A n).natDegree ≤ 2 * n :=
      natDegree_mul_le.trans (by simpa using hAn)
    obtain ⟨hdA', hposA'⟩ := natDegree_add_and_hasPosLeadingCoeff
      (q := C (v (n + 1)) ^ 2 * A n - 2 * C (v (n + 1)) * (C (a (n + 1)) * X + C (b (n + 1))) *
        B (n + 1)) hmul hmulpos (lt_of_le_of_lt (natDegree_sub_le _ _) (by lia))
    have hAeq : A (n + 2) = ((C (a (n + 1)) * X + C (b (n + 1))) ^ 2 - C (u (n + 1))) *
        A (n + 1) + (C (v (n + 1)) ^ 2 * A n - 2 * C (v (n + 1)) *
          (C (a (n + 1)) * X + C (b (n + 1))) * B (n + 1)) := by
      rw [h.A_succ n]
      ring
    refine ⟨by lia, ?_, ?_, ?_, ?_⟩
    · rw [hAeq]
      lia
    · rwa [hAeq]
    · rw [h.B_succ n, sub_eq_add_neg]
      lia
    · rw [h.B_succ n, sub_eq_add_neg]
      exact hposB'

/-- `deg Aₙ = 2n` for `n ≥ 1`. -/
theorem natDegree_A_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    (A (n + 1)).natDegree = 2 * n + 2 :=
  (natDegree_and_hasPosLeadingCoeff h n).2.1

/-- `deg Bₙ = 2n - 1` for `n ≥ 1`. -/
theorem natDegree_B_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    (B (n + 1)).natDegree = 2 * n + 1 :=
  (natDegree_and_hasPosLeadingCoeff h n).2.2.2.1

/-- `Aₙ` has positive leading coefficient for `n ≥ 1`. -/
theorem hasPosLeadingCoeff_A_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    HasPosLeadingCoeff (A (n + 1)) :=
  (natDegree_and_hasPosLeadingCoeff h n).2.2.1

/-- `Bₙ` has positive leading coefficient for `n ≥ 1`. -/
theorem hasPosLeadingCoeff_B_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    HasPosLeadingCoeff (B (n + 1)) :=
  (natDegree_and_hasPosLeadingCoeff h n).2.2.2.2

/-- `Aₙ` has positive leading coefficient for all `n`, including `A₀ = 1`. -/
theorem hasPosLeadingCoeff_A (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    HasPosLeadingCoeff (A n) := by
  cases n with
  | zero => simp [h.A_zero, HasPosLeadingCoeff]
  | succ n => exact h.hasPosLeadingCoeff_A_succ n

/-! ### Interlacing -/

/-- The constant `1` is interlaced by a polynomial of degree one. -/
private lemma interlaces_one_linear {a b : ℝ} (ha : 0 < a) :
    Interlaces 1 (C a * X + C b) := by
  have hne : C a * X + C b ≠ 0 := fun h0 => by
    simpa [natDegree_linear ha.ne'] using congrArg natDegree h0
  have hdeg : (C a * X + C b).degree ≤ 1 := degree_linear_le
  have hsplit : (C a * X + C b).Splits := Splits.of_degree_le_one hdeg
  have hroot : (C a * X + C b).roots = {-b / a} := by
    rw [roots_C_mul_X_add_C _ ha.ne']
    simp [div_eq_inv_mul]
  refine ⟨⟨hne, hsplit⟩, ⟨one_ne_zero, Splits.one⟩, by simp [natDegree_linear ha.ne'], [-b / a], [],
    by simp, by simp, by simp [hroot], by simp, by simp [ListInterlaces]⟩

/-- Second root-sign step: from `Aₙ ≺ Bₙ₊₁` we get `Bₙ₊₁ ≺ Aₙ₊₁`, for all `n ≥ 0`. -/
private lemma strictInterl_B_succ_A_succ_of_interlaces
    (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) (hI : Interlaces (A n) (B (n + 1))) :
    StrictInterl (B (n + 1)) (A (n + 1)) := by
  refine strictInterl_of_interlaces_eval_mul_neg_succ hI (h.hasPosLeadingCoeff_A n)
    (h.hasPosLeadingCoeff_A_succ n) (by rw [h.natDegree_A_succ, h.natDegree_B_succ]) ?_
  intro r hr
  have := h.eval_A_succ_mul_A_sub_sq_neg n r
  rwa [show (B (n + 1)).eval r = 0 from hr, zero_pow two_ne_zero, sub_zero] at this

/-- First root-sign step: from `Bₙ ≺ Aₙ` we get `Aₙ ≺ Bₙ₊₁`, for all `n ≥ 1`. -/
private lemma strictInterl_A_succ_B_succ_of_interlaces
    (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) (hI : Interlaces (B (n + 1)) (A (n + 1))) :
    StrictInterl (A (n + 1)) (B (n + 2)) := by
  refine strictInterl_of_interlaces_eval_mul_neg_succ hI (h.hasPosLeadingCoeff_B_succ n)
    (h.hasPosLeadingCoeff_B_succ (n + 1)) (by rw [h.natDegree_A_succ, h.natDegree_B_succ]; lia) ?_
  intro r hr
  have hA : (A (n + 1)).eval r = 0 := hr
  have hΔ := h.eval_A_succ_mul_A_sub_sq_neg n r
  rw [hA, zero_mul, zero_sub, neg_lt_zero] at hΔ
  have hv := h.v_pos n
  have hB := congrArg (eval r) (h.B_succ n)
  simp only [eval_sub, eval_mul, eval_C, hA, mul_zero, zero_sub] at hB
  rw [hB]
  nlinarith [mul_pos hv hΔ]

/-- The strict interlacing `Bₙ ≺ Aₙ` for `n ≥ 1`. -/
theorem strictInterl_B_succ_A_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    StrictInterl (B (n + 1)) (A (n + 1)) := by
  induction n with
  | zero =>
    refine h.strictInterl_B_succ_A_succ_of_interlaces 0 ?_
    rw [h.A_zero, h.B_one]
    exact interlaces_one_linear (h.a_pos 0)
  | succ n ih =>
    have h1 := h.strictInterl_A_succ_B_succ_of_interlaces n
      (ih.toInterlaces (by rw [h.natDegree_A_succ, h.natDegree_B_succ]))
    exact h.strictInterl_B_succ_A_succ_of_interlaces (n + 1)
      (h1.toInterlaces (by rw [h.natDegree_A_succ, h.natDegree_B_succ]; lia))

/-- The strict interlacing `Aₙ ≺ Bₙ₊₁` for `n ≥ 1`. -/
theorem strictInterl_A_succ_B_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    StrictInterl (A (n + 1)) (B (n + 2)) :=
  h.strictInterl_A_succ_B_succ_of_interlaces n
    ((h.strictInterl_B_succ_A_succ n).toInterlaces
      (by rw [h.natDegree_A_succ, h.natDegree_B_succ]))

/-- `Aₙ` and `Bₙ` have no common real root, for `n ≥ 1`. -/
theorem not_isRoot_A_succ_of_isRoot_B_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ)
    {r : ℝ} (hB : (B (n + 1)).IsRoot r) : ¬ (A (n + 1)).IsRoot r := fun hA => by
  have := h.eval_A_succ_mul_A_sub_sq_neg n r
  rw [show (B (n + 1)).eval r = 0 from hB, show (A (n + 1)).eval r = 0 from hA] at this
  simp at this

/-- `Aₙ` and `Bₙ` have simple real roots, for `n ≥ 1`. -/
theorem hasSimpleRoots_A_succ_and_B_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    HasSimpleRoots (B (n + 1)) ∧ HasSimpleRoots (A (n + 1)) :=
  (h.strictInterl_B_succ_A_succ n).hasSimpleRoots_of_no_common_root fun _ hr =>
    h.not_isRoot_A_succ_of_isRoot_B_succ n hr.1 hr.2

/-- `Bₙ` has simple real roots for `n ≥ 1`. -/
theorem hasSimpleRoots_B_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    HasSimpleRoots (B (n + 1)) :=
  (h.hasSimpleRoots_A_succ_and_B_succ n).1

/-- `Aₙ` has simple real roots for `n ≥ 1`. -/
theorem hasSimpleRoots_A_succ (h : CoupledQuadraticRecurrence a b u v A B) (n : ℕ) :
    HasSimpleRoots (A (n + 1)) :=
  (h.hasSimpleRoots_A_succ_and_B_succ n).2

end CoupledQuadraticRecurrence

end RealRooted
