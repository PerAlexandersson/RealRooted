import RealRooted.CombinatorialExamples.BigDescents321.Criterion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# From the Gegenbauer side back to `A_n` and `M_(n-2)`

The substitution `ρ = 1 - c⁻²` turns the zeros `a ∈ (0, 1)` of `G_k` into the zeros `ρ < 0` of
the reference Motzkin polynomial `M_k`, since `(c/2)^k M_k(1 - c⁻²) = μ_k(c) ∝ G_k(c)` and
`(c/2)^n A_n(1 - c⁻²) = Q_n(c)` (issue #1143, §13). Differentiating the first identity at a zero
gives `M_k'(ρ)` in terms of `G_k'(a)`, and the node relation `Q_n(a) = -a G_(k-1)(a) F_n(a)`
with `F_n(a) > 0` and `G_(k-1)(a) G_k'(a) > 0` yields `A_n(ρ) M_k'(ρ) < 0`.

## Main statements

* `eval_motzkinRef_pos_of_nonneg`: `M_k` has no zero on `[0, ∞)`.
* `eval_mul_derivative_neg`: `A_n(ρ) M_(n-2)'(ρ) < 0` at every zero `ρ` of `M_(n-2)`, `n ≥ 25`.
-/

open Polynomial Finset

namespace RealRooted.BigDescents321

/-- `M_k(x) > 0` for `x ≥ 0`: the coefficients are nonnegative and `M_k(0) = 2^k`. -/
theorem eval_motzkinRef_pos_of_nonneg (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < (motzkinRef k : ℝ[X]).eval x := by
  rw [eval_eq_sum_range]
  have h0 : (motzkinRef k : ℝ[X]).coeff 0 * x ^ 0 = 2 ^ k := by
    rw [pow_zero, mul_one, coeff_zero_eq_eval_zero, eval_zero_motzkinRef]
  calc (0 : ℝ) < 2 ^ k := by positivity
    _ = (motzkinRef k : ℝ[X]).coeff 0 * x ^ 0 := h0.symm
    _ ≤ ∑ i ∈ range ((motzkinRef k : ℝ[X]).natDegree + 1),
          (motzkinRef k : ℝ[X]).coeff i * x ^ i := by
      apply single_le_sum (f := fun i ↦ (motzkinRef k : ℝ[X]).coeff i * x ^ i)
      · intro i _
        rw [coeff_motzkinRef_eq_cast]
        positivity
      · simp

theorem neg_of_isRoot_motzkinRef {k : ℕ} {r : ℝ} (hr : (motzkinRef k : ℝ[X]).IsRoot r) : r < 0 := by
  by_contra h
  exact (eval_motzkinRef_pos_of_nonneg k (not_lt.mp h)).ne' hr

/-- The zero `a = (1 - ρ)^(-1/2) ∈ (0, 1)` of `G_k` attached to `ρ < 0`. -/
noncomputable def nodeOf (ρ : ℝ) : ℝ := 1 / Real.sqrt (1 - ρ)

theorem nodeOf_pos {ρ : ℝ} (hρ : ρ < 0) : 0 < nodeOf ρ := by
  unfold nodeOf
  have : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.mpr (by linarith)
  positivity

theorem nodeOf_lt_one {ρ : ℝ} (hρ : ρ < 0) : nodeOf ρ < 1 := by
  unfold nodeOf
  have h1 : 1 < Real.sqrt (1 - ρ) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  rw [div_lt_one (by linarith)]
  exact h1

theorem one_sub_inv_sq_nodeOf {ρ : ℝ} (hρ : ρ < 0) : 1 - (nodeOf ρ ^ 2)⁻¹ = ρ := by
  unfold nodeOf
  rw [div_pow, one_pow, Real.sq_sqrt (by linarith), one_div, inv_inv]
  ring

private theorem refHom_coeff_ne_zero (k : ℕ) :
    (((2 : ℚ) / ((k + 1) * (k + 2)) : ℚ) : ℝ) ≠ 0 := by
  have : (0 : ℚ) < 2 / ((k + 1) * (k + 2)) := by positivity
  exact Rat.cast_ne_zero.mpr this.ne'

/-- The node of a zero of `M_k` is a zero of `G_k`. -/
theorem aeval_gegen_nodeOf {k : ℕ} {r : ℝ} (hr : (motzkinRef k : ℝ[X]).IsRoot r) :
    aeval (nodeOf r) (gegen k) = 0 := by
  have hr0 := neg_of_isRoot_motzkinRef hr
  have h := aeval_refHom (nodeOf_pos hr0).ne' k
  rw [one_sub_inv_sq_nodeOf hr0, hr.eq_zero, mul_zero, refHom_eq_C_mul, map_mul, aeval_C,
    eq_ratCast] at h
  exact (mul_eq_zero.mp h).resolve_left (refHom_coeff_ne_zero k)

/-- Differentiating `μ_k(c) = (c/2)^k M_k(1 - c⁻²)` at a zero `a ≠ 0`. -/
theorem aeval_derivative_refHom {k : ℕ} {a : ℝ} (ha : a ≠ 0)
    (hM : (motzkinRef k : ℝ[X]).eval (1 - (a ^ 2)⁻¹) = 0) :
    aeval a (derivative (refHom k)) =
      (a / 2) ^ k * (motzkinRef k : ℝ[X]).derivative.eval (1 - (a ^ 2)⁻¹) *
        (2 * a / (a ^ 2) ^ 2) := by
  have h1 : HasDerivAt (fun c : ℝ ↦ aeval c (refHom k)) (aeval a (derivative (refHom k))) a :=
    Polynomial.hasDerivAt_aeval _ _
  have hin : HasDerivAt (fun c : ℝ ↦ 1 - (c ^ 2)⁻¹) (2 * a / (a ^ 2) ^ 2) a := by
    have h := ((hasDerivAt_pow 2 a).inv (pow_ne_zero 2 ha)).const_sub 1
    convert h using 1
    push_cast
    ring
  have h2 : HasDerivAt (fun c : ℝ ↦ (c / 2) ^ k * (motzkinRef k : ℝ[X]).eval (1 - (c ^ 2)⁻¹))
      (k * (a / 2) ^ (k - 1) * (1 / 2) * (motzkinRef k : ℝ[X]).eval (1 - (a ^ 2)⁻¹) +
        (a / 2) ^ k * ((motzkinRef k : ℝ[X]).derivative.eval (1 - (a ^ 2)⁻¹) *
          (2 * a / (a ^ 2) ^ 2))) a := by
    have hp : HasDerivAt (fun c : ℝ ↦ (c / 2) ^ k) (k * (a / 2) ^ (k - 1) * (1 / 2)) a := by
      have := ((hasDerivAt_id' a).div_const 2).pow k
      convert this using 1
    exact hp.mul (((motzkinRef k : ℝ[X]).hasDerivAt _).comp a hin)
  have heq : (fun c : ℝ ↦ aeval c (refHom k)) =ᶠ[nhds a]
      fun c ↦ (c / 2) ^ k * (motzkinRef k : ℝ[X]).eval (1 - (c ^ 2)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds ha] with c hc
    exact aeval_refHom hc k
  have := h1.unique (h2.congr_of_eventuallyEq heq)
  rw [this, hM, mul_zero, zero_add]
  ring

theorem aeval_gegen_eq (j : ℕ) (a : ℝ) :
    aeval a (gegen j) = (gegenLead j : ℝ) * (refMonic j).eval a := by
  rw [aeval_def, eval₂_eq_eval_map, ← gegenReal, gegenReal_eq, eval_mul, eval_C]

theorem aeval_derivative_gegen_eq (j : ℕ) (a : ℝ) :
    aeval a (derivative (gegen j)) = (gegenLead j : ℝ) * (refMonic j).derivative.eval a := by
  rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, ← gegenReal, gegenReal_eq, derivative_mul,
    derivative_C, zero_mul, zero_add, eval_mul, eval_C]

/-- `G_(k-1)(a) G_k'(a) > 0` at a zero `a` of `G_k`, `k ≥ 1`. -/
theorem gegen_mul_derivative_pos {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : aeval a (gegen k) = 0) :
    0 < aeval a (gegen (k - 1)) * aeval a (derivative (gegen k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by lia⟩
  have hl : ∀ j, (0 : ℝ) < gegenLead j := fun j ↦ by exact_mod_cast gegenLead_pos j
  have hroot : (refMonic (m + 1)).IsRoot a := by
    rw [aeval_gegen_eq] at ha
    exact (mul_eq_zero.mp ha).resolve_left (hl _).ne'
  have h := eval_mul_derivative_pos_of_isRoot_refMonic hroot
  rw [Nat.add_sub_cancel, aeval_gegen_eq, aeval_derivative_gegen_eq]
  have := mul_pos (mul_pos (hl m) (hl (m + 1))) h
  linarith [this]

/-- The sign condition `A_n(ρ) M_(n-2)'(ρ) < 0` at every zero `ρ` of `M_(n-2)`, `n ≥ 25`. -/
theorem eval_mul_derivative_neg {k : ℕ} (hk : 23 ≤ k) {r : ℝ}
    (hr : (motzkinRef k : ℝ[X]).IsRoot r) :
    (bigDescentPoly (k + 2) : ℝ[X]).eval r * (motzkinRef k : ℝ[X]).derivative.eval r < 0 := by
  have hr0 := neg_of_isRoot_motzkinRef hr
  set a := nodeOf r with ha_def
  have ha := nodeOf_pos hr0
  have ha1 := nodeOf_lt_one hr0
  have hρ := one_sub_inv_sq_nodeOf hr0
  have hG := aeval_gegen_nodeOf hr
  have hQ := aeval_transformed ha.ne' (k + 2)
  have hQ2 := aeval_transformed_eq_neg_mul (k := k) (by lia) hG
  have hD := aeval_derivative_refHom (k := k) ha.ne' (by rw [hρ]; exact hr)
  rw [refHom_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add, map_mul, aeval_C,
    eq_ratCast, hρ] at hD
  rw [hρ] at hQ
  have hF := zetaF_pos hk (x := a) (by rw [abs_of_pos ha]; exact ha1.le)
  have hs := gegen_mul_derivative_pos (k := k) (by lia) hG
  have hc : (0 : ℝ) < (((2 : ℚ) / ((k + 1) * (k + 2)) : ℚ) : ℝ) := by
    have : (0 : ℚ) < 2 / ((k + 1) * (k + 2)) := by positivity
    exact_mod_cast this
  set A := (bigDescentPoly (k + 2) : ℝ[X]).eval r
  set M' := (motzkinRef k : ℝ[X]).derivative.eval r
  have hP : 0 < (a / 2) ^ (k + 2) * ((a / 2) ^ k * (2 * a / (a ^ 2) ^ 2)) := by positivity
  have key : A * M' * ((a / 2) ^ (k + 2) * ((a / 2) ^ k * (2 * a / (a ^ 2) ^ 2))) =
      -a * (((2 : ℚ) / ((k + 1) * (k + 2)) : ℚ) : ℝ) * zetaF k a *
        (aeval a (gegen (k - 1)) * aeval a (derivative (gegen k))) := by
    have e1 : (a / 2) ^ (k + 2) * A = -a * aeval a (gegen (k - 1)) * zetaF k a := by
      rw [← hQ, hQ2]
    have e2 : (a / 2) ^ k * M' * (2 * a / (a ^ 2) ^ 2) =
        (((2 : ℚ) / ((k + 1) * (k + 2)) : ℚ) : ℝ) * aeval a (derivative (gegen k)) := hD.symm
    calc A * M' * ((a / 2) ^ (k + 2) * ((a / 2) ^ k * (2 * a / (a ^ 2) ^ 2)))
        = ((a / 2) ^ (k + 2) * A) * ((a / 2) ^ k * M' * (2 * a / (a ^ 2) ^ 2)) := by ring
      _ = _ := by rw [e1, e2]; ring
  have hneg : -a * (((2 : ℚ) / ((k + 1) * (k + 2)) : ℚ) : ℝ) * zetaF k a *
      (aeval a (gegen (k - 1)) * aeval a (derivative (gegen k))) < 0 := by
    have := mul_pos (mul_pos (mul_pos ha hc) hF) hs
    linarith
  by_contra hcon
  push Not at hcon
  have := mul_nonneg hcon hP.le
  linarith

/-! ### `M_k` splits with simple roots -/

theorem refMonic_ne_zero (k : ℕ) : refMonic k ≠ 0 :=
  (satisfiesFavardRecurrence_refMonic.monic k).ne_zero

/-- `G_k` has at least `⌊k/2⌋` positive zeros: its zeros are simple and symmetric. -/
theorem le_card_pos_roots_refMonic (k : ℕ) :
    k / 2 ≤ ((refMonic k).roots.toFinset.filter (0 < ·)).card := by
  set T := (refMonic k).roots.toFinset
  have hT : T.card = k := by
    rw [Multiset.toFinset_card_of_nodup (refMonic_roots_nodup k),
      (splits_iff_card_roots.mp (refMonic_splits k)),
      satisfiesFavardRecurrence_refMonic.natDegree_eq]
  have hmem : ∀ x, x ∈ T ↔ (refMonic k).IsRoot x := fun x ↦ by
    rw [Multiset.mem_toFinset, mem_roots (refMonic_ne_zero k)]
  have hneg : ∀ x, x ∈ T → -x ∈ T := fun x hx ↦ by
    rw [hmem] at hx ⊢
    rw [IsRoot.def, eval_neg_refMonic, hx.eq_zero, mul_zero]
  have hN : T.filter (· < 0) = (T.filter (0 < ·)).image (fun x ↦ -x) := by
    ext x
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hx, hx0⟩
      exact ⟨-x, ⟨hneg x hx, by linarith⟩, neg_neg x⟩
    · rintro ⟨y, ⟨hy, hy0⟩, rfl⟩
      exact ⟨hneg y hy, by linarith⟩
  have hNcard : (T.filter (· < 0)).card = (T.filter (0 < ·)).card := by
    rw [hN, card_image_of_injective _ neg_injective]
  have hZ : (T.filter (· = 0)).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    rw [(mem_filter.mp hx).2, (mem_filter.mp hy).2]
  have hsplit1 := card_filter_add_card_filter_not (s := T) (fun x : ℝ ↦ 0 < x)
  have hsplit2 := card_filter_add_card_filter_not (s := T.filter (fun x : ℝ ↦ ¬ 0 < x))
    (fun x : ℝ ↦ x < 0)
  have e1 : (T.filter (fun x : ℝ ↦ ¬ 0 < x)).filter (fun x ↦ x < 0) = T.filter (· < 0) := by
    ext x; simp only [mem_filter]; constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
  have e2 : (T.filter (fun x : ℝ ↦ ¬ 0 < x)).filter (fun x ↦ ¬ x < 0) = T.filter (· = 0) := by
    ext x; simp only [mem_filter]; constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, by linarith⟩
  rw [e1, e2] at hsplit2
  lia

/-- `M_k` splits over `ℝ` with simple zeros. -/
theorem motzkinRef_splits_nodup (k : ℕ) :
    (motzkinRef k : ℝ[X]).Splits ∧ (motzkinRef k : ℝ[X]).roots.Nodup := by
  set M := (motzkinRef k : ℝ[X])
  set P := (refMonic k).roots.toFinset.filter (0 < ·)
  have hM0 : M ≠ 0 := motzkinRef_ne_zero k
  have hsub : P.image (fun a ↦ 1 - (a ^ 2)⁻¹) ⊆ M.roots.toFinset := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    obtain ⟨har, ha0⟩ := mem_filter.mp ha
    have hroot : (refMonic k).IsRoot a :=
      (mem_roots (refMonic_ne_zero k)).mp (Multiset.mem_toFinset.mp har)
    have hG : aeval a (gegen k) = 0 := by rw [aeval_gegen_eq, hroot.eq_zero, mul_zero]
    have h := aeval_refHom (ne_of_gt ha0) k
    rw [refHom_eq_C_mul, map_mul, aeval_C, hG, mul_zero] at h
    have hpow : (a / 2) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
    rw [Multiset.mem_toFinset, mem_roots hM0]
    exact (mul_eq_zero.mp h.symm).resolve_left hpow
  have hinj : Set.InjOn (fun a : ℝ ↦ 1 - (a ^ 2)⁻¹) P := by
    intro a ha b hb hab
    have ha0 := (mem_filter.mp ha).2
    have hb0 := (mem_filter.mp hb).2
    have h2 : a ^ 2 = b ^ 2 := by
      have : (a ^ 2)⁻¹ = (b ^ 2)⁻¹ := by simpa using hab
      exact inv_injective this
    exact (pow_left_inj₀ ha0.le hb0.le two_ne_zero).mp h2
  have hcard : P.card ≤ M.roots.toFinset.card :=
    (card_image_of_injOn hinj).symm.le.trans (card_le_card hsub)
  have hdeg : M.natDegree = k / 2 := natDegree_motzkinRef k
  have hle1 : M.roots.toFinset.card ≤ Multiset.card M.roots := Multiset.toFinset_card_le _
  have hle2 : Multiset.card M.roots ≤ M.natDegree := card_roots' M
  have hP := le_card_pos_roots_refMonic k
  exact ⟨splits_iff_card_roots.mpr (by lia),
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by lia)⟩

end RealRooted.BigDescents321
