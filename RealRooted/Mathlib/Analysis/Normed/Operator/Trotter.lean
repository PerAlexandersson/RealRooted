/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Lie–Trotter product formula

For bounded operators `A` and `B` on a real Banach space,
`(exp ((t / n) • A) * exp ((t / n) • B)) ^ n` tends to `exp (t • (A + B))`.
No commutativity hypothesis is needed. The proof bounds the one-step defect by `C s²` from the
exponential power series and telescopes the difference of `n`-th powers.

The proof was found by Aristotle (Harmonic).
-/

@[expose] public section

open Filter Topology

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
private lemma norm_pow_le_of_one (h1 : ‖(1 : 𝔸)‖ ≤ 1) (X : 𝔸) (n : ℕ) :
    ‖X ^ n‖ ≤ ‖X‖ ^ n := by
  rcases n with _ | n
  · simpa using h1
  · exact norm_pow_le' X n.succ_pos

private lemma real_exp_eq_tsum (r : ℝ) : Real.exp r = ∑' n : ℕ, r ^ n / n.factorial := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

omit [CompleteSpace 𝔸] in
private lemma norm_exp_le' (h1 : ‖(1 : 𝔸)‖ ≤ 1) (X : 𝔸) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  rw [NormedSpace.exp_eq_tsum ℝ, real_exp_eq_tsum]
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' X)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (NormedSpace.norm_expSeries_summable' X)
    (Real.summable_pow_div_factorial _)
  rw [norm_smul, div_eq_inv_mul, norm_inv, Real.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_le_of_one h1 X n) (by positivity)

private lemma norm_exp_sub_one_sub_le (X : 𝔸) :
    ‖NormedSpace.exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) X
  have key : NormedSpace.exp X - 1 - X =
      ∑' n : ℕ, ((n + 2).factorial⁻¹ : ℝ) • X ^ (n + 2) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    beta_reduce
    rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hs).tsum_eq_zero_add]
    simp
  have hn : Summable fun n : ℕ => ‖((n + 2).factorial⁻¹ : ℝ) • X ^ (n + 2)‖ :=
    (summable_nat_add_iff 2).2 (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X)
  rw [key, real_exp_eq_tsum, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm hn).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hn
    ((Real.summable_pow_div_factorial _).mul_left _)
  rw [norm_smul, norm_inv, Real.norm_natCast]
  have h1 : ‖X ^ (n + 2)‖ ≤ ‖X‖ ^ 2 * ‖X‖ ^ n := by
    rw [← pow_add, add_comm]; exact norm_pow_le' X (by lia)
  have h2 : (n.factorial : ℝ) ≤ (n + 2).factorial := by
    exact_mod_cast Nat.factorial_le (by lia)
  have h3 : (0:ℝ) < n.factorial := by positivity
  calc ((n + 2).factorial : ℝ)⁻¹ * ‖X ^ (n + 2)‖
        ≤ ((n + 2).factorial : ℝ)⁻¹ * (‖X‖ ^ 2 * ‖X‖ ^ n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (n.factorial : ℝ)⁻¹ * (‖X‖ ^ 2 * ‖X‖ ^ n) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ h3 h2) (by positivity)
    _ = ‖X‖ ^ 2 * (‖X‖ ^ n / n.factorial) := by ring

private lemma exp_pow_eq (X : 𝔸) (k : ℕ) :
    NormedSpace.exp X ^ k = NormedSpace.exp ((k : ℝ) • X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
      ((Commute.refl X).smul_left _)
      ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)]
    congr 1; push_cast; rw [add_smul, one_smul]

omit [CompleteSpace 𝔸] in
private lemma norm_one_add_smul_le (h1 : ‖(1 : 𝔸)‖ ≤ 1) (s : ℝ) (X : 𝔸) :
    ‖1 + s • X‖ ≤ 1 + |s| * ‖X‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs]; linarith

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
private lemma trotter_identity (a b c x y : 𝔸) :
    a * b - c = (a - 1 - x) * b + (1 + x) * (b - 1 - y) + x * y - (c - 1 - (x + y)) := by
  noncomm_ring

private lemma local_estimate (h1 : ‖(1 : 𝔸)‖ ≤ 1) (A B : 𝔸) (T s : ℝ) (hs : |s| ≤ T) :
    ‖NormedSpace.exp (s • A) * NormedSpace.exp (s • B) -
        NormedSpace.exp (s • (A + B))‖ ≤
      (‖A‖ ^ 2 * Real.exp (T * ‖A‖) * Real.exp (T * ‖B‖)
        + (1 + T * ‖A‖) * (‖B‖ ^ 2 * Real.exp (T * ‖B‖)) + ‖A‖ * ‖B‖
        + ‖A + B‖ ^ 2 * Real.exp (T * ‖A + B‖)) * s ^ 2 := by
  have e : ∀ X : 𝔸,
      ‖NormedSpace.exp (s • X) - 1 - s • X‖ ≤ ‖X‖ ^ 2 * Real.exp (T * ‖X‖) * s ^ 2 := by
    intro X
    refine (norm_exp_sub_one_sub_le _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have : Real.exp (|s| * ‖X‖) ≤ Real.exp (T * ‖X‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    nlinarith [sq_nonneg s, sq_nonneg ‖X‖, mul_nonneg (sq_nonneg s) (sq_nonneg ‖X‖)]
  have eB : ‖NormedSpace.exp (s • B)‖ ≤ Real.exp (T * ‖B‖) := by
    refine (norm_exp_le' h1 _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  have o : ‖1 + s • A‖ ≤ 1 + T * ‖A‖ := (norm_one_add_smul_le h1 s A).trans
    (by nlinarith [norm_nonneg A])
  rw [trotter_identity _ _ _ (s • A) (s • B), smul_mul_smul, ← smul_add]
  have hAB : ‖(s * s) • (A * B)‖ ≤ ‖A‖ * ‖B‖ * s ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul_self, ← sq]
    nlinarith [norm_mul_le A B, sq_nonneg s]
  have hRA := e A
  have hRB := e B
  have hRAB := e (A + B)
  have p1 : ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)‖ ≤
      ‖A‖ ^ 2 * Real.exp (T * ‖A‖) * s ^ 2 * Real.exp (T * ‖B‖) :=
    (norm_mul_le _ _).trans (mul_le_mul hRA eB (norm_nonneg _) (by positivity))
  have p2 : ‖(1 + s • A) * (NormedSpace.exp (s • B) - 1 - s • B)‖ ≤
      (1 + T * ‖A‖) * (‖B‖ ^ 2 * Real.exp (T * ‖B‖) * s ^ 2) :=
    (norm_mul_le _ _).trans (mul_le_mul o hRB (norm_nonneg _) (by
      have := abs_nonneg s; nlinarith [norm_nonneg A]))
  calc _ ≤ ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)‖
        + ‖(1 + s • A) * (NormedSpace.exp (s • B) - 1 - s • B)‖
        + ‖(s * s) • (A * B)‖
        + ‖NormedSpace.exp (s • (A + B)) - 1 - s • (A + B)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
    _ ≤ _ := by nlinarith

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
private lemma telescope (P Q : 𝔸) (M K : ℝ) (hP : ‖P‖ ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, (∀ k < n, ‖Q ^ k‖ ≤ K) →
      ‖P ^ n - Q ^ n‖ ≤ n * ‖P - Q‖ * K * M ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hQ
    have hK : 0 ≤ K := (norm_nonneg _).trans (hQ 0 (by lia))
    have ih' := ih (fun k hk => hQ k (by lia))
    have hQn := hQ n (by lia)
    have eq : P ^ (n + 1) - Q ^ (n + 1) = P * (P ^ n - Q ^ n) + (P - Q) * Q ^ n := by
      rw [pow_succ', pow_succ']; noncomm_ring
    rw [eq]
    have hMn : 1 ≤ M ^ n := one_le_pow₀ hM
    have hδ := norm_nonneg (P - Q)
    have hD := norm_nonneg (P ^ n - Q ^ n)
    calc _ ≤ ‖P‖ * ‖P ^ n - Q ^ n‖ + ‖P - Q‖ * ‖Q ^ n‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (n * ‖P - Q‖ * K * M ^ n) + ‖P - Q‖ * K := by
          gcongr
      _ ≤ _ := by
          push_cast
          rw [pow_succ]
          have : ‖P - Q‖ * K ≤ ‖P - Q‖ * K * (M ^ n * M) := by
            have : 1 ≤ M ^ n * M := one_le_mul_of_one_le_of_one_le hMn hM
            nlinarith [mul_nonneg hδ hK]
          nlinarith


/-- The Lie--Trotter product formula for two bounded real linear operators on a Banach
space. No commutativity hypothesis is imposed. -/
theorem ContinuousLinearMap.tendsto_exp_add_trotter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (A B : E →L[ℝ] E) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (NormedSpace.exp ((t / (n + 1 : ℕ)) • A) *
          NormedSpace.exp ((t / (n + 1 : ℕ)) • B)) ^ (n + 1))
      atTop
      (nhds (NormedSpace.exp (t • (A + B)))) := by
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  set T := |t|
  set C := ‖A‖ ^ 2 * Real.exp (T * ‖A‖) * Real.exp (T * ‖B‖)
        + (1 + T * ‖A‖) * (‖B‖ ^ 2 * Real.exp (T * ‖B‖)) + ‖A‖ * ‖B‖
        + ‖A + B‖ ^ 2 * Real.exp (T * ‖A + B‖)
  set K := Real.exp (T * ‖A + B‖)
  set L := Real.exp (T * (‖A‖ + ‖B‖))
  have hC : 0 ≤ C := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    ((tendsto_const_div_atTop_nhds_zero_nat (C * t ^ 2 * K * L)).comp (tendsto_add_atTop_nat 1))
  simp only [Function.comp_apply]
  set N : ℕ := n + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  set s : ℝ := t / N with hs
  have hsN : (N : ℝ) * |s| = T := by
    rw [hs, abs_div, Nat.abs_cast]; field_simp; rfl
  have hsT : |s| ≤ T := by
    rw [← hsN]; exact le_mul_of_one_le_left (abs_nonneg _) (by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by lia))
  set P := NormedSpace.exp (s • A) * NormedSpace.exp (s • B)
  set Q := NormedSpace.exp (s • (A + B))
  have hQN : Q ^ N = NormedSpace.exp (t • (A + B)) := by
    rw [exp_pow_eq, smul_smul]
    congr 2; rw [hs]; field_simp
  set M := Real.exp (|s| * (‖A‖ + ‖B‖))
  have hP : ‖P‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    change _ ≤ Real.exp (|s| * (‖A‖ + ‖B‖))
    rw [mul_add, Real.exp_add]
    refine mul_le_mul ((norm_exp_le' h1 _).trans ?_) ((norm_exp_le' h1 _).trans ?_)
      (norm_nonneg _) (by positivity)
    · rw [norm_smul, Real.norm_eq_abs]
    · rw [norm_smul, Real.norm_eq_abs]
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hMN : M ^ N = L := by
    rw [← Real.exp_nat_mul, ← mul_assoc, hsN]
  have hQk : ∀ k < N, ‖Q ^ k‖ ≤ K := by
    intro k hk
    refine (norm_pow_le_of_one h1 _ _).trans ?_
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le' h1 _) k).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    rw [norm_smul, Real.norm_eq_abs, ← mul_assoc, ← hsN]
    gcongr
  have hloc := local_estimate h1 A B T s hsT
  have htel := telescope P Q M K hP hM N hQk
  rw [hQN, hMN] at htel
  have hK : 0 ≤ K := by positivity
  have hL : 0 ≤ L := by positivity
  calc ‖P ^ N - NormedSpace.exp (t • (A + B))‖ ≤ N * ‖P - Q‖ * K * L := htel
    _ ≤ N * (C * s ^ 2) * K * L := by gcongr
    _ = C * t ^ 2 * K * L / N := by
        rw [hs]; field_simp
    _ = _ := by rw [hN]

/-- Pointwise form of the Lie--Trotter product formula. -/
theorem ContinuousLinearMap.tendsto_exp_add_trotter_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (A B : E →L[ℝ] E) (t : ℝ) (x : E) :
    Tendsto
      (fun n : ℕ =>
        ((NormedSpace.exp ((t / (n + 1 : ℕ)) • A) *
          NormedSpace.exp ((t / (n + 1 : ℕ)) • B)) ^ (n + 1)) x)
      atTop
      (nhds (NormedSpace.exp (t • (A + B)) x)) := by
  exact (((ContinuousLinearMap.apply ℝ E) x).continuous.tendsto _).comp
    (ContinuousLinearMap.tendsto_exp_add_trotter A B t)

