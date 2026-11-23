/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Analysis.Complex.Dominance
public import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import RealRooted.Mathlib.Analysis.Complex.Montel
import TauCeti.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Limits of zeros at multiple dominant bases

We prove Sokal's Theorem 1.5(b) for any finite number of dominant bases, including vanishing
coefficients at the point in question. Failure of the liminf conclusion gives a zero-free
subsequence on a disc. Holomorphic roots and Montel selection produce a holomorphic function
whose modulus is the maximum modulus of the bases. The maximum modulus principle then forces
two tied bases to be unit multiples on an open dominance region, contradicting precisely
Sokal's no-degenerate-dominance hypothesis.

Reference: A. D. Sokal, *Chromatic roots are dense in the whole complex plane*,
arXiv:cond-mat/0012369v3, Theorem 1.5(b) and Theorem 3.2.
-/

public section

open Filter Topology Metric Set

namespace Complex

/-- The normalized exponential sum converges to its unique dominant coefficient. -/
private theorem tendsto_sum_div_pow {κ : Type*} (s : Finset κ) (a b : κ → ℂ)
    {i : κ} (hi : i ∈ s) (hb : b i ≠ 0)
    (hsmall : ∀ k ∈ s, k ≠ i → ‖b k‖ < ‖b i‖) :
    Tendsto (fun n : ℕ => (∑ k ∈ s, a k * b k ^ n) / b i ^ n) atTop (𝓝 (a i)) := by
  classical
  have ht : Tendsto (fun n : ℕ => ∑ k ∈ s.erase i, a k * (b k / b i) ^ n)
      atTop (𝓝 0) := by
    have hterm : ∀ k ∈ s.erase i,
        Tendsto (fun n : ℕ => a k * (b k / b i) ^ n) atTop (𝓝 (0 : ℂ)) := by
      intro k hk
      have hnorm : ‖b k / b i‖ < 1 := by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hb)).mpr
          (hsmall k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
      simpa only [mul_zero] using
        tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (s.erase i) hterm
  have heq : ∀ n : ℕ, (∑ k ∈ s, a k * b k ^ n) / b i ^ n =
      a i + ∑ k ∈ s.erase i, a k * (b k / b i) ^ n := by
    intro n
    rw [← Finset.sum_erase_add _ _ hi, add_div, mul_div_cancel_right₀ _ (pow_ne_zero n hb)]
    rw [Finset.sum_div, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [div_pow]; ring
  simpa only [heq, add_zero] using tendsto_const_nhds.add ht

/-- A convergent sequence of roots has the modulus of its dominant base when the normalized
powers converge to a nonzero coefficient. -/
private theorem norm_eq_of_tendsto_pow_div {u : ℕ → ℂ} {p : ℕ → ℕ} {a b g : ℂ}
    (hp : Tendsto p atTop atTop) (hp0 : ∀ n, p n ≠ 0)
    (hu : Tendsto u atTop (𝓝 g)) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : Tendsto (fun n => u n ^ p n / b ^ p n) atTop (𝓝 a)) :
    ‖g‖ = ‖b‖ := by
  have hinv : Tendsto (fun n => ((p n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp hp
  have hr := hv.norm.rpow hinv (Or.inl (norm_ne_zero_iff.mpr ha))
  simp only [Real.rpow_zero] at hr
  have heq : ∀ n, ‖u n ^ p n / b ^ p n‖ ^ ((p n : ℝ))⁻¹ = ‖u n‖ / ‖b‖ := by
    intro n
    rw [norm_div, norm_pow, norm_pow, ← div_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (div_nonneg (norm_nonneg _) (norm_nonneg _)),
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (hp0 n)), Real.rpow_one]
  have hratio : ‖g‖ / ‖b‖ = 1 :=
    tendsto_nhds_unique (hu.norm.div_const ‖b‖) (hr.congr (fun n => heq n))
  exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hb)).mp hratio

/-- On a sufficiently small disc the sum of coefficient norms and every base norm have
one common bound, at least one. -/
private theorem exists_ball_sum_norm_le {κ : Type*} (s : Finset κ) (α β : κ → ℂ → ℂ)
    {z₀ : ℂ} (hα : ∀ k ∈ s, ContinuousAt (α k) z₀)
    (hβ : ∀ k ∈ s, ContinuousAt (β k) z₀) :
    ∃ r > 0, ∃ M : ℝ, 1 ≤ M ∧ ∀ z ∈ ball z₀ r,
      (∑ k ∈ s, ‖α k z‖) ≤ M ∧ ∀ k ∈ s, ‖β k z‖ ≤ M := by
  classical
  let H : ℂ → ℝ := fun z => ∑ k ∈ s, (‖α k z‖ + ‖β k z‖)
  have hc : ContinuousAt H z₀ := by
    exact tendsto_finsetSum s fun k hk =>
      (hα k hk).norm.add (hβ k hk).norm
  have hev : ∀ᶠ z in 𝓝 z₀, H z < H z₀ + 1 :=
    hc.eventually (eventually_lt_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r, hr, H z₀ + 1, ?_, fun z hz => ⟨?_, fun k hk => ?_⟩⟩
  · have : 0 ≤ H z₀ := Finset.sum_nonneg fun k _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith
  · exact (Finset.sum_le_sum fun k _ => le_add_of_nonneg_right (norm_nonneg _)).trans
      (hball hz).le
  · have hkbound : ‖β k z‖ ≤ ‖α k z‖ + ‖β k z‖ :=
      le_add_of_nonneg_left (norm_nonneg _)
    have hsum : ‖α k z‖ + ‖β k z‖ ≤ H z := by
      exact Finset.single_le_sum (f := fun l => ‖α l z‖ + ‖β l z‖)
        (fun l _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hk
    exact hkbound.trans (hsum.trans (hball hz).le)

/-- A common bound for coefficients and bases bounds every positive-index holomorphic root. -/
private theorem norm_root_sum_le {κ : Type*} (s : Finset κ) (a b : κ → ℂ)
    {M : ℝ} {u : ℂ} {n : ℕ} (hM : 1 ≤ M) (hn : n ≠ 0)
    (ha : (∑ k ∈ s, ‖a k‖) ≤ M) (hb : ∀ k ∈ s, ‖b k‖ ≤ M)
    (hu : u ^ n = ∑ k ∈ s, a k * b k ^ n) : ‖u‖ ≤ M * M := by
  apply le_of_pow_le_pow_left₀ hn (by positivity)
  calc
    ‖u‖ ^ n = ‖∑ k ∈ s, a k * b k ^ n‖ := by rw [← norm_pow, hu]
    _ ≤ ∑ k ∈ s, ‖a k‖ * ‖b k‖ ^ n := by
      simpa only [norm_mul, norm_pow] using norm_sum_le s (fun k => a k * b k ^ n)
    _ ≤ ∑ k ∈ s, ‖a k‖ * M ^ n := Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb k hk) n) (norm_nonneg _)
    _ = (∑ k ∈ s, ‖a k‖) * M ^ n := (Finset.sum_mul ..).symm
    _ ≤ M * M ^ n := mul_le_mul_of_nonneg_right ha (by positivity)
    _ ≤ M ^ n * M ^ n := mul_le_mul_of_nonneg_right (le_self_pow₀ hM hn) (by positivity)
    _ = (M * M) ^ n := (mul_pow ..).symm

/-- Failure of the liminf conclusion yields a convergent holomorphic root subsequence on a
small disc. This is the normal-family step of the multiple-dominance argument. -/
private theorem exists_root_limit_of_not_isLimitOfZeros {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) {D : Set ℂ} {z₀ : ℂ}
    (hDo : IsOpen D) (hz₀ : z₀ ∈ D)
    (hα : ∀ k ∈ s, AnalyticOnNhd ℂ (α k) D)
    (hβ : ∀ k ∈ s, AnalyticOnNhd ℂ (β k) D)
    (hnot : ¬IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀) :
    ∃ r > 0, ball z₀ r ⊆ D ∧ ∃ (p : ℕ → ℕ) (G : ℕ → ℂ → ℂ) (g : ℂ → ℂ),
      Tendsto p atTop atTop ∧ (∀ n, p n ≠ 0) ∧ DifferentiableOn ℂ g (ball z₀ r) ∧
      TendstoLocallyUniformlyOn G g atTop (ball z₀ r) ∧
      ∀ n z, z ∈ ball z₀ r → G n z ^ p n = ∑ k ∈ s, α k z * β k z ^ p n := by
  classical
  obtain ⟨ε, hε, hbad⟩ : ∃ ε > 0, ∃ᶠ n in atTop,
      ¬∃ z ∈ ball z₀ ε, (∑ k ∈ s, α k z * β k z ^ n) = 0 := by
    simp only [IsLimitOfZeros, not_forall, not_eventually] at hnot
    obtain ⟨ε, hε, hbad⟩ := hnot
    exact ⟨ε, hε, hbad⟩
  have hbad' : ∃ᶠ n in atTop, n ≠ 0 ∧
      ¬∃ z ∈ ball z₀ ε, (∑ k ∈ s, α k z * β k z ^ n) = 0 :=
    (hbad.and_eventually (eventually_ne_atTop 0)).mono fun n hn => hn.symm
  obtain ⟨p, hp, hpbad⟩ := extraction_of_frequently_atTop hbad'
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp (hDo.mem_nhds hz₀)
  obtain ⟨ρ, hρ, M, hM, hbound⟩ := exists_ball_sum_norm_le s α β
    (fun k hk => (hα k hk z₀ hz₀).continuousAt)
    (fun k hk => (hβ k hk z₀ hz₀).continuousAt)
  let R := min ε (min δ ρ)
  have hR : 0 < R := lt_min hε (lt_min hδ hρ)
  have hRD : ball z₀ R ⊆ D := fun z hz => hδD
    (ball_subset_ball ((min_le_right ε _).trans (min_le_left δ ρ)) hz)
  have hRε : ball z₀ R ⊆ ball z₀ ε := ball_subset_ball (min_le_left _ _)
  have hRρ : ball z₀ R ⊆ ball z₀ ρ := ball_subset_ball
    ((min_le_right ε _).trans (min_le_right δ ρ))
  have hroots : ∀ n, ∃ u : ℂ → ℂ, DifferentiableOn ℂ u (ball z₀ R) ∧
      EqOn (fun z => u z ^ p n) (fun z => ∑ k ∈ s, α k z * β k z ^ p n) (ball z₀ R) := by
    intro n
    have : ContractibleSpace (ball z₀ R) := Metric.contractibleSpace_ball hR
    apply TauCeti.exists_differentiableOn_pow_eq (SimplyConnectedSpace.ofContractible _)
      isOpen_ball ?_ ?_ (hpbad n).1
    · intro z hz
      exact (Finset.analyticAt_fun_sum s fun k hk =>
        (hα k hk z (hRD hz)).mul
          ((hβ k hk z (hRD hz)).pow (p n))).differentiableAt.differentiableWithinAt
    · rintro ⟨z, hz, hzero⟩
      exact (hpbad n).2 ⟨z, hRε hz, hzero⟩
  choose G hG hGeq using hroots
  have hGbound : ∀ n z, z ∈ ball z₀ R → ‖G n z‖ ≤ M * M := by
    intro n z hz
    exact norm_root_sum_le s (fun k => α k z) (fun k => β k z) hM (hpbad n).1
      (hbound z (hRρ hz)).1 (hbound z (hRρ hz)).2 (hGeq n hz)
  have hhalf : 2 * (R / 2) = R := by ring
  obtain ⟨φ, g, hφ, hgd, hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_ball
    (r := R / 2) (by positivity) (by simpa only [hhalf] using hG)
    (by simpa only [hhalf] using hGbound)
  refine ⟨R / 2, by positivity, (ball_subset_ball (by linarith)).trans hRD,
    p ∘ φ, (fun n => G (φ n)), g, hp.tendsto_atTop.comp hφ.tendsto_atTop,
    (fun n => (hpbad (φ n)).1), hgd, hconv, ?_⟩
  exact fun n z hz => hGeq (φ n) (ball_subset_ball (by linarith) hz)

/-- The root limit has the maximum modulus of the bases throughout the smaller disc.
We first identify it at points of unique dominance, then use continuity and density. -/
private theorem root_limit_norm_max {κ : Type*} (s : Finset κ) (α β : κ → ℂ → ℂ)
    {D : Set ℂ} {z₀ : ℂ} {r : ℝ} {p : ℕ → ℕ} {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hsub : ball z₀ r ⊆ D) (hβ : ∀ k ∈ s, AnalyticOnNhd ℂ (β k) D)
    (hdense : Dense {z : D | ∃ i ∈ s, α i z ≠ 0 ∧ β i z ≠ 0 ∧
      ∀ k ∈ s, k ≠ i → ‖β k z‖ < ‖β i z‖})
    (hp : Tendsto p atTop atTop) (hp0 : ∀ n, p n ≠ 0)
    (hgd : DifferentiableOn ℂ g (ball z₀ r))
    (hconv : TendstoLocallyUniformlyOn G g atTop (ball z₀ r))
    (hGeq : ∀ n z, z ∈ ball z₀ r →
      G n z ^ p n = ∑ k ∈ s, α k z * β k z ^ p n) :
    (∀ z ∈ ball z₀ r, ∀ k ∈ s, ‖β k z‖ ≤ ‖g z‖) ∧
      ∀ z ∈ ball z₀ r, ∃ i ∈ s, ‖g z‖ = ‖β i z‖ := by
  have hd : Dense {z : ball z₀ r | ∃ i ∈ s, α i z ≠ 0 ∧ β i z ≠ 0 ∧
      ∀ k ∈ s, k ≠ i → ‖β k z‖ < ‖β i z‖} :=
    hdense.preimage (isOpen_ball.isOpenMap_inclusion hsub)
  have hnorm : ∀ z : ball z₀ r, (∃ i ∈ s, α i z ≠ 0 ∧ β i z ≠ 0 ∧
      ∀ k ∈ s, k ≠ i → ‖β k z‖ < ‖β i z‖) →
      ∃ i ∈ s, ‖g z‖ = ‖β i z‖ ∧ ∀ k ∈ s, ‖β k z‖ ≤ ‖β i z‖ := by
    rintro z ⟨i, hi, hai, hbi, hsmall⟩
    have hv : Tendsto (fun n => G n z ^ p n / β i z ^ p n) atTop (𝓝 (α i z)) := by
      apply ((tendsto_sum_div_pow s (fun k => α k z) (fun k => β k z) hi hbi hsmall).comp hp).congr
      intro n
      rw [hGeq n z z.2]
      rfl
    have heq := norm_eq_of_tendsto_pow_div hp hp0 (hconv.tendsto_at z.2) hai hbi hv
    refine ⟨i, hi, heq, fun k hk => ?_⟩
    by_cases hki : k = i
    · rw [hki]
    · exact (hsmall k hk hki).le
  have hgc : Continuous (fun z : ball z₀ r => ‖g z‖) := hgd.continuousOn.norm.domRestrict
  have hbc : ∀ k ∈ s, Continuous (fun z : ball z₀ r => ‖β k z‖) :=
    fun k hk => (((hβ k hk).continuousOn.mono hsub).norm).domRestrict
  constructor
  · intro z hz k hk
    have hc : IsClosed {z : ball z₀ r | ‖β k z‖ ≤ ‖g z‖} := isClosed_le (hbc k hk) hgc
    have hinc : {z : ball z₀ r | ∃ i ∈ s, α i z ≠ 0 ∧ β i z ≠ 0 ∧
        ∀ k ∈ s, k ≠ i → ‖β k z‖ < ‖β i z‖} ⊆
        {z : ball z₀ r | ‖β k z‖ ≤ ‖g z‖} := by
      intro w hw
      obtain ⟨i, _, heq, hmax⟩ := hnorm w hw
      exact (hmax k hk).trans_eq heq.symm
    have hcl := closure_mono hinc (hd ⟨z, hz⟩)
    rwa [hc.closure_eq] at hcl
  · intro z hz
    have hset : {z : ball z₀ r | ∃ i ∈ s, ‖g z‖ = ‖β i z‖} =
        ⋃ i ∈ s, {z : ball z₀ r | ‖g z‖ = ‖β i z‖} := by ext; simp
    have hc : IsClosed {z : ball z₀ r | ∃ i ∈ s, ‖g z‖ = ‖β i z‖} := by
      rw [hset]
      exact isClosed_biUnion_finset fun i hi => isClosed_eq hgc (hbc i hi)
    have hinc : {z : ball z₀ r | ∃ i ∈ s, α i z ≠ 0 ∧ β i z ≠ 0 ∧
        ∀ k ∈ s, k ≠ i → ‖β k z‖ < ‖β i z‖} ⊆
        {z : ball z₀ r | ∃ i ∈ s, ‖g z‖ = ‖β i z‖} := by
      intro w hw
      obtain ⟨i, hi, heq, _⟩ := hnorm w hw
      exact ⟨i, hi, heq⟩
    have hcl := closure_mono hinc (hd ⟨z, hz⟩)
    rwa [hc.closure_eq] at hcl


/-- A holomorphic maximum-modulus envelope cannot have two nonzero tied bases in a
nondegenerate family. -/
private theorem not_two_dominant_of_norm_max {κ : Type*} (s : Finset κ) (β : κ → ℂ → ℂ)
    {D : Set ℂ} {z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ} (hr : 0 < r)
    (hsub : ball z₀ r ⊆ D) (hDc : IsPreconnected D)
    (hβ : ∀ k ∈ s, AnalyticOnNhd ℂ (β k) D)
    (hβne : ∀ k ∈ s, ∃ z ∈ D, β k z ≠ 0)
    (hnd : HasNondegenerateDominance s β D)
    (hgd : DifferentiableOn ℂ g (ball z₀ r))
    (hle : ∀ z ∈ ball z₀ r, ∀ k ∈ s, ‖β k z‖ ≤ ‖g z‖)
    (heq : ∃ k ∈ s, ‖g z₀‖ = ‖β k z₀‖)
    {i j : κ} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hdomi : ∀ k ∈ s, ‖β k z₀‖ ≤ ‖β i z₀‖)
    (hdomj : ∀ k ∈ s, ‖β k z₀‖ ≤ ‖β j z₀‖)
    (hbi : β i z₀ ≠ 0) : False := by
  obtain ⟨k, hk, hkeq⟩ := heq
  have hgi : ‖g z₀‖ = ‖β i z₀‖ := le_antisymm
    (hkeq.trans_le (hdomi k hk)) (hle z₀ (mem_ball_self hr) i hi)
  have hgj : ‖g z₀‖ = ‖β j z₀‖ := le_antisymm
    (hkeq.trans_le (hdomj k hk)) (hle z₀ (mem_ball_self hr) j hj)
  have hg0 : g z₀ ≠ 0 := norm_ne_zero_iff.mp (hgi ▸ norm_ne_zero_iff.mpr hbi)
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ ball z₀ r ∧ g z ≠ 0 :=
    Filter.Eventually.and (ball_mem_nhds z₀ hr)
      ((hgd.continuousOn.continuousAt (ball_mem_nhds z₀ hr)).eventually_ne hg0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hδD : ball z₀ δ ⊆ D := fun z hz => hsub (hball hz).1
  have hnorm : ∀ l ∈ s, ‖g z₀‖ = ‖β l z₀‖ →
      ∀ z ∈ ball z₀ δ, ‖β l z‖ = ‖g z‖ := by
    intro l hl hgl
    have hd : DifferentiableOn ℂ (fun z => β l z / g z) (ball z₀ δ) := by
      intro z hz
      exact ((hβ l hl z (hδD hz)).differentiableAt.div
        ((hgd z (hball hz).1).differentiableAt (isOpen_ball.mem_nhds (hball hz).1))
        (hball hz).2).differentiableWithinAt
    have hcenter : ‖β l z₀ / g z₀‖ = 1 := by simp [← hgl, hg0]
    have hm : IsMaxOn (norm ∘ (fun z => β l z / g z)) (ball z₀ δ) z₀ := by
      intro z hz
      change ‖β l z / g z‖ ≤ ‖β l z₀ / g z₀‖
      rw [hcenter, norm_div]
      exact (div_le_one (norm_pos_iff.mpr (hball hz).2)).mpr (hle z (hball hz).1 l hl)
    have hc := norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball z₀ δ).isPreconnected
      isOpen_ball hd (mem_ball_self hδ) hm
    intro z hz
    have heq : ‖β l z‖ / ‖g z‖ = 1 := by simpa only [Function.comp_apply, norm_div,
      Function.const_apply, hcenter] using hc hz
    exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr (hball hz).2)).mp heq
  obtain ⟨ω, hω, hprop⟩ := exists_norm_eq_one_eqOn_mul (hβ i hi) (hβ j hj) hDc
    (hβne j hj) isOpen_ball hδD ⟨z₀, mem_ball_self hδ⟩
    (fun z hz => (hnorm i hi hgi z hz).trans (hnorm j hj hgj z hz).symm)
  have hinc : ball z₀ δ ⊆ interior {z | z ∈ D ∧ ∀ l ∈ s, ‖β l z‖ ≤ ‖β i z‖} :=
    interior_maximal (fun z hz => ⟨hδD hz, fun l hl =>
      (hle z (hball hz).1 l hl).trans_eq (hnorm i hi hgi z hz).symm⟩) isOpen_ball
  have hfalse := hinc (mem_ball_self hδ)
  simp only [hnd i hi j hj hij ω hω hprop, mem_empty_iff_false] at hfalse

/-- **Multiple dominant indices.** At a point with at least two dominant bases, a finite analytic
exponential sum has a liminf limit of zeros under Sokal's no-degenerate-dominance condition.
The coefficients may vanish at that point. This is Sokal, arXiv:cond-mat/0012369v3,
Theorem 1.5(b), for arbitrary finite sums. -/
theorem isLimitOfZeros_finset_dominant {κ : Type*} (s : Finset κ) (α β : κ → ℂ → ℂ)
    {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D)
    (hα : ∀ k ∈ s, AnalyticOnNhd ℂ (α k) D)
    (hβ : ∀ k ∈ s, AnalyticOnNhd ℂ (β k) D)
    (hαne : ∀ k ∈ s, ∃ z ∈ D, α k z ≠ 0)
    (hβne : ∀ k ∈ s, ∃ z ∈ D, β k z ≠ 0)
    (hnd : HasNondegenerateDominance s β D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) {i j : κ} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hdomi : ∀ k ∈ s, ‖β k z₀‖ ≤ ‖β i z₀‖)
    (hdomj : ∀ k ∈ s, ‖β k z₀‖ ≤ ‖β j z₀‖) :
    IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀ := by
  classical
  by_cases hbi : β i z₀ = 0
  · intro ε hε
    filter_upwards [eventually_ne_atTop 0] with n hn
    refine ⟨z₀, mem_ball_self hε, Finset.sum_eq_zero fun k hk => ?_⟩
    have hb : β k z₀ = 0 := norm_le_zero_iff.mp (by simpa only [hbi, norm_zero] using hdomi k hk)
    simp only [hb, zero_pow hn, mul_zero]
  · by_contra hnot
    obtain ⟨r, hr, hsub, p, G, g, hp, hp0, hgd, hconv, hGeq⟩ :=
      exists_root_limit_of_not_isLimitOfZeros s α β hDo hz₀ hα hβ hnot
    have hdense := hnd.dense_unique_dominant s α β hDo hDc ⟨i, hi⟩ hα hβ hαne hβne
    obtain ⟨hle, heq⟩ := root_limit_norm_max s α β hsub hβ hdense hp hp0 hgd hconv hGeq
    exact not_two_dominant_of_norm_max s β hr hsub hDc hβ hβne hnd hgd hle
      (heq z₀ (mem_ball_self hr)) hi hj hij hdomi hdomj hbi

end Complex
