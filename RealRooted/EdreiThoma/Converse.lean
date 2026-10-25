module

public import RealRooted.EdreiThoma.Continuation
public import RealRooted.EdreiThoma.Easy
public import RealRooted.EdreiThoma.FinalStep
public import RealRooted.EdreiThoma.OddPart
public import RealRooted.EdreiThoma.Reduction
public import RealRooted.Mathlib.Analysis.Complex.EdreiUniqueness

/-!
# The Edrei--Thoma converse

This module assembles the continuation, zero-free quotient, odd-part, and final affine-exponent
steps.  It identifies a normalized Pólya-frequency sequence with an Edrei--Thoma canonical
product.
-/

@[expose] public section

open Polynomial Filter Topology Complex

noncomputable section

namespace RealRooted.EdreiThoma

namespace Lib

private lemma hasSum_conv_mul {a b : ℕ → ℝ} {z : ℂ}
    (ha : Summable fun n => ‖(a n : ℂ) * z ^ n‖)
    (hb : Summable fun n => ‖(b n : ℂ) * z ^ n‖) :
    HasSum (fun n => (natCauchyConvolution a b n : ℂ) * z ^ n)
      ((∑' n, (a n : ℂ) * z ^ n) * ∑' n, (b n : ℂ) * z ^ n) := by
  have e : (fun n => (natCauchyConvolution a b n : ℂ) * z ^ n) =
      fun n => ∑ k ∈ Finset.range (n + 1),
        ((a k : ℂ) * z ^ k) * ((b (n - k) : ℂ) * z ^ (n - k)) := by
    funext n
    simp only [natCauchyConvolution, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show z ^ n = z ^ k * z ^ (n - k) by
      rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]]
    ring
  rw [e, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha hb]
  exact (summable_norm_sum_mul_range_of_summable_norm ha hb).of_norm.hasSum

private lemma hasSum_expSeq (ε : ℝ) (z : ℂ) :
    HasSum (fun n => (expSeq ε n : ℂ) * z ^ n) (Complex.exp (ε * z)) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((ε : ℂ) * z)
  rw [← Complex.exp_eq_exp_ℂ] at h
  convert h using 1
  funext n
  simp only [expSeq, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast, mul_pow]
  field_simp

private lemma summable_norm_expSeq (ε : ℝ) (z : ℂ) :
    Summable fun n => ‖(expSeq ε n : ℂ) * z ^ n‖ := by
  simpa [expSeq, norm_pow] using (hasSum_expSeq |ε| ‖z‖).summable.norm

private lemma eventually_disc (c : ℝ) : ∀ᶠ z in 𝓝 (0 : ℂ), c * ‖z‖ < 1 := by
  exact (continuous_const.mul continuous_norm).continuousAt.eventually_lt continuousAt_const
    (by simp)

private lemma eventually_hasSum_genFun {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) (h0 : a 0 = 1) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n => (a n : ℂ) * z ^ n) (∑' n, (a n : ℂ) * z ^ n) :=
  (eventually_disc (a 1)).mono fun _ hz => (IsPolyaFreqSeq.summable_genFun h h0 hz).hasSum

private lemma eventually_hasSum_conv_exp {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) (ε : ℝ) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n => (natCauchyConvolution a (expSeq ε) n : ℂ) * z ^ n)
      ((∑' n, (a n : ℂ) * z ^ n) * Complex.exp (ε * z)) :=
  (eventually_disc (a 1)).mono fun z hz => by
    have := hasSum_conv_mul (h.summable_norm_genFun h0 hz) (summable_norm_expSeq ε z)
    rwa [(hasSum_expSeq ε z).tsum_eq] at this

private lemma differentiable_tprod_one_add {c : ℕ → ℂ} (hc : Summable fun i => ‖c i‖) :
    Differentiable ℂ (fun z => ∏' i, (1 + c i * z)) := by
  intro z
  set R : ℝ := ‖z‖ + 1
  have hU : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hprod := Summable.hasProdLocallyUniformlyOn_nat_one_add (f := fun i x => c i * x) hU
    (u := fun i => ‖c i‖ * R) (hc.mul_right R)
    (Eventually.of_forall fun i x hx => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using (Metric.mem_ball.1 hx).le) (norm_nonneg _))
    (fun i => (continuous_const.mul continuous_id).continuousOn)
  have hd : DifferentiableOn ℂ (fun z => ∏' i, (1 + c i * z)) (Metric.ball 0 R) := by
    refine hprod.differentiableOn (Eventually.of_forall fun s => ?_) hU
    exact (Differentiable.differentiableOn (by fun_prop))
  exact hd.differentiableAt (hU.mem_nhds (by simp [R]))

private lemma tprod_one_add_ne_zero {c : ℕ → ℂ} (hc : Summable fun i => ‖c i‖) {z : ℂ}
    (h : ∀ i, 1 + c i * z ≠ 0) : ∏' i, (1 + c i * z) ≠ 0 :=
  tprod_one_add_ne_zero_of_summable h (by simpa [norm_mul] using hc.mul_right ‖z‖)

private lemma countable_zeros_tprod {c : ℕ → ℂ} (hc : Summable fun i => ‖c i‖) :
    {z : ℂ | ∏' i, (1 + c i * z) = 0}.Countable := by
  have hsub : {z : ℂ | ∏' i, (1 + c i * z) = 0} ⊆ ⋃ i, {z : ℂ | 1 + c i * z = 0} := by
    intro z hz
    by_contra hn
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hn
    exact tprod_one_add_ne_zero hc hn hz
  refine Set.Countable.mono hsub (Set.countable_iUnion fun i => ?_)
  refine Set.Subsingleton.countable fun x hx y hy => ?_
  simp only [Set.mem_ofPred_eq] at hx hy
  have hci : c i ≠ 0 := by rintro h; simp [h] at hx
  have : c i * x = c i * y := by linear_combination hx - hy
  exact mul_left_cancel₀ hci this

private lemma countable_preimage_sq {S : Set ℂ} (hS : S.Countable) :
    {z : ℂ | z ^ 2 ∈ S}.Countable := by
  have hsub : {z : ℂ | z ^ 2 ∈ S} ⊆ ⋃ w ∈ S, {z : ℂ | z ^ 2 = w} := by
    intro z hz; simp only [Set.mem_iUnion, Set.mem_ofPred_eq]; exact ⟨_, hz, rfl⟩
  refine Set.Countable.mono hsub (hS.biUnion fun w _ => ?_)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
  refine Set.Finite.countable (Set.Finite.subset (Set.toFinite ({s, -s} : Set ℂ)) ?_)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  rw [← hs] at hz
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hz with h | h <;> simp_all

private lemma summable_norm_ofReal {α : ℕ → ℝ} (sα : Summable α) :
    Summable fun i => ‖(α i : ℂ)‖ := by
  simpa [Complex.norm_real] using (summable_abs_iff.2 sα)

private lemma differentiable_prod_add {α : ℕ → ℝ} (sα : Summable α) :
    Differentiable ℂ (fun z => ∏' i, (1 + (α i : ℂ) * z)) :=
  differentiable_tprod_one_add (summable_norm_ofReal sα)

private lemma prod_sub_eq (β : ℕ → ℝ) (z : ℂ) :
    ∏' i, (1 - (β i : ℂ) * z) = ∏' i, (1 + ((-β i : ℝ) : ℂ) * z) := by
  congr 1; funext i; push_cast; ring

private lemma differentiable_prod_sub {β : ℕ → ℝ} (sβ : Summable β) :
    Differentiable ℂ (fun z => ∏' i, (1 - (β i : ℂ) * z)) := by
  rw [show (fun z : ℂ => ∏' i, (1 - (β i : ℂ) * z)) = _ from funext (prod_sub_eq β)]
  exact differentiable_prod_add (α := fun i => -β i) sβ.neg

private lemma countable_zeros_prod_sub {β : ℕ → ℝ} (sβ : Summable β) :
    {z : ℂ | ∏' i, (1 - (β i : ℂ) * z) = 0}.Countable := by
  simp only [prod_sub_eq β]
  exact countable_zeros_tprod (summable_norm_ofReal (α := fun i => -β i) sβ.neg)

private lemma prod_sub_zero (β : ℕ → ℝ) : ∏' i, (1 - (β i : ℂ) * 0) = 1 := by simp

private lemma prod_add_zero (β : ℕ → ℝ) : ∏' i, (1 + (β i : ℂ) * 0) = 1 := by simp

private lemma differentiable_powerSeries {c : ℕ → ℂ}
    (hc : ∀ z : ℂ, Summable fun k => c k * z ^ k) :
    Differentiable ℂ (fun z => ∑' k, c k * z ^ k) := by
  intro z
  set R : ℝ := ‖z‖ + 1
  have hU : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hu : Summable fun k => ‖c k * (R : ℂ) ^ k‖ := summable_norm_iff.2 (hc R)
  have hT := tendstoUniformlyOn_tsum hu (s := Metric.ball (0 : ℂ) R)
    (f := fun k (x : ℂ) => c k * x ^ k) (fun k x hx => by
      simp only [norm_mul, norm_pow]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ k) (norm_nonneg _)
      have := (Metric.mem_ball.1 hx).le
      simp only [dist_zero_right] at this
      simpa [Complex.norm_real, abs_of_nonneg (by positivity : (0:ℝ) ≤ R)] using this)
  have hd : DifferentiableOn ℂ (fun z => ∑' k, c k * z ^ k) (Metric.ball 0 R) := by
    refine hT.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun s => ?_) hU
    exact (Differentiable.differentiableOn (by fun_prop))
  exact hd.differentiableAt (hU.mem_nhds (by simp [R]))

private lemma tsum_mul_zero_pow (c : ℕ → ℂ) : ∑' n, c n * (0 : ℂ) ^ n = c 0 := by
  rw [tsum_eq_single 0] <;> simp_all [zero_pow]

private lemma hasSum_mul_zero_pow (c : ℕ → ℂ) :
    HasSum (fun n => c n * (0 : ℂ) ^ n) (c 0) := by
  convert hasSum_single (f := fun n => c n * (0 : ℂ) ^ n) 0 ?_ using 1 <;>
    simp_all [zero_pow]

private lemma eventually_inverse_mul {a b : ℕ → ℝ} (ha : IsPolyaFreqSeq a)
    (ha0 : a 0 = 1) (hb : IsPolyaFreqSeq b)
    (hb0 : b 0 = 1) (hrec : ∀ n, ∑ k ∈ Finset.range (n + 1),
      a k * ((-1) ^ (n - k) * b (n - k)) = if n = 0 then 1 else 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      (∑' n, (a n : ℂ) * z ^ n) * (∑' n, (b n : ℂ) * (-z) ^ n) = 1 := by
  filter_upwards [eventually_disc (a 1), eventually_disc (b 1)] with z h1 h2
  have e : ∀ n, (((-1) ^ n * b n : ℝ) : ℂ) * z ^ n = (b n : ℂ) * (-z) ^ n := by
    intro n; push_cast; rw [neg_pow]; ring
  have hb' : Summable fun n => ‖(((-1) ^ n * b n : ℝ) : ℂ) * z ^ n‖ := by
    refine (hb.summable_norm_genFun hb0 h2).congr fun n => ?_
    simp [norm_pow]
  have := hasSum_conv_mul (b := fun n => (-1) ^ n * b n) (ha.summable_norm_genFun ha0 h1) hb'
  simp only [e] at this
  have hc : ∀ n, (natCauchyConvolution a (fun n => (-1) ^ n * b n) n : ℂ) * z ^ n =
      ((fun n : ℕ => if n = 0 then (1 : ℂ) else 0) n) * z ^ n := by
    intro n
    simp only [natCauchyConvolution]
    rw [hrec n]
    split_ifs <;> simp
  simp only [hc] at this
  apply this.unique
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn <;> simp_all

private lemma eq_neg_inv_of_one_add_mul_eq_zero {c : ℝ} {z : ℂ} (h : 1 + (c : ℂ) * z = 0) :
    c ≠ 0 ∧ z = ((-(1 / c) : ℝ) : ℂ) := by
  have hc : c ≠ 0 := by rintro rfl; simp at h
  refine ⟨hc, ?_⟩
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp
  linear_combination h

private lemma summable_norm_of_nonneg_hasSum {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n)
    {F : ℂ → ℂ} (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z))
    (z : ℂ) : Summable fun n => ‖(p n : ℂ) * z ^ n‖ := by
  have h := (hF (‖z‖ : ℂ)).summable.norm
  refine h.congr fun n => ?_
  simp [norm_pow, abs_of_nonneg (hp n)]

end Lib

namespace FinalAux

private lemma nonneg_series_real {p : ℕ → ℝ} {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z)) (r : ℝ) :
    HasSum (fun n => p n * r ^ n) (F r).re ∧ (F r).im = 0 := by
  have h := (Complex.hasSum_iff _ _).1 (hF r)
  refine ⟨?_, ?_⟩
  · simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using h.1
  · have him := h.2
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im] at him
    exact him.unique hasSum_zero

private lemma nonneg_series_ge {p : ℕ → ℝ} (hp : ∀ n, 0 ≤ p n) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, HasSum (fun n => (p n : ℂ) * z ^ n) (F z))
    {r : ℝ} (hr : 0 ≤ r) : p 0 ≤ ‖F r‖ := by
  have h := (nonneg_series_real hF r).1
  have h0 : p 0 * r ^ 0 ≤ (F r).re :=
    le_hasSum h 0 (fun j _ => mul_nonneg (hp j) (pow_nonneg hr j))
  simp only [pow_zero, mul_one] at h0
  exact h0.trans (Complex.re_le_norm _)

end FinalAux

/-- **Edrei's Proposition A for sequences with property (P) (E8).**
`f = e^φ ∏(1+α z)/∏(1-β z)`
near `0` with `φ` entire and `α, β ≥ 0` summable; moreover `e^φ ∏(1+α z)` and
`e^{-φ(-z)} ∏(1+β z)` are everywhere convergent power series with nonnegative coefficients.
(Proof: `exists_entire_series_mul_tprod` for `a` and for the inverse PF sequence `b`, which has
property (P) by `A_eq_swap_of_inverse`; then `F(z) G(-z) = Q(z) N(z)` by the identity theorem;
zeros of
`N` are negative reals, where `G(-·) ≥ 1`; zeros of `Q` are positive reals where `F ≥ 1`;
`exists_exp_factorization_of_mul_neg_eq`.) -/
private theorem exists_hasSum_exp_mul_prod_div {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) (hP : ∀ n m, 0 < A a n m) :
    ∃ (φ : ℂ → ℂ) (α β : ℕ → ℝ), Differentiable ℂ φ ∧
      (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
      Summable α ∧ Summable β ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n)
        (Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) /
          (∏' i, (1 - (β i : ℂ) * z)))) ∧
      (∃ p : ℕ → ℝ, (∀ k, 0 ≤ p k) ∧ ∀ z : ℂ,
        HasSum (fun k => (p k : ℂ) * z ^ k)
        (Complex.exp (φ z) * ∏' i, (1 + (α i : ℂ) * z))) ∧
      (∃ q : ℕ → ℝ, (∀ k, 0 ≤ q k) ∧ ∀ z : ℂ,
        HasSum (fun k => (q k : ℂ) * z ^ k)
        (Complex.exp (-φ (-z)) * ∏' i, (1 + (β i : ℂ) * z))) := by
  obtain ⟨b, hbpf, hb0, hb⟩ := IsPolyaFreqSeq.exists_inverse hpf h0
  have hbP : ∀ n m, 0 < A b n m := fun n m => by
    rw [← A_eq_swap_of_inverse h0 hb m n]; exact hP m n
  obtain ⟨β, p, hβ, sβ, hp, hps, hpe⟩ := exists_entire_series_mul_tprod hpf h0 hP
  obtain ⟨α, q, hα, sα, hq, hqs, hqe⟩ := exists_entire_series_mul_tprod hbpf hb0 hbP
  set F : ℂ → ℂ := fun z => ∑' k, (p k : ℂ) * z ^ k with hF
  set G : ℂ → ℂ := fun z => ∑' k, (q k : ℂ) * z ^ k with hG
  set Qf : ℂ → ℂ := fun z => ∏' i, (1 - (β i : ℂ) * z) with hQf
  set N : ℂ → ℂ := fun z => ∏' i, (1 + (α i : ℂ) * z) with hN
  have dF : Differentiable ℂ F := Lib.differentiable_powerSeries hps
  have dG : Differentiable ℂ G := Lib.differentiable_powerSeries hqs
  have dQ : Differentiable ℂ Qf := Lib.differentiable_prod_sub sβ
  have dN : Differentiable ℂ N := Lib.differentiable_prod_add sα
  have hFs : ∀ z, HasSum (fun k => (p k : ℂ) * z ^ k) (F z) := fun z => (hps z).hasSum
  have hGs : ∀ z, HasSum (fun k => (q k : ℂ) * z ^ k) (G z) := fun z => (hqs z).hasSum
  have hQ0 : Qf 0 = 1 := Lib.prod_sub_zero β
  have hN0 : N 0 = 1 := Lib.prod_add_zero α
  have hNneg : ∀ z, ∏' i, (1 - (α i : ℂ) * (-z)) = N z := fun z => by
    simp only [hN]; congr 1; funext i; ring
  have hQneg : ∀ z, Qf (-z) = ∏' i, (1 + (β i : ℂ) * z) := fun z => by
    simp only [hQf]; congr 1; funext i; ring
  have hp0 : p 0 = 1 := by
    have e := hpe.self_of_nhds
    rw [Lib.tsum_mul_zero_pow, Lib.tsum_mul_zero_pow, Lib.prod_sub_zero] at e
    simp only [mul_one, h0, Complex.ofReal_one] at e
    exact_mod_cast e
  have hq0 : q 0 = 1 := by
    have e := hqe.self_of_nhds
    rw [Lib.tsum_mul_zero_pow, Lib.tsum_mul_zero_pow, Lib.prod_sub_zero] at e
    simp only [mul_one, hb0, Complex.ofReal_one] at e
    exact_mod_cast e
  have hFG : ∀ z, F z * G (-z) = Qf z * N z := by
    have t1 : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℂ))
    have hev : (fun z => F z * G (-z)) =ᶠ[𝓝 0] fun z => Qf z * N z := by
      filter_upwards [hpe, t1.eventually hqe, Lib.eventually_inverse_mul hpf h0 hbpf hb0 hb]
        with z e1 e2 e3
      have e2' : G (-z) = (∑' n, (b n : ℂ) * (-z) ^ n) * N z := by
        rw [← hNneg z]; exact e2
      rw [show F z = _ from e1, e2']
      linear_combination (Qf z * N z) * e3
    have dG' : Differentiable ℂ fun z => G (-z) := dG.comp differentiable_neg
    have h1 : AnalyticOnNhd ℂ (fun z => F z * G (-z)) Set.univ :=
      (dF.mul dG').differentiableOn.analyticOnNhd isOpen_univ
    have h2 : AnalyticOnNhd ℂ (fun z => Qf z * N z) Set.univ :=
      (dQ.mul dN).differentiableOn.analyticOnNhd isOpen_univ
    exact congrFun (h1.eq_of_eventuallyEq h2 hev)
  have hNz : ∀ z, N z = 0 → G (-z) ≠ 0 := by
    intro z hz
    obtain ⟨i, hi⟩ : ∃ i, 1 + (α i : ℂ) * z = 0 := by
      by_contra hc
      push Not at hc
      exact Lib.tprod_one_add_ne_zero (Lib.summable_norm_ofReal sα) hc hz
    obtain ⟨hai, hzi⟩ := Lib.eq_neg_inv_of_one_add_mul_eq_zero hi
    have hr : (0 : ℝ) ≤ 1 / α i := div_nonneg zero_le_one (hα i)
    have := FinalAux.nonneg_series_ge hq hGs hr
    rw [hq0] at this
    rw [hzi, ← Complex.ofReal_neg, neg_neg]
    intro h0'; rw [h0', norm_zero] at this; linarith
  have hQz : ∀ z, Qf z = 0 → F z ≠ 0 := by
    intro z hz
    obtain ⟨i, hi⟩ : ∃ i, 1 + ((-β i : ℝ) : ℂ) * z = 0 := by
      by_contra hc
      push Not at hc
      rw [show Qf z = _ from Lib.prod_sub_eq β z] at hz
      exact Lib.tprod_one_add_ne_zero
        (Lib.summable_norm_ofReal (α := fun i => -β i) sβ.neg) hc hz
    obtain ⟨hbi, hzi⟩ := Lib.eq_neg_inv_of_one_add_mul_eq_zero hi
    have hr : (0 : ℝ) ≤ -(1 / -β i) := by
      rw [div_neg, neg_neg]; exact div_nonneg zero_le_one (hβ i)
    have := FinalAux.nonneg_series_ge hp hFs hr
    rw [hp0] at this
    rw [hzi]
    intro h0'; rw [h0', norm_zero] at this; linarith
  obtain ⟨φ, hφ, hF1, hG1⟩ := exists_exp_factorization_of_mul_neg_eq dF dG dQ dN hFG hNz hQz
  refine ⟨φ, α, β, hφ, hα, hβ, sα, sβ, ?_,
    ⟨p, hp, fun z => ?_⟩, ⟨q, hq, fun z => ?_⟩⟩
  · have hQev : ∀ᶠ z in 𝓝 (0 : ℂ), Qf z ≠ 0 :=
      dQ.continuous.continuousAt.eventually_ne (by rw [hQ0]; exact one_ne_zero)
    filter_upwards [hpe, Lib.eventually_hasSum_genFun hpf h0, hQev] with z e1 e2 e3
    convert e2 using 1
    have : F z = (∑' n, (a n : ℂ) * z ^ n) * Qf z := e1
    rw [show Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) = F z from (hF1 z).symm, this]
    exact mul_div_cancel_right₀ _ e3
  · rw [show Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) = F z from (hF1 z).symm]
    exact hFs z
  · have := hG1 (-z)
    rw [neg_neg, hQneg] at this
    rw [← this]
    exact hGs z


/-- The zero-perturbation version of Edrei's final affine-exponent step. -/
private theorem exists_nonneg_eq_affine_of_series_zero {h : ℂ → ℂ}
    (hh : Differentiable ℂ h) {c : ℂ}
    (hodd : ∀ z, h z - h (-z) = 2 * c * z) {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (sα : Summable α) (sβ : Summable β)
    (h1 : ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n) ∧ ∀ z : ℂ,
      HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (h z) * ∏' i, (1 + (α i : ℂ) * z)))
    (h2 : ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n) ∧ ∀ z : ℂ,
      HasSum (fun n => (p n : ℂ) * z ^ n)
        (Complex.exp (-h (-z)) * ∏' i, (1 + (β i : ℂ) * z))) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z : ℂ, h z = h 0 + γ * z := by
  obtain ⟨p, hp, hp_sum⟩ := h1
  obtain ⟨q, hq, hq_sum⟩ := h2
  apply exists_nonneg_eq_affine_of_series hh hodd hα hβ sα sβ
  · intro ε hε
    refine ⟨natCauchyConvolution p (expSeq ε), ?_, fun z => ?_⟩
    · intro n
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (hp k) (div_nonneg (pow_nonneg hε.le _) (Nat.cast_nonneg _))
    · have hs := Lib.hasSum_conv_mul
        (Lib.summable_norm_of_nonneg_hasSum hp hp_sum z)
        (Lib.summable_norm_expSeq ε z)
      rw [(hp_sum z).tsum_eq, (Lib.hasSum_expSeq ε z).tsum_eq] at hs
      convert hs using 1
      rw [Complex.exp_add]
      ring
  · intro ε hε
    refine ⟨natCauchyConvolution q (expSeq ε), ?_, fun z => ?_⟩
    · intro n
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (hq k) (div_nonneg (pow_nonneg hε.le _) (Nat.cast_nonneg _))
    · have hs := Lib.hasSum_conv_mul
        (Lib.summable_norm_of_nonneg_hasSum hq hq_sum z)
        (Lib.summable_norm_expSeq ε z)
      rw [(hq_sum z).tsum_eq, (Lib.hasSum_expSeq ε z).tsum_eq] at hs
      convert hs using 1
      rw [sub_eq_add_neg, Complex.exp_add]
      ring

/-- The even part `a₀, a₂, a₄, …` of a PF sequence is PF: its Toeplitz matrix is a submatrix
of the Toeplitz matrix of `a`. -/
private theorem isPolyaFreqSeq_even {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) :
    IsPolyaFreqSeq (fun k => a (2 * k)) := by
  intro n r c hr hc
  have hm : StrictMono (fun x : ℕ => 2 * x) := fun x y (hxy : x < y) => by simp only; lia
  have e : (toeplitz fun k => a (2 * k)).submatrix r c =
      (toeplitz a).submatrix (fun i => 2 * r i) (fun i => 2 * c i) := by
    ext i j
    simp only [Matrix.submatrix_apply, toeplitz_apply]
    split_ifs <;> congr 1 <;> lia
  rw [e]
  exact h (hm.comp hr) (hm.comp hc)

/-- **Edrei's Proposition A for arbitrary PF sequences (E8, via `e^{εz}`).**
Apply `exists_hasSum_exp_mul_prod_div` to `a ⋆ exp(z)` and absorb `-z` into `φ`. -/
private theorem exists_hasSum_exp_mul_prod_div_of_pf {a : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq a) (h0 : a 0 = 1) :
    ∃ (φ : ℂ → ℂ) (α β : ℕ → ℝ), Differentiable ℂ φ ∧
      (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
      Summable α ∧ Summable β ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n)
        (Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) /
          (∏' i, (1 - (β i : ℂ) * z)))) := by
  obtain ⟨hg, hg0, hgP⟩ := reduction_to_P hpf h0 one_pos
  obtain ⟨φ, α, β, hφ, hα, hβ, sα, sβ, hrep, -, -⟩ :=
    exists_hasSum_exp_mul_prod_div hg hg0 hgP
  refine ⟨fun z => φ z - z, α, β, hφ.sub differentiable_id, hα, hβ, sα, sβ, ?_⟩
  filter_upwards [hrep, Lib.eventually_hasSum_conv_exp hpf h0 1,
    Lib.eventually_hasSum_genFun hpf h0] with z h1 h2 h3
  have e := h1.unique h2
  convert h3 using 1
  rw [Complex.exp_sub]
  have hz : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  simp only [Complex.ofReal_one, one_mul] at e
  rw [div_mul_eq_mul_div, div_div, mul_comm (Complex.exp z), ← div_div, e]
  field_simp

private lemma even_odd_hasSum {a : ℕ → ℝ} {z : ℂ} {s t u : ℂ}
    (h1 : HasSum (fun n => (a n : ℂ) * z ^ n) s)
    (h2 : HasSum (fun n => (a n : ℂ) * (-z) ^ n) t)
    (h3 : HasSum (fun n => (a (2 * n) : ℂ) * (z ^ 2) ^ n) u) : s + t = 2 * u := by
  have h12 := h1.add h2
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun x y h => by simpa using h
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k),
      (a n : ℂ) * z ^ n + (a n : ℂ) * (-z) ^ n = 0 := by
    intro n hn
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
      · exact absurd ⟨k, by simp only; lia⟩ hn
      · exact ho
    rw [hodd.neg_pow]; ring
  have h4 := (hinj.hasSum_iff hzero).2 h12
  have h5 : HasSum (fun k => 2 * ((a (2 * k) : ℂ) * (z ^ 2) ^ k)) (s + t) := by
    convert h4 using 1
    funext k
    simp only [Function.comp, ← pow_mul, Even.neg_pow (even_two_mul k)]
    ring
  exact h5.unique (h3.mul_left 2)

/-- **Edrei--Thoma for sequences with property (P) (E9--E12).**
Apply Proposition A to `a` and its even part, use `odd_part_linear`, and then apply the final
affine-exponent step. -/
private theorem exists_hasSum_edreiFunction_of_property_P {a : ℕ → ℝ}
    (hpf : IsPolyaFreqSeq a) (h0 : a 0 = 1) (hP : ∀ n m, 0 < A a n m) :
    ∃ (γ : ℝ) (α β : ℕ → ℝ), 0 ≤ γ ∧
      (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
      Summable α ∧ Summable β ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n)
        (Complex.EdreiThoma.edreiFunction 1 γ 0 α β z) := by
  obtain ⟨φ, α, β, hφ, hα, hβ, sα, sβ, hrep, hp, hq⟩ :=
    exists_hasSum_exp_mul_prod_div hpf h0 hP
  obtain ⟨φs, αs, βs, hφs, hαs, hβs, sαs, sβs, hreps⟩ :=
    exists_hasSum_exp_mul_prod_div_of_pf (isPolyaFreqSeq_even hpf) (by simpa using h0)
  set N : ℂ → ℂ := fun z => ∏' i, (1 + (α i : ℂ) * z) with hN
  set D : ℂ → ℂ := fun z => ∏' i, (1 - (β i : ℂ) * z) with hD
  set Ns : ℂ → ℂ := fun z => ∏' i, (1 + (αs i : ℂ) * z) with hNs
  set Ds : ℂ → ℂ := fun z => ∏' i, (1 - (βs i : ℂ) * z) with hDs
  have dN : Differentiable ℂ N := Lib.differentiable_prod_add sα
  have dD : Differentiable ℂ D := Lib.differentiable_prod_sub sβ
  have dNs : Differentiable ℂ Ns := Lib.differentiable_prod_add sαs
  have dDs : Differentiable ℂ Ds := Lib.differentiable_prod_sub sβs
  set L : ℂ → ℂ := fun z => Complex.exp (φ z) * N z / D z +
    Complex.exp (φ (-z)) * N (-z) / D (-z) with hL
  set R : ℂ → ℂ := fun z => 2 * Complex.exp (φs (z ^ 2)) * Ns (z ^ 2) / Ds (z ^ 2) with hR
  set U : Set ℂ := {z | D z ≠ 0 ∧ D (-z) ≠ 0 ∧ Ds (z ^ 2) ≠ 0} with hU
  have hUc : Uᶜ.Countable := by
    have hsub : Uᶜ ⊆
        {z | D z = 0} ∪ ({z | D (-z) = 0} ∪ {z | z ^ 2 ∈ {w | Ds w = 0}}) := by
      intro z hz
      simp only [hU, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_not] at hz
      simpa only [Set.mem_union, Set.mem_ofPred_eq] using hz
    refine Set.Countable.mono hsub ((Lib.countable_zeros_prod_sub sβ).union
      (Set.Countable.union ?_ (Lib.countable_preimage_sq (Lib.countable_zeros_prod_sub sβs))))
    have := (Lib.countable_zeros_prod_sub sβ).preimage neg_injective
    exact this
  have hUo : IsOpen U := by
    have c1 : Continuous D := dD.continuous
    have c2 : Continuous fun z => D (-z) := dD.continuous.comp continuous_neg
    have c3 : Continuous fun z : ℂ => Ds (z ^ 2) := dDs.continuous.comp (continuous_pow 2)
    exact (isOpen_ne_fun c1 continuous_const).inter
      ((isOpen_ne_fun c2 continuous_const).inter (isOpen_ne_fun c3 continuous_const))
  have hUconn : IsPreconnected U := by
    have := (hUc.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
    rwa [compl_compl] at this
  have h0U : (0 : ℂ) ∈ U := by
    simp only [hU, hD, hDs, Set.mem_ofPred_eq, neg_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Lib.prod_sub_zero, one_ne_zero, and_self]
  have hLa : AnalyticOnNhd ℂ L U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    obtain ⟨h1, h2, -⟩ := hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have e1 : DifferentiableAt ℂ (fun z => Complex.exp (φ z) * N z / D z) z :=
      (((hφ z).cexp).mul (dN z)).div (dD z) h1
    have hn : DifferentiableAt ℂ (fun z : ℂ => -z) z := differentiableAt_id.neg
    exact e1.add ((((hφ (-z)).comp z hn).cexp.mul ((dN (-z)).comp z hn)).div
      ((dD (-z)).comp z hn) h2)
  have hRa : AnalyticOnNhd ℂ R U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    obtain ⟨-, -, h3⟩ := hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hs : DifferentiableAt ℂ (fun z : ℂ => z ^ 2) z := differentiableAt_pow 2
    exact (((((hφs (z ^ 2)).comp z hs).cexp.const_mul 2).mul
      (DifferentiableAt.comp (g := Ns) z (dNs (z ^ 2)) hs)).div
        (DifferentiableAt.comp (g := Ds) z (dDs (z ^ 2)) hs) h3)
  have hev : L =ᶠ[𝓝 0] R := by
    have t1 : Tendsto (fun z : ℂ => -z) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℂ))
    have t2 : Tendsto (fun z : ℂ => z ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℂ))
    filter_upwards [hrep, t1.eventually hrep, t2.eventually hreps] with z e1 e2 e3
    have := even_odd_hasSum e1 e2 e3
    exact this.trans (by simp only [hR]; ring)
  have hrel : ∀ z : ℂ, (∏' i, (1 - (β i : ℂ) * z)) ≠ 0 →
      (∏' i, (1 - (β i : ℂ) * (-z))) ≠ 0 →
      (∏' i, (1 - (βs i : ℂ) * z ^ 2)) ≠ 0 →
      Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) / (∏' i, (1 - (β i : ℂ) * z)) +
        Complex.exp (φ (-z)) * (∏' i, (1 + (α i : ℂ) * (-z))) /
          (∏' i, (1 - (β i : ℂ) * (-z))) =
      2 * Complex.exp (φs (z ^ 2)) * (∏' i, (1 + (αs i : ℂ) * z ^ 2)) /
        (∏' i, (1 - (βs i : ℂ) * z ^ 2)) := fun z h1 h2 h3 =>
    hLa.eqOn_of_preconnected_of_eventuallyEq hRa hUconn h0U hev ⟨h1, h2, h3⟩
  obtain ⟨c, hc⟩ := odd_part_linear hφ hφs hα hβ hαs hβs sα sβ sαs sβs hrel
  obtain ⟨γ, hγ, hφγ⟩ := exists_nonneg_eq_affine_of_series_zero hφ hc hα hβ sα sβ hp hq
  have hφ0 : Complex.exp (φ 0) = 1 := by
    have e0 := hrep.self_of_nhds
    simpa [h0] using e0.unique (Lib.hasSum_mul_zero_pow fun n => (a n : ℂ))
  refine ⟨γ, α, β, hγ, hα, hβ, sα, sβ, ?_⟩
  filter_upwards [hrep] with z hz
  convert hz using 1
  unfold Complex.EdreiThoma.edreiFunction
  rw [hφγ z, Complex.exp_add, hφ0]
  simp

private lemma edreiFun_add_gamma (C γ δ : ℝ) (k : ℕ) (α β : ℕ → ℝ) (z : ℂ) :
    Complex.EdreiThoma.edreiFunction C (γ + δ) k α β z =
      Complex.exp (δ * z) * Complex.EdreiThoma.edreiFunction C γ k α β z := by
  unfold Complex.EdreiThoma.edreiFunction; push_cast
  rw [add_mul, Complex.exp_add]; ring

private lemma exists_edreiFunction_eq_mul_exp {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (γ : ℝ) (α β : ℕ → ℝ), 0 ≤ γ ∧
      (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
      Summable α ∧ Summable β ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), Complex.EdreiThoma.edreiFunction 1 γ 0 α β z =
        (∑' n, (a n : ℂ) * z ^ n) * Complex.exp (ε * z) := by
  obtain ⟨hg, hg0, hgP⟩ := reduction_to_P h h0 hε
  obtain ⟨γ, α, β, hγ, hα, hβ, sα, sβ, hrep⟩ :=
    exists_hasSum_edreiFunction_of_property_P hg hg0 hgP
  refine ⟨γ, α, β, hγ, hα, hβ, sα, sβ, ?_⟩
  filter_upwards [hrep, Lib.eventually_hasSum_conv_exp h h0 ε] with z h1 h2
  exact h1.unique h2

/-- **The Edrei--Thoma converse.** A normalized Pólya-frequency sequence has an analytic
Edrei--Thoma representation near zero, with nonnegative summable parameters. -/
theorem exists_hasSum_edreiFunction {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) (h0 : a 0 = 1) :
    ∃ (γ : ℝ) (α β : ℕ → ℝ), 0 ≤ γ ∧
      (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
      Summable α ∧ Summable β ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n)
        (Complex.EdreiThoma.edreiFunction 1 γ 0 α β z) := by
  obtain ⟨γ₁, α₁, β₁, hγ₁, hα₁, hβ₁, sα₁, sβ₁, h₁⟩ :=
    exists_edreiFunction_eq_mul_exp h h0 one_pos
  have hge : ∀ ε : ℝ, 0 < ε → -ε ≤ γ₁ - 1 := by
    intro ε hε
    obtain ⟨γ₂, α₂, β₂, hγ₂, hα₂, hβ₂, sα₂, sβ₂, h₂⟩ :=
      exists_edreiFunction_eq_mul_exp h h0 hε
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ),
        Complex.EdreiThoma.edreiFunction 1 (γ₁ + ε) 0 α₁ β₁ z =
          Complex.EdreiThoma.edreiFunction 1 (γ₂ + 1) 0 α₂ β₂ z := by
      filter_upwards [h₁, h₂] with z e1 e2
      rw [edreiFun_add_gamma, edreiFun_add_gamma, e1, e2]
      push_cast; ring
    obtain ⟨-, -, hγ, -, -⟩ :=
      Complex.EdreiThoma.params_eq_of_edreiFunction_eq one_pos one_pos hα₁ hβ₁ hα₂ hβ₂
        sα₁ sβ₁ sα₂ sβ₂ hev
    linarith
  have hγ : 0 ≤ γ₁ - 1 := by
    by_contra hneg
    push Not at hneg
    have := hge ((1 - γ₁) / 2) (by linarith)
    linarith
  refine ⟨γ₁ - 1, α₁, β₁, hγ, hα₁, hβ₁, sα₁, sβ₁, ?_⟩
  filter_upwards [h₁, Lib.eventually_hasSum_genFun h h0] with z e1 e2
  convert e2 using 1
  have e3 := edreiFun_add_gamma 1 (γ₁ - 1) 1 0 α₁ β₁ z
  rw [sub_add_cancel, e1] at e3
  have hz : Complex.exp ((1 : ℝ) * z) ≠ 0 := Complex.exp_ne_zero _
  push_cast at e3 hz ⊢
  apply mul_left_cancel₀ hz
  rw [← e3]; ring

/-- A normalized Pólya-frequency sequence has the parameters of a formal Edrei--Thoma
`canonicalProduct`; its generating series has the corresponding analytic germ. -/
theorem exists_canonicalProduct_representation {a : ℕ → ℝ} (h : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) :
    ∃ (γ : ℝ) (α β : ℕ → ℝ), 0 ≤ γ ∧
      (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
      Summable (fun i => α i + β i) ∧
      IsPolyaFreqSeq (fun n => PowerSeries.coeff n (canonicalProduct 1 0 γ α β)) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n => (a n : ℂ) * z ^ n)
        (Complex.EdreiThoma.edreiFunction 1 γ 0 α β z) := by
  obtain ⟨γ, α, β, hγ, hα, hβ, sα, sβ, hrep⟩ :=
    exists_hasSum_edreiFunction h h0
  have hsum : Summable (fun i => α i + β i) := sα.add sβ
  exact ⟨γ, α, β, hγ, hα, hβ, hsum,
    isPolyaFreqSeq_coeff_canonicalProduct zero_le_one hγ 0 hα hβ hsum, hrep⟩

end RealRooted.EdreiThoma
