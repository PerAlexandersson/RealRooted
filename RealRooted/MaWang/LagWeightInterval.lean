module

import RealRooted.MaWang.ForcingBudget
import RealRooted.Linear
public import RealRooted.SimpleRoots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.WithBot

/-!
# Sharp lag-weight intervals

We formalize the sharp interval in the unpublished manuscript
`derivative-matrix-root-threshold-2026-10-18.md`, §“Exact interval for a
derivative-plus-lag step” (RealRooted #1772). For `H_s = f + X f' + s G`,
only roots with positive lag ratio constrain a nonnegative weight. Their
finite minimum is taken in `WithTop ℝ`, so an empty family has threshold `⊤`.

We retain the degree and positive-leading-coefficient gates on the whole
admissible interval. This is a certificate for one current row and one lag;
it asserts no universal Weyl-matrix preservation or all-threshold Bell result.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace ForcingBudget

/-- The derivative-plus-lag output at weight `s`. -/
def lagStep (f G : ℝ[X]) (s : ℝ) : ℝ[X] := f + X * f.derivative + C s * G

/-- The first positive root-crossing weight; an empty family gives infinity. -/
def lagWeightThreshold (f G : ℝ[X]) : WithTop ℝ := by
  classical
  exact f.roots.toFinset.inf fun r =>
    if 0 < G.eval r / f.derivative.eval r then
      ((-r / (G.eval r / f.derivative.eval r) : ℝ) : WithTop ℝ) else ⊤

/-- The extended minimum is equivalent to all its active rootwise bounds. -/
theorem le_lagWeightThreshold_iff {f G : ℝ[X]} (hf : f ≠ 0) (s : ℝ) :
    (s : WithTop ℝ) ≤ lagWeightThreshold f G ↔
      ∀ r, f.IsRoot r → 0 < G.eval r / f.derivative.eval r →
        s ≤ -r / (G.eval r / f.derivative.eval r) := by
  classical
  simp only [lagWeightThreshold, Finset.le_inf_iff, Multiset.mem_toFinset,
    mem_roots hf]
  constructor
  · intro h r hr ha
    simpa only [ite_eq_left ha, WithTop.coe_le_coe] using h r hr
  · intro h r hr
    split_ifs with ha
    · exact WithTop.coe_le_coe.mpr (h r hr ha)
    · exact le_top

/-- The strict interior is equivalent to strict bounds at every active root. -/
theorem lt_lagWeightThreshold_iff {f G : ℝ[X]} (hf : f ≠ 0) (s : ℝ) :
    (s : WithTop ℝ) < lagWeightThreshold f G ↔
      ∀ r, f.IsRoot r → 0 < G.eval r / f.derivative.eval r →
        s < -r / (G.eval r / f.derivative.eval r) := by
  classical
  simp only [lagWeightThreshold, Finset.lt_inf_iff (WithTop.coe_lt_top s),
    Multiset.mem_toFinset, mem_roots hf]
  constructor
  · intro h r hr ha
    simpa only [ite_eq_left ha, WithTop.coe_lt_coe] using h r hr
  · intro h r hr
    split_ifs with ha
    · exact WithTop.coe_lt_coe.mpr (h r hr ha)
    · exact WithTop.coe_lt_top s

/-- No positive lag ratio means that there is no finite upper bound. -/
theorem lagWeightThreshold_eq_top_iff {f G : ℝ[X]} (hf : f ≠ 0) :
    lagWeightThreshold f G = ⊤ ↔
      ∀ r, f.IsRoot r → G.eval r / f.derivative.eval r ≤ 0 := by
  classical
  simp only [lagWeightThreshold, Finset.inf_eq_top_iff, Multiset.mem_toFinset,
    mem_roots hf, ite_eq_right_iff, WithTop.coe_ne_top, imp_false, not_lt]

/-- At a current root the derivative-plus-lag flux has this exact quotient form. -/
theorem eval_lagStep_div {f G : ℝ[X]} {r s : ℝ} (hr : f.IsRoot r)
    (hd : f.derivative.eval r ≠ 0) :
    (lagStep f G s).eval r / f.derivative.eval r =
      r + s * (G.eval r / f.derivative.eval r) := by
  simp only [lagStep, eval_add, eval_mul, eval_X, eval_C, hr.eq_zero, zero_add]
  field_simp [hd]

/-- Root signs divided by the nonzero derivative agree with division-free flux signs. -/
private theorem flux_nonpos_iff {q d : ℝ} (hd : d ≠ 0) :
    q * d ≤ 0 ↔ q / d ≤ 0 := by
  have heq : q / d = (q * d) / d ^ 2 := by field_simp [hd]
  rw [heq, div_le_iff₀ (sq_pos_iff.mpr hd)]
  simp

/-- Strict root signs can likewise be tested after dividing by the derivative. -/
private theorem flux_neg_iff {q d : ℝ} (hd : d ≠ 0) :
    q * d < 0 ↔ q / d < 0 := by
  have heq : q / d = (q * d) / d ^ 2 := by field_simp [hd]
  rw [heq, div_lt_iff₀ (sq_pos_iff.mpr hd)]
  simp

/-- The sharp weak interval at one admissible nonnegative weight. -/
theorem strictInterl_lagStep_iff {f G : ℝ[X]} {s : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (hs0 : 0 ≤ s)
    (hq : HasPosLeadingCoeff (lagStep f G s))
    (hlo : f.natDegree ≤ (lagStep f G s).natDegree)
    (hhi : (lagStep f G s).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (lagStep f G s) ↔ (s : WithTop ℝ) ≤ lagWeightThreshold f G := by
  rw [strictInterl_iff_eval_mul_derivative_nonpos hf hs hn hq hlo hhi,
    le_lagWeightThreshold_iff hf.ne_zero]
  have hd : ∀ {r : ℝ}, f.IsRoot r → f.derivative.eval r ≠ 0 :=
    (HasSimpleRoots.of_roots_nodup hf.ne_zero hn).eval_derivative_ne_zero
  constructor
  · intro h r hr ha
    have hh := (flux_nonpos_iff (hd hr)).1 (h r hr)
    rw [eval_lagStep_div hr (hd hr)] at hh
    exact (le_div_iff₀ ha).2 (by linarith)
  · intro h r hr
    apply (flux_nonpos_iff (hd hr)).2
    rw [eval_lagStep_div hr (hd hr)]
    by_cases ha : 0 < G.eval r / f.derivative.eval r
    · have hh := (le_div_iff₀ ha).1 (h r hr ha)
      linarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_not_gt ha)
      linarith [hrneg r hr]

/-- Strict interior weights give coprimality and simple output roots. -/
theorem strictInterl_isCoprime_lagStep_iff {f G : ℝ[X]} {s : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (hs0 : 0 ≤ s)
    (hq : HasPosLeadingCoeff (lagStep f G s))
    (hlo : f.natDegree ≤ (lagStep f G s).natDegree)
    (hhi : (lagStep f G s).natDegree ≤ f.natDegree + 1) :
    (StrictInterl f (lagStep f G s) ∧ IsCoprime f (lagStep f G s)) ↔
      (s : WithTop ℝ) < lagWeightThreshold f G := by
  rw [strictInterl_isCoprime_iff_eval_mul_derivative_neg hf hs hn hq hlo hhi,
    lt_lagWeightThreshold_iff hf.ne_zero]
  have hd : ∀ {r : ℝ}, f.IsRoot r → f.derivative.eval r ≠ 0 :=
    (HasSimpleRoots.of_roots_nodup hf.ne_zero hn).eval_derivative_ne_zero
  constructor
  · intro h r hr ha
    have hh := (flux_neg_iff (hd hr)).1 (h r hr)
    rw [eval_lagStep_div hr (hd hr)] at hh
    exact (lt_div_iff₀ ha).2 (by linarith)
  · intro h r hr
    apply (flux_neg_iff (hd hr)).2
    rw [eval_lagStep_div hr (hd hr)]
    by_cases ha : 0 < G.eval r / f.derivative.eval r
    · have hh := (lt_div_iff₀ ha).1 (h r hr ha)
      linarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_not_gt ha)
      linarith [hrneg r hr]

/-- The zero-aware convention has exactly the same sharp interval under the nonzero gates. -/
theorem interl_lagStep_iff {f G : ℝ[X]} {s : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (hs0 : 0 ≤ s)
    (hq : HasPosLeadingCoeff (lagStep f G s))
    (hlo : f.natDegree ≤ (lagStep f G s).natDegree)
    (hhi : (lagStep f G s).natDegree ≤ f.natDegree + 1) :
    Interl f (lagStep f G s) ↔ (s : WithTop ℝ) ≤ lagWeightThreshold f G := by
  rw [← strictInterl_lagStep_iff hf hs hn hrneg hs0 hq hlo hhi]
  exact ⟨fun h => h.toStrictInterl_of_ne hf.ne_zero hq.ne_zero, StrictInterl.toInterl⟩

/-- The full interval theorem keeps the cap `S` and its degree/leading-sign domain explicit. -/
theorem interl_lagStep_iff_of_mem_Icc {f G : ℝ[X]} {s S : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0)
    (hdom : ∀ t ∈ Set.Icc 0 S, HasPosLeadingCoeff (lagStep f G t) ∧
      f.natDegree ≤ (lagStep f G t).natDegree ∧
      (lagStep f G t).natDegree ≤ f.natDegree + 1)
    (hsI : s ∈ Set.Icc 0 S) :
    Interl f (lagStep f G s) ↔ (s : WithTop ℝ) ≤ lagWeightThreshold f G := by
  obtain ⟨hq, hlo, hhi⟩ := hdom s hsI
  exact interl_lagStep_iff hf hs hn hrneg hsI.1 hq hlo hhi

/-- Positive lag ratios cross strictly after weight zero when all current roots are negative. -/
theorem lagWeightThreshold_pos {f G : ℝ[X]} (hf : f ≠ 0)
    (hrneg : ∀ r, f.IsRoot r → r < 0) :
    (0 : WithTop ℝ) < lagWeightThreshold f G := by
  apply (lt_lagWeightThreshold_iff hf 0).2
  intro r hr ha
  exact div_pos (neg_pos.mpr (hrneg r hr)) ha

/-- A finite threshold is attained by a root with positive lag ratio. -/
theorem exists_root_lagWeightThreshold_eq {f G : ℝ[X]} (hf : f ≠ 0) {t : ℝ}
    (ht : lagWeightThreshold f G = (t : WithTop ℝ)) :
    ∃ r, f.IsRoot r ∧ 0 < G.eval r / f.derivative.eval r ∧
      t = -r / (G.eval r / f.derivative.eval r) := by
  classical
  have hle := (le_lagWeightThreshold_iff hf t).1 ht.ge
  by_contra h
  have hlt : (t : WithTop ℝ) < lagWeightThreshold f G := by
    apply (lt_lagWeightThreshold_iff hf t).2
    intro r hr ha
    exact lt_of_le_of_ne (hle r hr ha) (fun he => h ⟨r, hr, ha, he⟩)
  rw [ht] at hlt
  exact (lt_irrefl _) hlt

/-- At a finite endpoint the current row and output share a root.
This algebraic fact needs simple current roots, but no output degree or sign gate. -/
theorem exists_common_root_lagStep {f G : ℝ[X]} (hf : f ≠ 0)
    (hn : f.roots.Nodup) {t : ℝ}
    (ht : lagWeightThreshold f G = (t : WithTop ℝ)) :
    ∃ r, f.IsRoot r ∧ (lagStep f G t).IsRoot r := by
  obtain ⟨r, hr, ha, he⟩ := exists_root_lagWeightThreshold_eq hf ht
  have hd := (HasSimpleRoots.of_roots_nodup hf hn).eval_derivative_ne_zero hr
  refine ⟨r, hr, ?_⟩
  have hdiv : (lagStep f G t).eval r / f.derivative.eval r = 0 := by
    rw [eval_lagStep_div hr hd, he, div_mul_cancel₀ _ (ne_of_gt ha)]
    exact add_neg_cancel r
  have heval := (div_eq_iff hd).1 hdiv
  simpa only [IsRoot.def, zero_mul] using heval

/-- Interior weights have simple outputs as well as the exact directed interlacing relation. -/
theorem hasSimpleRoots_lagStep_of_lt {f G : ℝ[X]} {s : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (hs0 : 0 ≤ s)
    (hq : HasPosLeadingCoeff (lagStep f G s))
    (hlo : f.natDegree ≤ (lagStep f G s).natDegree)
    (hhi : (lagStep f G s).natDegree ≤ f.natDegree + 1)
    (hlt : (s : WithTop ℝ) < lagWeightThreshold f G) :
    HasSimpleRoots (lagStep f G s) := by
  obtain ⟨he, hc⟩ :=
    (strictInterl_isCoprime_lagStep_iff hf hs hn hrneg hs0 hq hlo hhi).2 hlt
  exact (he.hasSimpleRoots_of_isCoprime hc).2

/-- At an admissible finite endpoint interlacing holds and coprimality fails. -/
theorem interl_lagStep_and_not_isCoprime {f G : ℝ[X]} {t : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (ht0 : 0 ≤ t)
    (hq : HasPosLeadingCoeff (lagStep f G t))
    (hlo : f.natDegree ≤ (lagStep f G t).natDegree)
    (hhi : (lagStep f G t).natDegree ≤ f.natDegree + 1)
    (ht : lagWeightThreshold f G = (t : WithTop ℝ)) :
    Interl f (lagStep f G t) ∧ ¬ IsCoprime f (lagStep f G t) := by
  have he := (strictInterl_lagStep_iff hf hs hn hrneg ht0 hq hlo hhi).2 ht.ge
  refine ⟨he.toInterl, ?_⟩
  intro hc
  have hlt := (strictInterl_isCoprime_lagStep_iff hf hs hn hrneg ht0 hq hlo hhi).1 ⟨he, hc⟩
  rw [ht] at hlt
  exact (lt_irrefl _) hlt

/-- Above the threshold the requested orientation fails, with every output gate retained. -/
theorem not_interl_lagStep_of_lt {f G : ℝ[X]} {s : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (hs0 : 0 ≤ s)
    (hq : HasPosLeadingCoeff (lagStep f G s))
    (hlo : f.natDegree ≤ (lagStep f G s).natDegree)
    (hhi : (lagStep f G s).natDegree ≤ f.natDegree + 1)
    (hlt : lagWeightThreshold f G < (s : WithTop ℝ)) :
    ¬ Interl f (lagStep f G s) := by
  rw [interl_lagStep_iff hf hs hn hrneg hs0 hq hlo hhi]
  exact not_le_of_gt hlt

/-- Within the admissible domain an orientation cannot disappear and later reappear. -/
theorem interl_lagStep_of_le {f G : ℝ[X]} {s t : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hrneg : ∀ r, f.IsRoot r → r < 0) (hs0 : 0 ≤ s) (hst : s ≤ t)
    (hqs : HasPosLeadingCoeff (lagStep f G s))
    (hlos : f.natDegree ≤ (lagStep f G s).natDegree)
    (hhis : (lagStep f G s).natDegree ≤ f.natDegree + 1)
    (hqt : HasPosLeadingCoeff (lagStep f G t))
    (hlot : f.natDegree ≤ (lagStep f G t).natDegree)
    (hhit : (lagStep f G t).natDegree ≤ f.natDegree + 1)
    (he : Interl f (lagStep f G t)) : Interl f (lagStep f G s) := by
  apply (interl_lagStep_iff hf hs hn hrneg hs0 hqs hlos hhis).2
  exact (WithTop.coe_le_coe.mpr hst).trans
    ((interl_lagStep_iff hf hs hn hrneg (hs0.trans hst) hqt hlot hhit).1 he)

/-- For a linear combination of lags, the root coordinates are linear in their coefficients. -/
theorem interl_lagStep_sum_iff {ι : Type*} (u : Finset ι) (c : ι → ℝ)
    (g : ι → ℝ[X]) {f : ℝ[X]} {s : ℝ}
    (hf : HasPosLeadingCoeff f) (hs : f.Splits) (hn : f.roots.Nodup)
    (hq : HasPosLeadingCoeff (lagStep f (∑ i ∈ u, C (c i) * g i) s))
    (hlo : f.natDegree ≤ (lagStep f (∑ i ∈ u, C (c i) * g i) s).natDegree)
    (hhi : (lagStep f (∑ i ∈ u, C (c i) * g i) s).natDegree ≤ f.natDegree + 1) :
    Interl f (lagStep f (∑ i ∈ u, C (c i) * g i) s) ↔
      ∀ r, f.IsRoot r →
        r + s * ∑ i ∈ u, c i * ((g i).eval r / f.derivative.eval r) ≤ 0 := by
  have he : Interl f (lagStep f (∑ i ∈ u, C (c i) * g i) s) ↔
      StrictInterl f (lagStep f (∑ i ∈ u, C (c i) * g i) s) :=
    ⟨fun h => h.toStrictInterl_of_ne hf.ne_zero hq.ne_zero, StrictInterl.toInterl⟩
  rw [he, strictInterl_iff_eval_mul_derivative_nonpos hf hs hn hq hlo hhi]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro hr
  have hd := (HasSimpleRoots.of_roots_nodup hf.ne_zero hn).eval_derivative_ne_zero hr
  rw [flux_nonpos_iff hd, eval_lagStep_div hr hd]
  simp only [eval_finsetSum, eval_mul, eval_C, Finset.sum_div, mul_div_assoc]

/-- The threshold for a linear current row can be evaluated without choosing a root list. -/
theorem lagWeightThreshold_X_add_C (a b c : ℝ) :
    lagWeightThreshold (X + C b) (C a * X + C c) =
      if 0 < c - a * b then ((b / (c - a * b) : ℝ) : WithTop ℝ) else ⊤ := by
  classical
  simp [lagWeightThreshold, mul_neg, sub_eq_add_neg, add_comm]

/-- The arbitrary ordered-triple counterexample has sharp threshold `1/3`. -/
theorem lagWeightThreshold_X_add_one :
    lagWeightThreshold (X + C 1) (C 6 * X + C 9) = ((1 / 3 : ℝ) : WithTop ℝ) := by
  rw [lagWeightThreshold_X_add_C]
  norm_num

/-- The actual threshold-three row has no finite adverse root crossing. -/
theorem lagWeightThreshold_X_add_four :
    lagWeightThreshold (X + C 4) (C 3 * X + C 6) = ⊤ := by
  rw [lagWeightThreshold_X_add_C]
  norm_num

/-- Exact orientation regression: the arbitrary companion input fails at weight one. -/
theorem not_interl_X_add_one_eight_X_add_ten :
    ¬ Interl (X + C 1) (C 8 * X + C 10) := by
  intro h
  have heq : C (1 / 8 : ℝ) * (C 8 * X + C 10) = X + C (5 / 4) := by
    norm_num [mul_add, ← mul_assoc, ← C_mul]
  have hh := (h.toStrictInterl_of_ne (X_add_C_ne_zero 1)
    (by intro hz; have := congrArg (fun p : ℝ[X] => p.coeff 1) hz; norm_num at this)).C_mul_right
      (a := 1 / 8) (by norm_num)
  rw [heq] at hh
  have := StrictInterl.X_add_C_iff.mp hh
  norm_num at this

/-- Exact orientation regression: the actual threshold-three step has the desired direction. -/
theorem interl_X_add_four_five_X_add_ten :
    Interl (X + C 4) (C 5 * X + C 10) := by
  have heq : C (5 : ℝ) * (X + C 2) = C 5 * X + C 10 := by
    norm_num [mul_add, ← mul_assoc, ← C_mul]
  rw [← heq]
  exact ((StrictInterl.X_add_C_iff.mpr (by norm_num : (2 : ℝ) ≤ 4)).C_mul_right
    (by norm_num : (5 : ℝ) ≠ 0)).toInterl

end ForcingBudget
end RealRooted
