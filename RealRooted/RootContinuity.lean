import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Eval.Defs
import RealRooted.RootCountFinite
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# Root-continuity tools

This file collects coefficient and evaluation estimates used to control roots
under small perturbations of a real polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Reciprocal pencil scaling -/

/-- A nonzero right-pencil parameter can be inverted by scaling: `f + μ g`
is `μ` times `g + μ⁻¹ f`. -/
theorem add_right_eq_C_mul_add_left_inv
    {f g : ℝ[X]} {μ : ℝ} (hμ : μ ≠ 0) :
    f + C μ * g = C μ * (g + C μ⁻¹ * f) := by
  rw [mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hμ, C_1, one_mul,
    add_comm]

/-- The reciprocal right-pencil scaling preserves the root predicate. -/
theorem add_right_isRoot_iff_add_left_inv
    {f g : ℝ[X]} {μ x : ℝ} (hμ : μ ≠ 0) :
    (f + C μ * g).IsRoot x ↔ (g + C μ⁻¹ * f).IsRoot x := by
  rw [add_right_eq_C_mul_add_left_inv (f := f) (g := g) hμ]
  simp [Polynomial.IsRoot.def, hμ]

/-- The reciprocal right-pencil scaling preserves the root multiset. -/
theorem add_right_roots_eq_add_left_inv
    {f g : ℝ[X]} {μ : ℝ} (hμ : μ ≠ 0) :
    (f + C μ * g).roots = (g + C μ⁻¹ * f).roots := by
  rw [add_right_eq_C_mul_add_left_inv (f := f) (g := g) hμ,
    Polynomial.roots_C_mul _ hμ]

/-- The reciprocal right-pencil scaling preserves upper-threshold root counts. -/
theorem add_right_roots_gt_card_eq_add_left_inv
    {f g : ℝ[X]} {μ x : ℝ} (hμ : μ ≠ 0) :
    ((f + C μ * g).roots.filter (x < ·)).card =
      ((g + C μ⁻¹ * f).roots.filter (x < ·)).card := by
  rw [add_right_roots_eq_add_left_inv (f := f) (g := g) hμ]

/-! ## Root-continuity and interval count tools -/

/-- A real-rooted polynomial over `ℝ` splits over `ℝ`. -/
lemma IsRealRooted.splits {p : ℝ[X]} (hp_splits : p.Splits) : p.Splits :=
  hp_splits

/-- Finite coefficient sup bound over the `natDegree` range. -/
def coeffSumRange (p : ℝ[X]) : ℝ :=
  Finset.sum (Finset.range (p.natDegree + 1)) fun j => ‖p.coeff j‖

lemma coeff_norm_le_coeffSumRange (p : ℝ[X]) (i : ℕ) :
    ‖p.coeff i‖ ≤ coeffSumRange p := by
  by_cases hi : i ∈ Finset.range (p.natDegree + 1)
  · unfold coeffSumRange
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) hi
  · have hlt : p.natDegree < i := by simp_all
    rw [coeff_eq_zero_of_natDegree_lt hlt, norm_zero]
    have hnonneg : 0 ≤ coeffSumRange p := by
      unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    lia

/-- Coefficient difference for the affine perturbation `f + μ g`. -/
lemma norm_coeff_sub_add_C_mul (f g : ℝ[X]) (μ : ℝ) (i : ℕ) :
    ‖(f + C μ * g).coeff i - f.coeff i‖ = ‖μ * g.coeff i‖ := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]

/-- Uniform coefficient bound for `f + μ g` relative to `f`. -/
lemma norm_coeff_sub_add_C_mul_le
    (f g : ℝ[X]) {μ M : ℝ}
    (hμ : 0 ≤ μ)
    (hM : ∀ i : ℕ, ‖g.coeff i‖ ≤ M) :
    ∀ i : ℕ, ‖(f + C μ * g).coeff i - f.coeff i‖ ≤ μ * M := by
  intro i
  rw [norm_coeff_sub_add_C_mul]
  calc
    ‖μ * g.coeff i‖ = ‖μ‖ * ‖g.coeff i‖ := norm_mul _ _
    _ = μ * ‖g.coeff i‖ := by simp [Real.norm_of_nonneg hμ]
    _ ≤ μ * M := mul_le_mul_of_nonneg_left (hM i) hμ

/-- Complex-root continuity wrapper (via `aroots`): if monic `g` is
coefficientwise close to monic `f`, then each complex root of `f` has a nearby
complex root of `g`. This is the `aroots`-valued form used in limit arguments
where the target root may not yet be known real. -/
theorem exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
    {f g : ℝ[X]} {z : ℂ} {ε : ℝ}
    (hε : 0 < ε)
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hcoeff : ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε)
    (hg_rr_splits : g.Splits) :
    ∃ w : ℂ, w ∈ g.aroots ℂ ∧
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
  obtain ⟨w, hw_mem, hw_dist⟩ :=
    Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f) (g := g) (L := ℂ) hε hz hf_monic hg_monic hdeg hcoeff
      ((IsRealRooted.splits hg_rr_splits).map (algebraMap ℝ ℂ))
  grind

/-- Uniform coefficient control for normalized left-family perturbations:
`(1/(t+1)) * (t f + g)` is coefficientwise `O((t+1)⁻¹)` away from `f`. -/
lemma norm_coeff_sub_normalized_left_family_le
    (f g : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    ∀ i : ℕ,
      ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖ ≤
        (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by
  intro i
  have hcoeff :
      (C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i =
        (t + 1)⁻¹ * (g.coeff i - f.coeff i) := by
    calc
      (C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i
          = ((t + 1)⁻¹ * (t * f.coeff i + g.coeff i)) - f.coeff i := by
              simp
      _ = (t + 1)⁻¹ * (g.coeff i - f.coeff i) := by
            grind
  have hden_nonneg : 0 ≤ (t + 1)⁻¹ := by positivity
  calc
    ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖
        = ‖(t + 1)⁻¹ * (g.coeff i - f.coeff i)‖ := by lia
    _ = ‖(t + 1)⁻¹‖ * ‖g.coeff i - f.coeff i‖ := norm_mul _ _
    _ = (t + 1)⁻¹ * ‖g.coeff i - f.coeff i‖ := by
          simp [Real.norm_of_nonneg hden_nonneg]
    _ ≤ (t + 1)⁻¹ * (‖g.coeff i‖ + ‖f.coeff i‖) := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (t + 1)⁻¹ * (coeffSumRange g + coeffSumRange f) := by
          gcongr
          · exact coeff_norm_le_coeffSumRange g i
          · exact coeff_norm_le_coeffSumRange f i
    _ = (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by ring

/-- Strict coefficient control from an explicit scalar bound. -/
lemma norm_coeff_sub_normalized_left_family_lt
    (f g : ℝ[X]) {t ε : ℝ} (ht : 0 < t)
    (hbound :
      (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε) :
    ∀ i : ℕ, ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖ < ε :=
  fun i => lt_of_le_of_lt (norm_coeff_sub_normalized_left_family_le f g ht i) hbound

/-- For every target precision `ε > 0`, choosing `t` sufficiently large makes the normalized
left-family coefficient error smaller than `ε`. -/
theorem exists_t_pos_with_normalized_left_family_bound
    (f g : ℝ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε := by
  let c : ℝ := coeffSumRange f + coeffSumRange g
  have hc : 0 ≤ c := by
    refine add_nonneg ?_ ?_
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hε0 : ε ≠ 0 := ne_of_gt hε
  refine ⟨c / ε + 1, by positivity, ?_⟩
  have hden_pos : 0 < c / ε + 2 := by
    have hdiv_nonneg : 0 ≤ c / ε := div_nonneg hc (le_of_lt hε)
    linarith
  have hbound_div : c / (c / ε + 2) < ε := by
    rw [div_lt_iff₀ hden_pos]
    have hceq : ε * (c / ε) = c := by grind
    grind
  grind

/-- Root continuity for the normalized left affine family:
if `f, g` are monic of the same degree and `C t * f + g` is real-rooted, then under a
coefficient-smallness bound one gets a root of `C t * f + g` near any prescribed root of `f`. -/
theorem exists_real_root_near_in_left_family
    {f g : ℝ[X]} {a t ε : ℝ}
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (ht : 0 < t)
    (hcoeff_bound : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε)
    (hrr_ne : (C t * f + g) ≠ 0) (hrr_splits : (C t * f + g).Splits) :
    ∃ b : ℝ, (C t * f + g).IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  have hsum_nonneg : 0 ≤ coeffSumRange f + coeffSumRange g := by
    refine add_nonneg ?_ ?_
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoeff_nonneg : 0 ≤ (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) :=
    mul_nonneg (by positivity) hsum_nonneg
  have hε : 0 < ε := lt_of_le_of_lt hcoeff_nonneg hcoeff_bound
  let q : ℝ[X] := C (t + 1)⁻¹ * (C t * f + g)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have ht1_ne : t + 1 ≠ 0 := by positivity
  have hf_pos : HasPosLeadingCoeff f := hasPosLeadingCoeff_of_monic hf_monic
  have hg_pos : HasPosLeadingCoeff g := hasPosLeadingCoeff_of_monic hg_monic
  have hCt_f_pos : HasPosLeadingCoeff (C t * f) := hasPosLeadingCoeff_C_mul ht hf_pos
  have hsum_deg : (C t * f + g).natDegree = f.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by rw [natDegree_C_mul ht_ne]
    exact
      (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        (hCt_deg.trans hdeg.symm) hCt_f_pos hg_pos).trans hCt_deg
  have hsum_lc : (C t * f + g).leadingCoeff = t + 1 := by
    have hg_coeff : g.coeff f.natDegree = 1 := by simpa [hdeg] using hg_monic.coeff_natDegree
    unfold Polynomial.leadingCoeff
    simp_all
  have hq_monic : q.Monic := by
    unfold q
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_deg : q.natDegree = f.natDegree := by
    rw [show q = C (t + 1)⁻¹ * (C t * f + g) by rfl,
      natDegree_C_mul (inv_ne_zero ht1_ne), hsum_deg]
  have hq_rr : q ≠ 0 ∧ q.Splits := by simp_all [q]
  obtain ⟨b, hb_qroot, hb_dist⟩ :=
    exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f) (g := q) (a := a) (ε := ε) hε ha hf_monic hq_monic hq_deg
      (norm_coeff_sub_normalized_left_family_lt f g ht hcoeff_bound) (by simp_all [q])
  have hb_sum_mem : b ∈ (C t * f + g).roots := by
    simpa [q, roots_C_mul _ (inv_ne_zero ht1_ne)] using hb_qroot
  have hb_sum_root : (C t * f + g).IsRoot b := (Polynomial.mem_roots hrr_ne).mp hb_sum_mem
  grind

/-- Complex-root continuity for the normalized left affine family:
if `f, g` are monic of the same degree and `C t * f + g` is real-rooted, then
under a coefficient-smallness bound one gets a complex root of `C t * f + g`
near any prescribed complex root of `f`. -/
theorem exists_complex_aroot_near_in_left_family
    {f g : ℝ[X]} {z : ℂ} {t ε : ℝ}
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (ht : 0 < t)
    (hcoeff_bound : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε)
    (hrr_ne : (C t * f + g) ≠ 0) (hrr_splits : (C t * f + g).Splits) :
    ∃ w : ℂ, w ∈ (C t * f + g).aroots ℂ ∧
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
  have hsum_nonneg : 0 ≤ coeffSumRange f + coeffSumRange g := by
    refine add_nonneg ?_ ?_
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoeff_nonneg : 0 ≤ (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) :=
    mul_nonneg (by positivity) hsum_nonneg
  have hε : 0 < ε := lt_of_le_of_lt hcoeff_nonneg hcoeff_bound
  let q : ℝ[X] := C (t + 1)⁻¹ * (C t * f + g)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have ht1_ne : t + 1 ≠ 0 := by positivity
  have hf_pos : HasPosLeadingCoeff f := hasPosLeadingCoeff_of_monic hf_monic
  have hg_pos : HasPosLeadingCoeff g := hasPosLeadingCoeff_of_monic hg_monic
  have hCt_f_pos : HasPosLeadingCoeff (C t * f) := hasPosLeadingCoeff_C_mul ht hf_pos
  have hsum_deg : (C t * f + g).natDegree = f.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by rw [natDegree_C_mul ht_ne]
    exact
      (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        (hCt_deg.trans hdeg.symm) hCt_f_pos hg_pos).trans hCt_deg
  have hsum_lc : (C t * f + g).leadingCoeff = t + 1 := by
    have hg_coeff : g.coeff f.natDegree = 1 := by simpa [hdeg] using hg_monic.coeff_natDegree
    unfold Polynomial.leadingCoeff
    simp_all
  have hq_monic : q.Monic := by
    unfold q
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_deg : q.natDegree = f.natDegree := by
    rw [show q = C (t + 1)⁻¹ * (C t * f + g) by rfl,
      natDegree_C_mul (inv_ne_zero ht1_ne), hsum_deg]
  have hq_rr : q ≠ 0 ∧ q.Splits := by simp_all [q]
  obtain ⟨w, hw_qroot, hw_dist⟩ :=
    exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
      (f := f) (g := q) (z := z) (ε := ε) hε hz hf_monic hq_monic hq_deg
      (norm_coeff_sub_normalized_left_family_lt f g ht hcoeff_bound) hq_rr.2
  have hw_sum_mem : w ∈ (C t * f + g).aroots ℂ := by
    simpa [q, Polynomial.aroots_C_mul _ (inv_ne_zero ht1_ne)] using hw_qroot
  grind

/-- Any complex algebraic root of a real-rooted polynomial over `ℝ` has zero
imaginary part. -/
lemma im_eq_zero_of_mem_aroots_of_isRealRooted
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) {z : ℂ}
    (hz : z ∈ p.aroots ℂ) :
    z.im = 0 := by
  have hz_root : (p.map (algebraMap ℝ ℂ)).IsRoot z := by simp_all
  have hz_range : z ∈ (algebraMap ℝ ℂ).range :=
    (IsRealRooted.splits hp_splits).mem_range_of_isRoot hp_ne hz_root
  rcases hz_range with ⟨r, rfl⟩
  simp

/-- A continuous real-valued function that never vanishes on a closed interval
has endpoint values with the same nonzero sign. -/
theorem mul_pos_of_forall_ne_zero_Icc
    {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, F x ≠ 0) :
    0 < F a * F b := by
  have hmema : a ∈ Set.Icc a b := ⟨le_refl _, hab⟩
  have hmemb : b ∈ Set.Icc a b := ⟨hab, le_refl _⟩
  have ha : F a ≠ 0 := hne a hmema
  have hb : F b ≠ 0 := hne b hmemb
  rcases lt_or_gt_of_ne ha with hlt_a | hgt_a
  · rcases lt_or_gt_of_ne hb with hlt_b | hgt_b
    · exact mul_pos_of_neg_of_neg hlt_a hlt_b
    · exfalso
      have hzero : (0 : ℝ) ∈ Set.Icc (F a) (F b) :=
        ⟨le_of_lt hlt_a, le_of_lt hgt_b⟩
      obtain ⟨c, hc_mem, hc0⟩ := intermediate_value_Icc hab hcont hzero
      exact hne c hc_mem hc0
  · rcases lt_or_gt_of_ne hb with hlt_b | hgt_b
    · exfalso
      have hzero : (0 : ℝ) ∈ Set.Icc (F b) (F a) :=
        ⟨le_of_lt hlt_b, le_of_lt hgt_a⟩
      obtain ⟨c, hc_mem, hc0⟩ := intermediate_value_Icc' hab hcont hzero
      exact hne c hc_mem hc0
    · exact mul_pos hgt_a hgt_b

/-- **Endpoint noncrossing / constant sign for a continuous polynomial family.**

Let `p : ℝ → ℝ[X]` be a family of real polynomials whose evaluation at a fixed
point `a` varies continuously in the parameter `t` on `[t₀, t₁]`, and suppose
`a` is never a root of `p t` for `t` in this interval. Then the evaluation keeps
its sign along the interval: the product of the two endpoint values is strictly
positive. -/
theorem eval_endpoint_pos_of_forall_ne_zero
    {p : ℝ → ℝ[X]} {a t₀ t₁ : ℝ}
    (hle : t₀ ≤ t₁)
    (hcont : ContinuousOn (fun t => (p t).eval a) (Set.Icc t₀ t₁))
    (hne : ∀ t ∈ Set.Icc t₀ t₁, (p t).eval a ≠ 0) :
    0 < (p t₀).eval a * (p t₁).eval a := by
  exact mul_pos_of_forall_ne_zero_Icc hle hcont hne

/-- A polynomial with no roots on a closed real interval has endpoint
evaluations with the same nonzero sign. -/
theorem eval_mul_pos_of_forall_not_isRoot_Icc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hno : ∀ x ∈ Set.Icc a b, ¬ p.IsRoot x) :
    0 < p.eval a * p.eval b := by
  refine mul_pos_of_forall_ne_zero_Icc hab p.continuous.continuousOn ?_
  intro x hx
  exact (Polynomial.not_isRoot_iff_eval_ne_zero p x).mp (hno x hx)

/-- If `g` is root-free on a compact interval, then the parameters for which
`f + C μ * g` has a root in the interval are bounded in absolute value. -/
theorem exists_forall_isRoot_add_right_abs_le_of_right_not_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hg_no : ∀ z ∈ Set.Icc a b, ¬ g.IsRoot z) :
    ∃ K : ℝ, 0 < K ∧
      ∀ μ : ℝ, ∀ z ∈ Set.Icc a b, (f + C μ * g).IsRoot z → |μ| ≤ K := by
  let ρ : ℝ → ℝ := fun z => - f.eval z / g.eval z
  have hg_eval_ne : ∀ z ∈ Set.Icc a b, g.eval z ≠ 0 := by
    intro z hz
    exact (Polynomial.not_isRoot_iff_eval_ne_zero g z).mp (hg_no z hz)
  have hρ_cont : ContinuousOn ρ (Set.Icc a b) := by
    have hf_cont : ContinuousOn (fun z : ℝ => - f.eval z) (Set.Icc a b) :=
      f.continuous.neg.continuousOn
    have hg_cont : ContinuousOn (fun z : ℝ => g.eval z) (Set.Icc a b) :=
      g.continuous.continuousOn
    exact hf_cont.div₀ hg_cont hg_eval_ne
  obtain ⟨c, _hc, hcmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hρ_cont.abs
  refine ⟨|ρ c| + 1, by positivity, ?_⟩
  intro μ z hz hroot
  have hμ_eq : μ = ρ z := by
    have hzero : f.eval z + μ * g.eval z = 0 := by
      simpa [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        using hroot
    have hgz : g.eval z ≠ 0 := hg_eval_ne z hz
    have hmul : μ * g.eval z = - f.eval z := by linarith
    calc
      μ = (μ * g.eval z) / g.eval z := by field_simp [hgz]
      _ = - f.eval z / g.eval z := by rw [hmul]
  calc
    |μ| = |ρ z| := by rw [hμ_eq]
    _ ≤ |ρ c| := hcmax hz
    _ ≤ |ρ c| + 1 := by linarith

/-- If the right polynomial is root-free on a compact interval, then there is a
large parameter which dominates all right-family crossings in the interval and
whose reciprocal family is root-free there. -/
theorem exists_large_add_left_inv_not_isRoot_Icc_of_right_not_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hg_no : ∀ z ∈ Set.Icc a b, ¬ g.IsRoot z) :
    ∃ ν : ℝ, 0 < ν ∧
      (∀ μ : ℝ, ∀ z ∈ Set.Icc a b, (f + C μ * g).IsRoot z → |μ| < ν) ∧
      ∀ z ∈ Set.Icc a b, ¬ (g + C ν⁻¹ * f).IsRoot z := by
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    exists_forall_isRoot_add_right_abs_le_of_right_not_isRoot_Icc hab hg_no
  refine ⟨K + 1, by positivity, ?_, ?_⟩
  · intro μ z hz hμ_root
    have hμ_abs_le : |μ| ≤ K := hK_bound μ z hz hμ_root
    linarith
  · intro z hz hroot
    have hK1_pos : 0 < K + 1 := by positivity
    have hscaled : (f + C (K + 1) * g).IsRoot z :=
      (add_right_isRoot_iff_add_left_inv (f := f) (g := g)
        (μ := K + 1) (x := z) (ne_of_gt hK1_pos)).mpr hroot
    have hK1_abs_lt : |K + 1| < K + 1 := by
      have hK1_abs_le : |K + 1| ≤ K := hK_bound (K + 1) z hz hscaled
      linarith
    rw [abs_of_pos hK1_pos] at hK1_abs_lt
    linarith

/-- If `f` is root-free on a compact interval, then any parameter for which
`f + C μ * g` has a root in the interval is bounded away from zero. -/
theorem exists_forall_isRoot_add_right_le_abs_of_left_not_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf_no : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z) :
    ∃ m : ℝ, 0 < m ∧
      ∀ μ : ℝ, ∀ z ∈ Set.Icc a b, (f + C μ * g).IsRoot z → m ≤ |μ| := by
  have hF_cont : ContinuousOn (fun z : ℝ => |f.eval z|) (Set.Icc a b) :=
    f.continuous.continuousOn.abs
  obtain ⟨c, hc, hcmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hF_cont
  have hc_pos : 0 < |f.eval c| := by
    have hne : f.eval c ≠ 0 :=
      (Polynomial.not_isRoot_iff_eval_ne_zero f c).mp (hf_no c hc)
    exact abs_pos.mpr hne
  have hG_cont : ContinuousOn (fun z : ℝ => |g.eval z|) (Set.Icc a b) :=
    g.continuous.continuousOn.abs
  obtain ⟨d, _hd, hdmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hG_cont
  refine ⟨|f.eval c| / (|g.eval d| + 1), by positivity, ?_⟩
  intro μ z hz hroot
  have hzero : f.eval z + μ * g.eval z = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      using hroot
  have hf_eq : f.eval z = - (μ * g.eval z) := by linarith
  have h_abs_eq : |f.eval z| = |μ| * |g.eval z| := by
    rw [hf_eq]
    simp [abs_mul]
  have hmin_le : |f.eval c| ≤ |μ| * |g.eval z| := by
    simpa [h_abs_eq] using hcmin hz
  have hgz_le : |g.eval z| ≤ |g.eval d| + 1 := by
    have hmax : |g.eval z| ≤ |g.eval d| := hdmax hz
    linarith
  have hden_pos : 0 < |g.eval d| + 1 := by positivity
  rw [div_le_iff₀ hden_pos]
  exact le_trans hmin_le (mul_le_mul_of_nonneg_left hgz_le (abs_nonneg μ))

/-- If the left polynomial is root-free on a compact interval, then there is a
small positive parameter whose right-family member is root-free on the interval,
and which is strictly below the absolute value of every crossing parameter in
the interval. -/
theorem exists_small_add_right_not_isRoot_Icc_of_left_not_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf_no : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z) :
    ∃ ν : ℝ, 0 < ν ∧
      (∀ μ : ℝ, ∀ z ∈ Set.Icc a b, (f + C μ * g).IsRoot z → ν < |μ|) ∧
      ∀ z ∈ Set.Icc a b, ¬ (f + C ν * g).IsRoot z := by
  obtain ⟨m, hm_pos, hm_bound⟩ :=
    exists_forall_isRoot_add_right_le_abs_of_left_not_isRoot_Icc hab hf_no
  refine ⟨m / 2, by positivity, ?_, ?_⟩
  · intro μ z hz hroot
    have hm_le : m ≤ |μ| := hm_bound μ z hz hroot
    linarith
  · intro z hz hroot
    have hm_le : m ≤ |m / 2| := hm_bound (m / 2) z hz hroot
    rw [abs_of_pos (by positivity : 0 < m / 2)] at hm_le
    linarith

/-- If `f` is root-free on a compact interval, then every sufficiently small
right-family perturbation `f + C μ * g` is root-free on that interval. -/
theorem exists_forall_abs_lt_not_isRoot_add_right_of_left_not_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf_no : ∀ z ∈ Set.Icc a b, ¬ f.IsRoot z) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ μ : ℝ, |μ| < ε → ∀ z ∈ Set.Icc a b, ¬ (f + C μ * g).IsRoot z := by
  obtain ⟨m, hm_pos, hm_bound⟩ :=
    exists_forall_isRoot_add_right_le_abs_of_left_not_isRoot_Icc hab hf_no
  refine ⟨m, hm_pos, ?_⟩
  intro μ hμ z hz hroot
  exact (not_le_of_gt hμ) (hm_bound μ z hz hroot)

/-- Specialization of `eval_endpoint_pos_of_forall_ne_zero` to the affine
left-family `C t * f + g` used throughout the Chudnovsky--Seymour route. -/
theorem eval_endpoint_pos_left_family
    {f g : ℝ[X]} {a t₀ t₁ : ℝ}
    (hle : t₀ ≤ t₁)
    (hne : ∀ t ∈ Set.Icc t₀ t₁, ¬ (C t * f + g).IsRoot a) :
    0 < (C t₀ * f + g).eval a * (C t₁ * f + g).eval a := by
  have hcont : ContinuousOn (fun t => (C t * f + g).eval a) (Set.Icc t₀ t₁) := by
    have hrw : (fun t : ℝ => (C t * f + g).eval a)
        = fun t : ℝ => t * f.eval a + g.eval a := by
      funext t
      simp
    rw [hrw]
    fun_prop
  exact eval_endpoint_pos_of_forall_ne_zero (p := fun t => C t * f + g) hle hcont
    (fun t ht => hne t ht)

/-- Fixed-threshold no-crossing constancy of the lower root count. -/
theorem card_roots_filter_le_eq_of_no_isRoot_Ioc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card := by
  refine congr_arg Multiset.card (Multiset.filter_congr fun x hx => ?_)
  exact ⟨fun hx' => le_trans hx' hab,
    fun hx' => le_of_not_gt fun hx'' => h x hx'' hx' (Polynomial.isRoot_of_mem_roots hx)⟩

/-- Fixed-threshold no-crossing constancy of the upper root count. -/
theorem card_roots_filter_gt_eq_of_no_isRoot_Ioc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card := by
  refine congr_arg Multiset.card (Multiset.filter_congr fun x hx => ?_)
  exact ⟨fun hx' => not_le.1 fun hx'' => h x hx' hx'' (Polynomial.isRoot_of_mem_roots hx),
    fun hx' => lt_of_le_of_lt hab hx'⟩

/-- Additive threshold decomposition of the lower root count. -/
theorem card_roots_filter_le_add_card_Ioc_eq
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (· ≤ a)).card
        + (p.roots.filter (fun x => a < x ∧ x ≤ b)).card
      = (p.roots.filter (· ≤ b)).card := by
  convert congr_arg Multiset.card
    (Multiset.filter_add_not (fun x => x ≤ a) (p.roots.filter fun x => x ≤ b))
    using 1
  norm_num [Multiset.filter_filter]
  exact congr_arg _ (Multiset.filter_congr fun x _ => by
    exact ⟨fun hx' => ⟨hx', le_trans hx' hab⟩, fun hx' => hx'.1⟩)

/-- Lower threshold root-count monotonicity. -/
theorem card_roots_filter_le_mono_of_le
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card :=
  Nat.le.intro (card_roots_filter_le_add_card_Ioc_eq (p := p) hab)

/-- Upper threshold root-count antitonicity. -/
theorem card_roots_filter_gt_antitone_of_le
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card :=
  Multiset.card_le_card
    (Multiset.monotone_filter_right p.roots fun _ hx => lt_of_le_of_lt hab hx)

/-- Bundled lower-count monotonicity and upper-count antitonicity. -/
theorem card_roots_filter_le_and_gt_mono_of_le
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card :=
  ⟨card_roots_filter_le_mono_of_le hab, card_roots_filter_gt_antitone_of_le hab⟩

/-- Strict lower-count monotonicity and upper-count antitonicity. -/
theorem card_roots_filter_le_and_gt_mono_of_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b) :
    (p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card :=
  card_roots_filter_le_and_gt_mono_of_le (le_of_lt hab)

/-- Strict lower threshold root-count monotonicity. -/
theorem card_roots_filter_le_mono_of_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b) :
    (p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card :=
  card_roots_filter_le_mono_of_le (le_of_lt hab)

/-- Strict upper threshold root-count antitonicity. -/
theorem card_roots_filter_gt_antitone_of_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b) :
    (p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card :=
  card_roots_filter_gt_antitone_of_le (le_of_lt hab)

/-- If `p` has no root in `(a, b]`, that half-open window has root count zero. -/
theorem card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
  have hdec := card_roots_filter_le_add_card_Ioc_eq (p := p) hab
  have hcross := card_roots_filter_le_eq_of_no_isRoot_Ioc (p := p) hab h
  rw [hcross] at hdec
  exact Nat.add_left_cancel (hdec.trans (Nat.add_zero _).symm)

/-- Strict-interval wrapper for lower root-count constancy. -/
theorem card_roots_filter_le_eq_of_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card :=
  card_roots_filter_le_eq_of_no_isRoot_Ioc (le_of_lt hab) h

/-- Strict-interval wrapper for upper root-count constancy. -/
theorem card_roots_filter_gt_eq_of_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card :=
  card_roots_filter_gt_eq_of_no_isRoot_Ioc (le_of_lt hab) h

/-- Strict-interval wrapper for zero root count in `(a, b]`. -/
theorem card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 :=
  card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc (le_of_lt hab) h

/-- If the only root of `p` in `(a, b]` is a simple root `c`, then that
window has root count one.  The hypothesis `p.roots.count c = 1` records
simple-root multiplicity in the multiset `p.roots`. -/
theorem card_roots_filter_Ioc_eq_one_of_count_eq_one_of_no_isRoot_ne
    {p : ℝ[X]} (hp : p ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hcount : p.roots.count c = 1)
    (hno : ∀ z, a < z → z ≤ b → z ≠ c → ¬ p.IsRoot z) :
    (p.roots.filter (fun z => a < z ∧ z ≤ b)).card = 1 := by
  refine Multiset.card_filter_interval_eq_one_of_count_eq_one_of_forall_mem_eq
    p.roots hac hcb hcount ?_
  intro z hz haz hzb
  by_contra hzc
  exact hno z haz hzb hzc ((Polynomial.mem_roots hp).mp hz)

/-- Bundled strict-interval lower/upper root-count constancy. -/
theorem card_roots_filter_le_and_gt_eq_of_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card :=
  ⟨card_roots_filter_le_eq_of_no_isRoot_Ioc_lt hab h,
    card_roots_filter_gt_eq_of_no_isRoot_Ioc_lt hab h⟩

/-- Bundled strict-interval lower/upper/window root-count constancy. -/
theorem card_roots_filter_all_eq_of_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card ∧
        (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 :=
  ⟨card_roots_filter_le_eq_of_no_isRoot_Ioc_lt hab h,
    card_roots_filter_gt_eq_of_no_isRoot_Ioc_lt hab h,
    card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc_lt hab h⟩

/-- Lower root-count projection from the bundled strict-interval constancy
theorem. -/
theorem card_roots_filter_le_eq_of_all_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card :=
  (card_roots_filter_all_eq_of_no_isRoot_Ioc_lt hab h).1

/-- Upper root-count projection from the bundled strict-interval constancy
theorem. -/
theorem card_roots_filter_gt_eq_of_all_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card :=
  (card_roots_filter_all_eq_of_no_isRoot_Ioc_lt hab h).2.1

/-- Window-count projection from the bundled strict-interval constancy theorem. -/
theorem card_roots_filter_Ioc_eq_zero_of_all_no_isRoot_Ioc_lt
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 :=
  (card_roots_filter_all_eq_of_no_isRoot_Ioc_lt hab h).2.2

/-- Non-strict bundled lower/upper root-count constancy across a root-free
window. -/
theorem card_roots_filter_le_and_gt_eq_of_no_isRoot_Ioc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card :=
  ⟨card_roots_filter_le_eq_of_no_isRoot_Ioc hab h,
    card_roots_filter_gt_eq_of_no_isRoot_Ioc hab h⟩

/-- Non-strict bundled lower/upper/window root-count constancy. -/
theorem card_roots_filter_all_eq_of_no_isRoot_Ioc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card ∧
        (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 :=
  ⟨card_roots_filter_le_eq_of_no_isRoot_Ioc hab h,
    card_roots_filter_gt_eq_of_no_isRoot_Ioc hab h,
    card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc hab h⟩

/-- The half-open window count is the difference of lower-threshold counts. -/
theorem card_roots_filter_Ioc_eq_sub
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card
      = (p.roots.filter (· ≤ b)).card - (p.roots.filter (· ≤ a)).card :=
  Nat.eq_sub_of_add_eq
    ((Nat.add_comm _ _).trans (card_roots_filter_le_add_card_Ioc_eq (p := p) hab))

/-- Transitive bundled strict-interval root-count constancy across two
adjacent root-free windows. -/
theorem card_roots_filter_le_and_gt_eq_of_no_isRoot_Ioc_lt_trans
    {p : ℝ[X]} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hab_no : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x)
    (hbc_no : ∀ x, b < x → x ≤ c → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ c)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (c < ·)).card := by
  constructor
  · exact
      (card_roots_filter_le_eq_of_all_no_isRoot_Ioc_lt hab hab_no).trans
        (card_roots_filter_le_eq_of_all_no_isRoot_Ioc_lt hbc hbc_no)
  · exact
      (card_roots_filter_gt_eq_of_all_no_isRoot_Ioc_lt hab hab_no).trans
        (card_roots_filter_gt_eq_of_all_no_isRoot_Ioc_lt hbc hbc_no)

/-- Transitive bundled strict-interval lower/upper/window root-count constancy
across two adjacent root-free windows. -/
theorem card_roots_filter_all_eq_of_no_isRoot_Ioc_lt_trans
    {p : ℝ[X]} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hab_no : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x)
    (hbc_no : ∀ x, b < x → x ≤ c → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ c)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (c < ·)).card ∧
        (p.roots.filter (fun x => a < x ∧ x ≤ c)).card = 0 := by
  refine card_roots_filter_all_eq_of_no_isRoot_Ioc_lt (hab.trans hbc) ?_
  intro x hax hxc
  rcases le_or_gt x b with hxb | hbx
  · exact hab_no x hax hxb
  · exact hbc_no x hbx hxc

/-- Lower root-count projection from the transitive bundled theorem. -/
theorem card_roots_filter_le_eq_of_no_isRoot_Ioc_lt_trans
    {p : ℝ[X]} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hab_no : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x)
    (hbc_no : ∀ x, b < x → x ≤ c → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ c)).card :=
  (card_roots_filter_le_and_gt_eq_of_no_isRoot_Ioc_lt_trans
    hab hbc hab_no hbc_no).1

/-- Upper root-count projection from the transitive bundled theorem. -/
theorem card_roots_filter_gt_eq_of_no_isRoot_Ioc_lt_trans
    {p : ℝ[X]} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hab_no : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x)
    (hbc_no : ∀ x, b < x → x ≤ c → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (c < ·)).card :=
  (card_roots_filter_le_and_gt_eq_of_no_isRoot_Ioc_lt_trans
    hab hbc hab_no hbc_no).2

/-- Window-count projection from the transitive bundled theorem. -/
theorem card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc_lt_trans
    {p : ℝ[X]} {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (hab_no : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x)
    (hbc_no : ∀ x, b < x → x ≤ c → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ c)).card = 0 :=
  (card_roots_filter_all_eq_of_no_isRoot_Ioc_lt_trans
    hab hbc hab_no hbc_no).2.2

/-!
### Closed-segment and two-polynomial count-stability wrappers

The following wrappers repackage the root-free-window constancy lemmas above in
the shapes consumed downstream in `CommonInterleaverTwo`: closed-segment
(`Icc`) hypotheses, and pairwise integer differences of lower/upper threshold
counts for two polynomials `f` and `g`.  They introduce no new arithmetic; each
is a direct repackaging of the single-polynomial `Ioc` results.
-/

/-- Closed-segment (`Icc`) form of lower root-count constancy: if `p` has no
root anywhere in `[a, b]`, the lower-threshold count is unchanged. -/
theorem card_roots_filter_le_eq_of_no_isRoot_Icc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card :=
  card_roots_filter_le_eq_of_no_isRoot_Ioc hab
    (fun x hax hxb => h x (le_of_lt hax) hxb)

/-- Closed-segment (`Icc`) form of upper root-count constancy. -/
theorem card_roots_filter_gt_eq_of_no_isRoot_Icc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card :=
  card_roots_filter_gt_eq_of_no_isRoot_Ioc hab
    (fun x hax hxb => h x (le_of_lt hax) hxb)

/-- Closed-segment (`Icc`) form of the zero window-count statement. -/
theorem card_roots_filter_Ioc_eq_zero_of_no_isRoot_Icc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 :=
  card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc hab
    (fun x hax hxb => h x (le_of_lt hax) hxb)

/-- Bundled closed-segment (`Icc`) lower/upper/window root-count constancy. -/
theorem card_roots_filter_all_eq_of_no_isRoot_Icc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card ∧
        (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 :=
  ⟨card_roots_filter_le_eq_of_no_isRoot_Icc hab h,
    card_roots_filter_gt_eq_of_no_isRoot_Icc hab h,
    card_roots_filter_Ioc_eq_zero_of_no_isRoot_Icc hab h⟩

/-- **Pairwise lower-threshold difference stability.**  If neither `f` nor `g`
has a root in `(a, b]`, the integer difference of their lower-threshold counts
is the same at `a` and at `b`.  This is the form used to slide a threshold in
the interleaving bounds without reworking the filters. -/
theorem card_roots_filter_le_sub_eq_of_no_isRoot_Ioc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card
      = ((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card := by
  rw [card_roots_filter_le_eq_of_no_isRoot_Ioc hab hf,
    card_roots_filter_le_eq_of_no_isRoot_Ioc hab hg]

/-- **Pairwise upper-threshold difference stability.**  Companion of
`card_roots_filter_le_sub_eq_of_no_isRoot_Ioc` for the `x < ·` filters. -/
theorem card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card
      = ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card := by
  rw [card_roots_filter_gt_eq_of_no_isRoot_Ioc hab hf,
    card_roots_filter_gt_eq_of_no_isRoot_Ioc hab hg]

/-- **Lower-threshold interleaving-bound transport.**  Across a root-free window
`(a, b]` for both `f` and `g`, the paired `≤ 1` count bounds at `a` transfer to
`b`.  This lets `CommonInterleaverTwo` move a threshold across a no-root gap
without re-deriving the bounds. -/
theorem card_roots_filter_le_bound_of_no_isRoot_Ioc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (h : ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ a)).card : ℤ) - (f.roots.filter (· ≤ a)).card ≤ 1) :
    ((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) - (f.roots.filter (· ≤ b)).card ≤ 1 := by
  rw [← card_roots_filter_le_eq_of_no_isRoot_Ioc hab hf,
    ← card_roots_filter_le_eq_of_no_isRoot_Ioc hab hg]
  exact h

/-- **Upper-threshold interleaving-bound transport.**  Companion of
`card_roots_filter_le_bound_of_no_isRoot_Ioc` for the `x < ·` filters. -/
theorem card_roots_filter_gt_bound_of_no_isRoot_Ioc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (h : ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card ≤ 1 ∧
      ((g.roots.filter (a < ·)).card : ℤ) - (f.roots.filter (a < ·)).card ≤ 1) :
    ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card ≤ 1 ∧
      ((g.roots.filter (b < ·)).card : ℤ) - (f.roots.filter (b < ·)).card ≤ 1 := by
  rw [← card_roots_filter_gt_eq_of_no_isRoot_Ioc hab hf,
    ← card_roots_filter_gt_eq_of_no_isRoot_Ioc hab hg]
  exact h

/-- Transitive pairwise lower-threshold difference stability across two adjacent
root-free windows. -/
theorem card_roots_filter_le_sub_eq_of_no_isRoot_Ioc_trans
    {f g : ℝ[X]} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, a < x → x ≤ c → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ c → ¬ g.IsRoot x) :
    ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card
      = ((f.roots.filter (· ≤ c)).card : ℤ) - (g.roots.filter (· ≤ c)).card :=
  card_roots_filter_le_sub_eq_of_no_isRoot_Ioc (hab.trans hbc) hf hg

/-- Transitive pairwise upper-threshold difference stability across two adjacent
root-free windows. -/
theorem card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc_trans
    {f g : ℝ[X]} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, a < x → x ≤ c → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ c → ¬ g.IsRoot x) :
    ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card
      = ((f.roots.filter (c < ·)).card : ℤ) - (g.roots.filter (c < ·)).card :=
  card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc (hab.trans hbc) hf hg

/-!
### Closed-segment and bundled count-stability wrappers

These wrappers expose closed-segment (`Icc`) forms of the two-polynomial
count-stability API, plus bundled and transitive bound transport in the shapes
used downstream in `CommonInterleaverTwo`.
-/

/-- Closed-segment form of pairwise lower-threshold difference stability. -/
theorem card_roots_filter_le_sub_eq_of_no_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card
      = ((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card :=
  card_roots_filter_le_sub_eq_of_no_isRoot_Ioc hab
    (fun x hax hxb => hf x (le_of_lt hax) hxb)
    (fun x hax hxb => hg x (le_of_lt hax) hxb)

/-- Closed-segment form of pairwise upper-threshold difference stability. -/
theorem card_roots_filter_gt_sub_eq_of_no_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card
      = ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card :=
  card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc hab
    (fun x hax hxb => hf x (le_of_lt hax) hxb)
    (fun x hax hxb => hg x (le_of_lt hax) hxb)

/-- Closed-segment lower-threshold interleaving-bound transport. -/
theorem card_roots_filter_le_bound_of_no_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x)
    (h : ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ a)).card : ℤ) - (f.roots.filter (· ≤ a)).card ≤ 1) :
    ((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) - (f.roots.filter (· ≤ b)).card ≤ 1 :=
  card_roots_filter_le_bound_of_no_isRoot_Ioc hab
    (fun x hax hxb => hf x (le_of_lt hax) hxb)
    (fun x hax hxb => hg x (le_of_lt hax) hxb) h

/-- Closed-segment upper-threshold interleaving-bound transport. -/
theorem card_roots_filter_gt_bound_of_no_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x)
    (h : ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card ≤ 1 ∧
      ((g.roots.filter (a < ·)).card : ℤ) - (f.roots.filter (a < ·)).card ≤ 1) :
    ((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card ≤ 1 ∧
      ((g.roots.filter (b < ·)).card : ℤ) - (f.roots.filter (b < ·)).card ≤ 1 :=
  card_roots_filter_gt_bound_of_no_isRoot_Ioc hab
    (fun x hax hxb => hf x (le_of_lt hax) hxb)
    (fun x hax hxb => hg x (le_of_lt hax) hxb) h

/-- Bundled lower+upper bound transport across a root-free `(a, b]` window. -/
theorem card_roots_filter_le_and_gt_bound_of_no_isRoot_Ioc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (hle : ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ a)).card : ℤ) - (f.roots.filter (· ≤ a)).card ≤ 1)
    (hgt : ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card ≤ 1 ∧
      ((g.roots.filter (a < ·)).card : ℤ) - (f.roots.filter (a < ·)).card ≤ 1) :
    (((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) - (f.roots.filter (· ≤ b)).card ≤ 1) ∧
      (((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card ≤ 1 ∧
        ((g.roots.filter (b < ·)).card : ℤ) - (f.roots.filter (b < ·)).card ≤ 1) :=
  ⟨card_roots_filter_le_bound_of_no_isRoot_Ioc hab hf hg hle,
    card_roots_filter_gt_bound_of_no_isRoot_Ioc hab hf hg hgt⟩

/-- Bundled lower+upper bound transport across a root-free `[a, b]` segment. -/
theorem card_roots_filter_le_and_gt_bound_of_no_isRoot_Icc
    {f g : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x)
    (hle : ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ a)).card : ℤ) - (f.roots.filter (· ≤ a)).card ≤ 1)
    (hgt : ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card ≤ 1 ∧
      ((g.roots.filter (a < ·)).card : ℤ) - (f.roots.filter (a < ·)).card ≤ 1) :
    (((f.roots.filter (· ≤ b)).card : ℤ) - (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) - (f.roots.filter (· ≤ b)).card ≤ 1) ∧
      (((f.roots.filter (b < ·)).card : ℤ) - (g.roots.filter (b < ·)).card ≤ 1 ∧
        ((g.roots.filter (b < ·)).card : ℤ) - (f.roots.filter (b < ·)).card ≤ 1) :=
  ⟨card_roots_filter_le_bound_of_no_isRoot_Icc hab hf hg hle,
    card_roots_filter_gt_bound_of_no_isRoot_Icc hab hf hg hgt⟩

/-- Transitive lower-threshold bound transport across adjacent root-free windows. -/
theorem card_roots_filter_le_bound_of_no_isRoot_Ioc_trans
    {f g : ℝ[X]} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, a < x → x ≤ c → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ c → ¬ g.IsRoot x)
    (h : ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ a)).card : ℤ) - (f.roots.filter (· ≤ a)).card ≤ 1) :
    ((f.roots.filter (· ≤ c)).card : ℤ) - (g.roots.filter (· ≤ c)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ c)).card : ℤ) - (f.roots.filter (· ≤ c)).card ≤ 1 :=
  card_roots_filter_le_bound_of_no_isRoot_Ioc (hab.trans hbc) hf hg h

/-- Transitive upper-threshold bound transport across adjacent root-free windows. -/
theorem card_roots_filter_gt_bound_of_no_isRoot_Ioc_trans
    {f g : ℝ[X]} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, a < x → x ≤ c → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ c → ¬ g.IsRoot x)
    (h : ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card ≤ 1 ∧
      ((g.roots.filter (a < ·)).card : ℤ) - (f.roots.filter (a < ·)).card ≤ 1) :
    ((f.roots.filter (c < ·)).card : ℤ) - (g.roots.filter (c < ·)).card ≤ 1 ∧
      ((g.roots.filter (c < ·)).card : ℤ) - (f.roots.filter (c < ·)).card ≤ 1 :=
  card_roots_filter_gt_bound_of_no_isRoot_Ioc (hab.trans hbc) hf hg h

/-- Transitive closed-segment pairwise lower-threshold difference stability. -/
theorem card_roots_filter_le_sub_eq_of_no_isRoot_Icc_trans
    {f g : ℝ[X]} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, a ≤ x → x ≤ c → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ c → ¬ g.IsRoot x) :
    ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card
      = ((f.roots.filter (· ≤ c)).card : ℤ) - (g.roots.filter (· ≤ c)).card :=
  card_roots_filter_le_sub_eq_of_no_isRoot_Icc (hab.trans hbc) hf hg

/-- Transitive closed-segment pairwise upper-threshold difference stability. -/
theorem card_roots_filter_gt_sub_eq_of_no_isRoot_Icc_trans
    {f g : ℝ[X]} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∀ x, a ≤ x → x ≤ c → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ c → ¬ g.IsRoot x) :
    ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card
      = ((f.roots.filter (c < ·)).card : ℤ) - (g.roots.filter (c < ·)).card :=
  card_roots_filter_gt_sub_eq_of_no_isRoot_Icc (hab.trans hbc) hf hg

/-!
### Open-interval sample invariance

These wrappers let a proof choose any convenient sample point in a finite open
interval whose interior contains no roots of either polynomial.
-/

/-- The signed strict-upper root-count difference is independent of the sample
point chosen inside a root-free finite open interval. -/
theorem card_roots_filter_gt_sub_eq_of_no_isRoot_Ioo
    {f g : ℝ[X]} {a b x y : ℝ}
    (hf : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card =
      ((f.roots.filter (y < ·)).card : ℤ) - (g.roots.filter (y < ·)).card := by
  by_cases hxy : x ≤ y
  · exact
      card_roots_filter_gt_sub_eq_of_no_isRoot_Icc hxy
        (fun z hxz hzy => hf z (lt_of_lt_of_le hax hxz) (lt_of_le_of_lt hzy hyb))
        (fun z hxz hzy => hg z (lt_of_lt_of_le hax hxz) (lt_of_le_of_lt hzy hyb))
  · have hyx : y ≤ x := le_of_not_ge hxy
    exact
      (card_roots_filter_gt_sub_eq_of_no_isRoot_Icc hyx
        (fun z hyz hzx => hf z (lt_of_lt_of_le hay hyz) (lt_of_le_of_lt hzx hxb))
        (fun z hyz hzx => hg z (lt_of_lt_of_le hay hyz) (lt_of_le_of_lt hzx hxb))).symm

/-- Oddness of the signed strict-upper root-count difference is independent of
the sample point chosen inside a root-free finite open interval. -/
theorem odd_card_roots_filter_gt_sub_iff_of_no_isRoot_Ioo
    {f g : ℝ[X]} {a b x y : ℝ}
    (hf : ∀ z : ℝ, a < z → z < b → ¬ f.IsRoot z)
    (hg : ∀ z : ℝ, a < z → z < b → ¬ g.IsRoot z)
    (hax : a < x) (hxb : x < b) (hay : a < y) (hyb : y < b) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      Odd (((f.roots.filter (y < ·)).card : ℤ) -
        (g.roots.filter (y < ·)).card)) := by
  rw [card_roots_filter_gt_sub_eq_of_no_isRoot_Ioo hf hg hax hxb hay hyb]

end RealRooted
