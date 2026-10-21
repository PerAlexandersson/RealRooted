import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Mathlib.Algebra.Polynomial.Eval.Defs
import RealRooted.RootCountFinite
import Mathlib.Analysis.Complex.Polynomial.Basic
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
private theorem add_right_eq_C_mul_add_left_inv
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

/-- Finite coefficient sup bound over the `natDegree` range. -/
def coeffSumRange (p : ℝ[X]) : ℝ :=
  Finset.sum (Finset.range (p.natDegree + 1)) fun j => ‖p.coeff j‖

private lemma coeffSumRange_nonneg (p : ℝ[X]) : 0 ≤ coeffSumRange p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma coeff_norm_le_coeffSumRange (p : ℝ[X]) (i : ℕ) :
    ‖p.coeff i‖ ≤ coeffSumRange p := by
  by_cases hi : i ∈ Finset.range (p.natDegree + 1)
  · unfold coeffSumRange
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) hi
  · have hlt : p.natDegree < i := by simp_all
    rw [coeff_eq_zero_of_natDegree_lt hlt, norm_zero]
    exact coeffSumRange_nonneg p

/-- Coefficient difference for the affine perturbation `f + μ g`. -/
private lemma norm_coeff_sub_add_C_mul (f g : ℝ[X]) (μ : ℝ) (i : ℕ) :
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
  simpa [norm_mul, Real.norm_of_nonneg hμ] using mul_le_mul_of_nonneg_left (hM i) hμ

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
  simpa using
    Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := f) (g := g) (L := ℂ) hε hz hf_monic hg_monic hdeg hcoeff
      (hg_rr_splits.map (algebraMap ℝ ℂ))

/-- Uniform coefficient control for normalized left-family perturbations:
`(1/(t+1)) * (t f + g)` is coefficientwise `O((t+1)⁻¹)` away from `f`. -/
private lemma norm_coeff_sub_normalized_left_family_le
    (f g : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    ∀ i : ℕ,
      ‖(C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i‖ ≤
        (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by
  intro i
  rw [show (C (t + 1)⁻¹ * (C t * f + g)).coeff i - f.coeff i =
    (t + 1)⁻¹ * (g.coeff i - f.coeff i) by simp; grind]
  calc
    ‖(t + 1)⁻¹ * (g.coeff i - f.coeff i)‖ =
        (t + 1)⁻¹ * ‖g.coeff i - f.coeff i‖ := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (t + 1)⁻¹ * (‖g.coeff i‖ + ‖f.coeff i‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (t + 1)⁻¹ * (coeffSumRange g + coeffSumRange f) := by
      gcongr
      · exact coeff_norm_le_coeffSumRange g i
      · exact coeff_norm_le_coeffSumRange f i
    _ = (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) := by ring

/-- Strict coefficient control from an explicit scalar bound. -/
private lemma norm_coeff_sub_normalized_left_family_lt
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
  have hc : 0 ≤ c := add_nonneg (coeffSumRange_nonneg f) (coeffSumRange_nonneg g)
  have hε0 : ε ≠ 0 := ne_of_gt hε
  refine ⟨c / ε + 1, by positivity, ?_⟩
  have hden_pos : 0 < c / ε + 2 := by positivity
  have hbound_div : c / (c / ε + 2) < ε := by
    rw [div_lt_iff₀ hden_pos]
    have hceq : ε * (c / ε) = c := by grind
    grind
  grind

private lemma normalized_left_family_monic_natDegree
    {f g : ℝ[X]} (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree) {t : ℝ} (ht : 0 < t) :
    (C (t + 1)⁻¹ * (C t * f + g)).Monic ∧
      (C (t + 1)⁻¹ * (C t * f + g)).natDegree = f.natDegree := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have ht1_ne : t + 1 ≠ 0 := by positivity
  have hf_pos : HasPosLeadingCoeff f := hasPosLeadingCoeff_of_monic hf_monic
  have hg_pos : HasPosLeadingCoeff g := hasPosLeadingCoeff_of_monic hg_monic
  have hCt_f_pos : HasPosLeadingCoeff (C t * f) := hasPosLeadingCoeff_C_mul ht hf_pos
  have hCt_deg : (C t * f).natDegree = f.natDegree := by rw [natDegree_C_mul ht_ne]
  have hsum_deg : (C t * f + g).natDegree = f.natDegree :=
    (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
      (hCt_deg.trans hdeg.symm) hCt_f_pos hg_pos).trans hCt_deg
  have hsum_lc : (C t * f + g).leadingCoeff = t + 1 := by
    have hg_coeff : g.coeff f.natDegree = 1 := by simpa [hdeg] using hg_monic.coeff_natDegree
    unfold Polynomial.leadingCoeff
    simp_all
  constructor
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  · rw [natDegree_C_mul (inv_ne_zero ht1_ne), hsum_deg]

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
  have hε : 0 < ε := lt_of_le_of_lt
    (mul_nonneg (by positivity) (add_nonneg (coeffSumRange_nonneg f)
      (coeffSumRange_nonneg g))) hcoeff_bound
  let q : ℝ[X] := C (t + 1)⁻¹ * (C t * f + g)
  have ht1_ne : t + 1 ≠ 0 := by positivity
  obtain ⟨hq_monic, hq_deg⟩ :=
    normalized_left_family_monic_natDegree hf_monic hg_monic hdeg ht
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
  have hε : 0 < ε := lt_of_le_of_lt
    (mul_nonneg (by positivity) (add_nonneg (coeffSumRange_nonneg f)
      (coeffSumRange_nonneg g))) hcoeff_bound
  let q : ℝ[X] := C (t + 1)⁻¹ * (C t * f + g)
  have ht1_ne : t + 1 ≠ 0 := by positivity
  obtain ⟨hq_monic, hq_deg⟩ :=
    normalized_left_family_monic_natDegree hf_monic hg_monic hdeg ht
  have hq_rr : q ≠ 0 ∧ q.Splits := by simp_all [q]
  obtain ⟨w, hw_qroot, hw_dist⟩ :=
    exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
      (f := f) (g := q) (z := z) (ε := ε) hε hz hf_monic hq_monic hq_deg
      (norm_coeff_sub_normalized_left_family_lt f g ht hcoeff_bound) hq_rr.2
  have hw_sum_mem : w ∈ (C t * f + g).aroots ℂ := by
    simpa [q, Polynomial.aroots_C_mul _ (inv_ne_zero ht1_ne)] using hw_qroot
  grind

/-- A real polynomial splits if all of its complex roots have zero imaginary
part. -/
theorem splits_of_forall_aeval_im_eq_zero {p : ℝ[X]}
    (h : ∀ z : ℂ, p.aeval z = 0 → z.im = 0) :
    p.Splits := by
  apply (IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))).of_splits_algebraMap
  intro z hz
  exact ⟨z.re, Complex.ext (by simp)
    (by simpa using (h z (Polynomial.mem_rootSet.mp hz).2).symm)⟩

/-- A complex root of a nonzero split real polynomial is real. -/
theorem im_eq_zero_of_aeval_eq_zero {p : ℝ[X]} (hp : p ≠ 0) (hs : p.Splits)
    {z : ℂ} (hz : p.aeval z = 0) :
    z.im = 0 := by
  rcases hs.mem_range_of_isRoot hp (by
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hz) with ⟨r, rfl⟩
  simp

/-- If `(1 - u²) / u` is real for nonzero `u`, then `-u²` is real. -/
private theorem neg_sq_im_eq_zero_of_substitution_real {u : ℂ} (hu : u ≠ 0)
    (hreal : ((1 - u ^ 2) / u).im = 0) :
    (-(u ^ 2)).im = 0 := by
  rw [show (1 - u ^ 2) / u = u⁻¹ - u by field_simp, Complex.sub_im,
    Complex.inv_im] at hreal
  have hnorm : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have huim : u.im = 0 := by
    field_simp at hreal
    nlinarith
  rw [Complex.neg_im, pow_two, Complex.mul_im, huim]
  ring

/-- A symmetric substitution transfers splitness from `h` to `f`.

If `h` is a nonzero split real polynomial and
`f(-u²) = uⁿ h((1-u²)/u)` for every nonzero complex `u`, then `f` splits. -/
theorem splits_of_symmetric_substitution {f h : ℝ[X]} (n : ℕ)
    (hh : h ≠ 0) (hhs : h.Splits)
    (hrel : ∀ {u : ℂ}, u ≠ 0 →
      f.aeval (-(u ^ 2)) = u ^ n * h.aeval ((1 - u ^ 2) / u)) :
    f.Splits := by
  apply splits_of_forall_aeval_im_eq_zero
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  obtain ⟨u, hu2⟩ := IsAlgClosed.exists_pow_nat_eq (-z) (n := 2) (by norm_num)
  have hu : u ≠ 0 := by
    rintro rfl
    simp_all
  have hneg : -(u ^ 2) = z := by simp [hu2]
  have heval : h.aeval ((1 - u ^ 2) / u) = 0 := by
    have h := hrel hu
    rw [hneg, hz] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero n hu)
  rw [← hneg]
  exact neg_sq_im_eq_zero_of_substitution_real hu
    (im_eq_zero_of_aeval_eq_zero hh hhs heval)

/-- A monic polynomial is real-rooted if it has arbitrarily close monic,
same-degree, real-rooted approximants. -/
theorem splits_of_monic_of_coeff_approx {f : ℝ[X]} (hf : f.Monic)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℝ[X],
      g.Monic ∧ g.natDegree = f.natDegree ∧ g.Splits ∧
        ∀ i : ℕ, ‖g.coeff i - f.coeff i‖ < ε) :
    f.Splits := by
  by_cases hd0 : f.natDegree = 0
  · rw [hf.natDegree_eq_zero.mp hd0]
    exact Polynomial.Splits.one
  apply splits_of_forall_aeval_im_eq_zero
  intro z hzeval
  have hdpos : 0 < f.natDegree := Nat.pos_of_ne_zero hd0
  by_contra him
  have himpos : 0 < |z.im| := abs_pos.mpr him
  let M : ℝ := max ‖z‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let q : ℝ := |z.im| / M
  have hq : 0 < q := div_pos himpos hM
  let ε : ℝ := q ^ f.natDegree / (2 * ((f.natDegree : ℝ) + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨g, hgmonic, hgdeg, hgsplits, hgcoeff⟩ := happrox ε hε
  obtain ⟨w, hwmem, hwdist⟩ :=
    exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
      hε hzeval hf hgmonic hgdeg hgcoeff hgsplits
  have hwroot : (g.map (algebraMap ℝ ℂ)).IsRoot w := by simp_all
  have hwim : w.im = 0 := by
    rcases hgsplits.mem_range_of_isRoot hgmonic.ne_zero hwroot with ⟨r, rfl⟩
    simp
  have hrootbound :
      (((f.natDegree : ℝ) + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) < q := by
    rw [Real.rpow_inv_lt_iff_of_pos (by positivity) hq.le (by exact_mod_cast hdpos)]
    rw [Real.rpow_natCast]
    dsimp [ε]
    have hpow : 0 < q ^ f.natDegree := pow_pos hq _
    field_simp
    linarith
  have hbound :
      (((f.natDegree : ℝ) + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) *
          max ‖z‖ 1 < |z.im| := by
    change _ * M < |z.im|
    calc
      _ < q * M := mul_lt_mul_of_pos_right hrootbound hM
      _ = |z.im| := by
        dsimp [q]
        field_simp
  have hlower : |z.im| ≤ ‖z - w‖ := by
    simpa [Complex.sub_im, hwim] using Complex.abs_im_le_norm (z - w)
  exact (not_lt_of_ge hlower) (hwdist.trans hbound)

/-- A pointwise coefficient limit of monic, same-degree split polynomials is
split when the limit is monic. -/
theorem splits_of_monic_of_coeff_tendsto {f : ℝ[X]} (hf : f.Monic)
    {g : ℕ → ℝ[X]} (hg_monic : ∀ M, (g M).Monic)
    (hg_degree : ∀ M, (g M).natDegree = f.natDegree)
    (hg_splits : ∀ M, (g M).Splits)
    (hcoeff : ∀ i, Filter.Tendsto (fun M => (g M).coeff i) Filter.atTop
      (nhds (f.coeff i))) :
    f.Splits := by
  apply splits_of_monic_of_coeff_approx hf
  intro ε hε
  have hclose : ∀ᶠ M in Filter.atTop,
      ∀ i ∈ Finset.range (f.natDegree + 1), ‖(g M).coeff i - f.coeff i‖ < ε := by
    rw [Finset.eventually_all]
    intro i _
    simpa [dist_eq_norm] using Metric.tendsto_nhds.mp (hcoeff i) ε hε
  obtain ⟨M, hM⟩ := hclose.exists
  refine ⟨g M, hg_monic M, hg_degree M, hg_splits M, ?_⟩
  intro i
  by_cases hi : i ≤ f.natDegree
  · exact hM i (by simp_all)
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hg_degree M] using hlt)]
    simpa using hε

/-- A continuous real-valued function that never vanishes on a closed interval
has endpoint values with the same nonzero sign. -/
theorem mul_pos_of_forall_ne_zero_Icc
    {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn F (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, F x ≠ 0) :
    0 < F a * F b := by
  have ha := hne a ⟨le_refl _, hab⟩
  have hb := hne b ⟨hab, le_refl _⟩
  rcases lt_or_gt_of_ne ha with hlt_a | hgt_a <;>
    rcases lt_or_gt_of_ne hb with hlt_b | hgt_b
  · exact mul_pos_of_neg_of_neg hlt_a hlt_b
  · exfalso
    obtain ⟨c, hc_mem, hc0⟩ := intermediate_value_Icc hab hcont ⟨hlt_a.le, hgt_b.le⟩
    exact hne c hc_mem hc0
  · exfalso
    obtain ⟨c, hc_mem, hc0⟩ := intermediate_value_Icc' hab hcont ⟨hlt_b.le, hgt_a.le⟩
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
    0 < (p t₀).eval a * (p t₁).eval a :=
  mul_pos_of_forall_ne_zero_Icc hle hcont hne

/-- A polynomial with no roots on a closed real interval has endpoint
evaluations with the same nonzero sign. -/
theorem eval_mul_pos_of_forall_not_isRoot_Icc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hno : ∀ x ∈ Set.Icc a b, ¬ p.IsRoot x) :
    0 < p.eval a * p.eval b := by
  exact mul_pos_of_forall_ne_zero_Icc hab p.continuous.continuousOn fun x hx =>
    (Polynomial.not_isRoot_iff_eval_ne_zero p x).mp (hno x hx)

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
private theorem card_roots_filter_le_add_card_Ioc_eq
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

/-- If `p` has no root in `(a, b]`, that half-open window has root count zero. -/
theorem card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc
    {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
  have hdec := card_roots_filter_le_add_card_Ioc_eq (p := p) hab
  rw [card_roots_filter_le_eq_of_no_isRoot_Ioc (p := p) hab h] at hdec
  grind

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
  rcases le_total x y with hxy | hyx
  · exact
      card_roots_filter_gt_sub_eq_of_no_isRoot_Icc hxy
        (fun z hxz hzy => hf z (lt_of_lt_of_le hax hxz) (lt_of_le_of_lt hzy hyb))
        (fun z hxz hzy => hg z (lt_of_lt_of_le hax hxz) (lt_of_le_of_lt hzy hyb))
  · exact
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
