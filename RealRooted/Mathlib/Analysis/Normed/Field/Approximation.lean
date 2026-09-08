import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Thickening

/-!
# One-sided continuity of polynomial roots

This file adds a coefficient-neighborhood form of root continuity intended
for upstreaming to `Mathlib.Analysis.Normed.Field.Approximation`.
-/

open Polynomial
open Filter Topology

namespace Polynomial

noncomputable section

/-- A root of a positive-degree monic polynomial persists near itself in every
sufficiently close monic same-degree split polynomial. -/
theorem exists_coeff_radius_root_near
    {K : Type*} [NormedField K] {p : K[X]} {z : K}
    (hp : p.Monic) (hdegree : p.natDegree ≠ 0) (hz : p.IsRoot z)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : K[X], q.Monic →
      q.natDegree = p.natDegree →
      (∀ i : ℕ, ‖q.coeff i - p.coeff i‖ < δ) → q.Splits →
      ∃ w : K, q.IsRoot w ∧ ‖z - w‖ < η := by
  let B : ℝ := max ‖z‖ 1
  let ρ : ℝ := η / B
  let δ : ℝ := ρ ^ p.natDegree /
    (2 * ((p.natDegree + 1 : ℕ) : ℝ))
  have hdegree_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hdegree
  have hB : 0 < B :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hρ : 0 < ρ := div_pos hη hB
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro q hq hqdegree hcoeff hsplits
  obtain ⟨w, hwmem, hzw⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := p) (g := q) hδ hz hp hq hqdegree hcoeff hsplits
  have hfactor :
      (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
          ((p.natDegree : ℝ)⁻¹) < ρ := by
    rw [Real.rpow_inv_lt_iff_of_pos (by positivity) hρ.le
      (by exact_mod_cast hdegree_pos)]
    rw [Real.rpow_natCast]
    dsimp [δ]
    have hpow : 0 < ρ ^ p.natDegree := pow_pos hρ _
    field_simp
    nlinarith
  have hzw' :
      ‖z - w‖ < (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
          ((p.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
    simpa [Nat.cast_add, Nat.cast_one] using hzw
  refine ⟨w, (Polynomial.mem_roots hq.ne_zero).mp hwmem, hzw'.trans ?_⟩
  calc
    (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
          ((p.natDegree : ℝ)⁻¹) * max ‖z‖ 1 <
        ρ * B := by
      exact mul_lt_mul_of_pos_right hfactor hB
    _ = η := by
      dsimp [ρ]
      field_simp

/-- Every root of a sufficiently close monic polynomial of the same degree is
close to a root of a fixed positive-degree monic split polynomial. -/
theorem exists_coeff_radius_forall_root_near
    {K : Type*} [NormedField K] {p : K[X]}
    (hp : p.Monic) (hdegree : p.natDegree ≠ 0) (hsplits : p.Splits)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : K[X], q.Monic →
      q.natDegree = p.natDegree →
      (∀ i : ℕ, ‖q.coeff i - p.coeff i‖ < δ) →
      ∀ z : K, q.IsRoot z →
        ∃ w : K, p.IsRoot w ∧ ‖z - w‖ < η := by
  let B : ℝ := max (p.cauchyBound : ℝ) 1
  let ρ : ℝ := min (1 / 2 : ℝ) (η / (2 * B))
  let δ : ℝ := ρ ^ p.natDegree /
    (2 * ((p.natDegree + 1 : ℕ) : ℝ))
  have hdegree_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hdegree
  have hB : 0 < B := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hρ : 0 < ρ := by
    apply lt_min
    · norm_num
    · exact div_pos hη (mul_pos (by norm_num) hB)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro q hq hqdegree hcoeff z hz
  have hcoeff' : ∀ i : ℕ, ‖p.coeff i - q.coeff i‖ < δ := by
    intro i
    simpa [norm_sub_rev] using hcoeff i
  obtain ⟨w, hwmem, hzw⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := q) (g := p) hδ hz hq hp hqdegree.symm hcoeff' hsplits
  have hp0 : p ≠ 0 := hp.ne_zero
  have hw : p.IsRoot w := (Polynomial.mem_roots hp0).mp hwmem
  refine ⟨w, hw, ?_⟩
  have hfactor :
      (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
          ((p.natDegree : ℝ)⁻¹) < ρ := by
    rw [Real.rpow_inv_lt_iff_of_pos (by positivity) hρ.le
      (by exact_mod_cast hdegree_pos)]
    rw [Real.rpow_natCast]
    dsimp [δ]
    have hpow : 0 < ρ ^ p.natDegree := pow_pos hρ _
    field_simp
    nlinarith
  have hzw' :
      ‖z - w‖ < ρ * max ‖z‖ 1 := by
    have hmax : 0 < max ‖z‖ 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    calc
      ‖z - w‖ <
          (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
              ((p.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
        simpa [hqdegree] using hzw
      _ < ρ * max ‖z‖ 1 := mul_lt_mul_of_pos_right hfactor hmax
  have hwbound : ‖w‖ < B := by
    have hwbound' : ‖w‖ < (p.cauchyBound : ℝ) := by
      exact_mod_cast hw.norm_lt_cauchyBound hp0
    exact hwbound'.trans_le (le_max_left _ _)
  have hρhalf : ρ ≤ 1 / 2 := min_le_left _ _
  have hmaxbound : max ‖z‖ 1 < 2 * B := by
    rcases le_total ‖z‖ 1 with hzle | hzone
    · rw [max_eq_right hzle]
      have hBone : 1 ≤ B := le_max_right _ _
      linarith
    · rw [max_eq_left hzone] at hzw' ⊢
      have htriangle : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        calc
          ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      have hρnonneg : 0 ≤ ρ := hρ.le
      have hznonneg : 0 ≤ ‖z‖ := norm_nonneg _
      have hhalf : ρ * ‖z‖ ≤ (1 / 2 : ℝ) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hρhalf hznonneg
      nlinarith
  have hρη : ρ ≤ η / (2 * B) := min_le_right _ _
  calc
    ‖z - w‖ < ρ * max ‖z‖ 1 := hzw'
    _ < ρ * (2 * B) := mul_lt_mul_of_pos_left hmaxbound hρ
    _ ≤ (η / (2 * B)) * (2 * B) := by
      gcongr
    _ = η := by field_simp

/-- Coefficientwise continuity and a fixed degree give a single neighborhood
on which all polynomial coefficients are uniformly close. -/
theorem eventually_forall_norm_coeff_sub_lt
    {T K : Type*} [TopologicalSpace T] [NormedField K]
    (p : T → K[X]) {d : ℕ} (hdegree : ∀ t, (p t).natDegree = d)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (t : T) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u in 𝓝 t, ∀ i : ℕ, ‖(p u).coeff i - (p t).coeff i‖ < δ := by
  have hfinite : ∀ᶠ u in 𝓝 t,
      ∀ i ∈ Finset.range (d + 1),
        ‖(p u).coeff i - (p t).coeff i‖ < δ := by
    rw [Finset.eventually_all]
    intro i hi
    simpa [dist_eq_norm] using
      Metric.tendsto_nhds.mp (hcoeff i).continuousAt δ hδ
  filter_upwards [hfinite] with u hu
  intro i
  by_cases hi : i ≤ d
  · exact hu i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
  · have hdi : d < i := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hdegree u]),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hdegree t])]
    simpa using hδ

/-- If the roots of a continuous monic fixed positive-degree family stay in
the union of two disjoint open sets, the locus where every root lies in the
first set is clopen. -/
theorem isClopen_forall_isRoot_mem_of_partition
    {T K : Type*} [TopologicalSpace T] [NormedField K]
    (p : T → K[X]) {d : ℕ}
    (hmonic : ∀ t, (p t).Monic)
    (hdegree : ∀ t, (p t).natDegree = d) (hd : d ≠ 0)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (hsplits : ∀ t, (p t).Splits) {U V : Set K}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : ∀ t z, (p t).IsRoot z → z ∈ U ∪ V) :
    IsClopen {t | ∀ z, (p t).IsRoot z → z ∈ U} := by
  classical
  let L : Set T := {t | ∀ z, (p t).IsRoot z → z ∈ U}
  change IsClopen L
  have hopen : IsOpen L := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    let R : Set K := ↑(p t).roots.toFinset
    have hRcompact : IsCompact R :=
      (p t).roots.toFinset.finite_toSet.isCompact
    have hRU : R ⊆ U := by
      intro z hz
      apply ht z
      apply (Polynomial.mem_roots (hmonic t).ne_zero).mp
      simpa [R] using hz
    obtain ⟨η, hη, hthick⟩ :=
      hRcompact.exists_thickening_subset_open hU hRU
    obtain ⟨δ, hδ, hnear⟩ :=
      Polynomial.exists_coeff_radius_forall_root_near
        (hmonic t) (by simpa [hdegree t] using hd)
        (hsplits t) hη
    have hclose := Polynomial.eventually_forall_norm_coeff_sub_lt
      p hdegree hcoeff t hδ
    filter_upwards [hclose] with u hu
    intro z hz
    obtain ⟨w, hw, hzw⟩ := hnear (p u) (hmonic u)
      ((hdegree u).trans (hdegree t).symm) hu z hz
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨w, ?_, ?_⟩
    · apply Multiset.mem_toFinset.mpr
      exact (Polynomial.mem_roots (hmonic t).ne_zero).mpr hw
    · simpa [dist_eq_norm] using hzw
  refine ⟨?_, hopen⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro t ht
  change ¬(∀ z, (p t).IsRoot z → z ∈ U) at ht
  push Not at ht
  obtain ⟨z, hz, hznotU⟩ := ht
  have hzV : z ∈ V := (hcover t z hz).resolve_left hznotU
  obtain ⟨η, hη, hthick⟩ :=
    (isCompact_singleton (x := z)).exists_thickening_subset_open hV
      (Set.singleton_subset_iff.mpr hzV)
  obtain ⟨δ, hδ, hnear⟩ :=
    Polynomial.exists_coeff_radius_root_near
      (hmonic t) (by simpa [hdegree t] using hd) hz hη
  have hclose := Polynomial.eventually_forall_norm_coeff_sub_lt
    p hdegree hcoeff t hδ
  filter_upwards [hclose] with u hu
  change ¬(∀ w, (p u).IsRoot w → w ∈ U)
  obtain ⟨w, hw, hzw⟩ := hnear (p u) (hmonic u)
    ((hdegree u).trans (hdegree t).symm) hu
    (hsplits u)
  intro hallU
  have hwV : w ∈ V := by
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨z, Set.mem_singleton z, ?_⟩
    simpa [dist_eq_norm, norm_sub_rev] using hzw
  exact Set.disjoint_left.mp hUV (hallU w hw) hwV

/-- Root membership in one side of an open partition propagates along a
preconnected parameter set. -/
theorem forall_isRoot_mem_of_isPreconnected
    {T K : Type*} [TopologicalSpace T] [NormedField K]
    (p : T → K[X]) {d : ℕ}
    (hmonic : ∀ t, (p t).Monic)
    (hdegree : ∀ t, (p t).natDegree = d) (hd : d ≠ 0)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (hsplits : ∀ t, (p t).Splits) {U V : Set K}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : ∀ t z, (p t).IsRoot z → z ∈ U ∪ V)
    {s : Set T} (hs : IsPreconnected s) {a b : T}
    (ha : a ∈ s) (hb : b ∈ s)
    (hstart : ∀ z, (p a).IsRoot z → z ∈ U) :
    ∀ z, (p b).IsRoot z → z ∈ U := by
  let L : Set T := {t | ∀ z, (p t).IsRoot z → z ∈ U}
  have hclopen : IsClopen L := by
    exact Polynomial.isClopen_forall_isRoot_mem_of_partition
      p hmonic hdegree hd hcoeff hsplits hU hV hUV hcover
  have hsubset : s ⊆ L :=
    hs.subset_isClopen hclopen ⟨a, ha, hstart⟩
  exact hsubset hb

/-- In a continuous monic fixed positive-degree family of complex
polynomials whose roots avoid the real axis, the locus where every root lies
in the open lower half-plane is clopen. -/
theorem isClopen_forall_isRoot_im_neg
    {T : Type*} [TopologicalSpace T] (p : T → ℂ[X]) {d : ℕ}
    (hmonic : ∀ t, (p t).Monic)
    (hdegree : ∀ t, (p t).natDegree = d) (hd : d ≠ 0)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (havoid : ∀ t z, (p t).IsRoot z → z.im ≠ 0) :
    IsClopen {t | ∀ z, (p t).IsRoot z → z.im < 0} := by
  apply Polynomial.isClopen_forall_isRoot_mem_of_partition
    p hmonic hdegree hd hcoeff (fun t => IsAlgClosed.splits (p t))
    (isOpen_lt Complex.continuous_im continuous_const)
    (isOpen_lt continuous_const Complex.continuous_im)
  · exact Set.disjoint_left.mpr (by
      intro z hzneg hzpos
      change z.im < 0 at hzneg
      change 0 < z.im at hzpos
      exact (not_lt_of_ge hzpos.le) hzneg)
  · intro t z hz
    exact lt_or_gt_of_ne (havoid t z hz)

/-- Roots of a continuous monic fixed-degree family cannot move from the open
lower half-plane to the open upper half-plane along a preconnected parameter
set without some root crossing the real axis. -/
theorem forall_isRoot_im_neg_of_isPreconnected
    {T : Type*} [TopologicalSpace T] (p : T → ℂ[X]) {d : ℕ}
    (hmonic : ∀ t, (p t).Monic)
    (hdegree : ∀ t, (p t).natDegree = d) (hd : d ≠ 0)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (havoid : ∀ t z, (p t).IsRoot z → z.im ≠ 0)
    {s : Set T} (hs : IsPreconnected s) {a b : T}
    (ha : a ∈ s) (hb : b ∈ s)
    (hstart : ∀ z, (p a).IsRoot z → z.im < 0) :
    ∀ z, (p b).IsRoot z → z.im < 0 := by
  apply Polynomial.forall_isRoot_mem_of_isPreconnected
    p hmonic hdegree hd hcoeff (fun t => IsAlgClosed.splits (p t))
    (isOpen_lt Complex.continuous_im continuous_const)
    (isOpen_lt continuous_const Complex.continuous_im)
    (Set.disjoint_left.mpr (by
      intro z hzneg hzpos
      change z.im < 0 at hzneg
      change 0 < z.im at hzpos
      exact (not_lt_of_ge hzpos.le) hzneg))
    (fun t z hz => lt_or_gt_of_ne (havoid t z hz))
    hs ha hb hstart

end

end Polynomial
