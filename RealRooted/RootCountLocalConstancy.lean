import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import RealRooted.Mathlib.Algebra.Polynomial.Splits
import RealRooted.RootMultiplicityMatching

/-!
# Local Constancy of Root Counts

This file contains the positive-parameter local-constancy support for the
issue #42 succ-degree route.  The main point is to reduce global equality of
upper root counts on a compact positive parameter interval to a local
root-continuity statement, and to record the endpoint parity control that
comes from no root crossing the threshold.
-/

open Polynomial Set

noncomputable section

namespace RealRooted

/--
Choose one separation radius around the roots of `p` so that any same-degree
split polynomial with enough roots in each such ball has the same strict-upper
root count across a threshold `x`.

This is the polynomial bridge for the local-bound part of issue #42: after an
analytic continuity argument supplies the per-root lower counts near a fixed
positive parameter, the threshold count equality is finite bookkeeping.
-/
theorem exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts
    {p : ℝ[X]} {x : ℝ} (hx : x ∉ p.roots) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : ℝ[X], p.Splits → q.Splits →
      q.natDegree = p.natDegree →
      (∀ a ∈ p.roots.toFinset,
        p.roots.count a ≤ (q.roots.filter (fun r => |r - a| < ρ)).card) →
      (q.roots.filter (x < ·)).card = (p.roots.filter (x < ·)).card := by
  obtain ⟨η, hη_pos, hη⟩ := Multiset.exists_pos_le_abs_sub_of_not_mem p.roots hx
  obtain ⟨ρ, hρ_pos, hρη, hsep_centers⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset p.roots hη_pos
  refine ⟨ρ, hρ_pos, fun q hp_split hq_split hdeg hcount => ?_⟩
  refine Multiset.card_filter_gt_eq_of_forall_le_count_and_card_eq
    hsep_centers ?_ hcount ?_
  · intro r hr
    exact le_trans (le_of_lt hρη) (hη r hr)
  · rw [hq_split.natDegree_eq_card_roots.symm,
      hp_split.natDegree_eq_card_roots.symm, hdeg]

/--
Selected nearby root clusters imply same-degree preservation of the strict-upper
root count.

This is the local-constancy bridge for the selected-root version of the issue
#42 obstruction: once an analytic argument produces, near each root `a` of `p`,
a submultiset of roots of `q` with the right multiplicity inside the `ρ`-ball,
the finite threshold-count equality follows from the existing lower-count
bridge.
-/
theorem exists_radius_card_roots_filter_gt_eq_of_sameDegree_root_clusters
    {p : ℝ[X]} {x : ℝ} (hx : x ∉ p.roots) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : ℝ[X], p.Splits → q.Splits →
      q.natDegree = p.natDegree →
      (∀ a ∈ p.roots.toFinset, ∃ s : Multiset ℝ,
        s ≤ q.roots ∧ s.card = p.roots.count a ∧
          ∀ r ∈ s, |r - a| < ρ) →
      (q.roots.filter (x < ·)).card = (p.roots.filter (x < ·)).card := by
  obtain ⟨ρ, hρ_pos, hρ⟩ :=
    exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts hx
  refine ⟨ρ, hρ_pos, fun q hp_split hq_split hdeg hclusters => ?_⟩
  refine hρ q hp_split hq_split hdeg fun a ha => ?_
  obtain ⟨s, hs_le, hs_card, hs_near⟩ := hclusters a ha
  simpa [← hs_card] using Polynomial.card_le_card_roots_filter_of_le_roots hs_le hs_near

/-- A real function that is continuous and nowhere zero on `Set.Icc t₀ t₁`
has same-sign endpoint values. -/
theorem endpoint_same_sign_of_continuousOn_ne_zero
    {G : ℝ → ℝ} {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (hcont : ContinuousOn G (Set.Icc t₀ t₁))
    (hne : ∀ t ∈ Set.Icc t₀ t₁, G t ≠ 0) :
    0 < G t₀ * G t₁ := by
  have hmem0 : t₀ ∈ Set.Icc t₀ t₁ := ⟨le_refl _, hle⟩
  have hmem1 : t₁ ∈ Set.Icc t₀ t₁ := ⟨hle, le_refl _⟩
  have h0 : G t₀ ≠ 0 := hne t₀ hmem0
  have h1 : G t₁ ≠ 0 := hne t₁ hmem1
  rcases lt_or_gt_of_ne h0 with hlt0 | hgt0
  · rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
    · exact mul_pos_of_neg_of_neg hlt0 hlt1
    · have hzero : (0 : ℝ) ∈ Set.Icc (G t₀) (G t₁) :=
        ⟨le_of_lt hlt0, le_of_lt hgt1⟩
      obtain ⟨c, hc_mem, hc0⟩ := intermediate_value_Icc hle hcont hzero
      exact absurd hc0 (hne c hc_mem)
  · rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
    · have hzero : (0 : ℝ) ∈ Set.Icc (G t₁) (G t₀) :=
        ⟨le_of_lt hlt1, le_of_lt hgt0⟩
      obtain ⟨c, hc_mem, hc0⟩ := intermediate_value_Icc' hle hcont hzero
      exact absurd hc0 (hne c hc_mem)
    · exact mul_pos hgt0 hgt1

/-- A natural-number-valued function that is locally constant along a closed
real interval takes equal values at the endpoints. -/
theorem eq_of_locally_constant_on_Icc {N : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ ε > 0, ∀ u ∈ Set.Icc a b,
      |u - t| < ε → N u = N t) :
    N a = N b := by
  have hcont : ContinuousOn N (Set.Icc a b) := by
    intro t ht
    obtain ⟨ε, ε_pos, H⟩ := hloc t ht
    have hev : ∀ᶠ u in nhdsWithin t (Set.Icc a b), N u = N t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t ε_pos)] with u hu h'u
      exact H u hu (by rw [← Real.dist_eq]; exact h'u)
    exact tendsto_const_nhds.congr' (hev.mono fun u h => h.symm)
  exact IsPreconnected.constant isPreconnected_Icc hcont
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)

/-- If the upper root count of `f + C μ * g` is locally constant along
`Set.Icc μ₀ μ₁`, then it agrees at the endpoints. -/
theorem rightFamily_card_roots_gt_eq_of_locally_constant
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hloc : ∀ μ ∈ Set.Icc μ₀ μ₁, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁,
      |ν - μ| < ε →
        ((f + C ν * g).roots.filter (x < ·)).card =
          ((f + C μ * g).roots.filter (x < ·)).card) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card :=
  eq_of_locally_constant_on_Icc hμ₁ hloc

/-- Any right-family member with no root at `x` is nonzero. -/
theorem rightFamily_ne_zero_of_no_isRoot
    {f g : ℝ[X]} {μ x : ℝ} (hne : ¬ (f + C μ * g).IsRoot x) :
    f + C μ * g ≠ 0 := by
  intro h
  exact hne (by simp [Polynomial.IsRoot.def, h])

/-- If no member `f + C μ * g` has a root at `x` for `μ ∈ Set.Icc μ₀ μ₁`,
then the endpoint evaluations at `x` have the same nonzero sign. -/
theorem rightFamily_eval_same_sign_of_no_isRoot
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x) :
    0 < (f + C μ₀ * g).eval x * (f + C μ₁ * g).eval x := by
  apply endpoint_same_sign_of_continuousOn_ne_zero hμ₁
  · have hrw :
        (fun μ : ℝ => (f + C μ * g).eval x) =
          fun μ : ℝ => f.eval x + μ * g.eval x := by
      funext μ
      simp
    rw [hrw]
    exact (by fun_prop : Continuous _).continuousOn
  · exact fun t ht => by simpa [Polynomial.IsRoot.def] using hne t ht

/-- For a right-family member of constant `natDegree`
`n := (f + C μ₀ * g).natDegree`, the leading coefficient is affine in `μ`. -/
theorem rightFamily_leadingCoeff_eq
    {f g : ℝ[X]} {μ₀ μ : ℝ}
    (hdeg : (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree) :
    (f + C μ * g).leadingCoeff =
      f.coeff (f + C μ₀ * g).natDegree +
        μ * g.coeff (f + C μ₀ * g).natDegree := by
  rw [← hdeg, Polynomial.leadingCoeff, Polynomial.coeff_add, Polynomial.coeff_C_mul]

/-- If the right family keeps a constant `natDegree` and has no root at `x`
along `Set.Icc μ₀ μ₁`, then the endpoint leading coefficients have the same
nonzero sign. -/
theorem rightFamily_leadingCoeff_same_sign_of_no_isRoot
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x) :
    0 < (f + C μ₀ * g).leadingCoeff *
      (f + C μ₁ * g).leadingCoeff := by
  set n := (f + C μ₀ * g).natDegree
  set G : ℝ → ℝ := fun μ => f.coeff n + μ * g.coeff n
  have hG : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).leadingCoeff = G μ :=
    fun μ hμ => rightFamily_leadingCoeff_eq (hdeg μ hμ)
  have hG_cont : ContinuousOn G (Set.Icc μ₀ μ₁) := by fun_prop
  have hG_ne : ∀ μ ∈ Set.Icc μ₀ μ₁, G μ ≠ 0 := fun μ hμ =>
    hG μ hμ ▸ Polynomial.leadingCoeff_ne_zero.mpr
      (rightFamily_ne_zero_of_no_isRoot (hne μ hμ))
  have hG_pos : 0 < G μ₀ * G μ₁ :=
    endpoint_same_sign_of_continuousOn_ne_zero hμ₁ hG_cont hG_ne
  rwa [hG μ₀ ⟨le_rfl, hμ₁⟩, hG μ₁ ⟨hμ₁, le_rfl⟩]

/-- For a real-rooted right family with constant `natDegree` and no root at
`x` along `Set.Icc μ₀ μ₁`, the signed difference of the endpoint upper root
counts is even. -/
theorem rightFamily_even_intCard_roots_gt_sub_of_no_isRoot
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x) :
    Even ((((f + C μ₀ * g).roots.filter (x < ·)).card : ℤ) -
      ((f + C μ₁ * g).roots.filter (x < ·)).card) := by
  have m0 : μ₀ ∈ Set.Icc μ₀ μ₁ := ⟨le_rfl, hμ₁⟩
  have m1 : μ₁ ∈ Set.Icc μ₀ μ₁ := ⟨hμ₁, le_rfl⟩
  have H0 := Polynomial.Splits.eval_mul_leadingCoeff_neg_one_pow_pos
    (rightFamily_ne_zero_of_no_isRoot (hne μ₀ m0)) (hrr μ₀ m0) (hne μ₀ m0)
  have H1 := Polynomial.Splits.eval_mul_leadingCoeff_neg_one_pow_pos
    (rightFamily_ne_zero_of_no_isRoot (hne μ₁ m1)) (hrr μ₁ m1) (hne μ₁ m1)
  have heval := rightFamily_eval_same_sign_of_no_isRoot hμ₁ hne
  have hlc := rightFamily_leadingCoeff_same_sign_of_no_isRoot hμ₁ hdeg hne
  set N0 := ((f + C μ₀ * g).roots.filter (x < ·)).card with hN0
  set N1 := ((f + C μ₁ * g).roots.filter (x < ·)).card with hN1
  have hpos : 0 < (-1 : ℝ) ^ (N0 + N1) := by
    have hc :
        0 < ((f + C μ₀ * g).eval x * (f + C μ₁ * g).eval x) *
          ((f + C μ₀ * g).leadingCoeff * (f + C μ₁ * g).leadingCoeff) :=
      mul_pos heval hlc
    have hprod :
        0 <
          ((f + C μ₀ * g).eval x *
              (f + C μ₀ * g).leadingCoeff * (-1) ^ N0) *
            ((f + C μ₁ * g).eval x *
              (f + C μ₁ * g).leadingCoeff * (-1) ^ N1) :=
      mul_pos H0 H1
    have heq :
        ((f + C μ₀ * g).eval x *
              (f + C μ₀ * g).leadingCoeff * (-1) ^ N0) *
            ((f + C μ₁ * g).eval x *
              (f + C μ₁ * g).leadingCoeff * (-1) ^ N1)
          = (((f + C μ₀ * g).eval x * (f + C μ₁ * g).eval x) *
              ((f + C μ₀ * g).leadingCoeff *
                (f + C μ₁ * g).leadingCoeff)) *
            (-1) ^ (N0 + N1) := by
      rw [pow_add]
      ring
    rw [heq] at hprod
    exact (mul_pos_iff_of_pos_left hc).mp hprod
  have hev : Even (N0 + N1) := by
    rcases Nat.even_or_odd (N0 + N1) with he | ho
    · exact he
    · rw [ho.neg_one_pow] at hpos
      norm_num at hpos
  have hevZ : Even ((N0 : ℤ) + (N1 : ℤ)) := by
    exact_mod_cast hev
  rw [Int.even_sub]
  exact Int.even_add.mp hevZ

/-- If two natural numbers differ by at most one in both directions and their
integer difference is even, then they are equal. -/
private theorem nat_eq_of_even_int_sub_of_le_succ_of_le_succ {m n : ℕ}
    (he : Even ((m : ℤ) - n)) (hmn : m ≤ n + 1) (hnm : n ≤ m + 1) :
    m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : n = m + 1 := by lia
    have hdiff : ((m : ℤ) - n) = -1 := by
      rw [hn]
      simp
    rw [hdiff] at he
    norm_num at he
  · have hm : m = n + 1 := by lia
    have hdiff : ((m : ℤ) - n) = 1 := by
      rw [hm]
      simp
    rw [hdiff] at he
    norm_num at he

/-- If local root-continuity bounds the upper root-count jump by at most one,
then parity upgrades this to exact local constancy and hence endpoint equality.

This is the bridge from a future local root-continuity estimate to the global
positive-parameter count equality on `Set.Icc μ₀ μ₁`.
-/
theorem rightFamily_card_roots_gt_eq_of_local_count_bound
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x)
    (hlocal : ∀ μ ∈ Set.Icc μ₀ μ₁, ∃ ε > 0,
      ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
        ((f + C ν * g).roots.filter (x < ·)).card ≤
          ((f + C μ * g).roots.filter (x < ·)).card + 1 ∧
        ((f + C μ * g).roots.filter (x < ·)).card ≤
          ((f + C ν * g).roots.filter (x < ·)).card + 1) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  refine rightFamily_card_roots_gt_eq_of_locally_constant hμ₁ ?_
  intro μ hμ
  obtain ⟨ε, hε, hε_count⟩ := hlocal μ hμ
  refine ⟨ε, hε, ?_⟩
  intro ν hν hdist
  have hbounds := hε_count ν hν hdist
  by_cases hνμ : ν ≤ μ
  · have hsub : Set.Icc ν μ ⊆ Set.Icc μ₀ μ₁ := by
      intro τ hτ
      exact ⟨le_trans hν.1 hτ.1, le_trans hτ.2 hμ.2⟩
    have hdeg' : ∀ τ ∈ Set.Icc ν μ,
        (f + C τ * g).natDegree = (f + C ν * g).natDegree := by
      intro τ hτ
      rw [hdeg τ (hsub hτ), hdeg ν hν]
    have hrr' : ∀ τ ∈ Set.Icc ν μ, (f + C τ * g).Splits := by
      intro τ hτ
      exact hrr τ (hsub hτ)
    have hne' : ∀ τ ∈ Set.Icc ν μ, ¬ (f + C τ * g).IsRoot x := by
      intro τ hτ
      exact hne τ (hsub hτ)
    exact nat_eq_of_even_int_sub_of_le_succ_of_le_succ
      (rightFamily_even_intCard_roots_gt_sub_of_no_isRoot hνμ hdeg' hrr' hne')
      hbounds.1 hbounds.2
  · have hμν : μ ≤ ν := le_of_not_ge hνμ
    have hsub : Set.Icc μ ν ⊆ Set.Icc μ₀ μ₁ := by
      intro τ hτ
      exact ⟨le_trans hμ.1 hτ.1, le_trans hτ.2 hν.2⟩
    have hdeg' : ∀ τ ∈ Set.Icc μ ν,
        (f + C τ * g).natDegree = (f + C μ * g).natDegree := by
      intro τ hτ
      rw [hdeg τ (hsub hτ), hdeg μ hμ]
    have hrr' : ∀ τ ∈ Set.Icc μ ν, (f + C τ * g).Splits := by
      intro τ hτ
      exact hrr τ (hsub hτ)
    have hne' : ∀ τ ∈ Set.Icc μ ν, ¬ (f + C τ * g).IsRoot x := by
      intro τ hτ
      exact hne τ (hsub hτ)
    exact (nat_eq_of_even_int_sub_of_le_succ_of_le_succ
      (rightFamily_even_intCard_roots_gt_sub_of_no_isRoot hμν hdeg' hrr' hne')
      hbounds.2 hbounds.1).symm

/--
Analytic per-root lower counts imply local constancy of the strict-upper root
count near a fixed positive parameter.

This is the #42 local-constancy consumer for a multiplicity-preserving
root-continuity theorem: once each root of `f + C μ * g` keeps at least its
multiplicity inside every sufficiently small ball for nearby parameters, the
finite radius bridge gives exact equality of the upper count near `μ`.
-/
theorem rightFamily_local_card_roots_gt_eq_of_local_lower_counts
    {f g : ℝ[X]} {μ₀ μ₁ μ x : ℝ}
    (hμ : μ ∈ Set.Icc μ₀ μ₁)
    (hdeg : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ * g).natDegree)
    (hrr : ∀ ν ∈ Set.Icc μ₀ μ₁, (f + C ν * g).Splits)
    (hne : ∀ ν ∈ Set.Icc μ₀ μ₁, ¬ (f + C ν * g).IsRoot x)
    (hlower : ∀ ρ > 0, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁,
      |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset,
          (f + C μ * g).roots.count a ≤
            ((f + C ν * g).roots.filter (fun r => |r - a| < ρ)).card) :
    ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
      ((f + C ν * g).roots.filter (x < ·)).card =
        ((f + C μ * g).roots.filter (x < ·)).card := by
  have hx : x ∉ (f + C μ * g).roots := by
    intro hx
    exact hne μ hμ (Polynomial.isRoot_of_mem_roots hx)
  obtain ⟨ρ, hρ_pos, hρ⟩ :=
    exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts hx
  obtain ⟨ε, hε_pos, hε⟩ := hlower ρ hρ_pos
  refine ⟨ε, hε_pos, fun ν hν hνμ => ?_⟩
  exact hρ (f + C ν * g) (hrr μ hμ) (hrr ν hν) (hdeg ν hν) (hε ν hν hνμ)

/--
Selected nearby root clusters imply local constancy of the strict-upper root
count near a fixed positive parameter.

This is the selected-root-cluster version of
`rightFamily_local_card_roots_gt_eq_of_local_lower_counts`: once the analytic
input produces an exact-cardinality submultiset of nearby roots around each
root of the base parameter, the existing finite bridge turns it into the local
lower-count hypothesis.
-/
theorem rightFamily_local_card_roots_gt_eq_of_root_clusters
    {f g : ℝ[X]} {μ₀ μ₁ μ x : ℝ}
    (hμ : μ ∈ Set.Icc μ₀ μ₁)
    (hdeg : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ * g).natDegree)
    (hrr : ∀ ν ∈ Set.Icc μ₀ μ₁, (f + C ν * g).Splits)
    (hne : ∀ ν ∈ Set.Icc μ₀ μ₁, ¬ (f + C ν * g).IsRoot x)
    (hclusters : ∀ ρ > 0, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁,
      |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset, ∃ s : Multiset ℝ,
          s ≤ (f + C ν * g).roots ∧
            s.card = (f + C μ * g).roots.count a ∧
            ∀ r ∈ s, |r - a| < ρ) :
    ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
      ((f + C ν * g).roots.filter (x < ·)).card =
        ((f + C μ * g).roots.filter (x < ·)).card := by
  refine rightFamily_local_card_roots_gt_eq_of_local_lower_counts
    hμ hdeg hrr hne ?_
  intro ρ hρ
  obtain ⟨ε, hε_pos, hε⟩ := hclusters ρ hρ
  refine ⟨ε, hε_pos, fun ν hν hνμ a ha => ?_⟩
  obtain ⟨s, hs_le, hs_card, hs_near⟩ := hε ν hν hνμ a ha
  rw [← hs_card]
  exact Polynomial.card_le_card_roots_filter_of_le_roots hs_le hs_near

/--
Per-root lower counts along a root-free compact parameter interval imply
endpoint equality of strict-upper root counts.

This feeds the analytic local lower-count primitive directly into the existing
parity bridge `rightFamily_card_roots_gt_eq_of_local_count_bound`.
-/
theorem rightFamily_card_roots_gt_eq_of_local_lower_counts
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x)
    (hlower : ∀ μ ∈ Set.Icc μ₀ μ₁, ∀ ρ > 0, ∃ ε > 0,
      ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset,
          (f + C μ * g).roots.count a ≤
            ((f + C ν * g).roots.filter (fun r => |r - a| < ρ)).card) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  refine rightFamily_card_roots_gt_eq_of_locally_constant hμ₁ ?_
  intro μ hμ
  have hdegμ : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ * g).natDegree := by
    intro ν hν
    rw [hdeg ν hν, hdeg μ hμ]
  exact rightFamily_local_card_roots_gt_eq_of_local_lower_counts
    (f := f) (g := g) (μ := μ) hμ hdegμ hrr hne (hlower μ hμ)

/--
Selected nearby root clusters along a root-free compact parameter interval
imply endpoint equality of strict-upper root counts.

This is the interval-level consumer for selected-root cluster continuity on the
positive-parameter local-constancy side of issue #42.
-/
theorem rightFamily_card_roots_gt_eq_of_root_clusters
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x)
    (hclusters : ∀ μ ∈ Set.Icc μ₀ μ₁, ∀ ρ > 0, ∃ ε > 0,
      ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset, ∃ s : Multiset ℝ,
          s ≤ (f + C ν * g).roots ∧
            s.card = (f + C μ * g).roots.count a ∧
            ∀ r ∈ s, |r - a| < ρ) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  refine rightFamily_card_roots_gt_eq_of_locally_constant hμ₁ ?_
  intro μ hμ
  have hdegμ : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ * g).natDegree := by
    intro ν hν
    rw [hdeg ν hν, hdeg μ hμ]
  exact rightFamily_local_card_roots_gt_eq_of_root_clusters
    (f := f) (g := g) (μ := μ) hμ hdegμ hrr hne (hclusters μ hμ)

end RealRooted
