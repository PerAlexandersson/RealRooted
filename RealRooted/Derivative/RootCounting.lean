import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort
import RealRooted.Derivative.Algebra

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Rolle's theorem for polynomials -/

theorem exists_root_derivative_between {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c, a < c ∧ c < b ∧ p.derivative.IsRoot c := by
  have hcont : ContinuousOn (fun x => p.eval x) (Icc a b) :=
    p.continuous.continuousOn
  have hfab : p.eval a = p.eval b := by simp_all
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
    fun x _ => p.hasDerivAt x
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_zero hab hcont hfab hderiv
  exact ⟨c, hc_mem.1, hc_mem.2, hc_eq⟩

theorem isRoot_derivative_of_rootMultiplicity_ge_two {p : ℝ[X]} {r : ℝ}
    (hm : 2 ≤ p.rootMultiplicity r) :
    p.derivative.IsRoot r := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hm
  have hdvd : (X - C r) ^ 2 ∣ p := (le_rootMultiplicity_iff hp0).mp hm
  have hdvd' : (X - C r) ^ (2 - 1) ∣ p.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd
  simp only [Nat.reduceSubDiff, pow_one] at hdvd'
  exact dvd_iff_isRoot.mp hdvd'

/-- Extract two ordered distinct elements from a nodup multiset with cardinality
at least two. -/
private lemma exists_pair_mem_lt_of_one_lt_card {m : Multiset ℝ}
    (hcard : 1 < m.card) (hnodup : m.Nodup) :
    ∃ r₁ r₂, r₁ ∈ m ∧ r₂ ∈ m ∧ r₁ < r₂ := by
  have hm_pos : 0 < m.card := Nat.zero_lt_of_lt hcard
  obtain ⟨r₁, hr₁⟩ := Multiset.card_pos_iff_exists_mem.mp hm_pos
  have hm_erase_pos : 0 < (m.erase r₁).card := by
    simpa [Multiset.card_erase_of_mem hr₁] using Nat.sub_pos_of_lt hcard
  obtain ⟨r₂, hr₂erase⟩ := Multiset.card_pos_iff_exists_mem.mp hm_erase_pos
  have hr₂ : r₂ ∈ m := Multiset.mem_of_mem_erase hr₂erase
  have hr₁r₂ : r₁ ≠ r₂ := by
    intro h
    subst h
    exact hnodup.notMem_erase hr₂erase
  cases lt_or_gt_of_ne hr₁r₂ with
  | inl hlt => exact ⟨r₁, r₂, hr₁, hr₂, hlt⟩
  | inr hgt => exact ⟨r₂, r₁, hr₂, hr₁, hgt⟩

/-- Rolle-type interval root-count bound.  If `p.derivative` has no root in
the half-open interval `(a, b]`, then `p` has at most one root there, counted
with multiplicity. -/
theorem card_roots_filter_Ioc_le_one_of_derivative_no_root
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hno : ∀ x, a < x → x ≤ b → ¬ p.derivative.IsRoot x) :
    (p.roots.filter (fun r => a < r ∧ r ≤ b)).card ≤ 1 := by
  have _ : p ≠ 0 := hp
  by_contra h_contra
  have h_nodup : (p.roots.filter (fun r => a < r ∧ r ≤ b)).Nodup := by
    refine Multiset.nodup_iff_count_le_one.mpr ?_
    intro x
    by_cases hx : a < x ∧ x ≤ b
    · have hcount :
          (p.roots.filter (fun r => a < r ∧ r ≤ b)).count x =
            p.rootMultiplicity x := by
        simp [hx, count_roots]
      simpa [hcount] using Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a < r ∧ r ≤ b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :=
    exists_pair_mem_lt_of_one_lt_card
      (m := p.roots.filter (fun r => a < r ∧ r ≤ b))
      (Nat.lt_of_not_ge h_contra) h_nodup
  obtain ⟨c, hc₁, hc₂, hc₃⟩ : ∃ c, r₁ < c ∧ c < r₂ ∧ p.derivative.IsRoot c := by
    apply exists_root_derivative_between hr₁r₂
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₁).1
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₂).1
  exact hno c (by linarith [Multiset.mem_filter.mp hr₁])
    (by linarith [Multiset.mem_filter.mp hr₂]) hc₃

/-- Direct #42 Rolle-type strict-open interval root-count bound.  If
`p.derivative` has no root in `(a, b)`, then `p` has at most one root there,
counted with multiplicity. -/
theorem card_roots_filter_Ioo_le_one_of_derivative_no_root
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hno : ∀ x, a < x → x < b → ¬ p.derivative.IsRoot x) :
    (p.roots.filter (fun r => a < r ∧ r < b)).card ≤ 1 := by
  have _ : p ≠ 0 := hp
  by_contra h_contra
  have h_nodup : (p.roots.filter (fun r => a < r ∧ r < b)).Nodup := by
    refine Multiset.nodup_iff_count_le_one.mpr ?_
    intro x
    by_cases hx : a < x ∧ x < b
    · have hcount :
          (p.roots.filter (fun r => a < r ∧ r < b)).count x =
            p.rootMultiplicity x := by
        simp [hx, count_roots]
      simpa [hcount] using Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a < r ∧ r < b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :=
    exists_pair_mem_lt_of_one_lt_card
      (m := p.roots.filter (fun r => a < r ∧ r < b))
      (Nat.lt_of_not_ge h_contra) h_nodup
  obtain ⟨c, hc₁, hc₂, hc₃⟩ : ∃ c, r₁ < c ∧ c < r₂ ∧ p.derivative.IsRoot c := by
    apply exists_root_derivative_between hr₁r₂
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₁).1
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₂).1
  exact hno c (by linarith [Multiset.mem_filter.mp hr₁])
    (by linarith [Multiset.mem_filter.mp hr₂]) hc₃

/-- Rolle-type root-count bound for the half-open interval `[a, b)`. -/
theorem card_roots_filter_Ico_le_one_of_derivative_no_root
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hno : ∀ x, a ≤ x → x < b → ¬ p.derivative.IsRoot x) :
    (p.roots.filter (fun r => a ≤ r ∧ r < b)).card ≤ 1 := by
  have _ : p ≠ 0 := hp
  by_contra h_contra
  have h_nodup : (p.roots.filter (fun r => a ≤ r ∧ r < b)).Nodup := by
    refine Multiset.nodup_iff_count_le_one.mpr ?_
    intro x
    by_cases hx : a ≤ x ∧ x < b
    · have hcount :
          (p.roots.filter (fun r => a ≤ r ∧ r < b)).count x =
            p.rootMultiplicity x := by
        simp [hx, count_roots]
      simpa [hcount] using Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a ≤ r ∧ r < b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :=
    exists_pair_mem_lt_of_one_lt_card
      (m := p.roots.filter (fun r => a ≤ r ∧ r < b))
      (Nat.lt_of_not_ge h_contra) h_nodup
  obtain ⟨c, hc₁, hc₂, hc₃⟩ : ∃ c, r₁ < c ∧ c < r₂ ∧ p.derivative.IsRoot c := by
    apply exists_root_derivative_between hr₁r₂
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₁).1
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₂).1
  exact hno c (by linarith [Multiset.mem_filter.mp hr₁])
    (by linarith [Multiset.mem_filter.mp hr₂]) hc₃

/-- Rolle-type root-count bound for the closed interval `[a, b]`. -/
theorem card_roots_filter_Icc_le_one_of_derivative_no_root
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hno : ∀ x, a ≤ x → x ≤ b → ¬ p.derivative.IsRoot x) :
    (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card ≤ 1 := by
  have _ : p ≠ 0 := hp
  by_contra h_contra
  have h_nodup : (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).Nodup := by
    refine Multiset.nodup_iff_count_le_one.mpr ?_
    intro x
    by_cases hx : a ≤ x ∧ x ≤ b
    · have hcount :
          (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).count x =
            p.rootMultiplicity x := by
        simp [hx, count_roots]
      simpa [hcount] using Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :=
    exists_pair_mem_lt_of_one_lt_card
      (m := p.roots.filter (fun r => a ≤ r ∧ r ≤ b))
      (Nat.lt_of_not_ge h_contra) h_nodup
  obtain ⟨c, hc₁, hc₂, hc₃⟩ : ∃ c, r₁ < c ∧ c < r₂ ∧ p.derivative.IsRoot c := by
    apply exists_root_derivative_between hr₁r₂
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₁).1
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₂).1
  exact hno c (by linarith [Multiset.mem_filter.mp hr₁])
    (by linarith [Multiset.mem_filter.mp hr₂]) hc₃

private lemma exists_isRoot_derivative_of_one_lt_card_roots_filter
    {p : ℝ[X]} {q : ℝ → Prop} [DecidablePred q]
    (hcard : 1 < (p.roots.filter q).card)
    (hle : (∀ x, q x → ¬ p.derivative.IsRoot x) →
      (p.roots.filter q).card ≤ 1) :
    ∃ x, q x ∧ p.derivative.IsRoot x := by
  by_contra h
  exact (Nat.not_le.mpr hcard) (hle fun x hxq hroot => h ⟨x, hxq, hroot⟩)

/-- Contrapositive Rolle wrapper for `(a, b)`. -/
theorem exists_isRoot_derivative_mem_Ioo_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    ∃ x, a < x ∧ x < b ∧ p.derivative.IsRoot x := by
  simpa [and_assoc] using
    exists_isRoot_derivative_of_one_lt_card_roots_filter
      (q := fun x => a < x ∧ x < b) hcard
      (fun hno => card_roots_filter_Ioo_le_one_of_derivative_no_root hp
        (fun x hax hxb => hno x ⟨hax, hxb⟩))

/-- Contrapositive Rolle wrapper for `(a, b]`. -/
theorem exists_isRoot_derivative_mem_Ioc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r ≤ b)).card) :
    ∃ x, a < x ∧ x ≤ b ∧ p.derivative.IsRoot x := by
  simpa [and_assoc] using
    exists_isRoot_derivative_of_one_lt_card_roots_filter
      (q := fun x => a < x ∧ x ≤ b) hcard
      (fun hno => card_roots_filter_Ioc_le_one_of_derivative_no_root hp
        (fun x hax hxb => hno x ⟨hax, hxb⟩))

/-- Contrapositive Rolle wrapper for `[a, b]`. -/
theorem exists_isRoot_derivative_mem_Icc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ p.derivative.IsRoot x := by
  simpa [and_assoc] using
    exists_isRoot_derivative_of_one_lt_card_roots_filter
      (q := fun x => a ≤ x ∧ x ≤ b) hcard
      (fun hno => card_roots_filter_Icc_le_one_of_derivative_no_root hp
        (fun x hax hxb => hno x ⟨hax, hxb⟩))

/-- Contrapositive Rolle wrapper for `[a, b)`. -/
theorem exists_isRoot_derivative_mem_Ico_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r < b)).card) :
    ∃ x, a ≤ x ∧ x < b ∧ p.derivative.IsRoot x := by
  simpa [and_assoc] using
    exists_isRoot_derivative_of_one_lt_card_roots_filter
      (q := fun x => a ≤ x ∧ x < b) hcard
      (fun hno => card_roots_filter_Ico_le_one_of_derivative_no_root hp
        (fun x hax hxb => hno x ⟨hax, hxb⟩))

/-! ## Root-count transfer from `p` to its derivative

Applied, statement-shaped lemmas: whenever an interval carries more than one
root of `p` with multiplicity, Rolle's theorem forces at least one root of
`p.derivative` in the same interval.
-/

private lemma one_le_card_roots_filter_derivative_of_exists
    {p : ℝ[X]} {q : ℝ → Prop} [DecidablePred q]
    (hcard : 1 < (p.roots.filter q).card)
    (hexists : ∃ x, q x ∧ p.derivative.IsRoot x) :
    1 ≤ (p.derivative.roots.filter q).card := by
  have hle : (p.roots.filter q).card ≤ p.natDegree :=
    le_trans (Multiset.card_le_card (Multiset.filter_le _ p.roots))
      (Polynomial.card_roots' p)
  have hderiv_ne : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  obtain ⟨x, hxq, hroot⟩ := hexists
  have hx_mem : x ∈ p.derivative.roots.filter q :=
    Multiset.mem_filter.mpr ⟨Polynomial.mem_roots'.mpr ⟨hderiv_ne, hroot⟩, hxq⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx_mem⟩

/-- Rolle transfer on the open interval `(a, b)`. -/
theorem one_le_card_roots_filter_derivative_Ioo_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a < r ∧ r < b)).card := by
  refine one_le_card_roots_filter_derivative_of_exists hcard ?_
  simpa [and_assoc] using exists_isRoot_derivative_mem_Ioo_of_one_lt_card_roots hp hcard

/-- Rolle transfer on the half-open interval `(a, b]`. -/
theorem one_le_card_roots_filter_derivative_Ioc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r ≤ b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a < r ∧ r ≤ b)).card := by
  refine one_le_card_roots_filter_derivative_of_exists hcard ?_
  simpa [and_assoc] using exists_isRoot_derivative_mem_Ioc_of_one_lt_card_roots hp hcard

/-- Rolle transfer on the half-open interval `[a, b)`. -/
theorem one_le_card_roots_filter_derivative_Ico_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r < b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a ≤ r ∧ r < b)).card := by
  refine one_le_card_roots_filter_derivative_of_exists hcard ?_
  simpa [and_assoc] using exists_isRoot_derivative_mem_Ico_of_one_lt_card_roots hp hcard

/-- Rolle transfer on the closed interval `[a, b]`. -/
theorem one_le_card_roots_filter_derivative_Icc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card := by
  refine one_le_card_roots_filter_derivative_of_exists hcard ?_
  simpa [and_assoc] using exists_isRoot_derivative_mem_Icc_of_one_lt_card_roots hp hcard

end RealRooted
