import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort

/-!
# Derivative interlacing

The main result is that if `f` is a real-rooted polynomial of degree at least
two, then `f.derivative` is real-rooted and interlaces `f`.
-/

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Mathlib-version compatibility helpers

The following lemmas restate a handful of `Polynomial` facts about derivatives
using API that is stable across the Mathlib versions this file is built against.
-/

/-- Exact `natDegree` of a derivative over `ℝ` (a characteristic-zero field). -/
lemma natDegree_derivative_eq (p : ℝ[X]) :
    p.derivative.natDegree = p.natDegree - 1 := by
  rcases eq_or_ne p.natDegree 0 with h | h
  · have hle := Polynomial.natDegree_derivative_le p
    rw [h] at hle ⊢
    simpa using hle
  · refine le_antisymm (Polynomial.natDegree_derivative_le p) ?_
    refine Polynomial.le_natDegree_of_ne_zero ?_
    have hp0 : p ≠ 0 := fun hc => h (by simp [hc])
    have hidx : p.natDegree - 1 + 1 = p.natDegree := by lia
    rw [Polynomial.coeff_derivative, hidx]
    refine mul_ne_zero ?_ (by positivity)
    rw [← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0

/-- A polynomial of `natDegree` zero has vanishing derivative. -/
lemma derivative_eq_zero_of_natDegree_eq_zero {p : ℝ[X]} (h : p.natDegree = 0) :
    p.derivative = 0 := by
  rw [eq_C_of_natDegree_eq_zero h, derivative_C]

/-- A polynomial of positive `natDegree` has a nonzero derivative. -/
lemma derivative_ne_zero_of_natDegree_ne_zero {p : ℝ[X]} (h : p.natDegree ≠ 0) :
    p.derivative ≠ 0 := by
  intro hc
  have hp0 : p ≠ 0 := fun hpc => h (by simp [hpc])
  have hidx : p.natDegree - 1 + 1 = p.natDegree := by lia
  have hcoeff : p.derivative.coeff (p.natDegree - 1) ≠ 0 := by
    rw [Polynomial.coeff_derivative, hidx]
    refine mul_ne_zero ?_ (by positivity)
    rw [← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  rw [hc] at hcoeff
  simp at hcoeff

/-- A polynomial of `natDegree` zero splits in the zero-aware convention. -/
lemma splits_of_natDegree_eq_zero {p : ℝ[X]} (h : p.natDegree = 0) :
    p.Splits := by
  apply splits_of_card_roots
  have hle : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
  rw [h] at hle ⊢
  exact Nat.le_zero.mp hle

/-! ## Exact degree of derivative -/

protected lemma HasNonnegCoeffs.derivative {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.derivative := by
  intro n
  simpa [coeff_derivative] using mul_nonneg (hp (n + 1)) (by positivity)

protected lemma HasPosLeadingCoeff.derivative {f : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : f.natDegree ≠ 0) :
    HasPosLeadingCoeff f.derivative := by
  unfold HasPosLeadingCoeff at hf_pos ⊢
  rw [leadingCoeff, natDegree_derivative_eq f, coeff_derivative]
  rw [Nat.sub_add_cancel (by lia), coeff_natDegree] at *
  nlinarith

lemma HasNonnegCoeffs.iterate_derivative {p : ℝ[X]} :
    ∀ n : ℕ, HasNonnegCoeffs p → HasNonnegCoeffs ((derivative^[n]) p)
  | 0, hp => hp
  | n + 1, hp => by
      simpa [Function.iterate_succ_apply'] using (hp.iterate_derivative n).derivative

lemma coeff_one_sub_X_mul_derivative (p : ℝ[X]) (m : Nat) :
    ((1 - X) * p.derivative).coeff m =
      ((m + 1 : ℝ) * p.coeff (m + 1)) - ((m : ℝ) * p.coeff m) := by
  cases m <;> simp [sub_mul, coeff_derivative]
  ring_nf

/-- An exact double root has nonvanishing second derivative. -/
lemma eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
    {p : ℝ[X]} {x : ℝ} (hp0 : p ≠ 0) (hmult : p.rootMultiplicity x = 2) :
    p.derivative.derivative.eval x ≠ 0 := by
  have hp_root : p.IsRoot x :=
    (rootMultiplicity_pos hp0).mp (by lia)
  have hp_deg_ge2 : 2 ≤ p.natDegree := by
    calc
      2 = p.rootMultiplicity x := by lia
      _ = p.roots.count x := (count_roots p).symm
      _ ≤ p.roots.card := p.roots.count_le_card x
      _ ≤ p.natDegree := card_roots' p
  have hpd_ne : p.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  have hpd_rootmult : p.derivative.rootMultiplicity x = 1 := by
    rw [derivative_rootMultiplicity_of_root hp_root, hmult]
  intro hder2
  have hpd_root : p.derivative.IsRoot x :=
    (rootMultiplicity_pos hpd_ne).mp (by lia)
  have hpd_der_root : p.derivative.derivative.IsRoot x := by simp_all
  have hmult_gt : 1 < p.derivative.rootMultiplicity x :=
    (one_lt_rootMultiplicity_iff_isRoot hpd_ne).2 ⟨hpd_root, hpd_der_root⟩
  lia

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
      rw [hcount]
      exact Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a < r ∧ r ≤ b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a < r ∧ r ≤ b) ∧
        r₂ ∈ p.roots.filter (fun r => a < r ∧ r ≤ b) ∧ r₁ ≠ r₂ := by
    let m := p.roots.filter (fun r => a < r ∧ r ≤ b)
    have hm_card : 1 < m.card := Nat.lt_of_not_ge h_contra
    have hm_pos : 0 < m.card := Nat.zero_lt_of_lt hm_card
    obtain ⟨r₁, hr₁⟩ := Multiset.card_pos_iff_exists_mem.mp hm_pos
    have hm_erase_pos : 0 < (m.erase r₁).card := by
      rw [Multiset.card_erase_of_mem hr₁]
      exact Nat.sub_pos_of_lt hm_card
    obtain ⟨r₂, hr₂erase⟩ := Multiset.card_pos_iff_exists_mem.mp hm_erase_pos
    have hr₂ : r₂ ∈ m := Multiset.mem_of_mem_erase hr₂erase
    have hm_nodup : m.Nodup := h_nodup
    have hr₁_notin : r₁ ∉ m.erase r₁ := hm_nodup.notMem_erase
    have hr₁r₂ : r₁ ≠ r₂ := by
      intro h
      subst h
      exact hr₁_notin hr₂erase
    exact ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a < r ∧ r ≤ b) ∧
        r₂ ∈ p.roots.filter (fun r => a < r ∧ r ≤ b) ∧ r₁ < r₂ := by
    cases lt_or_gt_of_ne hr₁r₂ with
    | inl hlt => exact ⟨r₁, r₂, hr₁, hr₂, hlt⟩
    | inr hgt => exact ⟨r₂, r₁, hr₂, hr₁, hgt⟩
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
      rw [hcount]
      exact Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a < r ∧ r < b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a < r ∧ r < b) ∧
        r₂ ∈ p.roots.filter (fun r => a < r ∧ r < b) ∧ r₁ ≠ r₂ := by
    let m := p.roots.filter (fun r => a < r ∧ r < b)
    have hm_card : 1 < m.card := Nat.lt_of_not_ge h_contra
    have hm_pos : 0 < m.card := Nat.zero_lt_of_lt hm_card
    obtain ⟨r₁, hr₁⟩ := Multiset.card_pos_iff_exists_mem.mp hm_pos
    have hm_erase_pos : 0 < (m.erase r₁).card := by
      rw [Multiset.card_erase_of_mem hr₁]
      exact Nat.sub_pos_of_lt hm_card
    obtain ⟨r₂, hr₂erase⟩ := Multiset.card_pos_iff_exists_mem.mp hm_erase_pos
    have hr₂ : r₂ ∈ m := Multiset.mem_of_mem_erase hr₂erase
    have hm_nodup : m.Nodup := h_nodup
    have hr₁_notin : r₁ ∉ m.erase r₁ := hm_nodup.notMem_erase
    have hr₁r₂ : r₁ ≠ r₂ := by
      intro h
      subst h
      exact hr₁_notin hr₂erase
    exact ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a < r ∧ r < b) ∧
        r₂ ∈ p.roots.filter (fun r => a < r ∧ r < b) ∧ r₁ < r₂ := by
    cases lt_or_gt_of_ne hr₁r₂ with
    | inl hlt => exact ⟨r₁, r₂, hr₁, hr₂, hlt⟩
    | inr hgt => exact ⟨r₂, r₁, hr₂, hr₁, hgt⟩
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
      rw [hcount]
      exact Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a ≤ r ∧ r < b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a ≤ r ∧ r < b) ∧
        r₂ ∈ p.roots.filter (fun r => a ≤ r ∧ r < b) ∧ r₁ ≠ r₂ := by
    let m := p.roots.filter (fun r => a ≤ r ∧ r < b)
    have hm_card : 1 < m.card := Nat.lt_of_not_ge h_contra
    have hm_pos : 0 < m.card := Nat.zero_lt_of_lt hm_card
    obtain ⟨r₁, hr₁⟩ := Multiset.card_pos_iff_exists_mem.mp hm_pos
    have hm_erase_pos : 0 < (m.erase r₁).card := by
      rw [Multiset.card_erase_of_mem hr₁]
      exact Nat.sub_pos_of_lt hm_card
    obtain ⟨r₂, hr₂erase⟩ := Multiset.card_pos_iff_exists_mem.mp hm_erase_pos
    have hr₂ : r₂ ∈ m := Multiset.mem_of_mem_erase hr₂erase
    have hm_nodup : m.Nodup := h_nodup
    have hr₁_notin : r₁ ∉ m.erase r₁ := hm_nodup.notMem_erase
    have hr₁r₂ : r₁ ≠ r₂ := by
      intro h
      subst h
      exact hr₁_notin hr₂erase
    exact ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a ≤ r ∧ r < b) ∧
        r₂ ∈ p.roots.filter (fun r => a ≤ r ∧ r < b) ∧ r₁ < r₂ := by
    cases lt_or_gt_of_ne hr₁r₂ with
    | inl hlt => exact ⟨r₁, r₂, hr₁, hr₂, hlt⟩
    | inr hgt => exact ⟨r₂, r₁, hr₂, hr₁, hgt⟩
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
      rw [hcount]
      exact Nat.le_of_not_lt fun h =>
        hno x hx.1 hx.2 <| isRoot_derivative_of_rootMultiplicity_ge_two h
    · have hcount :
          (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).count x = 0 := by
        simp [hx]
      rw [hcount]
      exact Nat.zero_le _
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a ≤ r ∧ r ≤ b) ∧
        r₂ ∈ p.roots.filter (fun r => a ≤ r ∧ r ≤ b) ∧ r₁ ≠ r₂ := by
    let m := p.roots.filter (fun r => a ≤ r ∧ r ≤ b)
    have hm_card : 1 < m.card := Nat.lt_of_not_ge h_contra
    have hm_pos : 0 < m.card := Nat.zero_lt_of_lt hm_card
    obtain ⟨r₁, hr₁⟩ := Multiset.card_pos_iff_exists_mem.mp hm_pos
    have hm_erase_pos : 0 < (m.erase r₁).card := by
      rw [Multiset.card_erase_of_mem hr₁]
      exact Nat.sub_pos_of_lt hm_card
    obtain ⟨r₂, hr₂erase⟩ := Multiset.card_pos_iff_exists_mem.mp hm_erase_pos
    have hr₂ : r₂ ∈ m := Multiset.mem_of_mem_erase hr₂erase
    have hm_nodup : m.Nodup := h_nodup
    have hr₁_notin : r₁ ∉ m.erase r₁ := hm_nodup.notMem_erase
    have hr₁r₂ : r₁ ≠ r₂ := by
      intro h
      subst h
      exact hr₁_notin hr₂erase
    exact ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁r₂⟩ :
      ∃ r₁ r₂, r₁ ∈ p.roots.filter (fun r => a ≤ r ∧ r ≤ b) ∧
        r₂ ∈ p.roots.filter (fun r => a ≤ r ∧ r ≤ b) ∧ r₁ < r₂ := by
    cases lt_or_gt_of_ne hr₁r₂ with
    | inl hlt => exact ⟨r₁, r₂, hr₁, hr₂, hlt⟩
    | inr hgt => exact ⟨r₂, r₁, hr₂, hr₁, hgt⟩
  obtain ⟨c, hc₁, hc₂, hc₃⟩ : ∃ c, r₁ < c ∧ c < r₂ ∧ p.derivative.IsRoot c := by
    apply exists_root_derivative_between hr₁r₂
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₁).1
    · exact Polynomial.isRoot_of_mem_roots <| (Multiset.mem_filter.mp hr₂).1
  exact hno c (by linarith [Multiset.mem_filter.mp hr₁])
    (by linarith [Multiset.mem_filter.mp hr₂]) hc₃

/-- Contrapositive Rolle wrapper for `(a, b)`. -/
theorem exists_isRoot_derivative_mem_Ioo_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    ∃ x, a < x ∧ x < b ∧ p.derivative.IsRoot x := by
  by_contra h
  have hno : ∀ x, a < x → x < b → ¬ p.derivative.IsRoot x :=
    fun x hax hxb hroot => h ⟨x, hax, hxb, hroot⟩
  exact absurd (card_roots_filter_Ioo_le_one_of_derivative_no_root hp hno)
    (Nat.not_le.mpr hcard)

/-- Contrapositive Rolle wrapper for `(a, b]`. -/
theorem exists_isRoot_derivative_mem_Ioc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r ≤ b)).card) :
    ∃ x, a < x ∧ x ≤ b ∧ p.derivative.IsRoot x := by
  by_contra h
  have hno : ∀ x, a < x → x ≤ b → ¬ p.derivative.IsRoot x :=
    fun x hax hxb hroot => h ⟨x, hax, hxb, hroot⟩
  exact absurd (card_roots_filter_Ioc_le_one_of_derivative_no_root hp hno)
    (Nat.not_le.mpr hcard)

/-- Contrapositive Rolle wrapper for `[a, b]`. -/
theorem exists_isRoot_derivative_mem_Icc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ p.derivative.IsRoot x := by
  by_contra h
  have hno : ∀ x, a ≤ x → x ≤ b → ¬ p.derivative.IsRoot x :=
    fun x hax hxb hroot => h ⟨x, hax, hxb, hroot⟩
  exact absurd (card_roots_filter_Icc_le_one_of_derivative_no_root hp hno)
    (Nat.not_le.mpr hcard)

/-- Contrapositive Rolle wrapper for `[a, b)`. -/
theorem exists_isRoot_derivative_mem_Ico_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r < b)).card) :
    ∃ x, a ≤ x ∧ x < b ∧ p.derivative.IsRoot x := by
  by_contra h
  have hno : ∀ x, a ≤ x → x < b → ¬ p.derivative.IsRoot x :=
    fun x hax hxb hroot => h ⟨x, hax, hxb, hroot⟩
  exact absurd (card_roots_filter_Ico_le_one_of_derivative_no_root hp hno)
    (Nat.not_le.mpr hcard)

/-! ## Root-count transfer from `p` to its derivative

Applied, statement-shaped lemmas: whenever an interval carries more than one
root of `p` with multiplicity, Rolle's theorem forces at least one root of
`p.derivative` in the same interval.
-/

/-- Rolle transfer on the open interval `(a, b)`. -/
theorem one_le_card_roots_filter_derivative_Ioo_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r < b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hle : (p.roots.filter (fun r => a < r ∧ r < b)).card ≤ p.natDegree :=
    le_trans (Multiset.card_le_card (Multiset.filter_le _ p.roots))
      (Polynomial.card_roots' p)
  have hderiv_ne : p.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  obtain ⟨x, hax, hxb, hroot⟩ :=
    exists_isRoot_derivative_mem_Ioo_of_one_lt_card_roots hp hcard
  have hx_mem : x ∈ p.derivative.roots.filter (fun r => a < r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨Polynomial.mem_roots'.mpr ⟨hderiv_ne, hroot⟩, hax, hxb⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx_mem⟩

/-- Rolle transfer on the half-open interval `(a, b]`. -/
theorem one_le_card_roots_filter_derivative_Ioc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a < r ∧ r ≤ b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a < r ∧ r ≤ b)).card := by
  have hle : (p.roots.filter (fun r => a < r ∧ r ≤ b)).card ≤ p.natDegree :=
    le_trans (Multiset.card_le_card (Multiset.filter_le _ p.roots))
      (Polynomial.card_roots' p)
  have hderiv_ne : p.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  obtain ⟨x, hax, hxb, hroot⟩ :=
    exists_isRoot_derivative_mem_Ioc_of_one_lt_card_roots hp hcard
  have hx_mem : x ∈ p.derivative.roots.filter (fun r => a < r ∧ r ≤ b) :=
    Multiset.mem_filter.mpr ⟨Polynomial.mem_roots'.mpr ⟨hderiv_ne, hroot⟩, hax, hxb⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx_mem⟩

/-- Rolle transfer on the half-open interval `[a, b)`. -/
theorem one_le_card_roots_filter_derivative_Ico_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r < b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a ≤ r ∧ r < b)).card := by
  have hle : (p.roots.filter (fun r => a ≤ r ∧ r < b)).card ≤ p.natDegree :=
    le_trans (Multiset.card_le_card (Multiset.filter_le _ p.roots))
      (Polynomial.card_roots' p)
  have hderiv_ne : p.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  obtain ⟨x, hax, hxb, hroot⟩ :=
    exists_isRoot_derivative_mem_Ico_of_one_lt_card_roots hp hcard
  have hx_mem : x ∈ p.derivative.roots.filter (fun r => a ≤ r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨Polynomial.mem_roots'.mpr ⟨hderiv_ne, hroot⟩, hax, hxb⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx_mem⟩

/-- Rolle transfer on the closed interval `[a, b]`. -/
theorem one_le_card_roots_filter_derivative_Icc_of_one_lt_card_roots
    {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ}
    (hcard : 1 < (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card) :
    1 ≤ (p.derivative.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card := by
  have hle : (p.roots.filter (fun r => a ≤ r ∧ r ≤ b)).card ≤ p.natDegree :=
    le_trans (Multiset.card_le_card (Multiset.filter_le _ p.roots))
      (Polynomial.card_roots' p)
  have hderiv_ne : p.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  obtain ⟨x, hax, hxb, hroot⟩ :=
    exists_isRoot_derivative_mem_Icc_of_one_lt_card_roots hp hcard
  have hx_mem : x ∈ p.derivative.roots.filter (fun r => a ≤ r ∧ r ≤ b) :=
    Multiset.mem_filter.mpr ⟨Polynomial.mem_roots'.mpr ⟨hderiv_ne, hroot⟩, hax, hxb⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx_mem⟩

/-! ## Interleaving construction -/

/-- Recursively produce a root of `f'` between each consecutive pair in `rs`. -/
noncomputable def mkInterleaving (f : ℝ[X]) :
    (rs : List ℝ) → (hrs : ∀ r ∈ rs, f.IsRoot r) → List ℝ
  | [], _ | [_], _ => []
  | r₁ :: r₂ :: rest, hrs =>
    have hr₁ : f.IsRoot r₁ := hrs r₁ (.head _)
    have hr₂ : f.IsRoot r₂ := hrs r₂ (.tail _ (.head _))
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r := fun r hr => hrs r (.tail _ hr)
    let s := if hlt : r₁ < r₂ then
      (exists_root_derivative_between hlt hr₁ hr₂).choose
    else r₁
    s :: mkInterleaving f (r₂ :: rest) hrest

lemma mkInterleaving_length (f : ℝ[X]) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r),
    (mkInterleaving f rs hrs).length = rs.length - 1
  | [], _ | [_], _ => by simp [mkInterleaving]
  | _ :: r₂ :: rest, hrs => by
    simp only [mkInterleaving, List.length_cons]
    rw [mkInterleaving_length f (r₂ :: rest)]
    simp

/-! ## Properties of the construction

Key change: we generalize the multiset condition to `≤` (sub-multiset)
so that the induction goes through when we drop the first element. -/

/-- Each constructed element is a root of f' in [r₁, r₂].
    Uses sub-multiset condition `≤` to handle repeated roots. -/
lemma mkInterleaving_spec (f : ℝ[X]) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (_ : rs.Pairwise (· ≤ ·))
      (_ : (↑rs : Multiset ℝ) ≤ f.roots),
    (∀ s ∈ mkInterleaving f rs hrs, f.derivative.IsRoot s) ∧
    ListInterlaces (mkInterleaving f rs hrs) rs
  | [], _, _, _ | [_], _, _, _ => by
    refine ⟨?_, ?_⟩ <;> simp [mkInterleaving, ListInterlaces]
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r := fun r hr => hrs r (.tail _ hr)
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    -- The tail is also a sub-multiset of f.roots
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    -- Recursive result
    have ih := mkInterleaving_spec f (r₂ :: rest) hrest hsorted_tail hsub_tail
    simp only [mkInterleaving]
    constructor
    · -- All elements are roots of f'
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · -- First element: Rolle or multiplicity
        split_ifs with hlt
        · grind
        · -- r₁ = r₂, repeated root
          have heq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
          have hcount_list
              : 2 ≤ Multiset.count r₁ (↑(r₁ :: r₂ :: rest) : Multiset ℝ) := by
            simp [heq]
          have hcount : 2 ≤ Multiset.count r₁ f.roots :=
            le_trans hcount_list ((Multiset.le_iff_count.mp hsub) r₁)
          rw [count_roots] at hcount
          exact isRoot_derivative_of_rootMultiplicity_ge_two hcount
      · simp_all
    · -- ListInterlaces
      refine ⟨?_, ?_, ih.2⟩
      · -- r₁ ≤ s
        grind
      · -- s ≤ r₂
        grind

/-! ## Sortedness from interleaving -/

/-- If `ss` interleaves with sorted `rs`, then `ss` is sorted. -/
lemma sorted_of_listInterlaces :
    ∀ (ss rs : List ℝ),
    rs.Pairwise (· ≤ ·) →
    ListInterlaces ss rs →
    ss.Pairwise (· ≤ ·)
  | [], _, _, _ => List.Pairwise.nil
  | [_], _, _, _ => List.pairwise_singleton _ _
  | s₁ :: s₂ :: ss', r₁ :: r₂ :: r₃ :: rs', hrs, hint => by
    -- hint : r₁ ≤ s₁ ∧ s₁ ≤ r₂ ∧ ListInterlaces (s₂ :: ss') (r₂ :: r₃ :: rs')
    obtain ⟨_, hs₁r₂, hint_tail⟩ := hint
    -- From hint_tail: r₂ ≤ s₂ ∧ ...
    have hr₂s₂ : r₂ ≤ s₂ := hint_tail.1
    have hs₁s₂ : s₁ ≤ s₂ := le_trans hs₁r₂ hr₂s₂
    have hrs_tail : (r₂ :: r₃ :: rs').Pairwise (· ≤ ·) :=
      (List.pairwise_cons.mp hrs).2
    have ih := sorted_of_listInterlaces (s₂ :: ss') (r₂ :: r₃ :: rs') hrs_tail hint_tail
    grind
  | _ :: _ :: _, _ :: _ :: [], _, hint => by
    -- rs has exactly 2 elements, ss has ≥ 2 — impossible by ListInterlaces structure
    simp [ListInterlaces] at hint
  | _ :: _ :: _, _ :: [], _, hint => by simp [ListInterlaces] at hint
  | _ :: _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-! ## Sub-multiset relation -/

/-- All elements of the interleaving of `r₁ :: rest` are ≥ r₁. -/
private lemma mkInterleaving_ge (f : ℝ[X]) :
    ∀ (r₁ : ℝ) (rest : List ℝ) (hrs : ∀ r ∈ r₁ :: rest, f.IsRoot r)
      (_ : (r₁ :: rest).Pairwise (· ≤ ·))
      (_ : (↑(r₁ :: rest) : Multiset ℝ) ≤ f.roots),
    ∀ x ∈ mkInterleaving f (r₁ :: rest) hrs, r₁ ≤ x
  | _, [], _, _, _ => by simp [mkInterleaving]
  | r₁, r₂ :: rest', hrs, hsorted, hsub => by
    intro x hx
    simp only [mkInterleaving, List.mem_cons] at hx
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    rcases hx with rfl | hx
    · -- x is the head element
      grind
    · -- x is in the recursive tail
      have hrest := fun r hr => hrs r (.tail _ hr)
      have hsorted_tail := (List.pairwise_cons.mp hsorted).2
      have hsub_tail : (↑(r₂ :: rest') : Multiset ℝ) ≤ f.roots := by
        apply le_trans _ hsub
        simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
      exact le_trans hr₁r₂ (mkInterleaving_ge f r₂ rest' hrest hsorted_tail hsub_tail x hx)

/-- The sub-multiset relation: `↑ss ≤ f'.roots`. -/
lemma mkInterleaving_sub_multiset (f : ℝ[X])
    (hdeg : 2 ≤ f.natDegree) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (_ : rs.Pairwise (· ≤ ·))
      (_ : (↑rs : Multiset ℝ) ≤ f.roots),
    -- (A) sub-multiset of f'.roots
    (↑(mkInterleaving f rs hrs) : Multiset ℝ) ≤ f.derivative.roots ∧
    -- (B) count bound for elements in rs
    (∀ a, a ∈ (↑rs : Multiset ℝ) →
      (↑(mkInterleaving f rs hrs) : Multiset ℝ).count a + 1 ≤ (↑rs : Multiset ℝ).count a)
  | [], _, _, _ | [_], _, _, _ => ⟨Multiset.zero_le _, by simp [mkInterleaving]⟩
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r := fun r hr => hrs r (.tail _ hr)
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    have ih := mkInterleaving_sub_multiset f hdeg (r₂ :: rest) hrest hsorted_tail hsub_tail
    have hf'_ne : f.derivative ≠ 0 :=
      derivative_ne_zero_of_natDegree_ne_zero (by lia)
    have hge_tail : ∀ x ∈ mkInterleaving f (r₂ :: rest) hrest, r₂ ≤ x :=
      mkInterleaving_ge f r₂ rest hrest hsorted_tail hsub_tail
    -- Definitionally unfold mkInterleaving via let + rfl
    let s : ℝ := if hlt : r₁ < r₂ then
      (exists_root_derivative_between hlt (hrs r₁ (.head _))
        (hrs r₂ (.tail _ (.head _)))).choose
    else r₁
    have hunfold : mkInterleaving f (r₁ :: r₂ :: rest) hrs =
      s :: mkInterleaving f (r₂ :: rest) hrest := rfl
    rw [hunfold]
    -- Now goal is about ↑(s :: mkInterleaving f (r₂ :: rest) hrest)
    -- Helper: count of s in the tail
    have htail_count_s_rolle (hlt : r₁ < r₂) :
        (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ).count
          (exists_root_derivative_between hlt (hrs r₁ (.head _))
            (hrs r₂ (.tail _ (.head _)))).choose = 0 :=
      Multiset.count_eq_zero.mpr (by
        rw [Multiset.mem_coe]; grind)
    constructor
    · -- (A): s ::ₘ ↑ss' ≤ f'.roots
      change s ::ₘ ↑(mkInterleaving f (r₂ :: rest) hrest) ≤ f.derivative.roots
      -- s is a root of f' (proved in mkInterleaving_spec)
      have hs_root : f.derivative.IsRoot s :=
        (mkInterleaving_spec f (r₁ :: r₂ :: rest) hrs hsorted
          (le_of_eq rfl |>.trans hsub)).1 s (by simp_all)
      have hs_mem : s ∈ f.derivative.roots := (mem_roots hf'_ne).mpr hs_root
      by_cases hlt : r₁ < r₂
      · -- Rolle: s ∉ ↑ss' (all tail ≥ r₂ > s), use cons_le_of_notMem
        have hspec := (exists_root_derivative_between hlt
          (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
        have hs_notin : s ∉ (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ) := by
          rw [Multiset.mem_coe]; grind
        rw [Multiset.cons_le_of_notMem hs_notin]
        lia
      · -- Multiplicity: s = r₁ = r₂, use count argument via IH(B)
        have hr_eq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
        have hs : s = r₁ := dif_neg hlt
        rw [Multiset.le_iff_count]; intro a
        rw [Multiset.count_cons]
        split_ifs with heq
        · -- s = a: use IH(B) + multiplicity chain
          -- heq : s = a (or a = s depending on count_cons)
          have ih_B := ih.2 a (by
            simp_all)
          -- count a (r₁ :: r₂ :: rest) ≤ rootMultiplicity a f
          have hcount_full : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a ≤
            f.rootMultiplicity a := by
            rw [← count_roots]; exact Multiset.count_le_of_le a hsub
          -- (r₁ :: r₂ :: rest).count a = 1 + (r₂ :: rest).count a since r₁ = s = a
          have : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a =
            (↑(r₂ :: rest) : Multiset ℝ).count a + 1 := by
            simp_all
          rw [this] at hcount_full
          have hmult := rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
            f a hf'_ne
          -- Goal involves Multiset.count and rootMultiplicity — close with lia
          simp only [count_roots] at *; lia
        · -- s ≠ a: use IH directly
          simp only [add_zero]; exact Multiset.count_le_of_le a ih.1
    · -- (B): count bound: ∀ a ∈ ↑rs, count a ss + 1 ≤ count a rs
      intro a ha
      change a ∈ (r₁ ::ₘ ↑(r₂ :: rest) : Multiset ℝ) at ha
      rw [Multiset.mem_cons] at ha
      change (s ::ₘ ↑(mkInterleaving f (r₂ :: rest) hrest)).count a + 1 ≤
        (r₁ ::ₘ ↑(r₂ :: rest) : Multiset ℝ).count a
      rw [Multiset.count_cons, Multiset.count_cons]
      by_cases heq : a = s <;> by_cases hr₁a : a = r₁
      · -- a = s, a = r₁
        rw [if_pos heq, if_pos hr₁a]
        have hr_eq : r₁ = r₂ := by grind
        simp_all
      · -- a = s, a ≠ r₁: vacuous
        rw [if_pos heq, if_neg hr₁a]; exfalso
        rcases ha with rfl | ha_tail
        · lia
        · by_cases hlt : r₁ < r₂
          · -- Rolle: s < r₂ ≤ all tail elements, so s ∉ tail
            have hspec := (exists_root_derivative_between hlt
              (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
            have : a < r₂ := by lia
            have : r₂ ≤ a := by
              have hmem := Multiset.mem_coe.mp ha_tail
              rcases List.mem_cons.mp hmem with h | h <;> simp_all
            linarith
          · lia
      · -- a ≠ s, a = r₁
        rw [if_neg heq, if_pos hr₁a]
        by_cases ha2 : a ∈ (↑(r₂ :: rest) : Multiset ℝ)
        · grind
        · have hlt : r₁ < r₂ := by lia
          have : (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ).count a = 0 :=
            Multiset.count_eq_zero.mpr (by
              rw [Multiset.mem_coe]; grind)
          lia
      · -- a ≠ s, a ≠ r₁
        grind

/-! ## Main theorem -/

/-- **Derivative interlacing**: if `f` is real-rooted of degree ≥ 2,
    then `f.derivative` interlaces `f`. -/
theorem derivative_interlaces {f : ℝ[X]} (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) :
    Interlaces f.derivative f := by
  -- Sort the roots of f
  set rs := f.roots.sort (· ≤ ·) with hrs_def
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_multiset : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_length : rs.length = f.natDegree := by
    rw [hrs_def, Multiset.length_sort, card_roots_of_splits hf]
  have hrs_root : ∀ r ∈ rs, f.IsRoot r := by simp_all
  -- Construct interleaving
  set ss := mkInterleaving f rs hrs_root
  have hss_length : ss.length = f.natDegree - 1 := by
    rw [mkInterleaving_length]; lia
  -- Properties from the construction
  have hsub_rs : (↑rs : Multiset ℝ) ≤ f.roots := le_of_eq hrs_multiset
  have hspec := mkInterleaving_spec f rs hrs_root hrs_sorted hsub_rs
  have hss_roots : ∀ s ∈ ss, f.derivative.IsRoot s := hspec.1
  have hss_interlaces : ListInterlaces ss rs := hspec.2
  -- Sub-multiset relation
  have hsub : (↑ss : Multiset ℝ) ≤ f.derivative.roots :=
    (mkInterleaving_sub_multiset f hdeg rs hrs_root hrs_sorted hsub_rs).1
  -- Degree and cardinality → f' is real-rooted
  have hf'_ne : f.derivative ≠ 0 :=
    derivative_ne_zero_of_natDegree_ne_zero (by lia)
  have hf'_card : f.derivative.roots.card = f.derivative.natDegree := by
    apply le_antisymm (card_roots' _)
    calc f.derivative.natDegree
      _ = f.natDegree - 1 := natDegree_derivative_eq f
      _ = ss.length := hss_length.symm
      _ = (↑ss : Multiset ℝ).card := (Multiset.coe_card ss).symm
      _ ≤ f.derivative.roots.card := Multiset.card_le_card hsub
  have hf'_rr : (f.derivative ≠ 0 ∧ f.derivative.Splits) :=
    ⟨hf'_ne, splits_of_card_roots hf'_card⟩
  -- Multiset equality (sub-multiset + same cardinality)
  have hss_eq : (↑ss : Multiset ℝ) = f.derivative.roots :=
    Multiset.eq_of_le_of_card_le hsub
      (le_of_eq (by rw [hf'_card, natDegree_derivative_eq f, ← hss_length,
        ← Multiset.coe_card]))
  -- Sortedness from interleaving
  have hss_sorted : ss.Pairwise (· ≤ ·) :=
    sorted_of_listInterlaces ss rs hrs_sorted hss_interlaces
  -- Assemble
  exact ⟨⟨by rintro rfl; simp at hf'_ne, hf⟩, hf'_rr, by rw [natDegree_derivative_eq f]; lia,
    rs, ss, hrs_sorted, hss_sorted, hrs_multiset, hss_eq, hss_interlaces⟩

/-- Splitting is preserved by differentiation in the zero-aware convention. -/
theorem eq_zero_or_splits_derivative {p : ℝ[X]}
    (hp : p = 0 ∨ p.Splits) :
    p.derivative = 0 ∨ p.derivative.Splits := by
  rcases hp with rfl | hp
  · simp
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hdeg0 : p.natDegree = 0
  · have hder0 : p.derivative = 0 := derivative_eq_zero_of_natDegree_eq_zero hdeg0
    rw [hder0]
    exact Or.inl rfl
  by_cases hdeg1 : p.natDegree = 1
  · exact Or.inr (splits_of_natDegree_eq_zero (by rw [natDegree_derivative_eq p, hdeg1]))
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact Or.inr (derivative_interlaces hp hdeg2).2.1.2

/-- Strict real-rootedness is preserved by differentiation unless the
derivative vanishes. -/
theorem derivative_eq_zero_or_ne_zero_and_splits {p : ℝ[X]}
    (hp_splits : p.Splits) :
    p.derivative = 0 ∨ (p.derivative ≠ 0 ∧ p.derivative.Splits) := by
  by_cases hdeg0 : p.natDegree = 0
  · left
    exact derivative_eq_zero_of_natDegree_eq_zero hdeg0
  by_cases hdeg1 : p.natDegree = 1
  · right
    have hder_ne : p.derivative ≠ 0 := derivative_ne_zero_of_natDegree_ne_zero hdeg0
    have hder_splits : p.derivative.Splits :=
      splits_of_natDegree_eq_zero (by rw [natDegree_derivative_eq p, hdeg1])
    exact ⟨hder_ne, hder_splits⟩
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact Or.inr (derivative_interlaces hp_splits hdeg2).2.1

/-- A closed segment of real-rooted polynomials has a zero-aware real-rooted
derivative segment. -/
theorem closedSegment_derivative_eq_zero_or_ne_zero_and_splits
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (C (1 - β) * f.derivative + C β * g.derivative = 0) ∨
      ((C (1 - β) * f.derivative + C β * g.derivative) ≠ 0 ∧
        (C (1 - β) * f.derivative + C β * g.derivative).Splits) := by
  simpa using
    (derivative_eq_zero_or_ne_zero_and_splits
      (p := C (1 - β) * f + C β * g) (hseg hβ0 hβ1).2)

/-- Nonzero members of the derivative segment of a closed real-rooted segment
are real-rooted. -/
theorem closedSegment_derivative_splits_of_ne
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hder_ne : C (1 - β) * f.derivative + C β * g.derivative ≠ 0) :
    (C (1 - β) * f.derivative + C β * g.derivative).Splits := by
  rcases closedSegment_derivative_eq_zero_or_ne_zero_and_splits
      hseg hβ0 hβ1 with hzero | hsplit
  · exact False.elim (hder_ne hzero)
  · exact hsplit.2

/-- Nonzero-and-splits wrapper for a derivative of a closed real-rooted
segment.  This packages `closedSegment_derivative_splits_of_ne` in the
`≠ 0 ∧ Splits` shape used by positive-combination arguments. -/
theorem closedSegment_derivative_ne_zero_and_splits_of_ne
    {f g : ℝ[X]}
    (hseg : ∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
      ((C (1 - β) * f + C β * g) ≠ 0 ∧
        (C (1 - β) * f + C β * g).Splits))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hder_ne : C (1 - β) * f.derivative + C β * g.derivative ≠ 0) :
    C (1 - β) * f.derivative + C β * g.derivative ≠ 0 ∧
      (C (1 - β) * f.derivative + C β * g.derivative).Splits :=
  ⟨hder_ne, closedSegment_derivative_splits_of_ne hseg hβ0 hβ1 hder_ne⟩

/-- Right positive family, zero-aware: for each `μ > 0`, the derivative member
`f' + C μ * g'` is either zero or real-rooted. -/
theorem posFamily_derivative_eq_zero_or_ne_zero_and_splits
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ) :
    (f.derivative + C μ * g.derivative = 0) ∨
      ((f.derivative + C μ * g.derivative) ≠ 0 ∧
        (f.derivative + C μ * g.derivative).Splits) := by
  simpa using
    (derivative_eq_zero_or_ne_zero_and_splits
      (p := f + C μ * g) (hfam hμ).2)

/-- Explicit-binder variant of `posFamily_derivative_eq_zero_or_ne_zero_and_splits`. -/
theorem posFamily_derivative_eq_zero_or_ne_zero_and_splits_explicit
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)) :
    ∀ μ : ℝ, 0 < μ →
      (f.derivative + C μ * g.derivative = 0) ∨
        ((f.derivative + C μ * g.derivative) ≠ 0 ∧
          (f.derivative + C μ * g.derivative).Splits) := by
  intro μ hμ
  exact posFamily_derivative_eq_zero_or_ne_zero_and_splits hfam hμ

/-- Zero-or-splits projection for a derivative member of a positive right
family. -/
theorem posFamily_derivative_eq_zero_or_splits
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ) :
    (f.derivative + C μ * g.derivative = 0) ∨
      (f.derivative + C μ * g.derivative).Splits := by
  rcases posFamily_derivative_eq_zero_or_ne_zero_and_splits hfam hμ with hzero | hsplit
  · exact Or.inl hzero
  · exact Or.inr hsplit.2

/-- Explicit-binder zero-or-splits projection for derivative members of a
positive right family. -/
theorem posFamily_derivative_eq_zero_or_splits_explicit
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)) :
    ∀ μ : ℝ, 0 < μ →
      (f.derivative + C μ * g.derivative = 0) ∨
        (f.derivative + C μ * g.derivative).Splits := by
  intro μ hμ
  exact posFamily_derivative_eq_zero_or_splits hfam hμ

/-- Nonzero members of the derivative of a real-rooted right family
`f + C μ * g`, for `μ > 0`, are real-rooted. -/
theorem posFamily_derivative_splits_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ)
    (hder_ne : f.derivative + C μ * g.derivative ≠ 0) :
    (f.derivative + C μ * g.derivative).Splits := by
  rcases posFamily_derivative_eq_zero_or_ne_zero_and_splits hfam hμ with
    hzero | hsplit
  · exact absurd hzero hder_ne
  · exact hsplit.2

/-- Nonzero-and-splits packaging for a derivative member of a positive right
family. -/
theorem posFamily_derivative_ne_zero_and_splits
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    {μ : ℝ} (hμ : 0 < μ)
    (hder_ne : f.derivative + C μ * g.derivative ≠ 0) :
    f.derivative + C μ * g.derivative ≠ 0 ∧
      (f.derivative + C μ * g.derivative).Splits :=
  ⟨hder_ne, posFamily_derivative_splits_of_ne hfam hμ hder_ne⟩

/-- If every derivative member of a positive right family is nonzero, then the
derivative family has the same `≠ 0 ∧ Splits` positive-family shape. -/
theorem posFamily_derivative_family_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ {μ : ℝ}, 0 < μ →
      (f.derivative + C μ * g.derivative ≠ 0 ∧
        (f.derivative + C μ * g.derivative).Splits) :=
  fun hμ => posFamily_derivative_ne_zero_and_splits hfam hμ (hder_ne hμ)

/-- Explicit-binder variant of `posFamily_derivative_family_of_ne`. -/
theorem posFamily_derivative_family_explicit_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ μ : ℝ, 0 < μ →
      (f.derivative + C μ * g.derivative ≠ 0 ∧
        (f.derivative + C μ * g.derivative).Splits) :=
  fun μ hμ => posFamily_derivative_ne_zero_and_splits hfam hμ (hder_ne μ hμ)

/-- Splitting projection from the implicit derivative-family wrapper. -/
theorem posFamily_derivative_family_splits_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ {μ : ℝ}, 0 < μ → (f.derivative + C μ * g.derivative).Splits :=
  fun hμ => (posFamily_derivative_family_of_ne hfam hder_ne hμ).2

/-- Nonzero projection from the implicit derivative-family wrapper. -/
theorem posFamily_derivative_family_ne_zero_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ {μ : ℝ}, 0 < μ → f.derivative + C μ * g.derivative ≠ 0 :=
  fun hμ => (posFamily_derivative_family_of_ne hfam hder_ne hμ).1

/-- Splitting projection from the explicit derivative-family wrapper. -/
theorem posFamily_derivative_splits_explicit_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ μ : ℝ, 0 < μ → (f.derivative + C μ * g.derivative).Splits :=
  fun μ hμ => (posFamily_derivative_family_explicit_of_ne hfam hder_ne μ hμ).2

/-- Nonzero projection from the explicit derivative-family wrapper. -/
theorem posFamily_derivative_ne_zero_explicit_of_ne
    {f g : ℝ[X]}
    (hfam : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits))
    (hder_ne : ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0) :
    ∀ μ : ℝ, 0 < μ → f.derivative + C μ * g.derivative ≠ 0 :=
  fun μ hμ => (posFamily_derivative_family_explicit_of_ne hfam hder_ne μ hμ).1

/-- If all roots of a real-rooted polynomial are nonpositive, then all roots of
its derivative are nonpositive. -/
theorem roots_nonpos_derivative_of_roots_nonpos {p : ℝ[X]}
    (hp_splits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    ∀ r ∈ p.derivative.roots, r ≤ 0 := by
  by_cases hdeg0 : p.natDegree = 0
  · have hder0 : p.derivative = 0 := derivative_eq_zero_of_natDegree_eq_zero hdeg0
    rw [hder0]
    simp
  by_cases hdeg1 : p.natDegree = 1
  · have hderdeg : p.derivative.natDegree = 0 := by
      rw [natDegree_derivative_eq p, hdeg1]
    have hderC : p.derivative = C (p.derivative.coeff 0) :=
      eq_C_of_natDegree_eq_zero hderdeg
    rw [hderC]
    simp
  · have hdeg2 : 2 ≤ p.natDegree := by lia
    exact roots_le_of_prec_right (derivative_interlaces hp_splits hdeg2).toPrec hroots

/-- Standard Rolle--Obreschkoff input: differentiation preserves weak proper
position in the oriented, zero-aware `Prec0` convention. -/
def derivativePreservesPrec0Statement : Prop :=
  ∀ {p q : ℝ[X]}, Prec0 p q → Prec0 p.derivative q.derivative

end RealRooted
