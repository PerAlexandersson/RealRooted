/-
# Recursive multiset rook-Eulerian polynomials

This file deliberately starts from the row-deletion recurrences rather than
from words.  It is meant as a Lean staging area for the corrected multiset
proof in the rook-Eulerian paper.

The key point is that the refined polynomial for a prepended first row is
`rowAfterDelete lambda beta i`, not a fixed-content matrix action.  The
content has to be decremented at the row label.
-/
import RealRooted.Linear
import RealRooted.WagnerX
import RealRooted.CommonInterleaverTwo

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted
namespace MultisetRook

abbrev Board := List Nat
abbrev Content := List Nat

/--
Local compatibility predicate used for this recursive staging file.

This matches the Chudnovsky--Seymour two-polynomial compatibility convention:
every nonnegative linear combination is real-rooted, allowing the zero
polynomial in degenerate cases.
-/
def Compatible (f g : ℝ[X]) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
    C a * f + C b * g = 0 ∨ IsRealRooted (C a * f + C b * g)

theorem compatible_zero_zero : Compatible 0 0 := by
  intro _a _b _ha _hb
  left
  simp

namespace Compatible

theorem comm {f g : ℝ[X]} (h : Compatible f g) : Compatible g f := by
  intro a b ha hb
  simpa [Compatible, add_comm] using h b a hb ha

end Compatible

theorem compatible_zero_left_of_zero_or_isRealRooted {f : ℝ[X]}
    (hf : f = 0 ∨ IsRealRooted f) :
    Compatible 0 f := by
  intro _a b _ha _hb
  rcases hf with rfl | hf
  · left
    simp
  · by_cases hb0 : b = 0
    · left
      simp [hb0]
    · right
      simpa using isRealRooted_C_mul hf hb0

theorem compatible_zero_right_of_zero_or_isRealRooted {f : ℝ[X]}
    (hf : f = 0 ∨ IsRealRooted f) :
    Compatible f 0 :=
  (compatible_zero_left_of_zero_or_isRealRooted hf).comm

theorem compatible_self_of_zero_or_isRealRooted {f : ℝ[X]}
    (hf : f = 0 ∨ IsRealRooted f) :
    Compatible f f := by
  intro a b _ha _hb
  rcases hf with rfl | hf
  · left
    simp
  · have hsum :
        C a * f + C b * f = C (a + b) * f := by
      rw [← add_mul, ← C_add]
    by_cases hab : a + b = 0
    · left
      simp [hsum, hab]
    · right
      rw [hsum]
      exact isRealRooted_C_mul hf hab

/-- Weighted sum of a finite polynomial family. -/
def weightedSum : List (ℝ × ℝ[X]) → ℝ[X]
  | [] => 0
  | (a, p) :: rest => C a * p + weightedSum rest

/-- Remove terms whose polynomial factor is zero. -/
def dropZeroTerms : List (ℝ × ℝ[X]) → List (ℝ × ℝ[X])
  | [] => []
  | (a, p) :: rest =>
      if p = 0 then dropZeroTerms rest else (a, p) :: dropZeroTerms rest

@[simp] theorem weightedSum_dropZeroTerms :
    ∀ l : List (ℝ × ℝ[X]), weightedSum (dropZeroTerms l) = weightedSum l
  | [] => by
      simp [dropZeroTerms, weightedSum]
  | (a, p) :: rest => by
      by_cases hp : p = 0
      · simp [dropZeroTerms, weightedSum, hp, weightedSum_dropZeroTerms rest]
      · simp [dropZeroTerms, weightedSum, hp, weightedSum_dropZeroTerms rest]

theorem weightedSum_eq_global :
    ∀ l : List (ℝ × ℝ[X]),
      weightedSum l = _root_.RealRooted.weightedSum l
  | [] => by
      simp [weightedSum, _root_.RealRooted.weightedSum]
  | (a, p) :: rest => by
      simp [weightedSum, _root_.RealRooted.weightedSum,
        weightedSum_eq_global rest]

theorem mem_dropZeroTerms :
    ∀ {ap : ℝ × ℝ[X]} {l : List (ℝ × ℝ[X])},
      ap ∈ dropZeroTerms l → ap ∈ l ∧ ap.2 ≠ 0
  | _ap, [], hap => by
      simp [dropZeroTerms] at hap
  | ap, (a, p) :: rest, hap => by
      by_cases hp : p = 0
      · have hrest : ap ∈ dropZeroTerms rest := by
          simpa [dropZeroTerms, hp] using hap
        rcases mem_dropZeroTerms hrest with ⟨hmem, hne⟩
        exact ⟨by simp [hmem], hne⟩
      · have hcases :
            ap = (a, p) ∨ ap ∈ dropZeroTerms rest := by
          simpa [dropZeroTerms, hp] using hap
        rcases hcases with rfl | hrest
        · exact ⟨by simp, hp⟩
        · rcases mem_dropZeroTerms hrest with ⟨hmem, hne⟩
          exact ⟨by simp [hmem], hne⟩

theorem dropZeroTerms_mem_filter
    {fs : List ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hmem : ∀ ap ∈ l, ap.2 ∈ fs) :
    ∀ ap ∈ dropZeroTerms l, ap.2 ∈ fs.filter (fun p => p ≠ 0) := by
  classical
  intro ap hap
  rcases mem_dropZeroTerms hap with ⟨hap_l, hne⟩
  exact List.mem_filter.mpr ⟨hmem ap hap_l, by simpa using hne⟩

theorem dropZeroTerms_nonneg
    {l : List (ℝ × ℝ[X])}
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1) :
    ∀ ap ∈ dropZeroTerms l, 0 ≤ ap.1 := by
  intro ap hap
  exact hnonneg ap (mem_dropZeroTerms hap).1

/-- Full finite-family compatibility. -/
def FamilyCompatible (fs : List ℝ[X]) : Prop :=
  ∀ l : List (ℝ × ℝ[X]),
    (∀ ap ∈ l, ap.2 ∈ fs) →
    (∀ ap ∈ l, 0 ≤ ap.1) →
    weightedSum l = 0 ∨ IsRealRooted (weightedSum l)

/-- Pairwise compatibility indexed by list positions. -/
def PairwiseCompatible (fs : List ℝ[X]) : Prop :=
  ∀ i j : Fin fs.length, i < j → Compatible (fs.get i) (fs.get j)

theorem pairwiseCompatible_of_all_pairs
    {fs : List ℝ[X]}
    (h : ∀ f ∈ fs, ∀ g ∈ fs, Compatible f g) :
    PairwiseCompatible fs := by
  intro i j _hij
  exact h (fs.get i) (List.get_mem fs i) (fs.get j) (List.get_mem fs j)

theorem familyCompatible_of_forall_mem
    {fs gs : List ℝ[X]}
    (hfamily : FamilyCompatible fs)
    (hsub : ∀ p ∈ gs, p ∈ fs) :
    FamilyCompatible gs := by
  intro l hmem hnonneg
  exact hfamily l
    (fun ap hap => hsub ap.2 (hmem ap hap))
    hnonneg

theorem familyCompatible_left_of_append
    {left right : List ℝ[X]}
    (hfamily : FamilyCompatible (left ++ right)) :
    FamilyCompatible left := by
  exact familyCompatible_of_forall_mem hfamily
    (by
      intro p hp
      exact List.mem_append_left right hp)

theorem familyCompatible_right_of_append
    {left right : List ℝ[X]}
    (hfamily : FamilyCompatible (left ++ right)) :
    FamilyCompatible right := by
  exact familyCompatible_of_forall_mem hfamily
    (by
      intro p hp
      exact List.mem_append_right left hp)

theorem familyCompatible_of_filter_ne_zero
    {fs : List ℝ[X]}
    (hfilter : FamilyCompatible (fs.filter (fun p => p ≠ 0))) :
    FamilyCompatible fs := by
  classical
  intro l hmem hnonneg
  have hdrop := hfilter (dropZeroTerms l)
    (dropZeroTerms_mem_filter hmem)
    (dropZeroTerms_nonneg hnonneg)
  simpa using hdrop

theorem globalCompatible_of_compatible {f g : ℝ[X]}
    (h : Compatible f g) :
    _root_.RealRooted.Compatible f g := by
  intro a b ha hb
  exact h a b ha hb

theorem familyCompatible_of_globalFamilyCompatible
    {fs : List ℝ[X]}
    (hfamily : _root_.RealRooted.FamilyCompatible fs) :
    FamilyCompatible fs := by
  intro l hmem hnonneg
  have hglobal := hfamily l hmem hnonneg
  simpa [weightedSum_eq_global] using hglobal

theorem zero_or_isRealRooted_of_mem_familyCompatible
    {fs : List ℝ[X]} {p : ℝ[X]}
    (hfamily : FamilyCompatible fs) (hp : p ∈ fs) :
    p = 0 ∨ IsRealRooted p := by
  have hweighted :
      weightedSum [((1 : ℝ), p)] = 0 ∨
        IsRealRooted (weightedSum [((1 : ℝ), p)]) := by
    exact hfamily [((1 : ℝ), p)]
      (by
        intro ap hap
        simp only [List.mem_singleton] at hap
        rcases hap with rfl
        exact hp)
      (by
        intro ap hap
        simp only [List.mem_singleton] at hap
        rcases hap with rfl
        positivity)
  simpa [weightedSum] using hweighted

theorem compatible_of_mem_familyCompatible
    {fs : List ℝ[X]} {f g : ℝ[X]}
    (hfamily : FamilyCompatible fs) (hf : f ∈ fs) (hg : g ∈ fs) :
    Compatible f g := by
  intro a b ha hb
  have hweighted :
      weightedSum [(a, f), (b, g)] = 0 ∨
        IsRealRooted (weightedSum [(a, f), (b, g)]) := by
    exact hfamily [(a, f), (b, g)]
      (by
        intro ap hap
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
        rcases hap with rfl | rfl
        · exact hf
        · exact hg)
      (by
        intro ap hap
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hap
        rcases hap with rfl | rfl
        · exact ha
        · exact hb)
  simpa [weightedSum] using hweighted

@[simp] theorem weightedSum_append (l₁ l₂ : List (ℝ × ℝ[X])) :
    weightedSum (l₁ ++ l₂) = weightedSum l₁ + weightedSum l₂ := by
  induction l₁ with
  | nil =>
      simp [weightedSum]
  | cons ap rest ih =>
      rcases ap with ⟨a, p⟩
      simp [weightedSum, ih, add_assoc]

@[simp] theorem weightedSum_map_const (a : ℝ) (fs : List ℝ[X]) :
    weightedSum (fs.map (fun p => (a, p))) = C a * fs.sum := by
  induction fs with
  | nil =>
      simp [weightedSum]
  | cons p rest ih =>
      simp [weightedSum, ih, mul_add]

theorem compatible_sum_pair_of_familyCompatible {left right : List ℝ[X]}
    (hfamily : FamilyCompatible (left ++ right)) :
    Compatible left.sum right.sum := by
  intro a b ha hb
  have hweighted :
      weightedSum
          (left.map (fun p => (a, p)) ++ right.map (fun p => (b, p))) = 0 ∨
        IsRealRooted
          (weightedSum
            (left.map (fun p => (a, p)) ++ right.map (fun p => (b, p)))) := by
    exact hfamily
      (left.map (fun p => (a, p)) ++ right.map (fun p => (b, p)))
      (by
        intro ap hap
        rw [List.mem_append] at hap ⊢
        rcases hap with hap | hap
        · left
          rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
          exact hp
        · right
          rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
          exact hp)
      (by
        intro ap hap
        rw [List.mem_append] at hap
        rcases hap with hap | hap
        · rcases List.mem_map.mp hap with ⟨p, _hp, rfl⟩
          exact ha
        · rcases List.mem_map.mp hap with ⟨p, _hp, rfl⟩
          exact hb)
  simpa [weightedSum_append, weightedSum_map_const] using hweighted

theorem sum_zero_or_isRealRooted_of_familyCompatible {fs : List ℝ[X]}
    (hfamily : FamilyCompatible fs) :
    fs.sum = 0 ∨ IsRealRooted fs.sum := by
  have hweighted :
      weightedSum (fs.map (fun p => ((1 : ℝ), p))) = 0 ∨
        IsRealRooted (weightedSum (fs.map (fun p => ((1 : ℝ), p)))) := by
    exact hfamily
      (fs.map (fun p => ((1 : ℝ), p)))
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
        exact hp)
      (by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨p, _hp, rfl⟩
        positivity)
  simpa [weightedSum_map_const] using hweighted

theorem isRealRooted_X : IsRealRooted (X : ℝ[X]) := by
  simpa using (isRealRooted_X_sub_C 0)

theorem linear_zero_or_isRealRooted (a b : ℝ) (_ha : 0 ≤ a) (hb : 0 ≤ b) :
    C a + C b * X = 0 ∨ IsRealRooted (C a + C b * X) := by
  by_cases hb0 : b = 0
  · subst hb0
    by_cases ha0 : a = 0
    · left
      simp [ha0]
    · right
      apply isRealRooted_of_deg_zero
      · simp [ha0]
      · simp
  · right
    have hfactor : C a + C b * X = C b * (X - C (-(a / b))) := by
      simp only [map_neg, sub_neg_eq_add]
      rw [mul_add, ← C_mul]
      ring_nf
      have hbainv : b * a * b⁻¹ = a := by
        field_simp [hb0]
      rw [hbainv]
      abel
    rw [hfactor]
    exact isRealRooted_C_mul (isRealRooted_X_sub_C (-(a / b))) hb0

theorem one_zero_or_isRealRooted :
    (1 : ℝ[X]) = 0 ∨ IsRealRooted (1 : ℝ[X]) := by
  simpa using
    (linear_zero_or_isRealRooted 1 0 (by norm_num) (by norm_num))

theorem x_mul_linear_zero_or_isRealRooted (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    C a * X + C b * (X * X) = 0 ∨
      IsRealRooted (C a * X + C b * (X * X)) := by
  have hfactor : C a * X + C b * (X * X) = X * (C a + C b * X) := by
    ring
  rcases linear_zero_or_isRealRooted a b ha hb with hzero | hrr
  · left
    rw [hfactor, hzero, mul_zero]
  · right
    rw [hfactor]
    exact isRealRooted_mul isRealRooted_X hrr

theorem weightedSum_supported_zero_one_X
    (l : List (ℝ × ℝ[X]))
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsupp : ∀ ap ∈ l, ap.2 = 0 ∨ ap.2 = 1 ∨ ap.2 = X) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ weightedSum l = C a + C b * X := by
  induction l with
  | nil =>
      refine ⟨0, 0, by positivity, by positivity, ?_⟩
      simp [weightedSum]
  | cons ap rest ih =>
      rcases ap with ⟨c, p⟩
      have hc : 0 ≤ c := hnonneg (c, p) (by simp)
      have hrest_nonneg : ∀ ap ∈ rest, 0 ≤ ap.1 := by
        intro ap hap
        exact hnonneg ap (by simp [hap])
      have hrest_supp :
          ∀ ap ∈ rest, ap.2 = 0 ∨ ap.2 = 1 ∨ ap.2 = X := by
        intro ap hap
        exact hsupp ap (by simp [hap])
      rcases ih hrest_nonneg hrest_supp with ⟨a, b, ha, hb, hsum⟩
      have hp := hsupp (c, p) (by simp)
      rcases hp with hp0 | hp1 | hpX
      · have hp0' : p = 0 := hp0
        subst p
        refine ⟨a, b, ha, hb, ?_⟩
        simp [weightedSum, hsum]
      · have hp1' : p = 1 := hp1
        subst p
        refine ⟨c + a, b, add_nonneg hc ha, hb, ?_⟩
        simp [weightedSum, hsum]
        ring
      · have hpX' : p = X := hpX
        subst p
        refine ⟨a, c + b, ha, add_nonneg hc hb, ?_⟩
        simp [weightedSum, hsum]
        ring

theorem weightedSum_supported_zero_X_XX
    (l : List (ℝ × ℝ[X]))
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsupp : ∀ ap ∈ l, ap.2 = 0 ∨ ap.2 = X ∨ ap.2 = X * X) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ weightedSum l =
      C a * X + C b * (X * X) := by
  induction l with
  | nil =>
      refine ⟨0, 0, by positivity, by positivity, ?_⟩
      simp [weightedSum]
  | cons ap rest ih =>
      rcases ap with ⟨c, p⟩
      have hc : 0 ≤ c := hnonneg (c, p) (by simp)
      have hrest_nonneg : ∀ ap ∈ rest, 0 ≤ ap.1 := by
        intro ap hap
        exact hnonneg ap (by simp [hap])
      have hrest_supp :
          ∀ ap ∈ rest, ap.2 = 0 ∨ ap.2 = X ∨ ap.2 = X * X := by
        intro ap hap
        exact hsupp ap (by simp [hap])
      rcases ih hrest_nonneg hrest_supp with ⟨a, b, ha, hb, hsum⟩
      have hp := hsupp (c, p) (by simp)
      rcases hp with hp0 | hpX | hpXX
      · have hp0' : p = 0 := hp0
        subst p
        refine ⟨a, b, ha, hb, ?_⟩
        simp [weightedSum, hsum]
      · have hpX' : p = X := hpX
        subst p
        refine ⟨c + a, b, add_nonneg hc ha, hb, ?_⟩
        simp [weightedSum, hsum]
        ring
      · have hpXX' : p = X * X := hpXX
        subst p
        refine ⟨a, c + b, ha, add_nonneg hc hb, ?_⟩
        simp [weightedSum, hsum]
        ring

theorem familyCompatible_of_supported_zero_one_X
    {fs : List ℝ[X]}
    (hsupp : ∀ p ∈ fs, p = 0 ∨ p = 1 ∨ p = X) :
    FamilyCompatible fs := by
  intro l hmem hnonneg
  have hsupp_l : ∀ ap ∈ l, ap.2 = 0 ∨ ap.2 = 1 ∨ ap.2 = X := by
    intro ap hap
    exact hsupp ap.2 (hmem ap hap)
  rcases weightedSum_supported_zero_one_X l hnonneg hsupp_l with
    ⟨a, b, ha, hb, hsum⟩
  rw [hsum]
  exact linear_zero_or_isRealRooted a b ha hb

theorem familyCompatible_of_supported_zero_X_XX
    {fs : List ℝ[X]}
    (hsupp : ∀ p ∈ fs, p = 0 ∨ p = X ∨ p = X * X) :
    FamilyCompatible fs := by
  intro l hmem hnonneg
  have hsupp_l : ∀ ap ∈ l, ap.2 = 0 ∨ ap.2 = X ∨ ap.2 = X * X := by
    intro ap hap
    exact hsupp ap.2 (hmem ap hap)
  rcases weightedSum_supported_zero_X_XX l hnonneg hsupp_l with
    ⟨a, b, ha, hb, hsum⟩
  rw [hsum]
  exact x_mul_linear_zero_or_isRealRooted a b ha hb

theorem list_sum_map_toList {ι M : Type} [AddCommMonoid M]
    (s : Finset ι) (f : ι → M) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  rw [Finset.sum_eq_multiset_sum]
  rw [← Multiset.sum_coe]
  simp

/-- The multiplicity of the zero-based letter `i`. -/
def count (α : Content) (i : Nat) : Nat :=
  α.getD i 0

/-- Decrement the multiplicity of the zero-based letter `i`, truncated at `0`. -/
def decAt (i : Nat) (α : Content) : Content :=
  α.modify i (fun n => n - 1)

theorem count_decAt_of_ne {α : Content} {i k : Nat} (hki : k ≠ i) :
    count (decAt k α) i = count α i := by
  simp [count, decAt, List.getD, List.getElem?_modify_ne _ _ hki]

theorem list_all_zero_eq_false_of_count_pos
    {α : Content} {i : Nat} (h : 0 < count α i) :
    α.all (fun n => n = 0) = false := by
  rw [List.all_eq_false]
  cases hopt : α[i]? with
  | none =>
      simp [count, List.getD, hopt] at h
  | some n =>
      have hnpos : 0 < n := by
        simpa [count, List.getD, hopt] using h
      refine ⟨n, ?_, ?_⟩
      · rw [List.mem_iff_getElem?]
        exact ⟨i, hopt⟩
      · simp [Nat.ne_of_gt hnpos]

/-- The monomial contribution of the boundary ascent from `a` to `b`. -/
def ascWeight (a b : Nat) : ℝ[X] :=
  if a < b then X else 1

theorem hasNonnegCoeffs_zero : HasNonnegCoeffs (0 : ℝ[X]) := by
  intro n
  simp

theorem hasNonnegCoeffs_X : HasNonnegCoeffs (X : ℝ[X]) := by
  intro n
  cases n with
  | zero =>
      simp [coeff_X_zero]
  | succ n =>
      cases n with
      | zero =>
          simp [coeff_X]
      | succ n =>
          simp [coeff_X]

theorem hasNonnegCoeffs_add {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p + q) := by
  intro n
  rw [coeff_add]
  exact add_nonneg (hp n) (hq n)

theorem hasNonnegCoeffs_finset_sum {ι : Type}
    (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    HasNonnegCoeffs (∑ i ∈ s, f i) := by
  intro n
  rw [finset_sum_coeff]
  exact Finset.sum_nonneg fun i hi => hf i hi n

theorem ascWeight_hasNonnegCoeffs (a b : Nat) :
    HasNonnegCoeffs (ascWeight a b) := by
  unfold ascWeight
  by_cases h : a < b
  · simpa [h] using hasNonnegCoeffs_X
  · simpa [h] using hasNonnegCoeffs_one

/--
`boundary lambda alpha a` is the ascent-generating polynomial for suffixes on
`lambda` with content `alpha`, with an extra boundary letter `a` immediately to
the left.  The ascent between `a` and the first suffix letter is included.
-/
def boundary : Board → Content → Nat → ℝ[X]
  | [], α, _ => if α.all (fun n => n = 0) then 1 else 0
  | m :: tail, α, a =>
      ∑ b ∈ Finset.range m,
        if 0 < count α b then
          ascWeight a b * boundary tail (decAt b α) b
        else
          0

theorem boundary_hasNonnegCoeffs :
    ∀ tail : Board, ∀ α : Content, ∀ a : Nat,
      HasNonnegCoeffs (boundary tail α a)
  | [], α, _ => by
      unfold boundary
      by_cases h : α.all (fun n => n = 0)
      · simpa [h] using hasNonnegCoeffs_one
      · simpa [h] using hasNonnegCoeffs_zero
  | m :: tail, α, a => by
      rw [boundary]
      apply hasNonnegCoeffs_finset_sum
      intro b hb
      by_cases h : 0 < count α b
      · have hterm :
            HasNonnegCoeffs
              (ascWeight a b * boundary tail (decAt b α) b) :=
          (ascWeight_hasNonnegCoeffs a b).mul
            (boundary_hasNonnegCoeffs tail (decAt b α) b)
        simpa [h] using hterm
      · simpa [h] using hasNonnegCoeffs_zero

/--
The zero-aware version of `B_i(lambda, beta - e_i)`.

If there is no `i` in `beta`, this is defined to be `0`; otherwise the content
is decremented and the boundary polynomial is evaluated with boundary `i`.
-/
def rowAfterDelete (tail : Board) (β : Content) (i : Nat) : ℝ[X] :=
  if 0 < count β i then boundary tail (decAt i β) i else 0

theorem rowAfterDelete_hasNonnegCoeffs
    (tail : Board) (β : Content) (i : Nat) :
    HasNonnegCoeffs (rowAfterDelete tail β i) := by
  unfold rowAfterDelete
  by_cases h : 0 < count β i
  · simpa [h] using boundary_hasNonnegCoeffs tail (decAt i β) i
  · simpa [h] using hasNonnegCoeffs_zero

theorem rowAfterDelete_hasPosLeadingCoeff_of_ne_zero
    {tail : Board} {β : Content} {i : Nat}
    (h0 : rowAfterDelete tail β i ≠ 0) :
    HasPosLeadingCoeff (rowAfterDelete tail β i) :=
  (rowAfterDelete_hasNonnegCoeffs tail β i).pos_leadingCoeff h0

theorem count_pos_of_rowAfterDelete_ne_zero
    {tail : Board} {β : Content} {i : Nat}
    (h0 : rowAfterDelete tail β i ≠ 0) :
    0 < count β i := by
  unfold rowAfterDelete at h0
  by_cases h : 0 < count β i
  · exact h
  · simp [h] at h0

theorem rowAfterDelete_nil_zero_or_isRealRooted
    (β : Content) (i : Nat) :
    rowAfterDelete [] β i = 0 ∨ IsRealRooted (rowAfterDelete [] β i) := by
  unfold rowAfterDelete
  by_cases h : 0 < count β i
  · rw [if_pos h]
    unfold boundary
    by_cases hall : (decAt i β).all (fun n => n = 0)
    · simpa [hall] using one_zero_or_isRealRooted
    · simp [hall]
  · rw [if_neg h]
    simp

def RowAfterDeleteRealRooted (tail : Board) : Prop :=
  ∀ β : Content, ∀ i : Nat,
    rowAfterDelete tail β i = 0 ∨ IsRealRooted (rowAfterDelete tail β i)

theorem rowAfterDeleteRealRooted_nil : RowAfterDeleteRealRooted [] :=
  rowAfterDelete_nil_zero_or_isRealRooted

theorem rowAfterDelete_nil_eq_zero_of_ne_pos
    {β : Content} {first other : Nat}
    (hne : first ≠ other) (hother : 0 < count β other) :
    rowAfterDelete [] β first = 0 := by
  have hcount : 0 < count (decAt first β) other := by
    simpa [count_decAt_of_ne hne] using hother
  have hall : (decAt first β).all (fun n => n = 0) = false :=
    list_all_zero_eq_false_of_count_pos hcount
  simp [rowAfterDelete, boundary, hall]

/-- The row-deletion boundary list indexed by the allowed first row letters. -/
def boundaryDeleteList (tail : Board) (m : Nat) (β : Content) : List ℝ[X] :=
  (Finset.range m).toList.map (fun j => rowAfterDelete tail β j)

theorem boundaryDeleteList_hasNonnegCoeffs
    {tail : Board} {m : Nat} {β : Content} {p : ℝ[X]}
    (hp : p ∈ boundaryDeleteList tail m β) :
    HasNonnegCoeffs p := by
  unfold boundaryDeleteList at hp
  rcases List.mem_map.mp hp with ⟨j, _hj, rfl⟩
  exact rowAfterDelete_hasNonnegCoeffs tail β j

/--
The first-entry refinement `R_j(lambda, alpha; t)`, recursively defined.

For a nonempty board `m :: lambda`, the first letter must be `< m` and present
in the content.  The remaining suffix is exactly a boundary polynomial.
-/
def refined : Board → Content → Nat → ℝ[X]
  | [], _, _ => 0
  | m :: tail, α, j => if j < m then rowAfterDelete tail α j else 0

theorem refined_hasNonnegCoeffs
    (board : Board) (α : Content) (j : Nat) :
    HasNonnegCoeffs (refined board α j) := by
  cases board with
  | nil =>
      simp [refined, hasNonnegCoeffs_zero]
  | cons m tail =>
      unfold refined
      by_cases h : j < m
      · simpa [h] using rowAfterDelete_hasNonnegCoeffs tail α j
      · simpa [h] using hasNonnegCoeffs_zero

/-- The total multiset rook-Eulerian polynomial. -/
def total : Board → Content → ℝ[X]
  | [], α => if α.all (fun n => n = 0) then 1 else 0
  | m :: tail, α => ∑ j ∈ Finset.range m, refined (m :: tail) α j

/-- First-entry refinements as a finite list, with zero entries included. -/
def refinedList : Board → Content → List ℝ[X]
  | [], _ => []
  | m :: tail, α => boundaryDeleteList tail m α

theorem refinedList_hasNonnegCoeffs
    {board : Board} {α : Content} {p : ℝ[X]}
    (hp : p ∈ refinedList board α) :
    HasNonnegCoeffs p := by
  cases board with
  | nil =>
      simp [refinedList] at hp
  | cons m tail =>
      exact boundaryDeleteList_hasNonnegCoeffs (tail := tail) (m := m)
        (β := α) hp

theorem refinedList_hasPosLeadingCoeff_of_ne_zero
    {board : Board} {α : Content} {p : ℝ[X]}
    (hp : p ∈ refinedList board α) (h0 : p ≠ 0) :
    HasPosLeadingCoeff p :=
  (refinedList_hasNonnegCoeffs hp).pos_leadingCoeff h0

theorem total_cons_eq_refinedList_sum
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = (refinedList (m :: tail) α).sum := by
  rw [total, refinedList, boundaryDeleteList, list_sum_map_toList]
  apply Finset.sum_congr rfl
  intro j hj
  simp [refined, Finset.mem_range.mp hj]

theorem total_cons_zero_or_isRealRooted_of_refinedList_familyCompatible
    {m : Nat} {tail : Board} {α : Content}
    (hfamily : FamilyCompatible (refinedList (m :: tail) α)) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  simpa [total_cons_eq_refinedList_sum] using
    sum_zero_or_isRealRooted_of_familyCompatible hfamily

@[simp] theorem count_def (α : Content) (i : Nat) :
    count α i = α.getD i 0 := rfl

@[simp] theorem boundary_nil (α : Content) (a : Nat) :
    boundary [] α a = if α.all (fun n => n = 0) then 1 else 0 := rfl

@[simp] theorem boundary_cons (m : Nat) (tail : Board) (α : Content) (a : Nat) :
    boundary (m :: tail) α a =
      ∑ b ∈ Finset.range m,
        if 0 < count α b then
          ascWeight a b * boundary tail (decAt b α) b
        else
          0 := rfl

@[simp] theorem refined_nil (α : Content) (j : Nat) :
    refined [] α j = 0 := rfl

@[simp] theorem refined_cons (m : Nat) (tail : Board) (α : Content) (j : Nat) :
    refined (m :: tail) α j =
      if j < m then rowAfterDelete tail α j else 0 := rfl

theorem refined_cons_of_lt {m : Nat} {tail : Board} {α : Content} {j : Nat}
    (hj : j < m) :
    refined (m :: tail) α j = rowAfterDelete tail α j := by
  simp [refined, hj]

theorem refined_cons_eq_boundary_of_lt_of_count_pos
    {m : Nat} {tail : Board} {α : Content} {j : Nat}
    (hj : j < m) (hαj : 0 < count α j) :
    refined (m :: tail) α j = boundary tail (decAt j α) j := by
  rw [refined_cons_of_lt hj]
  have hpos : 0 < α.getD j 0 := by
    simpa [count] using hαj
  have hne : ¬ α[j]?.getD 0 = 0 := by
    simpa [List.getD] using (Nat.ne_of_gt hpos)
  simp [rowAfterDelete, count, List.getD, hne]

/--
The one-step branch produced after removing first letter `first` and then
choosing second letter `next`.
-/
def branch (tail : Board) (β : Content) (first next : Nat) : ℝ[X] :=
  if 0 < count β first then
    ascWeight first next * rowAfterDelete tail (decAt first β) next
  else
    0

theorem branch_hasNonnegCoeffs
    (tail : Board) (β : Content) (first next : Nat) :
    HasNonnegCoeffs (branch tail β first next) := by
  unfold branch
  by_cases h : 0 < count β first
  · have hterm :
        HasNonnegCoeffs
          (ascWeight first next *
            rowAfterDelete tail (decAt first β) next) :=
      (ascWeight_hasNonnegCoeffs first next).mul
        (rowAfterDelete_hasNonnegCoeffs tail (decAt first β) next)
    have hget : 0 < β[first]?.getD 0 := by
      simpa [count] using h
    simpa [hget] using hterm
  · have hget : ¬ 0 < β[first]?.getD 0 := by
      simpa [count] using h
    simpa [hget] using hasNonnegCoeffs_zero

theorem branch_nil_eq_zero_or_one_or_X
    (β : Content) (first next : Nat) :
    branch [] β first next = 0 ∨
      branch [] β first next = 1 ∨
      branch [] β first next = X := by
  unfold branch
  by_cases hfirst : 0 < count β first
  · rw [if_pos hfirst]
    unfold rowAfterDelete
    by_cases hnext : 0 < count (decAt first β) next
    · rw [if_pos hnext]
      rw [boundary_nil]
      by_cases hall : (decAt next (decAt first β)).all (fun n => n = 0)
      · rw [if_pos hall]
        unfold ascWeight
        by_cases hlt : first < next
        · rw [if_pos hlt]
          simp
        · rw [if_neg hlt]
          simp
      · rw [if_neg hall]
        simp
    · rw [if_neg hnext]
      simp
  · rw [if_neg hfirst]
    simp

theorem branch_nil_eq_zero_of_other_pos
    {β : Content} {first next other : Nat}
    (hfirst_other : first ≠ other) (hnext_other : next ≠ other)
    (hother : 0 < count β other) :
    branch [] β first next = 0 := by
  have hcount1 : 0 < count (decAt first β) other := by
    rw [count_decAt_of_ne hfirst_other]
    exact hother
  have hcount2 : 0 < count (decAt next (decAt first β)) other := by
    rw [count_decAt_of_ne hnext_other]
    exact hcount1
  have hall : (decAt next (decAt first β)).all (fun n => n = 0) = false :=
    list_all_zero_eq_false_of_count_pos hcount2
  unfold branch rowAfterDelete
  by_cases hfirst : 0 < count β first
  · rw [if_pos hfirst]
    by_cases hnext : 0 < count (decAt first β) next
    · rw [if_pos hnext]
      simp [boundary, hall]
    · rw [if_neg hnext]
      simp
  · rw [if_neg hfirst]

theorem branch_nil_eq_zero_or_X_of_lt
    {β : Content} {first next : Nat} (hlt : first < next) :
    branch [] β first next = 0 ∨ branch [] β first next = X := by
  unfold branch rowAfterDelete
  by_cases hfirst : 0 < count β first
  · rw [if_pos hfirst]
    by_cases hnext : 0 < count (decAt first β) next
    · rw [if_pos hnext]
      rw [boundary_nil]
      by_cases hall : (decAt next (decAt first β)).all (fun n => n = 0)
      · rw [if_pos hall]
        simp [ascWeight, hlt]
      · rw [if_neg hall]
        simp
    · rw [if_neg hnext]
      simp
  · rw [if_neg hfirst]
    simp

theorem shifted_branch_nil_eq_zero_or_X_or_XX
    (β : Content) (first next : Nat) :
    X * branch [] β first next = 0 ∨
      X * branch [] β first next = X ∨
      X * branch [] β first next = X * X := by
  rcases branch_nil_eq_zero_or_one_or_X β first next with h | h | h
  · left
    simp [h]
  · right
    left
    simp [h]
  · right
    right
    simp [h]

theorem shifted_branch_nil_eq_zero_or_X_of_not_lt
    {β : Content} {first next : Nat} (hlt : ¬ first < next) :
    X * branch [] β first next = 0 ∨
      X * branch [] β first next = X := by
  unfold branch rowAfterDelete
  by_cases hfirst : 0 < count β first
  · rw [if_pos hfirst]
    by_cases hnext : 0 < count (decAt first β) next
    · rw [if_pos hnext]
      rw [boundary_nil]
      by_cases hall : (decAt next (decAt first β)).all (fun n => n = 0)
      · rw [if_pos hall]
        simp [ascWeight, hlt]
      · rw [if_neg hall]
        simp
    · rw [if_neg hnext]
      simp
  · rw [if_neg hfirst]
    simp

/-- The branch polynomials appearing in a row-deletion recurrence. -/
def branchList (tail : Board) (m : Nat) (β : Content) (first : Nat) :
    List ℝ[X] :=
  (Finset.range m).toList.map (fun next => branch tail β first next)

/-- The same branch list after multiplying each branch by `X`. -/
def shiftedBranchList (tail : Board) (m : Nat) (β : Content) (first : Nat) :
    List ℝ[X] :=
  (Finset.range m).toList.map (fun next => X * branch tail β first next)

theorem branchList_hasNonnegCoeffs
    {tail : Board} {m : Nat} {β : Content} {first : Nat} {p : ℝ[X]}
    (hp : p ∈ branchList tail m β first) :
    HasNonnegCoeffs p := by
  unfold branchList at hp
  rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
  exact branch_hasNonnegCoeffs tail β first next

theorem shiftedBranchList_hasNonnegCoeffs
    {tail : Board} {m : Nat} {β : Content} {first : Nat} {p : ℝ[X]}
    (hp : p ∈ shiftedBranchList tail m β first) :
    HasNonnegCoeffs p := by
  unfold shiftedBranchList at hp
  rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
  exact hasNonnegCoeffs_X.mul
    (branch_hasNonnegCoeffs tail β first next)

theorem branchList_sum (tail : Board) (m : Nat) (β : Content) (first : Nat) :
    (branchList tail m β first).sum =
      ∑ next ∈ Finset.range m, branch tail β first next := by
  exact list_sum_map_toList (Finset.range m) (fun next => branch tail β first next)

theorem shiftedBranchList_sum (tail : Board) (m : Nat) (β : Content) (first : Nat) :
    (shiftedBranchList tail m β first).sum =
      X * (branchList tail m β first).sum := by
  rw [shiftedBranchList, branchList]
  rw [list_sum_map_toList, list_sum_map_toList]
  rw [Finset.mul_sum]

/--
Formal row-deletion recurrence for `rowAfterDelete`.

This is the corrected replacement for the invalid fixed-content matrix input:
the content is first decremented at `first`, and only then the sum over the next
letter is formed.
-/
theorem rowAfterDelete_cons (m : Nat) (tail : Board) (β : Content) (first : Nat) :
    rowAfterDelete (m :: tail) β first =
      ∑ next ∈ Finset.range m, branch tail β first next := by
  by_cases hfirst : 0 < count β first
  · simp [rowAfterDelete, branch, boundary, mul_ite]
  · simp [rowAfterDelete, branch]

theorem rowAfterDelete_cons_list
    (m : Nat) (tail : Board) (β : Content) (first : Nat) :
    rowAfterDelete (m :: tail) β first =
      (branchList tail m β first).sum := by
  rw [rowAfterDelete_cons, branchList_sum]

/--
Pairwise boundary compatibility: this is the compatibility form of
`B_k(lambda,beta-e_k) \preceq B_i(lambda,beta-e_i)` for `i < k`.
-/
def BoundaryPairCompatible (tail : Board) : Prop :=
  ∀ β : Content, ∀ i k : Nat, i < k →
    0 < count β k → 0 < count β i →
    Compatible (rowAfterDelete tail β k) (rowAfterDelete tail β i) ∧
    Compatible (X * rowAfterDelete tail β k) (rowAfterDelete tail β i)

theorem boundaryPairCompatible_nil : BoundaryPairCompatible [] := by
  intro β i k hik hβk hβi
  have hki : k ≠ i := by omega
  have hik_ne : i ≠ k := by omega
  have hk_zero : rowAfterDelete [] β k = 0 :=
    rowAfterDelete_nil_eq_zero_of_ne_pos hki hβi
  have hi_zero : rowAfterDelete [] β i = 0 :=
    rowAfterDelete_nil_eq_zero_of_ne_pos hik_ne hβk
  constructor
  · simpa [hk_zero, hi_zero] using compatible_zero_zero
  · simpa [hk_zero, hi_zero] using compatible_zero_zero

/--
The corresponding compatibility statement for first-entry refinements, with
zero entries ignored.  The hypotheses `0 < count alpha k` and
`0 < count alpha i` are the content-side eligibility conditions.
-/
def RefinedPairCompatible (tail : Board) : Prop :=
  ∀ α : Content, ∀ i k : Nat, i < k →
    k < (match tail with | [] => 0 | m :: _ => m) →
    0 < count α k → 0 < count α i →
    Compatible (refined tail α k) (refined tail α i) ∧
    Compatible (X * refined tail α k) (refined tail α i)

theorem refinedList_all_pairs_compatible_of_refinedPairCompatible
    {m : Nat} {tail : Board} {α : Content}
    (hrefined : RefinedPairCompatible (m :: tail))
    (hrr : ∀ p ∈ refinedList (m :: tail) α, p = 0 ∨ IsRealRooted p) :
    ∀ f ∈ refinedList (m :: tail) α,
      ∀ g ∈ refinedList (m :: tail) α, Compatible f g := by
  intro f hf g hg
  by_cases hf0 : f = 0
  · subst f
    exact compatible_zero_left_of_zero_or_isRealRooted (hrr g hg)
  by_cases hg0 : g = 0
  · subst g
    exact compatible_zero_right_of_zero_or_isRealRooted (hrr f hf)
  rw [refinedList, boundaryDeleteList] at hf hg
  rcases List.mem_map.mp hf with ⟨a, ha_mem, rfl⟩
  rcases List.mem_map.mp hg with ⟨b, hb_mem, rfl⟩
  have ha_range : a ∈ Finset.range m := by
    exact Finset.mem_toList.mp ha_mem
  have hb_range : b ∈ Finset.range m := by
    exact Finset.mem_toList.mp hb_mem
  have ha_lt : a < m := Finset.mem_range.mp ha_range
  have hb_lt : b < m := Finset.mem_range.mp hb_range
  have hαa : 0 < count α a :=
    count_pos_of_rowAfterDelete_ne_zero hf0
  have hαb : 0 < count α b :=
    count_pos_of_rowAfterDelete_ne_zero hg0
  by_cases hab : a = b
  · subst b
    exact compatible_self_of_zero_or_isRealRooted
      (hrr (rowAfterDelete tail α a)
        (by
          rw [refinedList, boundaryDeleteList]
          exact List.mem_map.mpr ⟨a, ha_mem, rfl⟩))
  · rcases Nat.lt_or_gt_of_ne hab with hab_lt | hba_lt
    · have hpair := hrefined α a b hab_lt hb_lt hαb hαa
      simpa [refined, ha_lt, hb_lt] using hpair.1.comm
    · have hpair := hrefined α b a hba_lt ha_lt hαa hαb
      simpa [refined, ha_lt, hb_lt] using hpair.1

theorem refinedList_pairwiseCompatible_of_refinedPairCompatible
    {m : Nat} {tail : Board} {α : Content}
    (hrefined : RefinedPairCompatible (m :: tail))
    (hrr : ∀ p ∈ refinedList (m :: tail) α, p = 0 ∨ IsRealRooted p) :
    PairwiseCompatible (refinedList (m :: tail) α) :=
  pairwiseCompatible_of_all_pairs
    (refinedList_all_pairs_compatible_of_refinedPairCompatible
      hrefined hrr)

/--
Zero-aware Chudnovsky--Seymour finite-family upgrade in the local language of
this file.  The nonnegative-coefficient hypothesis is included so nonzero
entries can later be converted to positive leading coefficient entries before
applying the existing strict CS theorem.
-/
def ZeroAwarePairwiseToFamilyCompatible : Prop :=
  ∀ fs : List ℝ[X],
    (∀ p ∈ fs, HasNonnegCoeffs p) →
    (∀ p ∈ fs, p = 0 ∨ IsRealRooted p) →
    PairwiseCompatible fs →
    FamilyCompatible fs

/-- A slightly stronger but easier-to-use zero-aware CS wrapper. -/
def ZeroAwareAllPairsToFamilyCompatible : Prop :=
  ∀ fs : List ℝ[X],
    (∀ p ∈ fs, HasNonnegCoeffs p) →
    (∀ p ∈ fs, p = 0 ∨ IsRealRooted p) →
    (∀ f ∈ fs, ∀ g ∈ fs, Compatible f g) →
    FamilyCompatible fs

theorem zeroAwareAllPairsToFamilyCompatible_of_pairBridgePos
    (htwo : _root_.RealRooted.CompatiblePairHasCommonInterleaverStatement) :
    ZeroAwareAllPairsToFamilyCompatible := by
  intro fs hnn hrr hall
  classical
  let fs' := fs.filter (fun p => p ≠ 0)
  have hrr' : ∀ p ∈ fs', IsRealRooted p := by
    intro p hp
    rcases List.mem_filter.mp hp with ⟨hpfs, hpne_dec⟩
    have hpne : p ≠ 0 := of_decide_eq_true hpne_dec
    rcases hrr p hpfs with hp0 | hpRR
    · exact False.elim (hpne hp0)
    · exact hpRR
  have hpos' : ∀ p ∈ fs', HasPosLeadingCoeff p := by
    intro p hp
    rcases List.mem_filter.mp hp with ⟨hpfs, hpne_dec⟩
    have hpne : p ≠ 0 := of_decide_eq_true hpne_dec
    exact (hnn p hpfs).pos_leadingCoeff hpne
  have hpair' : _root_.RealRooted.PairwiseCompatible fs' := by
    intro i j _hij
    apply globalCompatible_of_compatible
    have hi_mem_filter : fs'.get i ∈ fs' := List.get_mem fs' i
    have hj_mem_filter : fs'.get j ∈ fs' := List.get_mem fs' j
    have hi_mem : fs'.get i ∈ fs :=
      (List.mem_filter.mp hi_mem_filter).1
    have hj_mem : fs'.get j ∈ fs :=
      (List.mem_filter.mp hj_mem_filter).1
    exact hall (fs'.get i) hi_mem (fs'.get j) hj_mem
  have hglobalFamily :
      _root_.RealRooted.FamilyCompatible fs' :=
    ((_root_.RealRooted.pairwiseCompatible_iff_familyCompatible_of_pairBridgePos
      hrr' hpos' htwo).mp hpair')
  exact familyCompatible_of_filter_ne_zero
    (by
      simpa [fs'] using
        familyCompatible_of_globalFamilyCompatible hglobalFamily)

/--
The separate singleton real-rootedness input needed for refined lists.  This is
not automatic from the `i < k` pair conditions when the list has only one
nonzero entry.
-/
def RefinedListRealRootedOfPairCompatible : Prop :=
  ∀ m : Nat, ∀ tail : Board, ∀ α : Content,
    RefinedPairCompatible (m :: tail) →
      ∀ p ∈ refinedList (m :: tail) α, p = 0 ∨ IsRealRooted p

/--
The external Chudnovsky--Seymour upgrade needed at the end of the proof:
the refined pair conditions for a nonempty board imply full compatibility of
the finite first-entry family.
-/
def RefinedPairToFamilyCompatible : Prop :=
  ∀ m : Nat, ∀ tail : Board, ∀ α : Content,
    RefinedPairCompatible (m :: tail) →
      FamilyCompatible (refinedList (m :: tail) α)

theorem refinedPairToFamilyCompatible_of_zeroAwarePairwiseToFamily
    (hCS : ZeroAwarePairwiseToFamilyCompatible)
    (hrr : RefinedListRealRootedOfPairCompatible) :
    RefinedPairToFamilyCompatible := by
  intro m tail α hrefined
  exact hCS (refinedList (m :: tail) α)
    (fun p hp => refinedList_hasNonnegCoeffs hp)
    (hrr m tail α hrefined)
    (refinedList_pairwiseCompatible_of_refinedPairCompatible
      hrefined (hrr m tail α hrefined))

theorem refinedPairToFamilyCompatible_of_zeroAwareAllPairsToFamily
    (hCS : ZeroAwareAllPairsToFamilyCompatible)
    (hrr : RefinedListRealRootedOfPairCompatible) :
    RefinedPairToFamilyCompatible := by
  intro m tail α hrefined
  exact hCS (refinedList (m :: tail) α)
    (fun p hp => refinedList_hasNonnegCoeffs hp)
    (hrr m tail α hrefined)
    (refinedList_all_pairs_compatible_of_refinedPairCompatible
      hrefined (hrr m tail α hrefined))

/--
Boundary compatibility for the tail implies refined compatibility after
prepending a row.  This is the formal version of the main repair: the target
row `k` uses the content `alpha - e_k`, and the target row `i` uses
`alpha - e_i`.
-/
theorem refinedPairCompatible_cons_of_boundaryPairCompatible
    {m : Nat} {tail : Board}
    (htail : BoundaryPairCompatible tail) :
    RefinedPairCompatible (m :: tail) := by
  intro α i k hik hk hαk hαi
  have hi : i < m := lt_trans hik hk
  have hpair := htail α i k hik hαk hαi
  simpa [refined, hk, hi] using hpair

/--
The branch family obtained before summing over the second deleted letter.

This packet is useful as a diagnostic, but it is too strong as an induction
target: the individual branch family need not be compatible, even when the two
summed boundary rows are compatible.  The live proof target below is therefore
`BoundaryRowStepCompatible`, which keeps the second-letter sum intact.
-/
def transferFamily (tail : Board) (m : Nat) (β : Content) (i k : Nat) :
    List ℝ[X] :=
  branchList tail m β k ++ branchList tail m β i

/-- Shift only the `k`-branch in the transfer family. -/
def shiftedTransferFamily (tail : Board) (m : Nat) (β : Content) (i k : Nat) :
    List ℝ[X] :=
  shiftedBranchList tail m β k ++ branchList tail m β i

theorem transferFamily_hasNonnegCoeffs
    {tail : Board} {m : Nat} {β : Content} {i k : Nat} {p : ℝ[X]}
    (hp : p ∈ transferFamily tail m β i k) :
    HasNonnegCoeffs p := by
  rw [transferFamily, List.mem_append] at hp
  rcases hp with hp | hp
  · exact branchList_hasNonnegCoeffs hp
  · exact branchList_hasNonnegCoeffs hp

theorem shiftedTransferFamily_hasNonnegCoeffs
    {tail : Board} {m : Nat} {β : Content} {i k : Nat} {p : ℝ[X]}
    (hp : p ∈ shiftedTransferFamily tail m β i k) :
    HasNonnegCoeffs p := by
  rw [shiftedTransferFamily, List.mem_append] at hp
  rcases hp with hp | hp
  · exact shiftedBranchList_hasNonnegCoeffs hp
  · exact branchList_hasNonnegCoeffs hp

theorem transferFamily_hasPosLeadingCoeff_of_ne_zero
    {tail : Board} {m : Nat} {β : Content} {i k : Nat} {p : ℝ[X]}
    (hp : p ∈ transferFamily tail m β i k) (h0 : p ≠ 0) :
    HasPosLeadingCoeff p :=
  (transferFamily_hasNonnegCoeffs hp).pos_leadingCoeff h0

theorem shiftedTransferFamily_hasPosLeadingCoeff_of_ne_zero
    {tail : Board} {m : Nat} {β : Content} {i k : Nat} {p : ℝ[X]}
    (hp : p ∈ shiftedTransferFamily tail m β i k) (h0 : p ≠ 0) :
    HasPosLeadingCoeff p :=
  (shiftedTransferFamily_hasNonnegCoeffs hp).pos_leadingCoeff h0

theorem transferFamily_nil_supported_zero_one_X
    (m : Nat) (β : Content) (i k : Nat) :
    ∀ p ∈ transferFamily [] m β i k, p = 0 ∨ p = 1 ∨ p = X := by
  intro p hp
  rw [transferFamily, branchList, List.mem_append] at hp
  rcases hp with hp | hp
  · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
    exact branch_nil_eq_zero_or_one_or_X β k next
  · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
    exact branch_nil_eq_zero_or_one_or_X β i next

theorem shiftedTransferFamily_nil_familyCompatible
    (m : Nat) (β : Content) (i k : Nat) (hik : i < k) :
    FamilyCompatible (shiftedTransferFamily [] m β i k) := by
  by_cases hi : 0 < count β i
  · by_cases hk : 0 < count β k
    · apply familyCompatible_of_supported_zero_X_XX
      intro p hp
      have hik_ne : i ≠ k := by omega
      rw [shiftedTransferFamily, shiftedBranchList, branchList, List.mem_append] at hp
      rcases hp with hp | hp
      · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
        by_cases hnext : next = i
        · subst next
          rcases shifted_branch_nil_eq_zero_or_X_of_not_lt
              (β := β) (first := k) (next := i) (by omega) with h | h
          · left
            exact h
          · right
            left
            exact h
        · have hzero : branch [] β k next = 0 :=
            branch_nil_eq_zero_of_other_pos
              (β := β) (first := k) (next := next) (other := i)
              (by omega) hnext hi
          left
          simp [hzero]
      · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
        by_cases hnext : next = k
        · subst next
          rcases branch_nil_eq_zero_or_X_of_lt
              (β := β) (first := i) (next := k) hik with h | h
          · left
            exact h
          · right
            left
            exact h
        · have hzero : branch [] β i next = 0 :=
            branch_nil_eq_zero_of_other_pos
              (β := β) (first := i) (next := next) (other := k)
              hik_ne hnext hk
          left
          exact hzero
    · apply familyCompatible_of_supported_zero_one_X
      intro p hp
      rw [shiftedTransferFamily, shiftedBranchList, branchList, List.mem_append] at hp
      rcases hp with hp | hp
      · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
        have hzero : branch [] β k next = 0 := by
          unfold branch
          rw [if_neg hk]
        left
        simp [hzero]
      · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
        exact branch_nil_eq_zero_or_one_or_X β i next
  · apply familyCompatible_of_supported_zero_X_XX
    intro p hp
    rw [shiftedTransferFamily, shiftedBranchList, branchList, List.mem_append] at hp
    rcases hp with hp | hp
    · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
      exact shifted_branch_nil_eq_zero_or_X_or_XX β k next
    · rcases List.mem_map.mp hp with ⟨next, _hnext, rfl⟩
      have hzero : branch [] β i next = 0 := by
        unfold branch
        rw [if_neg hi]
      left
      exact hzero

/--
An over-strong transfer-family obligation.  It is retained because several
formal consequences below are useful regression tests, but this is no longer
the intended proof obligation.
-/
def TransferCompatible (tail : Board) : Prop :=
  ∀ m : Nat, ∀ β : Content, ∀ i k : Nat, i < k →
    FamilyCompatible (transferFamily tail m β i k) ∧
    FamilyCompatible (shiftedTransferFamily tail m β i k)

def TransferRowCompatible (tail : Board) : Prop :=
  TransferCompatible tail ∧ RowAfterDeleteRealRooted tail

theorem transferCompatible_nil : TransferCompatible [] := by
  intro m β i k hik
  constructor
  · exact familyCompatible_of_supported_zero_one_X
      (transferFamily_nil_supported_zero_one_X m β i k)
  · exact shiftedTransferFamily_nil_familyCompatible m β i k hik

theorem transferRowCompatible_nil : TransferRowCompatible [] :=
  ⟨transferCompatible_nil, rowAfterDeleteRealRooted_nil⟩

/-- The one-row induction step for the transfer lemma. -/
def TransferStepCompatible : Prop :=
  ∀ m : Nat, ∀ tail : Board,
    TransferCompatible tail → TransferCompatible (m :: tail)

/-- Strengthened one-row step carrying the singleton real-rootedness packet. -/
def TransferRowStepCompatible : Prop :=
  ∀ m : Nat, ∀ tail : Board,
    TransferRowCompatible tail → TransferRowCompatible (m :: tail)

theorem transferCompatible_all_of_base_step
    (hbase : TransferCompatible [])
    (hstep : TransferStepCompatible) :
    ∀ tail : Board, TransferCompatible tail := by
  intro tail
  induction tail with
  | nil =>
      exact hbase
  | cons m tail ih =>
      exact hstep m tail ih

theorem transferCompatible_all_of_step
    (hstep : TransferStepCompatible) :
    ∀ tail : Board, TransferCompatible tail :=
  transferCompatible_all_of_base_step transferCompatible_nil hstep

theorem rowAfterDelete_cons_zero_or_isRealRooted_of_transferCompatible
    {m : Nat} {tail : Board}
    (htransfer : TransferCompatible tail)
    (hrr_tail : RowAfterDeleteRealRooted tail) :
    RowAfterDeleteRealRooted (m :: tail) := by
  intro β first
  cases m with
  | zero =>
      rw [rowAfterDelete_cons]
      simp
  | succ m' =>
      cases m' with
      | zero =>
          rw [rowAfterDelete_cons]
          by_cases hfirst : 0 < count β first
          · have hget : 0 < β[first]?.getD 0 := by
              simpa [count] using hfirst
            simpa [branch, ascWeight, hget] using
              hrr_tail (decAt first β) 0
          · have hget : ¬ 0 < β[first]?.getD 0 := by
              simpa [count] using hfirst
            left
            simp [branch, hget]
      | succ m'' =>
          let m2 := Nat.succ (Nat.succ m'')
          by_cases hfirst0 : first = 0
          · subst first
            have hfamilies := htransfer m2 β 0 1 (by omega)
            have hbranch :
                FamilyCompatible (branchList tail m2 β 0) := by
              have hright := familyCompatible_right_of_append
                (left := branchList tail m2 β 1)
                (right := branchList tail m2 β 0)
                hfamilies.1
              simpa [transferFamily, m2] using hright
            simpa [m2, rowAfterDelete_cons_list] using
              sum_zero_or_isRealRooted_of_familyCompatible hbranch
          · have hfirst_pos : 0 < first := Nat.pos_of_ne_zero hfirst0
            have hfamilies := htransfer m2 β 0 first hfirst_pos
            have hbranch :
                FamilyCompatible (branchList tail m2 β first) := by
              have hleft := familyCompatible_left_of_append
                (left := branchList tail m2 β first)
                (right := branchList tail m2 β 0)
                hfamilies.1
              simpa [transferFamily, m2] using hleft
            simpa [m2, rowAfterDelete_cons_list] using
              sum_zero_or_isRealRooted_of_familyCompatible hbranch

theorem rowAfterDelete_zero_or_isRealRooted_all_of_transfer_step
    (hstep : TransferStepCompatible) :
    ∀ tail : Board, ∀ β : Content, ∀ i : Nat,
      rowAfterDelete tail β i = 0 ∨
        IsRealRooted (rowAfterDelete tail β i) := by
  intro tail
  induction tail with
  | nil =>
      exact rowAfterDelete_nil_zero_or_isRealRooted
  | cons m tail ih =>
      exact rowAfterDelete_cons_zero_or_isRealRooted_of_transferCompatible
        (m := m) (tail := tail)
        (transferCompatible_all_of_step hstep tail) ih

theorem transferRowCompatible_all_of_step
    (hstep : TransferRowStepCompatible) :
    ∀ tail : Board, TransferRowCompatible tail := by
  intro tail
  induction tail with
  | nil =>
      exact transferRowCompatible_nil
  | cons m tail ih =>
      exact hstep m tail ih

theorem transferCompatible_all_of_transferRow_step
    (hstep : TransferRowStepCompatible) :
    ∀ tail : Board, TransferCompatible tail := by
  intro tail
  exact (transferRowCompatible_all_of_step hstep tail).1

theorem rowAfterDeleteRealRooted_all_of_transferRow_step
    (hstep : TransferRowStepCompatible) :
    ∀ tail : Board, RowAfterDeleteRealRooted tail := by
  intro tail
  exact (transferRowCompatible_all_of_step hstep tail).2

theorem refinedListRealRootedOfPairCompatible_of_transfer_step
    (hstep : TransferStepCompatible) :
    RefinedListRealRootedOfPairCompatible := by
  intro m tail α _hrefined p hp
  rw [refinedList, boundaryDeleteList] at hp
  rcases List.mem_map.mp hp with ⟨j, _hj, rfl⟩
  exact rowAfterDelete_zero_or_isRealRooted_all_of_transfer_step
    hstep tail α j

theorem refinedListRealRootedOfPairCompatible_of_transferRow_step
    (hstep : TransferRowStepCompatible) :
    RefinedListRealRootedOfPairCompatible := by
  intro m tail α _hrefined p hp
  rw [refinedList, boundaryDeleteList] at hp
  rcases List.mem_map.mp hp with ⟨j, _hj, rfl⟩
  exact rowAfterDeleteRealRooted_all_of_transferRow_step hstep tail α j

/--
The transfer-family obligation is exactly strong enough to propagate boundary
pair compatibility through one prepended row.
-/
theorem boundaryPairCompatible_cons_of_transferCompatible
    {m : Nat} {tail : Board}
    (htransfer : TransferCompatible tail) :
    BoundaryPairCompatible (m :: tail) := by
  intro β i k hik _hβk _hβi
  have hfamilies := htransfer m β i k hik
  constructor
  · have hcompat :
        Compatible
          (branchList tail m β k).sum
          (branchList tail m β i).sum :=
      compatible_sum_pair_of_familyCompatible hfamilies.1
    simpa [rowAfterDelete_cons_list, transferFamily] using hcompat
  · have hcompat :
        Compatible
          (shiftedBranchList tail m β k).sum
          (branchList tail m β i).sum :=
      compatible_sum_pair_of_familyCompatible hfamilies.2
    simpa [rowAfterDelete_cons_list, shiftedTransferFamily,
      shiftedBranchList_sum] using hcompat

theorem boundaryPairCompatible_all_of_transferCompatible_all
    (hbase : BoundaryPairCompatible [])
    (htransfer : ∀ tail : Board, TransferCompatible tail) :
    ∀ tail : Board, BoundaryPairCompatible tail := by
  intro tail
  cases tail with
  | nil =>
      exact hbase
  | cons m rest =>
      exact boundaryPairCompatible_cons_of_transferCompatible
        (m := m) (tail := rest) (htransfer rest)

theorem boundaryPairCompatible_all_of_transfer_step
    (hstep : TransferStepCompatible) :
    ∀ tail : Board, BoundaryPairCompatible tail :=
  boundaryPairCompatible_all_of_transferCompatible_all
    boundaryPairCompatible_nil (transferCompatible_all_of_step hstep)

theorem boundaryPairCompatible_all_of_transferRow_step
    (hstep : TransferRowStepCompatible) :
    ∀ tail : Board, BoundaryPairCompatible tail :=
  boundaryPairCompatible_all_of_transferCompatible_all
    boundaryPairCompatible_nil
    (transferCompatible_all_of_transferRow_step hstep)

theorem refinedPairCompatible_cons_of_transferCompatible_all
    (hboundaryBase : BoundaryPairCompatible [])
    (htransfer : ∀ tail : Board, TransferCompatible tail)
    (m : Nat) (tail : Board) :
    RefinedPairCompatible (m :: tail) := by
  exact refinedPairCompatible_cons_of_boundaryPairCompatible
    (boundaryPairCompatible_all_of_transferCompatible_all
      hboundaryBase htransfer tail)

theorem refinedPairCompatible_cons_of_base_step
    (hboundaryBase : BoundaryPairCompatible [])
    (htransferBase : TransferCompatible [])
    (hstep : TransferStepCompatible)
    (m : Nat) (tail : Board) :
    RefinedPairCompatible (m :: tail) := by
  exact refinedPairCompatible_cons_of_transferCompatible_all
    hboundaryBase
    (transferCompatible_all_of_base_step htransferBase hstep)
    m tail

theorem refinedPairCompatible_cons_of_transfer_base_step
    (htransferBase : TransferCompatible [])
    (hstep : TransferStepCompatible)
    (m : Nat) (tail : Board) :
    RefinedPairCompatible (m :: tail) := by
  exact refinedPairCompatible_cons_of_base_step
    boundaryPairCompatible_nil htransferBase hstep m tail

theorem refinedPairCompatible_cons_of_transfer_step
    (hstep : TransferStepCompatible)
    (m : Nat) (tail : Board) :
    RefinedPairCompatible (m :: tail) := by
  exact refinedPairCompatible_cons_of_transfer_base_step
    transferCompatible_nil hstep m tail

theorem refinedPairCompatible_cons_of_transferRow_step
    (hstep : TransferRowStepCompatible)
    (m : Nat) (tail : Board) :
    RefinedPairCompatible (m :: tail) := by
  exact refinedPairCompatible_cons_of_transferCompatible_all
    boundaryPairCompatible_nil
    (transferCompatible_all_of_transferRow_step hstep)
    m tail

theorem total_cons_zero_or_isRealRooted_of_proof_obligations
    (hboundaryBase : BoundaryPairCompatible [])
    (htransferBase : TransferCompatible [])
    (hstep : TransferStepCompatible)
    (hpairToFamily : RefinedPairToFamilyCompatible)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  have hrefined : RefinedPairCompatible (m :: tail) :=
    refinedPairCompatible_cons_of_base_step
      hboundaryBase htransferBase hstep m tail
  exact total_cons_zero_or_isRealRooted_of_refinedList_familyCompatible
    (hpairToFamily m tail α hrefined)

theorem total_cons_zero_or_isRealRooted_of_transfer_obligations
    (htransferBase : TransferCompatible [])
    (hstep : TransferStepCompatible)
    (hpairToFamily : RefinedPairToFamilyCompatible)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  exact total_cons_zero_or_isRealRooted_of_proof_obligations
    boundaryPairCompatible_nil htransferBase hstep hpairToFamily m tail α

theorem total_cons_zero_or_isRealRooted_of_transfer_step
    (hstep : TransferStepCompatible)
    (hpairToFamily : RefinedPairToFamilyCompatible)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  exact total_cons_zero_or_isRealRooted_of_transfer_obligations
    transferCompatible_nil hstep hpairToFamily m tail α

theorem total_cons_zero_or_isRealRooted_of_transfer_step_and_zeroAwareCS
    (hstep : TransferStepCompatible)
    (hCS : ZeroAwarePairwiseToFamilyCompatible)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  exact total_cons_zero_or_isRealRooted_of_transfer_step hstep
    (refinedPairToFamilyCompatible_of_zeroAwarePairwiseToFamily
      hCS (refinedListRealRootedOfPairCompatible_of_transfer_step hstep))
    m tail α

theorem total_cons_zero_or_isRealRooted_of_transfer_step_and_pairBridge
    (hstep : TransferStepCompatible)
    (htwo : _root_.RealRooted.CompatiblePairHasCommonInterleaverStatement)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  exact total_cons_zero_or_isRealRooted_of_transfer_step hstep
    (refinedPairToFamilyCompatible_of_zeroAwareAllPairsToFamily
      (zeroAwareAllPairsToFamilyCompatible_of_pairBridgePos htwo)
      (refinedListRealRootedOfPairCompatible_of_transfer_step hstep))
    m tail α

theorem total_cons_zero_or_isRealRooted_of_transferRow_step_and_pairBridge
    (hstep : TransferRowStepCompatible)
    (htwo : _root_.RealRooted.CompatiblePairHasCommonInterleaverStatement)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  have hrefined : RefinedPairCompatible (m :: tail) :=
    refinedPairCompatible_cons_of_transferRow_step hstep m tail
  have hpairToFamily : RefinedPairToFamilyCompatible :=
    refinedPairToFamilyCompatible_of_zeroAwareAllPairsToFamily
      (zeroAwareAllPairsToFamilyCompatible_of_pairBridgePos htwo)
      (refinedListRealRootedOfPairCompatible_of_transferRow_step hstep)
  exact total_cons_zero_or_isRealRooted_of_refinedList_familyCompatible
    (hpairToFamily m tail α hrefined)

/--
The summed induction packet.  It packages exactly the information that would
be needed after one first-row deletion:

* pairwise boundary compatibility for every coupled content;
* singleton real-rootedness for each boundary row.

Unlike `TransferCompatible`, this statement does not ask the unsummed
second-letter branches to be compatible.  Expanded recurrence diagnostics now
show that even this boundary packet is too strong as a universal theorem, so
the definitions below should be read as conditional interfaces/regression
targets rather than the final paper statement.
-/
def BoundaryRowCompatible (tail : Board) : Prop :=
  BoundaryPairCompatible tail ∧ RowAfterDeleteRealRooted tail

theorem boundaryRowCompatible_nil : BoundaryRowCompatible [] :=
  ⟨boundaryPairCompatible_nil, rowAfterDeleteRealRooted_nil⟩

/-- A candidate row-induction theorem in the summed boundary language.

This is known to be too strong for unrestricted contents; see
`MULTISET_NOTES.md` in the paper workspace for the current counterexample
ledger.
-/
def BoundaryRowStepCompatible : Prop :=
  ∀ m : Nat, ∀ tail : Board,
    BoundaryRowCompatible tail → BoundaryRowCompatible (m :: tail)

theorem boundaryRowCompatible_all_of_boundaryRow_step
    (hstep : BoundaryRowStepCompatible) :
    ∀ tail : Board, BoundaryRowCompatible tail := by
  intro tail
  induction tail with
  | nil =>
      exact boundaryRowCompatible_nil
  | cons m tail ih =>
      exact hstep m tail ih

theorem boundaryPairCompatible_all_of_boundaryRow_step
    (hstep : BoundaryRowStepCompatible) :
    ∀ tail : Board, BoundaryPairCompatible tail := by
  intro tail
  exact (boundaryRowCompatible_all_of_boundaryRow_step hstep tail).1

theorem rowAfterDeleteRealRooted_all_of_boundaryRow_step
    (hstep : BoundaryRowStepCompatible) :
    ∀ tail : Board, RowAfterDeleteRealRooted tail := by
  intro tail
  exact (boundaryRowCompatible_all_of_boundaryRow_step hstep tail).2

theorem refinedListRealRootedOfPairCompatible_of_boundaryRow_step
    (hstep : BoundaryRowStepCompatible) :
    RefinedListRealRootedOfPairCompatible := by
  intro m tail α _hrefined p hp
  rw [refinedList, boundaryDeleteList] at hp
  rcases List.mem_map.mp hp with ⟨j, _hj, rfl⟩
  exact rowAfterDeleteRealRooted_all_of_boundaryRow_step hstep tail α j

theorem refinedPairCompatible_cons_of_boundaryRow_step
    (hstep : BoundaryRowStepCompatible)
    (m : Nat) (tail : Board) :
    RefinedPairCompatible (m :: tail) := by
  exact refinedPairCompatible_cons_of_boundaryPairCompatible
    ((boundaryRowCompatible_all_of_boundaryRow_step hstep tail).1)

theorem total_cons_zero_or_isRealRooted_of_boundaryRow_step_and_pairBridge
    (hstep : BoundaryRowStepCompatible)
    (htwo : _root_.RealRooted.CompatiblePairHasCommonInterleaverStatement)
    (m : Nat) (tail : Board) (α : Content) :
    total (m :: tail) α = 0 ∨ IsRealRooted (total (m :: tail) α) := by
  have hrefined : RefinedPairCompatible (m :: tail) :=
    refinedPairCompatible_cons_of_boundaryRow_step hstep m tail
  have hpairToFamily : RefinedPairToFamilyCompatible :=
    refinedPairToFamilyCompatible_of_zeroAwareAllPairsToFamily
      (zeroAwareAllPairsToFamilyCompatible_of_pairBridgePos htwo)
      (refinedListRealRootedOfPairCompatible_of_boundaryRow_step hstep)
  exact total_cons_zero_or_isRealRooted_of_refinedList_familyCompatible
    (hpairToFamily m tail α hrefined)

end MultisetRook
end RealRooted
