import RealRooted.HosterStump.Step
import RealRooted.HosterStump.Permutation
import RealRooted.GammaTransform.ProperPosition
import RealRooted.PosCombo
import RealRooted.PFPolynomial
import RealRooted.ThresholdMatrix.Basic

/-!
# Hoster--Stump: Chow, dual Chow and augmented Chow polynomials (Theorems 1.1 and 1.2)

Hoster and Stump, *Chow polynomials of simplicial posets* (arXiv:2508.15538), define for a
flag `h`-vector `β` of the poset `P̂` the Chow polynomial (1.1) and the augmented Chow
polynomial (1.2).  Here `chowOfFlagH n β` and `augChowOfFlagH n β` are these definitions for an
arbitrary `β : Finset ℕ → ℝ`, with the paper's `1`-based positions `{1, …, n}` replaced by
`0`-based positions `range n`.

A graded simplicial poset enters only through identity (1.3) (Stanley), expressing `β` through
the `h`-vector and permutation statistics; it is the predicate `IsSimplicialFlagH n h β`,
proved for posets in `RealRooted.HosterStump.PosetChow` (`isSimplicialFlagH_flagH`).  Under it
we prove

* Lemma 3.1: the `γ`-polynomials of the Chow polynomials are `∑ₖ hₖ p^{T}_{n,k}`
  (`chowOfFlagH_eq_gammaTransform`, `augChowOfFlagH_eq_gammaTransform`,
  `chowOfFlagH_dualFlagH_eq_gammaTransform`, `augChowOfFlagH_dualFlagH`);
* Theorem 1.1: real-rootedness of the Chow and augmented Chow polynomials
  (`isRealRooted_chowOfFlagH`, `isRealRooted_augChowOfFlagH`);
* Theorem 1.2: real-rootedness of the dual Chow polynomial and its interlacing with the
  augmented one (`isRealRooted_chowOfFlagH_dualFlagH`,
  `strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH`);
* assumption-free corollaries for `β := flagHOfH n h`, the right-hand side of (1.3).

The analytic content is the interlacing diagram of Theorem 3.3
(`isInterlacingDiagram_range`), the identification of the refined family with permutation
statistics (`refinedPerm_eq_refined`) and Petersen's `γ`-transform lemmas
(`isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs`,
`strictInterl_gammaTransform_succ_iff`).  Example 1.3 (`n = 2`, `h = (1, 2, 3)`) is checked at
the end of the file.
-/

open Polynomial

noncomputable section

namespace RealRooted.HosterStump

/-- Reflection `s ↦ n - 1 - s` of `0`-based positions in `{0, …, n - 1}`; this is the paper's
`S ↦ n + 1 - S` for the `1`-based positions `{1, …, n}`. -/
def reflectSet (n : ℕ) (S : Finset ℕ) : Finset ℕ := S.image fun s => n - 1 - s

/-- The isolated subsets of `U`, i.e. the subsets of `U` containing no two consecutive
positions. -/
def isolatedSubsets (U : Finset ℕ) : Finset (Finset ℕ) := U.powerset.filter IsIsolated

/-- Hoster--Stump (1.1): the Chow polynomial attached to a flag `h`-vector `β`.  The paper's
`S ⊆ {2, …, n}` is `S ⊆ Icc 1 (n - 1)` for `0`-based positions. -/
noncomputable def chowOfFlagH (n : ℕ) (β : Finset ℕ → ℝ) : ℝ[X] :=
  ∑ S ∈ isolatedSubsets (Finset.Icc 1 (n - 1)),
    C (β S) * X ^ S.card * (X + 1) ^ (n - 2 * S.card)

/-- Hoster--Stump (1.2): the augmented Chow polynomial attached to a flag `h`-vector `β`.
The paper's `S ⊆ {1, …, n}` is `S ⊆ range n` for `0`-based positions. -/
noncomputable def augChowOfFlagH (n : ℕ) (β : Finset ℕ → ℝ) : ℝ[X] :=
  ∑ S ∈ isolatedSubsets (Finset.range n),
    C (β S) * X ^ S.card * (X + 1) ^ (n + 1 - 2 * S.card)

/-- The flag `h`-vector of the dual poset: `β^*(S) = β(n + 1 - S)`. -/
def dualFlagH (n : ℕ) (β : Finset ℕ → ℝ) : Finset ℕ → ℝ := fun S => β (reflectSet n S)

/-- Membership in `isolatedSubsets`. -/
lemma mem_isolatedSubsets {U S : Finset ℕ} : S ∈ isolatedSubsets U ↔ S ⊆ U ∧ IsIsolated S := by
  simp [isolatedSubsets]

/-- Membership in a reflected set. -/
lemma mem_reflectSet {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) {i : ℕ} :
    i ∈ reflectSet n S ↔ i < n ∧ n - 1 - i ∈ S := by
  simp only [reflectSet, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' := Finset.mem_range.1 (hS hs)
    refine ⟨by lia, ?_⟩
    have e : n - 1 - (n - 1 - s) = s := by lia
    rwa [e]
  · rintro ⟨hi, hmem⟩
    exact ⟨n - 1 - i, hmem, by lia⟩

/-- A reflected set lies in `range n`. -/
lemma reflectSet_subset_range {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
    reflectSet n S ⊆ Finset.range n := fun _ hi =>
  Finset.mem_range.2 ((mem_reflectSet hS).1 hi).1

/-- Reflection preserves cardinality. -/
lemma card_reflectSet {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
    (reflectSet n S).card = S.card := by
  refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
  have h1 := Finset.mem_range.1 (hS ha)
  have h2 := Finset.mem_range.1 (hS hb)
  lia

/-- Reflection is an involution on subsets of `range n`. -/
lemma reflectSet_reflectSet {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
    reflectSet n (reflectSet n S) = S := by
  ext i
  rw [mem_reflectSet (reflectSet_subset_range hS), mem_reflectSet hS]
  constructor
  · rintro ⟨_, _, hm⟩
    have e : n - 1 - (n - 1 - i) = i := by lia
    rwa [e] at hm
  · intro hi
    have h1 := Finset.mem_range.1 (hS hi)
    have e : n - 1 - (n - 1 - i) = i := by lia
    exact ⟨h1, by lia, by rw [e]; exact hi⟩

/-- Reflection preserves isolated sets. -/
lemma isIsolated_reflectSet {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n)
    (hiso : IsIsolated S) : IsIsolated (reflectSet n S) := by
  intro i hi hi1
  rw [mem_reflectSet hS] at hi hi1
  have := hiso (n - 1 - (i + 1)) hi1.2
  have e : n - 1 - (i + 1) + 1 = n - 1 - i := by lia
  rw [e] at this
  exact this hi.2

private lemma sum_isolatedSubsets_reflect {n : ℕ} {U V : Finset ℕ} (hU : U ⊆ Finset.range n)
    (hV : V ⊆ Finset.range n) (hUV : ∀ i, i < n → (i ∈ V ↔ n - 1 - i ∈ U))
    (F : Finset ℕ → ℝ[X]) :
    ∑ S ∈ isolatedSubsets U, F (reflectSet n S) = ∑ D ∈ isolatedSubsets V, F D := by
  refine Finset.sum_nbij' (reflectSet n) (reflectSet n) ?_ ?_ ?_ ?_ fun _ _ => rfl
  · intro S hS
    rw [mem_isolatedSubsets] at hS ⊢
    have hSr : S ⊆ Finset.range n := hS.1.trans hU
    refine ⟨fun i hi => ?_, isIsolated_reflectSet hSr hS.2⟩
    rw [mem_reflectSet hSr] at hi
    exact (hUV i hi.1).2 (hS.1 hi.2)
  · intro D hD
    rw [mem_isolatedSubsets] at hD ⊢
    have hDr : D ⊆ Finset.range n := hD.1.trans hV
    refine ⟨fun i hi => ?_, isIsolated_reflectSet hDr hD.2⟩
    rw [mem_reflectSet hDr] at hi
    have h1 := hD.1 hi.2
    have := (hUV (n - 1 - i) (by lia)).1 h1
    have e : n - 1 - (n - 1 - i) = i := by lia
    rwa [e] at this
  · intro S hS
    exact reflectSet_reflectSet ((mem_isolatedSubsets.1 hS).1.trans hU)
  · intro D hD
    exact reflectSet_reflectSet ((mem_isolatedSubsets.1 hD).1.trans hV)


/-- Hoster--Stump (1.3) (Stanley): `β` is the flag `h`-vector of `P̂`, for a graded simplicial
poset `P` of rank `n` with `h`-vector `h`.  Position `i` of the paper is `i - 1` here, and
`desCount n k D` counts the permutations `w` of `n + 1` letters with `w 1 = k + 1` and
descent set `D`.

This is identity (1.3) of Hoster and Stump, *Chow polynomials of simplicial posets*
(arXiv:2508.15538), after Stanley.  It is proved for every graded simplicial poset with a
bottom element in `RealRooted.HosterStump.isSimplicialFlagH_flagH`
(`RealRooted.HosterStump.PosetChow`), where `β` and `h` are the flag `h`-vector `flagH` and the
`h`-vector `hVec`.  Theorems taking `IsSimplicialFlagH n h β` as a hypothesis derive the
real-rootedness and interlacing conclusions from the formalized interlacing diagrams
(`isInterlacingDiagram_range`); for the vector `flagHOfH n h` the identity holds by
definition, see `isSimplicialFlagH_flagHOfH`. -/
def IsSimplicialFlagH (n : ℕ) (h : ℕ → ℝ) (β : Finset ℕ → ℝ) : Prop :=
  ∀ S ⊆ Finset.range n,
    β S = ∑ k ∈ Finset.range (n + 1), h k * (desCount n k (reflectSet n S) : ℝ)

/-- The right-hand side of (1.3) as a function on subsets: the vector `β` determined by the
`h`-vector `h` through the permutation statistics. -/
noncomputable def flagHOfH (n : ℕ) (h : ℕ → ℝ) : Finset ℕ → ℝ := fun S =>
  ∑ k ∈ Finset.range (n + 1), h k * (desCount n k (reflectSet n S) : ℝ)

/-- The vector `flagHOfH n h` satisfies identity (1.3) by definition. -/
theorem isSimplicialFlagH_flagHOfH (n : ℕ) (h : ℕ → ℝ) : IsSimplicialFlagH n h (flagHOfH n h) :=
  fun _ _ => rfl

/-! ### Isolated sets and the refined family -/

private lemma card_le_of_isIsolated_of_subset_Ico {a m : ℕ} {D : Finset ℕ} (hD : IsIsolated D)
    (hsub : D ⊆ Finset.Ico a (a + m)) : D.card ≤ (m + 1) / 2 := by
  have hmaps : ∀ i ∈ D, (i - a) / 2 ∈ Finset.range ((m + 1) / 2) := by
    intro i hi
    have := Finset.mem_Ico.1 (hsub hi)
    rw [Finset.mem_range]
    lia
  have hinj : Set.InjOn (fun i => (i - a) / 2) (D : Set ℕ) := by
    intro i hi j hj hij
    have hi' := Finset.mem_Ico.1 (hsub hi)
    have hj' := Finset.mem_Ico.1 (hsub hj)
    have hij' : (i - a) / 2 = (j - a) / 2 := hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have e : j = i + 1 := by lia
      exact hD i hi (e ▸ hj)
    · have e : i = j + 1 := by lia
      exact hD j hj (e ▸ hi)
  calc D.card ≤ (Finset.range ((m + 1) / 2)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (m + 1) / 2 := Finset.card_range _

private lemma card_le_of_mem_isolatedSubsets_Icc {n : ℕ} {D : Finset ℕ}
    (hD : D ∈ isolatedSubsets (Finset.Icc 1 (n - 1))) : D.card ≤ n / 2 := by
  rw [mem_isolatedSubsets] at hD
  have := card_le_of_isIsolated_of_subset_Ico (a := 1) (m := n - 1) hD.2 (fun i hi => by
    have := Finset.mem_Icc.1 (hD.1 hi)
    rw [Finset.mem_Ico]
    lia)
  lia

private lemma card_le_of_mem_isolatedSubsets_range_pred {n : ℕ} {D : Finset ℕ}
    (hD : D ∈ isolatedSubsets (Finset.range (n - 1))) : D.card ≤ n / 2 := by
  rw [mem_isolatedSubsets] at hD
  have := card_le_of_isIsolated_of_subset_Ico (a := 0) (m := n - 1) hD.2 (fun i hi => by
    have := Finset.mem_range.1 (hD.1 hi)
    rw [Finset.mem_Ico]
    lia)
  lia

private lemma card_le_of_mem_isolatedSubsets_range {n : ℕ} {D : Finset ℕ}
    (hD : D ∈ isolatedSubsets (Finset.range n)) : D.card ≤ (n + 1) / 2 := by
  rw [mem_isolatedSubsets] at hD
  exact card_le_of_isIsolated_of_subset_Ico (a := 0) (m := n) hD.2 (fun i hi => by
    have := Finset.mem_range.1 (hD.1 hi)
    rw [Finset.mem_Ico]
    lia)

private lemma refined_empty_eq_sum_isolatedSubsets {n k : ℕ} (hk : k ≤ n) (T : Finset ℕ) :
    refined n k ∅ T =
      ∑ D ∈ isolatedSubsets T, C (desCount n k D : ℝ) * X ^ D.card := by
  rw [← refinedPerm_eq_refined hk]
  unfold refinedPerm
  rw [← Finset.sum_fiberwise_of_maps_to (g := desSet) (t := isolatedSubsets T)]
  · refine Finset.sum_congr rfl fun D hD => ?_
    rw [mem_isolatedSubsets] at hD
    have hset : ((Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter
        (fun w => (w 0 : ℕ) = k ∧ IsIsolated (desSet w) ∧ ∅ ⊆ desSet w ∧
          desSet w ⊆ T)).filter (fun w => desSet w = D) =
        (Finset.univ : Finset (Equiv.Perm (Fin (n + 1)))).filter
          (fun w => (w 0 : ℕ) = k ∧ desSet w = D) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.empty_subset]
      grind
    rw [hset]
    rw [Finset.sum_congr rfl (g := fun _ => (X : ℝ[X]) ^ D.card) (fun w hw => by
      rw [(Finset.mem_filter.1 hw).2.2])]
    rw [Finset.sum_const, nsmul_eq_mul, map_natCast]
    rfl
  · intro w hw
    rw [mem_isolatedSubsets]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨hw.2.2.2, hw.2.1⟩

private lemma sum_C_mul_refined_eq (n : ℕ) (h : ℕ → ℝ) (T : Finset ℕ) :
    ∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T =
      ∑ D ∈ isolatedSubsets T,
        C (∑ k ∈ Finset.range (n + 1), h k * (desCount n k D : ℝ)) * X ^ D.card := by
  calc ∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T
      = ∑ k ∈ Finset.range (n + 1), ∑ D ∈ isolatedSubsets T,
          C (h k * (desCount n k D : ℝ)) * X ^ D.card := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [refined_empty_eq_sum_isolatedSubsets (by have := Finset.mem_range.1 hk; lia),
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun D _ => ?_
        rw [map_mul, mul_assoc]
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun D _ => ?_
        rw [map_sum, Finset.sum_mul]


/-! ### Lemma 3.1: the gamma-polynomials of the Chow polynomials -/

private lemma sum_isolatedSubsets_eq_gammaTransform {d : ℕ} {T : Finset ℕ} (c : Finset ℕ → ℝ)
    (hcard : ∀ D ∈ isolatedSubsets T, D.card ≤ d / 2) :
    ∑ D ∈ isolatedSubsets T, C (c D) * X ^ D.card * (X + 1) ^ (d - 2 * D.card) =
      gammaTransform d (∑ D ∈ isolatedSubsets T, C (c D) * X ^ D.card) := by
  rw [gammaTransform_finset_sum]
  refine Finset.sum_congr rfl fun D hD => ?_
  rw [mul_assoc, C_mul_X_pow_eq_monomial, gammaTransform_monomial]
  simp only [hcard D hD, ↓reduceIte, gammaBasisTerm]

private lemma Icc_subset_range {n : ℕ} : Finset.Icc 1 (n - 1) ⊆ Finset.range n := fun i hi => by
  have := Finset.mem_Icc.1 hi
  rw [Finset.mem_range]
  lia

private lemma range_pred_subset_range {n : ℕ} : Finset.range (n - 1) ⊆ Finset.range n :=
  Finset.range_mono (by lia)

/-- Hoster--Stump, Lemma 3.1 (Chow polynomial): the `γ`-polynomial of the Chow polynomial is
`∑ₖ hₖ p^{[1, n-1]}_{n,k}`, here `refined n k ∅ (range (n - 1))`. -/
theorem chowOfFlagH_eq_gammaTransform {n : ℕ} {h : ℕ → ℝ} {β : Finset ℕ → ℝ}
    (hβ : IsSimplicialFlagH n h β) :
    chowOfFlagH n β = gammaTransform n
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range (n - 1))) := by
  rw [sum_C_mul_refined_eq]
  set b : Finset ℕ → ℝ := fun D => ∑ k ∈ Finset.range (n + 1), h k * (desCount n k D : ℝ)
    with hb
  rw [← sum_isolatedSubsets_eq_gammaTransform b
    (fun D hD => card_le_of_mem_isolatedSubsets_range_pred hD)]
  unfold chowOfFlagH
  set F : Finset ℕ → ℝ[X] := fun D => C (b D) * X ^ D.card * (X + 1) ^ (n - 2 * D.card)
    with hFdef
  have hF : ∀ S ∈ isolatedSubsets (Finset.Icc 1 (n - 1)),
      C (β S) * X ^ S.card * (X + 1) ^ (n - 2 * S.card) = F (reflectSet n S) := by
    intro S hS
    have hSr : S ⊆ Finset.range n := (mem_isolatedSubsets.1 hS).1.trans Icc_subset_range
    simp only [card_reflectSet hSr, hβ S hSr, hb, hFdef]
  rw [Finset.sum_congr rfl hF]
  exact sum_isolatedSubsets_reflect (n := n) Icc_subset_range range_pred_subset_range
    (fun i hi => by simp only [Finset.mem_range, Finset.mem_Icc]; lia) F

/-- Hoster--Stump, Lemma 3.1 (augmented Chow polynomial): the `γ`-polynomial of the augmented
Chow polynomial is `∑ₖ hₖ p^{[1, n]}_{n,k}`, here `refined n k ∅ (range n)`. -/
theorem augChowOfFlagH_eq_gammaTransform {n : ℕ} {h : ℕ → ℝ} {β : Finset ℕ → ℝ}
    (hβ : IsSimplicialFlagH n h β) :
    augChowOfFlagH n β = gammaTransform (n + 1)
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range n)) := by
  rw [sum_C_mul_refined_eq]
  set b : Finset ℕ → ℝ := fun D => ∑ k ∈ Finset.range (n + 1), h k * (desCount n k D : ℝ)
    with hb
  rw [← sum_isolatedSubsets_eq_gammaTransform b
    (fun D hD => card_le_of_mem_isolatedSubsets_range hD)]
  unfold augChowOfFlagH
  set F : Finset ℕ → ℝ[X] := fun D => C (b D) * X ^ D.card * (X + 1) ^ (n + 1 - 2 * D.card)
    with hFdef
  have hF : ∀ S ∈ isolatedSubsets (Finset.range n),
      C (β S) * X ^ S.card * (X + 1) ^ (n + 1 - 2 * S.card) = F (reflectSet n S) := by
    intro S hS
    have hSr : S ⊆ Finset.range n := (mem_isolatedSubsets.1 hS).1
    simp only [card_reflectSet hSr, hβ S hSr, hb, hFdef]
  rw [Finset.sum_congr rfl hF]
  exact sum_isolatedSubsets_reflect (n := n) le_rfl le_rfl
    (fun i hi => by simp only [Finset.mem_range]; lia) F

/-- Hoster--Stump, Lemma 3.1 (dual Chow polynomial): the `γ`-polynomial of the Chow polynomial
of the dual poset is `∑ₖ hₖ p^{[2, n]}_{n,k}`, here `refined n k ∅ (Icc 1 (n - 1))`. -/
theorem chowOfFlagH_dualFlagH_eq_gammaTransform {n : ℕ} {h : ℕ → ℝ} {β : Finset ℕ → ℝ}
    (hβ : IsSimplicialFlagH n h β) :
    chowOfFlagH n (dualFlagH n β) = gammaTransform n
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.Icc 1 (n - 1))) := by
  rw [sum_C_mul_refined_eq]
  set b : Finset ℕ → ℝ := fun D => ∑ k ∈ Finset.range (n + 1), h k * (desCount n k D : ℝ)
    with hb
  rw [← sum_isolatedSubsets_eq_gammaTransform b
    (fun D hD => card_le_of_mem_isolatedSubsets_Icc hD)]
  unfold chowOfFlagH
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSr : S ⊆ Finset.range n := (mem_isolatedSubsets.1 hS).1.trans Icc_subset_range
  have h1 : dualFlagH n β S = b S := by
    rw [dualFlagH, hβ _ (reflectSet_subset_range hSr), reflectSet_reflectSet hSr]
  rw [h1]

/-- The augmented Chow polynomial is invariant under passing to the dual flag `h`-vector
(Hoster--Stump, Lemma 3.1, last assertion). -/
theorem augChowOfFlagH_dualFlagH (n : ℕ) (β : Finset ℕ → ℝ) :
    augChowOfFlagH n (dualFlagH n β) = augChowOfFlagH n β := by
  unfold augChowOfFlagH
  set F : Finset ℕ → ℝ[X] := fun D => C (β D) * X ^ D.card * (X + 1) ^ (n + 1 - 2 * D.card)
    with hFdef
  have hF : ∀ S ∈ isolatedSubsets (Finset.range n),
      C (dualFlagH n β S) * X ^ S.card * (X + 1) ^ (n + 1 - 2 * S.card) =
        F (reflectSet n S) := by
    intro S hS
    have hSr : S ⊆ Finset.range n := (mem_isolatedSubsets.1 hS).1
    simp only [card_reflectSet hSr, dualFlagH, hFdef]
  rw [Finset.sum_congr rfl hF]
  exact sum_isolatedSubsets_reflect (n := n) le_rfl le_rfl
    (fun i hi => by simp only [Finset.mem_range]; lia) F


/-! ### Real-rootedness of the `γ`-polynomials -/

private lemma list_sum_range_map (f : ℕ → ℝ[X]) (m : ℕ) :
    ((List.range m).map f).sum = ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem isRealRooted_sum_C_mul_of_interl {n : ℕ} (F : ℕ → ℝ[X]) (h : ℕ → ℝ)
    (hh : ∀ k, 0 ≤ h k) (hnn : ∀ k, HasNonnegCoeffs (F k))
    (hsp : ∀ k, k ≤ n → F k ≠ 0 → (F k).Splits)
    (hrow : ∀ i j, i < j → j ≤ n → Interl (F i) (F j))
    (hne : ∑ k ∈ Finset.range (n + 1), C (h k) * F k ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * F k) ≠ 0 ∧
      (∑ k ∈ Finset.range (n + 1), C (h k) * F k).Splits := by
  set gs : List ℝ[X] := (List.range (n + 1)).map fun k => C (h k) * F k with hgs
  have hsum : gs.sum = ∑ k ∈ Finset.range (n + 1), C (h k) * F k := list_sum_range_map _ _
  have hpair : gs.Pairwise Interl := by
    rw [hgs, List.pairwise_map]
    refine (List.pairwise_lt_range : (List.range (n + 1)).Pairwise (· < ·)).imp_of_mem ?_
    intro i j hi hj hij
    have hj' := List.mem_range.1 hj
    exact ((hrow i j hij (by lia)).C_mul_left_of_nonneg (hh i)).C_mul_right_of_nonneg (hh j)
  have hseq : IsInterlacingSeq0Nonneg gs := by
    refine ⟨isInterlacingSeq0_iff_pairwise.2 hpair, ?_⟩
    intro f hf
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hf
    exact nonnegCoeffs_C_mul (hh k) (hnn k)
  have hreal : ∀ f ∈ gs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
    intro f hf hf0
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf
    have hk' := List.mem_range.1 hk
    have hFk : F k ≠ 0 := fun h0 => hf0 (by simp [h0])
    exact ⟨hf0, Polynomial.Splits.mul (Polynomial.Splits.C _) (hsp k (by lia) hFk)⟩
  have := isRealRooted_sum_of_isInterlacingSeq0Nonneg hseq hreal (by rwa [hsum])
  rwa [hsum] at this

private lemma coeff_zero_sum_C_mul_refined (n : ℕ) (h : ℕ → ℝ) (T : Finset ℕ) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T).coeff 0 = h 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_zero_refined]
  simp

private lemma hasNonnegCoeffs_sum_C_mul_refined (n : ℕ) {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (S T : Finset ℕ) : HasNonnegCoeffs (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k S T) :=
  hasNonnegCoeffs_finsetSum _ _ fun k _ =>
    nonnegCoeffs_C_mul (hh k) (hasNonnegCoeffs_refined n k S T)

private lemma natDegree_sum_C_mul_refined_le (n : ℕ) (h : ℕ → ℝ) {T : Finset ℕ} {b : ℕ}
    (hcard : ∀ D ∈ isolatedSubsets T, D.card ≤ b) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T).natDegree ≤ b := by
  rw [sum_C_mul_refined_eq]
  exact natDegree_sum_le_of_forall_le _ _ fun D hD => (natDegree_C_mul_X_pow_le _ _).trans
    (hcard D hD)

private lemma isRealRooted_sum_C_mul_refined {n : ℕ} {T : Finset ℕ} {h : ℕ → ℝ}
    (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0)
    (hsp : ∀ k, k ≤ n → refined n k ∅ T ≠ 0 → (refined n k ∅ T).Splits)
    (hrow : ∀ i j, i < j → j ≤ n → Interl (refined n i ∅ T) (refined n j ∅ T)) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T) ≠ 0 ∧
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T).Splits := by
  refine isRealRooted_sum_C_mul_of_interl (fun k => refined n k ∅ T) h hh
    (fun k => hasNonnegCoeffs_refined n k ∅ T) hsp hrow ?_
  intro hzero
  have := coeff_zero_sum_C_mul_refined n h T
  rw [hzero, coeff_zero_eq_eval_zero] at this
  simp only [eval_zero] at this
  exact h0.ne this

private lemma ne_zero_splits_of_natDegree_le_one {γ : ℝ[X]} (h0 : γ.coeff 0 ≠ 0)
    (hdeg : γ.natDegree ≤ 1) : γ ≠ 0 ∧ γ.Splits :=
  ⟨fun hz => h0 (by simp [hz]), Polynomial.Splits.of_natDegree_le_one hdeg⟩

private lemma erase_zero_range (n : ℕ) : (Finset.range n).erase 0 = Finset.Icc 1 (n - 1) := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
  lia

/-- Real-rootedness of `∑ₖ hₖ p^{[1, n-1]}_{n,k}`. -/
theorem isRealRooted_sum_refined_range_pred {n : ℕ} {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (h0 : 0 < h 0) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range (n - 1))) ≠ 0 ∧
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range (n - 1))).Splits := by
  rcases lt_or_ge n 2 with hn | hn
  · refine ne_zero_splits_of_natDegree_le_one (by
      rw [coeff_zero_sum_C_mul_refined]; exact h0.ne') ?_
    exact (natDegree_sum_C_mul_refined_le n h
      (fun D hD => card_le_of_mem_isolatedSubsets_range_pred hD)).trans (by lia)
  · have hD := (isInterlacingDiagram_range n hn).2
    exact isRealRooted_sum_C_mul_refined hh h0 (fun k hk _ => (hD.splits k hk).2.1)
      (fun i j hij hj => hD.mid_row i j hij hj)

/-- Real-rootedness of `∑ₖ hₖ p^{[1, n]}_{n,k}`. -/
theorem isRealRooted_sum_refined_range {n : ℕ} {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (h0 : 0 < h 0) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range n)) ≠ 0 ∧
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range n)).Splits := by
  rcases lt_or_ge n 2 with hn | hn
  · refine ne_zero_splits_of_natDegree_le_one (by
      rw [coeff_zero_sum_C_mul_refined]; exact h0.ne') ?_
    exact (natDegree_sum_C_mul_refined_le n h
      (fun D hD => card_le_of_mem_isolatedSubsets_range hD)).trans (by lia)
  · have hD := (isInterlacingDiagram_range n hn).1
    exact isRealRooted_sum_C_mul_refined hh h0 (fun k hk _ => (hD.splits k hk).2.1)
      (fun i j hij hj => hD.mid_row i j hij hj)

/-- Real-rootedness of `∑ₖ hₖ p^{[2, n]}_{n,k}`. -/
theorem isRealRooted_sum_refined_Icc {n : ℕ} {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (h0 : 0 < h 0) :
    (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.Icc 1 (n - 1))) ≠ 0 ∧
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.Icc 1 (n - 1))).Splits := by
  rcases lt_or_ge n 2 with hn | hn
  · refine ne_zero_splits_of_natDegree_le_one (by
      rw [coeff_zero_sum_C_mul_refined]; exact h0.ne') ?_
    exact (natDegree_sum_C_mul_refined_le n h
      (fun D hD => card_le_of_mem_isolatedSubsets_Icc hD)).trans (by lia)
  · have hD := (isInterlacingDiagram_range n hn).1
    rw [← erase_zero_range]
    exact isRealRooted_sum_C_mul_refined hh h0 (fun k hk => (hD.splits k hk).1)
      (fun i j hij hj => hD.top_row i j hij hj)


/-! ### Theorem 1.1 and Theorem 1.2: real-rootedness -/

/-- Hoster--Stump, Theorem 1.1 (Chow polynomial): for a flag `h`-vector `β` satisfying (1.3)
with a nonnegative `h`-vector with `h 0 > 0`, the Chow polynomial `chowOfFlagH n β` is
real-rooted.  For posets, `hβ` is `isSimplicialFlagH_flagH`. -/
theorem isRealRooted_chowOfFlagH {n : ℕ} {h : ℕ → ℝ} {β : Finset ℕ → ℝ}
    (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) (hβ : IsSimplicialFlagH n h β) :
    chowOfFlagH n β ≠ 0 ∧ (chowOfFlagH n β).Splits := by
  rw [chowOfFlagH_eq_gammaTransform hβ]
  obtain ⟨hne, hsp⟩ := isRealRooted_sum_refined_range_pred (n := n) hh h0
  exact isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (natDegree_sum_C_mul_refined_le n h
      (fun D hD => card_le_of_mem_isolatedSubsets_range_pred hD))
    hne hsp (hasNonnegCoeffs_sum_C_mul_refined n hh _ _)

/-- Hoster--Stump, Theorem 1.1 (augmented Chow polynomial): under the hypotheses of
`isRealRooted_chowOfFlagH`, the augmented Chow polynomial `augChowOfFlagH n β` is
real-rooted. -/
theorem isRealRooted_augChowOfFlagH {n : ℕ} {h : ℕ → ℝ} {β : Finset ℕ → ℝ}
    (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) (hβ : IsSimplicialFlagH n h β) :
    augChowOfFlagH n β ≠ 0 ∧ (augChowOfFlagH n β).Splits := by
  rw [augChowOfFlagH_eq_gammaTransform hβ]
  obtain ⟨hne, hsp⟩ := isRealRooted_sum_refined_range (n := n) hh h0
  exact isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (natDegree_sum_C_mul_refined_le n h
      (fun D hD => card_le_of_mem_isolatedSubsets_range hD))
    hne hsp (hasNonnegCoeffs_sum_C_mul_refined n hh _ _)

/-- Hoster--Stump, Theorem 1.2 (real-rootedness part): the Chow polynomial of the dual poset,
`chowOfFlagH n (dualFlagH n β)`, is real-rooted under the hypotheses of
`isRealRooted_chowOfFlagH`. -/
theorem isRealRooted_chowOfFlagH_dualFlagH {n : ℕ} {h : ℕ → ℝ} {β : Finset ℕ → ℝ}
    (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) (hβ : IsSimplicialFlagH n h β) :
    chowOfFlagH n (dualFlagH n β) ≠ 0 ∧ (chowOfFlagH n (dualFlagH n β)).Splits := by
  rw [chowOfFlagH_dualFlagH_eq_gammaTransform hβ]
  obtain ⟨hne, hsp⟩ := isRealRooted_sum_refined_Icc (n := n) hh h0
  exact isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (natDegree_sum_C_mul_refined_le n h
      (fun D hD => card_le_of_mem_isolatedSubsets_Icc hD))
    hne hsp (hasNonnegCoeffs_sum_C_mul_refined n hh _ _)

/-! ### Theorem 1.2: interlacing -/

private theorem strictInterl_sum_refined_Icc_sum_refined_range {n : ℕ} (hn : 2 ≤ n)
    {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) :
    StrictInterl (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.Icc 1 (n - 1)))
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range n)) := by
  have hD := (isInterlacingDiagram_range n hn).1
  obtain ⟨hne3, hsp3⟩ := isRealRooted_sum_refined_Icc (n := n) hh h0
  obtain ⟨hne2, hsp2⟩ := isRealRooted_sum_refined_range (n := n) hh h0
  rw [← erase_zero_range] at hne3 hsp3 ⊢
  have hbot : Interl (∑ k ∈ Finset.range (n + 1),
        C (h k) * refined n k ∅ ((Finset.range n).erase 0))
      (∑ k ∈ Finset.range (n + 1), C (h k) * bot n (Finset.range n) k) := by
    refine Interl.finsetSum_pairwise_of_nonneg _ _ _ _ (fun i hi j hj => ?_)
      (fun k _ => nonnegCoeffs_C_mul (hh k) (hasNonnegCoeffs_refined n k ∅ _))
      (fun k _ => nonnegCoeffs_C_mul (hh k) (hasNonnegCoeffs_refined n k {0} _))
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    exact ((hD.top_bot i j (by lia) (by lia)).C_mul_left_of_nonneg (hh i)).C_mul_right_of_nonneg
      (hh j)
  have hsum : ∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range n) =
      ∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ ((Finset.range n).erase 0) +
        ∑ k ∈ Finset.range (n + 1), C (h k) * bot n (Finset.range n) k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_add]
    exact congrArg (C (h k) * ·) (mid_eq_top_add_bot n (Finset.range n) k)
  have hint : Interl (∑ k ∈ Finset.range (n + 1),
        C (h k) * refined n k ∅ ((Finset.range n).erase 0))
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ (Finset.range n)) := by
    rw [hsum]
    exact interl_add_right_of_common_left_of_nonneg (Interl.refl fun _ => hsp3) hbot
      (hasNonnegCoeffs_sum_C_mul_refined n hh _ _)
      (hasNonnegCoeffs_finsetSum _ _ fun k _ =>
        nonnegCoeffs_C_mul (hh k) (hasNonnegCoeffs_refined n k {0} _))
  exact hint.toStrictInterl_of_ne hne3 hne2


private theorem strictInterl_sum_refined_Icc_sum_refined_range_one {h : ℕ → ℝ}
    (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) :
    StrictInterl (∑ k ∈ Finset.range (1 + 1), C (h k) * refined 1 k ∅ (Finset.Icc 1 (1 - 1)))
      (∑ k ∈ Finset.range (1 + 1), C (h k) * refined 1 k ∅ (Finset.range 1)) := by
  have e3 : ∑ k ∈ Finset.range (1 + 1), C (h k) * refined 1 k ∅ (Finset.Icc 1 (1 - 1)) =
      C (h 0) := by
    simp [refined]
  have e2 : ∑ k ∈ Finset.range (1 + 1), C (h k) * refined 1 k ∅ (Finset.range 1) =
      C (h 1) * X + C (h 0) := by
    simp [Finset.sum_range_succ, refined, add_comm]
  rw [e3, e2]
  rcases (hh 1).eq_or_lt with h1 | h1
  · rw [← h1]
    simp only [map_zero, zero_mul, zero_add]
    exact StrictInterl.refl (by simpa using h0.ne') (Polynomial.Splits.C _)
  · have hdeg : (C (h 1) * X + C (h 0)).natDegree = 1 := natDegree_linear h1.ne'
    have := ((interlaces_one_linear hdeg).toStrictInterl).C_mul_left h0.ne'
    simpa using this

/-- Hoster--Stump, Theorem 1.2 (interlacing part): the roots of the Chow polynomial of the dual
poset interlace the roots of the augmented Chow polynomial, that is,
`chowOfFlagH n (dualFlagH n β) ≪ augChowOfFlagH n β` in the sense of `StrictInterl`
(shared roots allowed).  For posets, `hβ` is `isSimplicialFlagH_flagH`.
Since `augChowOfFlagH n (dualFlagH n β) = augChowOfFlagH n β`
(`augChowOfFlagH_dualFlagH`), this is the paper's statement for `P̂^*`. -/
theorem strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH {n : ℕ} (hn : 1 ≤ n) {h : ℕ → ℝ}
    {β : Finset ℕ → ℝ} (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) (hβ : IsSimplicialFlagH n h β) :
    StrictInterl (chowOfFlagH n (dualFlagH n β)) (augChowOfFlagH n β) := by
  rw [chowOfFlagH_dualFlagH_eq_gammaTransform hβ, augChowOfFlagH_eq_gammaTransform hβ]
  have hcoeff : ∀ T : Finset ℕ,
      (∑ k ∈ Finset.range (n + 1), C (h k) * refined n k ∅ T).coeff 0 ≠ 0 := fun T => by
    rw [coeff_zero_sum_C_mul_refined]
    exact h0.ne'
  refine (strictInterl_gammaTransform_succ_iff (d := n)
    (natDegree_sum_C_mul_refined_le n h (fun D hD => card_le_of_mem_isolatedSubsets_Icc hD))
    (natDegree_sum_C_mul_refined_le n h (fun D hD => card_le_of_mem_isolatedSubsets_range hD))
    (hasNonnegCoeffs_sum_C_mul_refined n hh _ _) (hasNonnegCoeffs_sum_C_mul_refined n hh _ _)
    (hcoeff _) (hcoeff _)).2 ?_
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by lia
    exact strictInterl_sum_refined_Icc_sum_refined_range_one hh h0
  · exact strictInterl_sum_refined_Icc_sum_refined_range h2 hh h0


/-! ### Assumption-free corollaries for `β = flagHOfH n h` -/

/-- Theorem 1.1 (Chow polynomial) for the flag `h`-vector `flagHOfH n h` of (1.3); no
hypothesis on a poset model is involved. -/
theorem isRealRooted_chowOfFlagH_flagHOfH {n : ℕ} {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (h0 : 0 < h 0) :
    chowOfFlagH n (flagHOfH n h) ≠ 0 ∧ (chowOfFlagH n (flagHOfH n h)).Splits :=
  isRealRooted_chowOfFlagH hh h0 (isSimplicialFlagH_flagHOfH n h)

/-- Theorem 1.1 (augmented Chow polynomial) for the flag `h`-vector `flagHOfH n h` of (1.3). -/
theorem isRealRooted_augChowOfFlagH_flagHOfH {n : ℕ} {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (h0 : 0 < h 0) :
    augChowOfFlagH n (flagHOfH n h) ≠ 0 ∧ (augChowOfFlagH n (flagHOfH n h)).Splits :=
  isRealRooted_augChowOfFlagH hh h0 (isSimplicialFlagH_flagHOfH n h)

/-- Theorem 1.2 (dual Chow polynomial) for the flag `h`-vector `flagHOfH n h` of (1.3). -/
theorem isRealRooted_chowOfFlagH_dualFlagH_flagHOfH {n : ℕ} {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k)
    (h0 : 0 < h 0) :
    chowOfFlagH n (dualFlagH n (flagHOfH n h)) ≠ 0 ∧
      (chowOfFlagH n (dualFlagH n (flagHOfH n h))).Splits :=
  isRealRooted_chowOfFlagH_dualFlagH hh h0 (isSimplicialFlagH_flagHOfH n h)

/-- Theorem 1.2 (interlacing) for the flag `h`-vector `flagHOfH n h` of (1.3). -/
theorem strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH_flagHOfH {n : ℕ} (hn : 1 ≤ n)
    {h : ℕ → ℝ} (hh : ∀ k, 0 ≤ h k) (h0 : 0 < h 0) :
    StrictInterl (chowOfFlagH n (dualFlagH n (flagHOfH n h))) (augChowOfFlagH n (flagHOfH n h)) :=
  strictInterl_chowOfFlagH_dualFlagH_augChowOfFlagH hn hh h0 (isSimplicialFlagH_flagHOfH n h)

/-! ### Example 1.3: the lattice of flats of `U_{3,4}` (`n = 2`, `h = (1, 2, 3)`) -/

section Example

private def exampleH : ℕ → ℝ := fun k => if k = 0 then 1 else if k = 1 then 2 else 3

private lemma desCount_two :
    desCount 2 0 ∅ = 1 ∧ desCount 2 0 {1} = 1 ∧ desCount 2 0 {0} = 0 ∧
    desCount 2 0 {0, 1} = 0 ∧ desCount 2 1 ∅ = 0 ∧ desCount 2 1 {1} = 1 ∧
    desCount 2 1 {0} = 1 ∧ desCount 2 1 {0, 1} = 0 ∧ desCount 2 2 ∅ = 0 ∧
    desCount 2 2 {1} = 0 ∧ desCount 2 2 {0} = 1 ∧ desCount 2 2 {0, 1} = 1 := by
  decide +kernel

private lemma reflectSet_two_zero : reflectSet 2 {0} = {1} := by decide +kernel

private lemma reflectSet_two_one : reflectSet 2 {1} = {0} := by decide +kernel

private lemma reflectSet_two_pair : reflectSet 2 {0, 1} = {0, 1} := by decide +kernel

private lemma flagH_two : flagHOfH 2 exampleH ∅ = 1 ∧ flagHOfH 2 exampleH {0} = 3 ∧
    flagHOfH 2 exampleH {1} = 5 ∧ flagHOfH 2 exampleH {0, 1} = 3 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := desCount_two
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [flagHOfH, Finset.sum_range_succ, exampleH, reflectSet, a1, a5, a9]
  · simp [flagHOfH, Finset.sum_range_succ, exampleH, reflectSet_two_zero, a2, a6, a10]
    norm_num
  · simp [flagHOfH, Finset.sum_range_succ, exampleH, reflectSet_two_one, a3, a7, a11]
    norm_num
  · simp [flagHOfH, Finset.sum_range_succ, exampleH, reflectSet_two_pair, a4, a8, a12]

private lemma isolatedSubsets_Icc_two : isolatedSubsets (Finset.Icc 1 (2 - 1)) = {∅, {1}} := by
  decide +kernel

private lemma isolatedSubsets_range_two : isolatedSubsets (Finset.range 2) = {∅, {0}, {1}} := by
  decide +kernel

/-- Example 1.3: `H_{P̂}(x) = x² + 7x + 1`. -/
example : chowOfFlagH 2 (flagHOfH 2 exampleH) = X ^ 2 + 7 * X + 1 := by
  obtain ⟨b0, b1, b2, b3⟩ := flagH_two
  rw [chowOfFlagH, isolatedSubsets_Icc_two, Finset.sum_pair (by decide), b0, b2]
  simp [map_ofNat]
  ring

/-- Example 1.3: `H_{P̂^*}(x) = x² + 5x + 1`. -/
example : chowOfFlagH 2 (dualFlagH 2 (flagHOfH 2 exampleH)) = X ^ 2 + 5 * X + 1 := by
  obtain ⟨b0, b1, b2, b3⟩ := flagH_two
  rw [chowOfFlagH, isolatedSubsets_Icc_two, Finset.sum_pair (by decide)]
  simp [dualFlagH, reflectSet, b0, b1, map_ofNat]
  ring

/-- Example 1.3: `H^{aug}_{P̂}(x) = x³ + 11x² + 11x + 1`. -/
example : augChowOfFlagH 2 (flagHOfH 2 exampleH) = X ^ 3 + 11 * X ^ 2 + 11 * X + 1 := by
  obtain ⟨b0, b1, b2, b3⟩ := flagH_two
  rw [augChowOfFlagH, isolatedSubsets_range_two, Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  simp [b0, b1, b2, map_ofNat]
  ring

/-- Example 3.2: the `γ`-polynomials `1 + 5x`, `1 + 3x` and `1 + 8x`. -/
example : (∑ k ∈ Finset.range (2 + 1), C (exampleH k) * refined 2 k ∅ (Finset.range (2 - 1))) =
    1 + 5 * X ∧
    (∑ k ∈ Finset.range (2 + 1), C (exampleH k) * refined 2 k ∅ (Finset.Icc 1 (2 - 1))) =
      1 + 3 * X ∧
    (∑ k ∈ Finset.range (2 + 1), C (exampleH k) * refined 2 k ∅ (Finset.range 2)) =
      1 + 8 * X := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Finset.sum_range_succ, refined, exampleH, map_ofNat] <;> ring

end Example

end RealRooted.HosterStump
