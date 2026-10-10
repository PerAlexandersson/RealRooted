import RealRooted.HosterStump.Chow
import RealRooted.HosterStump.PosetBasic

/-!
# Descent-set counts and Möbius inversion

Hoster--Stump (F6): `desLeCount n k E = ∑ D ⊆ E, desCount n k D`, and by Möbius inversion on the
Boolean lattice of subsets of `range n`,
`desCount n k (reflectSet n S) = ∑ T ⊆ S, (-1)^|S \ T| desLeCount n k (reflectSet n T)`.
-/

open Finset

noncomputable section

namespace RealRooted.HosterStump

/-- Partition the permutations with `w 0 = k` and descent set in `E` by their descent set. -/
theorem desLeCount_eq_sum_desCount (n k : ℕ) (E : Finset ℕ) :
    desLeCount n k E = ∑ D ∈ E.powerset, desCount n k D := by
  classical
  unfold desLeCount desCount
  rw [card_eq_sum_card_fiberwise (f := fun w : Equiv.Perm (Fin (n + 1)) => w.descentSet)
    (t := E.powerset) (fun w hw => ?_)]
  · refine sum_congr rfl fun D hD => ?_
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and]
    have hDE := mem_powerset.mp hD
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 ▸ hDE⟩, h3⟩
  · simp only [coe_filter, mem_univ, true_and, mem_coe, mem_powerset] at hw ⊢
    exact hw.2

/-- Möbius inversion on the Boolean lattice: if `G T = ∑ D ⊆ T, F D` for all `T ⊆ S`, then
`F S = ∑ T ⊆ S, (-1)^|S \ T| G T`. -/
private lemma eq_sum_powerset_neg_one_pow_card_mul (F G : Finset ℕ → ℝ) (S : Finset ℕ)
    (h : ∀ T ⊆ S, G T = ∑ D ∈ T.powerset, F D) :
    F S = ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * G T := by
  have h1 : ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * G T =
      ∑ T ∈ S.powerset, ∑ D ∈ T.powerset, (-1 : ℝ) ^ (S \ T).card * F D := by
    refine sum_congr rfl fun T hT => ?_
    rw [h T (mem_powerset.mp hT), mul_sum]
  rw [h1, sum_comm' (t' := S.powerset) (s' := fun D => S.powerset.filter (D ⊆ ·))
    (h := fun T D => by
      simp only [mem_powerset, mem_filter]
      grind)]
  have h2 : ∀ D ∈ S.powerset, ∑ T ∈ S.powerset.filter (D ⊆ ·), (-1 : ℝ) ^ (S \ T).card * F D =
      if D = S then F S else 0 := by
    intro D hD
    have hDS := mem_powerset.mp hD
    rw [← sum_mul]
    have h3 : ∑ T ∈ S.powerset.filter (D ⊆ ·), (-1 : ℝ) ^ (S \ T).card =
        ∑ U ∈ (S \ D).powerset, (-1 : ℝ) ^ U.card := by
      refine sum_nbij' (fun T => S \ T) (fun U => S \ U) ?_ ?_ ?_ ?_ ?_
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT ⊢
        grind
      · intro U hU
        simp only [mem_filter, mem_powerset] at hU ⊢
        grind
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        grind
      · intro U hU
        simp only [mem_powerset] at hU
        grind
      · intro T _
        rfl
    have h4 := congrArg (Int.cast : ℤ → ℝ)
      (sum_powerset_neg_one_pow_card (x := S \ D))
    push_cast at h4
    rw [h3, h4]
    by_cases hDS' : D = S
    · subst hDS'
      simp only [sdiff_self, bot_eq_empty, ↓reduceIte, one_mul]
    · have : S \ D ≠ ∅ := fun he => hDS' (Subset.antisymm hDS (sdiff_eq_empty_iff_subset.mp he))
      simp only [this, hDS', ↓reduceIte, zero_mul]
  rw [sum_congr rfl h2, sum_ite_eq' S.powerset S (fun _ => F S)]
  simp only [mem_powerset, subset_refl, ↓reduceIte]

/-- Reflection maps the subsets of `T ⊆ range n` onto the subsets of `reflectSet n T`. -/
private lemma powerset_reflectSet {n : ℕ} {T : Finset ℕ} (hT : T ⊆ range n) :
    (reflectSet n T).powerset = T.powerset.image (reflectSet n) := by
  ext D
  simp only [mem_powerset, mem_image]
  constructor
  · intro hD
    have hD' : D ⊆ range n := hD.trans (reflectSet_subset_range hT)
    refine ⟨reflectSet n D, ?_, reflectSet_reflectSet hD'⟩
    calc reflectSet n D ⊆ reflectSet n (reflectSet n T) := image_subset_image hD
      _ = T := reflectSet_reflectSet hT
  · rintro ⟨D', hD', rfl⟩
    exact image_subset_image hD'

/-- Reflection is injective on subsets of `range n`. -/
private lemma reflectSet_injOn (n : ℕ) :
    Set.InjOn (reflectSet n) {D : Finset ℕ | D ⊆ range n} := fun A hA B hB hAB => by
  rw [← reflectSet_reflectSet hA, ← reflectSet_reflectSet hB, hAB]

/-- The number of permutations with `w 0 = k` and descent set exactly the reflection of `S` is
the alternating sum over `T ⊆ S` of the counts with descent set inside the reflection of `T`. -/
theorem desCount_reflectSet_eq_sum (n k : ℕ) {S : Finset ℕ} (hS : S ⊆ range n) :
    (desCount n k (reflectSet n S) : ℝ) =
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * (desLeCount n k (reflectSet n T) : ℝ) := by
  refine eq_sum_powerset_neg_one_pow_card_mul (fun D => (desCount n k (reflectSet n D) : ℝ))
    (fun T => (desLeCount n k (reflectSet n T) : ℝ)) S fun T hT => ?_
  have hTr : T ⊆ range n := hT.trans hS
  rw [desLeCount_eq_sum_desCount, Nat.cast_sum, powerset_reflectSet hTr,
    sum_image fun A hA B hB hAB => reflectSet_injOn n
      ((mem_powerset.mp (mem_coe.mp hA)).trans hTr)
      ((mem_powerset.mp (mem_coe.mp hB)).trans hTr) hAB]

end RealRooted.HosterStump

end
