/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Content
public import Mathlib.Data.Finsupp.Multiset
import Mathlib.Tactic

/-! Counting multiplicities by their total at each permitted positive length.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section
namespace RealRooted.LongCycleDescents.Necklace

open Finset RealRooted.LongCycleDescents.Words

/-- A finite profile of multiplicity totals, one at each index of positive weight. -/
def WeightedProfile {ι : Type*} [Fintype ι] (w : ι → ℕ) (n k : ℕ) :=
  {p : ι → Fin (n + 1) // (∑ i, w i * (p i).val) = n ∧ ∀ i, w i < k → p i = 0}

/-- Weighted multiplicity profiles of fixed bounded total form a finite type. -/
noncomputable instance instFintypeWeightedProfile {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ) (n k : ℕ) : Fintype (WeightedProfile w n k) := by
  unfold WeightedProfile
  infer_instance

/-- Multiplicities of types indexed by weight, with total weight and a lower cutoff. -/
def WeightedContent {ι : Type*} [Fintype ι] (β : ι → Type*) [∀ i, Fintype (β i)]
    (w : ι → ℕ) (n k : ℕ) :=
  {a : (Sigma β) → ℕ // (∑ N, w N.1 * a N) = n ∧ ∀ N, 0 < a N → k ≤ w N.1}

section Weighted

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)]
variable {w : ι → ℕ} {n k : ℕ}

private def fiberCounts (α : Type*) [Fintype α] (m : ℕ) :
    Sym α m ≃ {p : α → ℕ // ∑ a, p a = m} := by
  classical
  exact Sym.equivNatSumOfFintype α m

private def profilesToContent
    (s : Σ p : WeightedProfile w n k, ∀ i, Sym (β i) (p.val i).val) :
    WeightedContent β w n k := by
  let a (N : Sigma β) := (fiberCounts (β N.1) _ (s.2 N.1)).val N.2
  have exactMass (i : ι) : (∑ b : β i, a ⟨i, b⟩) = (s.1.val i).val :=
    (fiberCounts (β i) _ (s.2 i)).property
  refine ⟨a, ?_, ?_⟩
  · rw [Fintype.sum_sigma]
    simpa only [← Finset.mul_sum, exactMass] using s.1.property.1
  · intro N positive
    apply Nat.le_of_not_gt
    intro below
    have total_zero : (∑ b : β N.1, a ⟨N.1, b⟩) = 0 := by
      rw [exactMass, s.1.property.2 N.1 below]
      rfl
    have bounded : a N ≤ ∑ b : β N.1, a ⟨N.1, b⟩ :=
      Finset.single_le_sum (f := fun b : β N.1 ↦ a ⟨N.1, b⟩)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ N.2)
    lia

private theorem profilesToContent_injective :
    Function.Injective (profilesToContent (β := β) (w := w) (n := n) (k := k)) := by
  rintro ⟨p, s⟩ ⟨q, t⟩ equal
  have same (i : ι) (b : β i) :
      (fiberCounts (β i) _ (s i)).val b = (fiberCounts (β i) _ (t i)).val b :=
    congrArg (fun a : WeightedContent β w n k ↦ a.val ⟨i, b⟩) equal
  have profilesEqual : p = q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rw [← (fiberCounts (β i) _ (s i)).property,
      ← (fiberCounts (β i) _ (t i)).property]
    exact sum_congr rfl fun a _ ↦ same i a
  subst q
  congr 1
  funext i
  apply (fiberCounts (β i) _).injective
  exact Subtype.ext (funext (same i))

private theorem sum_by_index (a : Sigma β → ℕ) :
    (∑ N, w N.1 * a N) = ∑ i, w i * (∑ b : β i, a ⟨i, b⟩) := by
  rw [Fintype.sum_sigma]
  simp only [Finset.mul_sum]

private theorem profilesToContent_surjective (positive : ∀ i, 0 < w i) :
    Function.Surjective (profilesToContent (β := β) (w := w) (n := n) (k := k)) := by
  intro a
  let totals (i : ι) := ∑ b : β i, a.val ⟨i, b⟩
  have totalWeight : (∑ i, w i * totals i) = n :=
    (sum_by_index (w := w) a.val).symm.trans a.property.1
  have bounded (i : ι) : totals i < n + 1 := by
    have leTerm : w i * totals i ≤ n :=
      totalWeight ▸ (Finset.single_le_sum (f := fun j ↦ w j * totals j)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ i) :
        w i * totals i ≤ ∑ j, w j * totals j)
    have leMul : totals i ≤ w i * totals i := by
      simpa using Nat.mul_le_mul_right (totals i) (positive i)
    exact Nat.lt_succ_of_le (leMul.trans leTerm)
  let profile : WeightedProfile w n k :=
    ⟨fun i ↦ ⟨totals i, bounded i⟩, totalWeight, by
      intro i below
      apply Fin.ext
      change totals i = 0
      apply sum_eq_zero
      intro b _
      exact Nat.eq_zero_of_not_pos fun h ↦ (not_le_of_gt below) (a.property.2 ⟨i,b⟩ h)⟩
  let fiber (i : ι) : Sym (β i) (profile.val i).val :=
    (fiberCounts (β i) _).symm ⟨fun b ↦ a.val ⟨i, b⟩, rfl⟩
  refine ⟨⟨profile, fiber⟩, Subtype.ext ?_⟩
  funext N
  obtain ⟨i, b⟩ := N
  change (fiberCounts (β i) _ (fiber i)).val b = a.val ⟨i, b⟩
  simp [fiber]

/-- Partition the multiplicity functions by their totals at every length and count each class. -/
theorem card_weightedContent_eq_sum [DecidableEq ι] (positive : ∀ i, 0 < w i) :
    Nat.card (WeightedContent β w n k) =
      ∑ p : WeightedProfile w n k, ∏ i, Nat.multichoose (Fintype.card (β i)) (p.val i).val := by
  classical
  have eqv := Equiv.ofBijective (profilesToContent (β := β) (w := w) (n := n) (k := k))
    ⟨profilesToContent_injective, profilesToContent_surjective positive⟩
  rw [← Nat.card_congr eqv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [Fintype.card_pi]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [← Nat.card_eq_fintype_card, card_multisets]

end Weighted
/-- Multiplicity profiles indexed by factorial-divisor lengths. -/
abbrev LengthProfile (n k : ℕ) :=
  WeightedProfile (fun d : Lengths n ↦ d.val) n k

/-- The count for the original content model indexed by the factorial divisors. -/
theorem card_necklaceContent_eq_sum (n q k : ℕ) :
    Nat.card (NecklaceContent n q k) =
      ∑ p : LengthProfile n k, ∏ d : Lengths n,
        Nat.multichoose (Fintype.card (PrimitiveNecklace d.val q)) (p.val d).val :=
  card_weightedContent_eq_sum (fun d ↦ Nat.pos_of_mem_divisors d.property)

private def smallLengthEquiv (n : ℕ) : Fin n ≃ {d : Lengths n // d.val ≤ n} where
  toFun j :=
    ⟨⟨j.val + 1, Nat.mem_divisors.mpr
      ⟨Nat.dvd_factorial (Nat.succ_pos _) (Nat.succ_le_of_lt j.isLt),
        (Nat.factorial_pos n).ne'⟩⟩, Nat.succ_le_of_lt j.isLt⟩
  invFun d := ⟨d.val.val - 1, by
    have h := Nat.pos_of_mem_divisors d.val.property
    have le := d.property
    lia⟩
  left_inv j := by
    apply Fin.ext
    exact Nat.add_sub_cancel _ _
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    exact Nat.sub_add_cancel (Nat.pos_of_mem_divisors d.val.property)

private def smallTypeEquiv (n q : ℕ) :
    (Σ j : Fin n, PrimitiveNecklace (j.val + 1) q) ≃
      {N : Types n q // N.1.val ≤ n} := by
  let regroup :
      (Σ d : {d : Lengths n // d.val ≤ n}, PrimitiveNecklace d.val.val q) ≃
        {N : Types n q // N.1.val ≤ n} :=
    { toFun := fun ⟨⟨d, h⟩, N⟩ ↦ ⟨⟨d, N⟩, h⟩
      invFun := fun ⟨⟨d, N⟩, h⟩ ↦ ⟨⟨d, h⟩, N⟩
      left_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl
      right_inv := by rintro ⟨⟨_, _⟩, _⟩; rfl }
  exact (Equiv.sigmaCongr (smallLengthEquiv n) (fun j ↦
    Equiv.refl (PrimitiveNecklace (j.val + 1) q))).trans regroup

private theorem smallType_length (n q : ℕ)
    (N : Σ j : Fin n, PrimitiveNecklace (j.val + 1) q) :
    ((smallTypeEquiv n q N).val.1.val) = N.1.val + 1 := rfl

private theorem content_zero_of_large {n q k : ℕ} (a : NecklaceContent n q k)
    (N : Types n q) (large : n < N.1.val) : a.val N = 0 := by
  have hterm :
      N.1.val * a.val N ≤ ∑ T : Types n q, T.1.val * a.val T :=
    Finset.single_le_sum (f := fun T : Types n q ↦ T.1.val * a.val T)
      (fun _ _ ↦ Nat.zero_le _) (mem_univ N)
  rw [a.property.1] at hterm
  apply Nat.eq_zero_of_not_pos
  intro h
  have below : N.1.val ≤ N.1.val * a.val N := by
    simpa using Nat.mul_le_mul_left N.1.val h
  exact (not_le_of_gt large) (below.trans hterm)

private theorem sum_short_types {n q : ℕ} (f : Types n q → ℕ)
    (vanish : ∀ N, n < N.1.val → f N = 0) :
    (∑ N, f N) = ∑ T, f (smallTypeEquiv n q T).val := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun N : Types n q ↦ N.1.val ≤ n) f]
  have zero : (∑ X : {N : Types n q // ¬ N.1.val ≤ n}, f X.val) = 0 :=
    sum_eq_zero fun X _ ↦ vanish X.val (Nat.lt_of_not_ge X.property)
  rw [zero, add_zero]
  exact ((smallTypeEquiv n q).sum_comp (fun N ↦ f N.val)).symm

private def restrictContent (n q k : ℕ) (a : NecklaceContent n q k) :
    WeightedContent (fun j : Fin n ↦ PrimitiveNecklace (j.val + 1) q)
      (fun j ↦ j.val + 1) n k := by
  refine ⟨fun T ↦ a.val (smallTypeEquiv n q T).val, ?_, ?_⟩
  · have h := sum_short_types (fun N : Types n q ↦ N.1.val * a.val N)
      (fun N large ↦ by rw [content_zero_of_large a N large, Nat.mul_zero])
    rw [a.property.1] at h
    simpa only [smallType_length] using h.symm
  · intro T positive
    simpa only [smallType_length] using a.property.2 (smallTypeEquiv n q T).val positive

private theorem restrictContent_injective (n q k : ℕ) :
    Function.Injective (restrictContent n q k) := by
  intro a b equal
  apply Subtype.ext
  funext N
  by_cases small : N.1.val ≤ n
  · have h := congrArg (fun c ↦ c.val ((smallTypeEquiv n q).symm ⟨N, small⟩)) equal
    change a.val (smallTypeEquiv n q ((smallTypeEquiv n q).symm ⟨N, small⟩)).val =
      b.val (smallTypeEquiv n q ((smallTypeEquiv n q).symm ⟨N, small⟩)).val at h
    simpa only [Equiv.apply_symm_apply] using h
  · rw [content_zero_of_large a N (Nat.lt_of_not_ge small),
      content_zero_of_large b N (Nat.lt_of_not_ge small)]

private theorem restrictContent_surjective (n q k : ℕ) :
    Function.Surjective (restrictContent n q k) := by
  intro a
  let extend (N : Types n q) :=
    if h : N.1.val ≤ n then a.val ((smallTypeEquiv n q).symm ⟨N, h⟩) else 0
  have exact_value (T : Σ j : Fin n, PrimitiveNecklace (j.val + 1) q) :
      extend (smallTypeEquiv n q T).val = a.val T := by
    simp [extend, (smallTypeEquiv n q T).property]
  have total : (∑ N, N.1.val * extend N) = n := by
    rw [sum_short_types _ (fun N large ↦ by simp [extend, Nat.not_le_of_gt large])]
    simpa only [smallType_length, exact_value] using a.property.1
  have cutoff (N : Types n q) (positive : 0 < extend N) : k ≤ N.1.val := by
    by_cases h : N.1.val ≤ n
    · have hc := a.property.2 ((smallTypeEquiv n q).symm ⟨N, h⟩) (by
        simpa [extend, h] using positive)
      have d := smallType_length n q ((smallTypeEquiv n q).symm ⟨N, h⟩)
      rw [Equiv.apply_symm_apply] at d
      exact hc.trans_eq d.symm
    · simp [extend, h] at positive
  refine ⟨⟨extend, total, cutoff⟩, Subtype.ext ?_⟩
  exact funext exact_value

/-- Profiles indexed exactly by the lengths 1 through n, where j denotes length j+1. -/
abbrev PositiveLengthProfile (n k : ℕ) :=
  WeightedProfile (fun j : Fin n ↦ j.val + 1) n k

/-- The positive product formula from the actual necklace content, with no length-zero term. -/
theorem card_necklaceContent_eq_positive_sum (n q k : ℕ) :
    Nat.card (NecklaceContent n q k) =
      ∑ p : PositiveLengthProfile n k, ∏ j : Fin n,
        Nat.multichoose (Fintype.card (PrimitiveNecklace (j.val + 1) q)) (p.val j).val := by
  rw [Nat.card_congr (Equiv.ofBijective (restrictContent n q k)
    ⟨restrictContent_injective n q k, restrictContent_surjective n q k⟩)]
  exact card_weightedContent_eq_sum (fun j ↦ Nat.succ_pos j.val)

/-- The same positive product formula for the original finite-alphabet descent specialization. -/
theorem letters_eq_positive_sum {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    letters n q (descentPolynomial n k).coeff =
      ∑ p : PositiveLengthProfile n k, ∏ j : Fin n,
        (Nat.multichoose (Fintype.card (PrimitiveNecklace (j.val + 1) q)) (p.val j).val : ℤ) := by
  rw [letters_eq_necklace_content hn q k, card_necklaceContent_eq_positive_sum]
  simp

open scoped ArithmeticFunction.Moebius

/-- The integer Möbius formula used by the positive counting product. -/
def primitiveCount (j q : ℕ) : ℕ :=
  ((∑ d ∈ j.divisors, μ d * (q : ℤ) ^ (j / d)) / (j : ℤ)).toNat

/-- The integer Möbius expression counts the primitive necklace classes exactly. -/
theorem primitiveCount_eq_card {j : ℕ} (hj : 0 < j) (q : ℕ) :
    primitiveCount j q = Fintype.card (PrimitiveNecklace j q) := by
  unfold primitiveCount
  rw [← card_primitiveNecklace hj q, Int.toNat_natCast]

/-- The positive product specialization using integer Möbius sums and ordinary choose. -/
theorem letters_eq_positive_choose {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    letters n q (descentPolynomial n k).coeff =
      ∑ p : PositiveLengthProfile n k, ∏ j : Fin n,
        (Nat.choose (primitiveCount (j.val + 1) q + (p.val j).val - 1) (p.val j).val : ℤ) := by
  rw [letters_eq_positive_sum hn q k]
  simp only [primitiveCount_eq_card (Nat.succ_pos _), Nat.multichoose_eq]

/-- Total weight zero gives the unique empty inventory. -/
theorem card_necklaceContent_zero (q k : ℕ) : Nat.card (NecklaceContent 0 q k) = 1 := by
  have h := card_allowedCompatible_eq_letters_add_empty 0 q k
  rw [Nat.card_congr (originalNecklaceEquiv 0 q k)] at h
  have cast : (Nat.card (NecklaceContent 0 q k) : ℤ) = 1 := by
    simpa [letters] using h
  exact_mod_cast cast

end RealRooted.LongCycleDescents.Necklace

end
