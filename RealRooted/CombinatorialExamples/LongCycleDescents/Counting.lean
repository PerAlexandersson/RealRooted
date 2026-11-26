/-
Copyright (c) 2026 Bowen Zuo and Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo, Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import RealRooted.CombinatorialExamples.LongCycleDescents.Content
public import RealRooted.CombinatorialExamples.LongCycleDescents.Words
import Mathlib.Tactic

/-!
# Counting restricted permutations

Positive-length necklace profiles give the product formula and an executable counting
recurrence. Binomial inversion recovers descent coefficients. Cycle types remove
redundant cutoffs above the first single-cycle cutoff.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0).
-/

@[expose] public noncomputable section

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

namespace RealRooted.LongCycleDescents.Necklace
open Finset Polynomial

/-- Multisets of size a from a type with M elements. -/
def multiplicityWeight (M a : ℕ) : ℕ := M.ascFactorial a / a.factorial

/-- The multiset weight is the usual stars-and-bars binomial coefficient. -/
theorem multiplicityWeight_eq_choose (M a : ℕ) :
    multiplicityWeight M a = (M + a - 1).choose a :=
  (Nat.choose_eq_asc_factorial_div_factorial' M a).symm

/-- Truncated factor contributed by one positive-length factor. -/
noncomputable def lengthFactor (bound weight M : ℕ) : ℕ[X] :=
  ∑ a : Fin (bound + 1), monomial (weight * a.val) (multiplicityWeight M a.val)

private theorem prod_monomial_eq {ι : Type*} (s : Finset ι) (e c : ι → ℕ) :
    (∏ i ∈ s, monomial (e i) (c i)) = monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      Polynomial.monomial_mul_monomial]

private theorem forbidden_factor_zero (a : ℕ) (positive : 0 < a) :
    multiplicityWeight 0 a = 0 := by
  rw [multiplicityWeight_eq_choose]
  exact Nat.choose_eq_zero_of_lt (by lia)

/-- The weighted profile sum is exactly one coefficient of the product of length factors. -/
theorem coeff_lengthFactors_eq_profile {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w M : ι → ℕ) (n k : ℕ) :
    (∏ i, lengthFactor n (w i) (if w i < k then 0 else M i)).coeff n =
      ∑ p : WeightedProfile w n k, ∏ i, multiplicityWeight (M i) (p.val i).val := by
  classical
  simp only [lengthFactor, Fintype.prod_sum, prod_monomial_eq, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply]
  let valid (f : ι → Fin (n + 1)) : Prop :=
    (∑ i, w i * (f i).val) = n ∧ ∀ i, w i < k → f i = 0
  have convertSum :
      (∑ p : WeightedProfile w n k, ∏ i, multiplicityWeight (M i) (p.val i).val) =
        ∑ f ∈ univ.filter valid, ∏ i, multiplicityWeight (M i) (f i).val := by
    change (∑ p : {f // valid f}, ∏ i, multiplicityWeight (M i) (p.val i).val) = _
    exact (Finset.sum_subtype (p := valid) (univ.filter valid)
      (fun _ ↦ by simp only [mem_filter, mem_univ, true_and])
      (fun f ↦ ∏ i, multiplicityWeight (M i) (f i).val)).symm
  rw [convertSum, Finset.sum_filter]
  apply sum_congr rfl
  intro f _
  by_cases total : (∑ i, w i * (f i).val) = n
  · by_cases allowed : ∀ i, w i < k → f i = 0
    · have hv : valid f := ⟨total, allowed⟩
      rw [ite_eq_left total, ite_eq_left hv]
      apply prod_congr rfl
      intro i _
      by_cases cut : w i < k
      · rw [ite_eq_left cut, allowed i cut]
        simp [multiplicityWeight]
      · rw [ite_eq_right cut]
    · have hm : ¬ valid f := fun h ↦ allowed h.2
      push Not at allowed
      obtain ⟨i, cut, nonzero⟩ := allowed
      rw [ite_eq_left total, ite_eq_right hm]
      apply Finset.prod_eq_zero (mem_univ i)
      rw [ite_eq_left cut]
      exact forbidden_factor_zero _ (Nat.pos_of_ne_zero (fun e ↦ nonzero (Fin.ext e)))
  · have hm : ¬ valid f := fun h ↦ total h.1
    rw [ite_eq_right total, ite_eq_right hm]

private theorem coeff_mul_monomial_piece (p : ℕ[X]) (w c d : ℕ) :
    (p * monomial w c).coeff d = if w ≤ d then p.coeff (d - w) * c else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow']
  split
  · rw [coeff_mul_C]
  · rfl

/-- Each coefficient uses only multiplicities that fit the remaining weight. -/
theorem coeff_mul_lengthFactor (p : ℕ[X]) {bound w : ℕ} (positive : 0 < w)
    (M : ℕ) {d : ℕ} (fits : d ≤ bound) :
    (p * lengthFactor bound w M).coeff d =
      ∑ a ∈ range (d / w + 1), p.coeff (d - w * a) * multiplicityWeight M a := by
  rw [lengthFactor, mul_sum, Polynomial.finsetSum_coeff]
  simp only [coeff_mul_monomial_piece]
  rw [Fin.sum_univ_eq_sum_range
    (fun a ↦ if w * a ≤ d then p.coeff (d - w * a) * multiplicityWeight M a else 0)]
  have contain : range (d / w + 1) ⊆ range (bound + 1) :=
    range_mono (Nat.succ_le_succ ((Nat.div_le_self d w).trans fits))
  have admissible (a : ℕ) : w * a ≤ d ↔ a ∈ range (d / w + 1) := by
    rw [mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le positive, Nat.mul_comm a w]
  rw [← sum_subset contain (fun a _ excluded ↦ ite_eq_right ((admissible a).not.mpr excluded))]
  exact sum_congr rfl fun a included ↦ ite_eq_left ((admissible a).mpr included)

private theorem list_range_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

/-- Store coefficient values through the fixed truncation bound. -/
def initialTable (bound : ℕ) : Array ℕ :=
  Array.ofFn fun d : Fin (bound + 1) ↦ if d.val = 0 then 1 else 0

/-- Update the descentPolynomial by one positive-length factor, using only in-range shifts. -/
def convolveTable (bound weight M : ℕ) (old : Array ℕ) : Array ℕ :=
  if M = 0 then old else
    let weights := Array.ofFn (fun a : Fin (bound / weight + 1) ↦
      multiplicityWeight M a.val)
    Array.ofFn fun d : Fin (bound + 1) ↦
      ((List.range (d.val / weight + 1)).map (fun a ↦
        old.getD (d.val - weight * a) 0 * weights.getD a 0)).sum

private theorem getD_ofFn_nat {bound d : ℕ} (fits : d ≤ bound)
    (f : Fin (bound + 1) → ℕ) : (Array.ofFn f).getD d 0 = f ⟨d, Nat.lt_succ_of_le fits⟩ := by
  have index_lt : d < (Array.ofFn f).size := by simpa using Nat.lt_succ_of_le fits
  rw [Array.getD, dite_eq_left index_lt]
  change (Array.ofFn f)[d]'index_lt = _
  rw [Array.getElem_ofFn]

/-- The executable descentPolynomial update is exact on every stored coefficient. -/
theorem convolveTable_correct {bound w : ℕ} (positive : 0 < w) (M : ℕ)
    (old : Array ℕ) (p : ℕ[X])
    (correct : ∀ i ≤ bound, old.getD i 0 = p.coeff i)
    {d : ℕ} (fits : d ≤ bound) :
    (convolveTable bound w M old).getD d 0 = (p * lengthFactor bound w M).coeff d := by
  by_cases empty : M = 0
  · subst M
    rw [convolveTable, ite_eq_left rfl, correct d fits, coeff_mul_lengthFactor p positive 0 fits,
      sum_eq_single_of_mem 0 (mem_range.mpr (Nat.succ_pos _))]
    · simp [multiplicityWeight]
    · intro a _ nonzero
      rw [forbidden_factor_zero a (Nat.pos_of_ne_zero nonzero), Nat.mul_zero]
  · rw [convolveTable, ite_eq_right empty, getD_ofFn_nat fits, list_range_sum,
      coeff_mul_lengthFactor p positive M fits]
    apply sum_congr rfl
    intro a ha
    have shiftBound : a ≤ bound / w :=
      (Nat.lt_succ_iff.mp (mem_range.mp ha)).trans (Nat.div_le_div_right fits)
    rw [getD_ofFn_nat shiftBound, correct (d - w * a) ((Nat.sub_le ..).trans fits)]

/-- Fold through factors from right to left, as in the descending-length implementation. -/
def countTable (bound : ℕ) (factors : List (ℕ × ℕ)) : Array ℕ :=
  factors.foldr (fun pair old ↦ convolveTable bound pair.1 pair.2 old) (initialTable bound)

/-- The complete dynamic-programming table represents the product's truncated coefficients. -/
theorem countTable_correct (bound : ℕ) (factors : List (ℕ × ℕ))
    (positive : ∀ pair ∈ factors, 0 < pair.1) {d : ℕ} (fits : d ≤ bound) :
    (countTable bound factors).getD d 0 =
      (factors.map (fun pair ↦ lengthFactor bound pair.1 pair.2)).prod.coeff d := by
  induction factors generalizing d with
  | nil =>
    rw [countTable, List.foldr_nil, initialTable, getD_ofFn_nat fits]
    simp [Polynomial.coeff_one]
  | cons pair tail ih =>
    have hw := positive pair (List.mem_cons_self)
    have ht : ∀ f ∈ tail, 0 < f.1 := fun f hf ↦ positive f (List.mem_cons_of_mem _ hf)
    let previous := (tail.map (fun f ↦ lengthFactor bound f.1 f.2)).prod
    change (convolveTable bound pair.1 pair.2 (countTable bound tail)).getD d 0 =
      (lengthFactor bound pair.1 pair.2 * previous).coeff d
    rw [mul_comm]
    have old : ∀ i ≤ bound, (countTable bound tail).getD i 0 = previous.coeff i := by
      intro i hi
      exact ih ht (d := i) hi
    exact convolveTable_correct hw pair.2 (countTable bound tail) previous old fits

/-- For each positive length, store the number of available types.
Below-cutoff factors have no types. -/
def positiveFactors (n q k : ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun j : Fin n ↦
    (j.val + 1, if j.val + 1 < k then 0 else primitiveCount (j.val + 1) q))

/-- The positive inventory count obtained from the final dynamic-programming coefficient. -/
def positiveCountDP (n q k : ℕ) : ℕ :=
  (countTable n (positiveFactors n q k)).getD n 0

/-- The dynamic program sums exactly the allowed multiplicity profiles. -/
theorem positiveCountDP_eq_profile (n q k : ℕ) :
    positiveCountDP n q k =
      ∑ p : PositiveLengthProfile n k, ∏ j : Fin n,
        multiplicityWeight (primitiveCount (j.val + 1) q) (p.val j).val := by
  have pos : ∀ pair ∈ positiveFactors n q k, 0 < pair.1 := by
    intro pair h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact Nat.succ_pos i.val
  unfold positiveCountDP
  rw [countTable_correct n _ pos (le_refl _)]
  simp only [positiveFactors, List.map_ofFn, List.prod_ofFn]
  exact coeff_lengthFactors_eq_profile (fun j : Fin n ↦ j.val + 1)
    (fun j : Fin n ↦ primitiveCount (j.val + 1) q) n k

/-- The executable count also includes the unique empty inventory at total weight zero. -/
theorem card_necklaceContent_eq_positiveCountDP (n q k : ℕ) :
    Nat.card (NecklaceContent n q k) = positiveCountDP n q k := by
  rw [card_necklaceContent_eq_positive_sum, positiveCountDP_eq_profile]
  simp only [multiplicityWeight_eq_choose, Nat.multichoose_eq,
    primitiveCount_eq_card (Nat.succ_pos _)]

/-- Exact readout of the original finite-alphabet specialization by the positive DP. -/
theorem letters_eq_positiveCountDP {n : ℕ} (hn : 0 < n) (q k : ℕ) :
    letters n q (descentPolynomial n k).coeff =
      (positiveCountDP n q k : ℤ) := by
  rw [letters_eq_positive_choose hn q k, positiveCountDP_eq_profile]
  simp [multiplicityWeight_eq_choose]

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents.Necklace
open PowerSeries Finset RealRooted.LongCycleDescents

/-- The degree-bounded numerator associated to an ascending coefficient function. -/
def numerator (n : ℕ) (d : ℕ → ℤ) : PowerSeries ℤ :=
  ∑ i ∈ range n, C (d i) * X ^ i

/-- Below the truncation degree, the numerator has the supplied coefficients. -/
theorem coeff_numerator (n r : ℕ) (d : ℕ → ℤ) (hr : r < n) :
    coeff r (numerator n d) = d r := by
  simp only [numerator,map_sum,coeff_C_mul_X_pow]
  simp [hr]

/-- Alphabet specializations are the numerator divided by a power of one minus the variable. -/
theorem series_of_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    mk (fun r ↦ letters n (r + 1) d) =
      numerator n d * (mk (fun j ↦ ((n + j).choose n : ℤ)) : PowerSeries ℤ) := by
  ext r
  rw [coeff_mk,numerator,Finset.sum_mul,map_sum]
  unfold letters
  apply sum_congr rfl
  intro i _
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  by_cases hi : i ≤ r
  · rw [ite_eq_left hi,coeff_mk]
    congr 3
    lia
  · rw [ite_eq_right hi,Nat.choose_eq_zero_of_lt (show (r + 1 + n - 1 - i) < n by lia)]
    simp

/-- Multiplying the alphabet series by the binomial denominator recovers the numerator. -/
theorem numerator_from_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) :
    numerator n d = (1 - X : PowerSeries ℤ)^(n + 1) *
      PowerSeries.mk (fun r ↦ letters n (r + 1) d) := by
  rw [series_of_letters hn, mul_comm, mul_assoc, mk_add_choose_mul_one_sub_pow_eq_one, mul_one]

/-- The coefficients of a power of one minus the variable are signed binomial coefficients. -/
theorem coeff_one_sub_X_pow (n j : ℕ) :
    coeff j ((1 - X : PowerSeries ℤ)^n) = (-1:ℤ)^j * n.choose j := by
  have h := coeff_rescale ((X + 1 : PowerSeries ℤ)^n) (-1) j
  have plus : coeff j ((X + 1 : PowerSeries ℤ)^n) = (n.choose j : ℤ) := by
    simpa only [← Polynomial.coe_X, ← Polynomial.coe_one, ← Polynomial.coe_add,
      ← Polynomial.coe_pow,Polynomial.coeff_coe] using Polynomial.coeff_X_add_one_pow (R := ℤ) n j
  rw [plus] at h
  simpa [map_pow,map_add,sub_eq_add_neg,add_comm] using h

/-- Signed binomial inversion recovers each numerator coefficient from alphabet evaluations. -/
theorem invert_letters {n : ℕ} (hn : 0 < n) (d : ℕ → ℤ) {r : ℕ} (hr : r < n) :
    d r = ∑ j ∈ range (r + 1), (-1:ℤ)^j * (n + 1).choose j * letters n (r - j + 1) d := by
  rw [← coeff_numerator n r d hr,numerator_from_letters hn,coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow,coeff_mk]

/-- Recover the original descent coefficients from necklace-content cardinalities. -/
theorem coeff_descentPolynomial_from_necklaces {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    (descentPolynomial n k).coeff r = ∑ j ∈ range (r + 1), (-1:ℤ)^j * (n + 1).choose j *
      (Nat.card (NecklaceContent n (r - j + 1) k) : ℤ) := by
  simpa only [letters_eq_necklace_content hn] using invert_letters hn (descentPolynomial n
    k).coeff hr

/-- Division and binomial coefficients here are the natural/integer ones of the finite checker. -/
theorem coeff_descentPolynomial_positive_choose {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    (descentPolynomial n k).coeff r = ∑ j ∈ range (r + 1), (-1:ℤ)^j * (n + 1).choose j *
      (∑ p : PositiveLengthProfile n k, ∏ i : Fin n,
        (Nat.choose (primitiveCount (i.val + 1) (r - j + 1) + (p.val i).val - 1)
          (p.val i).val : ℤ)) := by
  simpa only [letters_eq_positive_choose hn] using invert_letters hn (descentPolynomial n
    k).coeff hr

end RealRooted.LongCycleDescents.Necklace

namespace RealRooted.LongCycleDescents

open Finset Polynomial
/-- Every genuine cycle length of an admissible permutation meets the
cutoff. Mathlib's cycleType omits fixed points; support_univ_of_allowed
below is needed before its sum may be identified with n. -/
theorem le_of_mem_cycleType {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : HasLongCycles k σ) {m : ℕ} (hm : m ∈ σ.cycleType) : k ≤ m := by
  obtain ⟨c, τ, heq, hd, hc, hm'⟩ := Equiv.Perm.mem_cycleType_iff.mp hm
  have ho : orderOf c = m := hc.orderOf.trans hm'
  obtain ⟨x, hx, _⟩ := hc
  have hf : τ x = x := (hd x).resolve_left hx
  have hmpos : 0 < m := lt_trans (by decide : 0 < 1)
    (Equiv.Perm.one_lt_of_mem_cycleType hm)
  have hpow : (c ^ m) = 1 := ho ▸ pow_orderOf_eq_one c
  by_contra! hmk
  apply h x m hmpos hmk
  rw [heq, hd.commute.mul_pow, Equiv.Perm.mul_apply,
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hf, hpow, Equiv.Perm.one_apply]

/-- A cutoff above one forces every point into the permutation support. -/
theorem support_univ_of_allowed {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : HasLongCycles k σ) (hk : 1 < k) : σ.support = Finset.univ := by
  ext x
  simp [Equiv.Perm.mem_support, ne_fixed_of_allowed h hk x]

/-- Recover the original return-time test from cycleType. Its omitted
fixed points have to be excluded explicitly. -/
theorem allowed_of_cycleType_lower {n k : ℕ} {σ : Equiv.Perm (Fin n)}
    (hs : σ.support = Finset.univ) (hl : ∀ m ∈ σ.cycleType, k ≤ m) :
    HasLongCycles k σ := by
  classical
  intro x j hj hjk
  have hx : x ∈ σ.support := by rw [hs]; exact Finset.mem_univ _
  have hmove := Equiv.Perm.mem_support.mp hx
  have hc := Equiv.Perm.isCycle_cycleOf σ hmove
  have hm : (σ.cycleOf x).support.card ∈ σ.cycleType := by
    rw [Equiv.Perm.cycleType, Multiset.mem_map]
    exact ⟨σ.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx, rfl⟩
  have hjord : j < orderOf (σ.cycleOf x) := by
    rw [hc.orderOf]
    exact hjk.trans_le (hl _ hm)
  have hx' : x ∈ (σ.cycleOf x).support := Equiv.Perm.mem_support.mpr (by
    simpa only [Equiv.Perm.cycleOf_apply_self] using hmove)
  rw [← hc.support_pow_of_pos_of_lt_orderOf hj hjord, Equiv.Perm.mem_support,
    Equiv.Perm.cycleOf_pow_apply_self] at hx'
  exact hx'

private theorem allowed_iff_single_cycleType {n k : ℕ} (hk : 2 ≤ k) (kn : k ≤ n)
    (one : n < 2 * k) (σ : Equiv.Perm (Fin n)) :
    HasLongCycles k σ ↔ σ.cycleType = {n} := by
  constructor
  · intro allowed
    have sum : σ.cycleType.toList.sum = n := by
      simp [Equiv.Perm.sum_cycleType, support_univ_of_allowed allowed hk]
    have lower : ∀ j ∈ σ.cycleType.toList, k ≤ j :=
      fun j hj ↦ le_of_mem_cycleType allowed (by simpa using hj)
    have single : σ.cycleType.toList = [n] := by
      generalize σ.cycleType.toList = l at sum lower ⊢
      cases l with
      | nil => simp only [List.sum_nil] at sum; lia
      | cons a rest =>
        cases rest with
        | nil => simpa using sum
        | cons b rest =>
          have ha := lower a (by simp)
          have hb := lower b (by simp)
          simp only [List.sum_cons] at sum
          lia
    simpa using congrArg (fun words : List ℕ ↦ (words : Multiset ℕ)) single
  · intro single
    apply allowed_of_cycleType_lower
    · apply Finset.eq_univ_of_card
      rw [← Equiv.Perm.sum_cycleType, single, Fintype.card_fin]
      simp
    · intro j hj
      rw [single, Multiset.mem_singleton] at hj
      exact hj.symm ▸ kn

/-- The last distinct cutoff needed at size n is the first that permits only one cycle. -/
def lastRepresentative (n : ℕ) : ℕ := max 3 (n / 2 + 1)

/-- Cutoffs above the first single-cycle cutoff give the same original descent polynomial. -/
theorem row_eq_representative {n k : ℕ} (hk : 3 ≤ k) (kn : k ≤ n) :
    descentPolynomial n k =
      descentPolynomial n (min k (lastRepresentative n)) := by
  by_cases below : k ≤ lastRepresentative n
  · rw [min_eq_left below]
  · have h := Nat.lt_of_not_ge below
    have atLeast : 3 ≤ lastRepresentative n := le_max_left ..
    have larger : n / 2 + 1 ≤ lastRepresentative n := le_max_right ..
    rw [min_eq_right h.le]
    unfold descentPolynomial
    apply sum_congr rfl
    intro σ _
    rw [allowed_iff_single_cycleType (by lia) kn (by lia),
      allowed_iff_single_cycleType (by lia) (h.le.trans kn) (by lia)]

end RealRooted.LongCycleDescents
