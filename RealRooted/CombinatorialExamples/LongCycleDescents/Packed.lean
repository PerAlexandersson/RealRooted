/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Coefficients
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Radix compression of the positive necklace dynamic program

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset
open scoped Classical

private theorem countTable_cons_at (bound : ℕ) {w M d : ℕ}
    (hw : 0 < w) (fits : d ≤ bound) (l : List (ℕ × ℕ))
    (positive : ∀ pair ∈ l, 0 < pair.1) :
    (countTable bound ((w, M) :: l)).getD d 0 =
      ∑ a ∈ range (d / w + 1),
        (countTable bound l).getD (d - w * a) 0 * multiplicityWeight M a := by
  have all : ∀ pair ∈ (w, M) :: l, 0 < pair.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · simpa [h] using hw
    · exact positive p h
  rw [countTable_correct bound _ all fits, List.map_cons, List.prod_cons, mul_comm,
    coeff_mul_lengthFactor _ hw M fits]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [countTable_correct bound l positive ((Nat.sub_le ..).trans fits)]

private theorem countTable_largeLengths (bound d : ℕ) (fits : d ≤ bound)
    (l : List (ℕ × ℕ)) (above : ∀ pair ∈ l, d < pair.1) :
    (countTable bound l).getD d 0 = (initialTable bound).getD d 0 := by
  induction l with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨w, M⟩
    have hw : d < w := above _ List.mem_cons_self
    have tail : ∀ p ∈ rest, d < p.1 := fun p hp ↦ above p (List.mem_cons_of_mem _ hp)
    rw [countTable_cons_at bound (Nat.zero_lt_of_lt hw) fits rest
      (fun p hp ↦ Nat.zero_lt_of_lt (tail p hp))]
    simpa [Nat.div_eq_of_lt hw, multiplicityWeight] using ih tail

/-- Truncation to smaller weights commutes with deleting a suffix of heavier factors. -/
theorem countTable_trim {small large : ℕ} (cap : small ≤ large)
    (kept extra : List (ℕ × ℕ)) (positive : ∀ p ∈ kept, 0 < p.1)
    (above : ∀ p ∈ extra, small < p.1) {d : ℕ} (fits : d ≤ small) :
    (countTable large (kept ++ extra)).getD d 0 = (countTable small kept).getD d 0 := by
  induction kept generalizing d with
  | nil =>
    simp only [List.nil_append]
    rw [countTable_largeLengths large d (fits.trans cap) extra
      (fun p hp ↦ fits.trans_lt (above p hp))]
    simp [countTable, initialTable, fits, fits.trans cap]
  | cons pair rest ih =>
    rcases pair with ⟨w, M⟩
    have hw : 0 < w := positive _ List.mem_cons_self
    have tail : ∀ p ∈ rest, 0 < p.1 := fun p hp ↦ positive p (List.mem_cons_of_mem _ hp)
    have combined : ∀ p ∈ rest ++ extra, 0 < p.1 := by
      intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact tail p h
      · exact Nat.zero_lt_of_lt (above p h)
    rw [List.cons_append, countTable_cons_at large hw (fits.trans cap) _ combined,
      countTable_cons_at small hw fits _ tail]
    exact sum_congr rfl fun a _ ↦
      congrArg (· * multiplicityWeight M a) (ih tail ((Nat.sub_le ..).trans fits))

/-- One counting table built at a larger cap also answers every smaller size. -/
theorem positiveCountDP_at_cap {n bound : ℕ} (fits : n ≤ bound) (q k : ℕ) :
    (countTable bound (positiveFactors bound q k)).getD n 0 = positiveCountDP n q k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le fits
  let remaining := List.ofFn fun i : Fin m ↦
    (n + i.val + 1, if n + i.val + 1 < k then 0 else primitiveCount (n + i.val + 1) q)
  have split : positiveFactors (n + m) q k = positiveFactors n q k ++ remaining := by
    rw [positiveFactors, List.ofFn_add]
    rfl
  have positive : ∀ p ∈ positiveFactors n q k, 0 < p.1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact Nat.succ_pos i.val
  have above : ∀ p ∈ remaining, n < p.1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    change n < n + i.val + 1
    lia
  rw [split]
  exact countTable_trim (by lia) _ _ positive above le_rfl

private theorem positiveCountDP_le_words {n q k : ℕ} (hn : 0 < n) :
    positiveCountDP n q k ≤ q ^ n := by
  have card : Nat.card (AllowedCompatible n q k) = positiveCountDP n q k := by
    have h := card_allowedCompatible_eq_letters hn q k
    rw [letters_eq_positiveCountDP hn q k] at h
    exact_mod_cast h
  rw [← card]
  let forget (x : AllowedCompatible n q k) := (wordEquiv n q).symm x.val
  have inj : Function.Injective forget := fun _ _ e ↦
    Subtype.ext ((wordEquiv n q).symm.injective e)
  simpa [Nat.card_fun] using Nat.card_le_card_of_injective forget inj

/-- The base is strictly larger than every retained coefficient for this alphabet. -/
def cutoffRadix (bound q : ℕ) : ℕ := q ^ bound + 1

private theorem eval_divX_split (base : ℕ) (p : ℕ[X]) :
    p.eval base = p.coeff 0 + (divX p).eval base * base := by
  conv_lhs => rw [← divX_mul_X_add p]
  simp [add_comm]

/-- A coefficient below the radix is the corresponding digit of polynomial evaluation. -/
theorem eval_radix_digit (base : ℕ) (positive : 0 < base) (p : ℕ[X]) (d : ℕ)
    (bounded : ∀ i ≤ d, p.coeff i < base) :
    p.eval base / base ^ d % base = p.coeff d := by
  induction d generalizing p with
  | zero =>
    rw [pow_zero, Nat.div_one, eval_divX_split, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (bounded 0 le_rfl)]
  | succ d ih =>
    have div : p.eval base / base = (divX p).eval base := by
      rw [eval_divX_split, Nat.add_comm, Nat.mul_comm ((divX p).eval base), Nat.mul_add_div
        positive,
        Nat.div_eq_of_lt (bounded 0 (Nat.zero_le _)), Nat.add_zero]
    rw [pow_succ, Nat.mul_comm (base ^ d), ← Nat.div_div_eq_div_mul, div,
      ih (divX p) (fun i hi ↦ by
        rw [coeff_divX]
        exact bounded _ (Nat.succ_le_succ hi)), coeff_divX]

/-- Only monomials that affect the retained degree range are needed in the coded factor. -/
def codedLengthFactor (base bound weight M : ℕ) : ℕ :=
  ((List.range (bound / weight + 1)).map fun j ↦
    multiplicityWeight M j * base ^ (weight * j)).sum

private theorem codedLengthFactor_cast (base bound : ℕ) {weight : ℕ} (hw : 0 < weight) (M : ℕ) :
    ((codedLengthFactor base bound weight M : ℕ) : ZMod (base ^ (bound + 1))) =
      (((lengthFactor bound weight M).eval base : ℕ) : ZMod (base ^ (bound + 1))) := by
  classical
  unfold codedLengthFactor lengthFactor
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ multiplicityWeight M i * base ^ (weight * i))]
  simp only [Nat.cast_sum]
  apply sum_subset (range_mono (Nat.succ_le_succ (Nat.div_le_self _ _)))
  intro a _ notIn
  have greater : bound + 1 ≤ weight * a := by
    by_contra! small
    have fits : weight * a ≤ bound := Nat.lt_succ_iff.mp small
    exact notIn <| mem_range.mpr <| Nat.lt_succ_of_le <|
      (Nat.le_div_iff_mul_le hw).mpr (by simpa [Nat.mul_comm] using fits)
  have disappears : (((base ^ (weight * a) : ℕ) : ZMod (base ^ (bound + 1)))) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le greater
    rw [hm, pow_add base (bound + 1) m]
    exact Nat.dvd_mul_right _ _
  rw [Nat.cast_mul, disappears, mul_zero]

/-- Multiply the truncated factors as integers, reducing after each factor. -/
def codedProduct (base bound : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 1 % base ^ (bound + 1)
  | p :: ps => codedProduct base bound ps * codedLengthFactor base bound p.1 p.2 %
      base ^ (bound + 1)

private theorem codedProduct_eq (base bound : ℕ) (factors : List (ℕ × ℕ))
    (positive : ∀ p ∈ factors, 0 < p.1) :
    codedProduct base bound factors =
      ((factors.map (fun p ↦ lengthFactor bound p.1 p.2)).prod.eval base) %
        base ^ (bound + 1) := by
  induction factors with
  | nil => simp only [codedProduct, List.map_nil, List.prod_nil, eval_one]
  | cons p ps ih =>
    have hp := positive p List.mem_cons_self
    have ht : ∀ v ∈ ps, 0 < v.1 := fun v hv ↦ positive v (List.mem_cons_of_mem _ hv)
    rw [codedProduct, ih ht, List.map_cons, List.prod_cons, eval_mul]
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    simp only [ZMod.natCast_mod, Nat.cast_mul, codedLengthFactor_cast base bound hp]
    exact mul_comm _ _

/-- A scalar encoding of the whole truncated positive-necklace coefficient table. -/
def packedCount (n q k : ℕ) : ℕ :=
  let base := cutoffRadix n q
  let code := codedProduct base n (positiveFactors n q k)
  code / base ^ n % base

/-- The scalar encoding computes exactly the same count as the proved array DP. -/
theorem packedCount_eq {n q : ℕ} (hq : 0 < q) (k : ℕ) :
    packedCount n q k = positiveCountDP n q k := by
  have positive : ∀ p ∈ positiveFactors n q k, 0 < p.1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact Nat.succ_pos _
  let p := ((positiveFactors n q k).map (fun a ↦ lengthFactor n a.1 a.2)).prod
  have bounded {d : ℕ} (hd : d ≤ n) : p.coeff d < cutoffRadix n q := by
    change _ < q ^ n + 1
    rw [← countTable_correct n _ positive hd, positiveCountDP_at_cap hd]
    apply Nat.lt_succ_of_le
    by_cases zero : d = 0
    · subst d
      change 1 ≤ q ^ n
      exact Nat.one_le_pow n q hq
    · exact positiveCountDP_le_words (Nat.pos_of_ne_zero zero) |>.trans
        (Nat.pow_le_pow_right hq hd)
  dsimp only [packedCount]
  rw [codedProduct_eq _ _ _ positive]
  have modulus :
      p.eval (cutoffRadix n q) % cutoffRadix n q ^ (n + 1) /
          cutoffRadix n q ^ n % cutoffRadix n q =
        p.eval (cutoffRadix n q) / cutoffRadix n q ^ n % cutoffRadix n q := by
    rw [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mod]
  rw [modulus, eval_radix_digit _ (by simp only [cutoffRadix]; positivity) p n
    (fun _ hd ↦ bounded hd)]
  exact (countTable_correct n _ positive le_rfl).symm

/-- Alphabet counts produced by compressed products. -/
def packedAlphabet (n k : ℕ) : Array ℕ :=
  Array.ofFn fun r : Fin n ↦ packedCount n (r.val + 1) k

/-- The compressed alphabet has the exact permutation-alphabet interpretation. -/
theorem packedAlphabet_eq (n k : ℕ) :
    packedAlphabet n k = descentAlphabetTable n k := by
  unfold packedAlphabet descentAlphabetTable
  congr 1
  funext r
  exact packedCount_eq (Nat.succ_pos _) k

end RealRooted.LongCycleDescents.Necklace
