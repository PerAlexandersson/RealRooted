/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import Mathlib.Data.List.Infix
import RealRooted.LGV.ChipNetwork.Matrix

/-!
# Finite words of lower-bidiagonal chips

This file packages stage weights as a literal finite word and identifies every
interval transfer product with the matrix product of the corresponding slice.
-/

namespace RealRooted
namespace LGV
namespace ChipNetwork

noncomputable section

/-- A lower-bidiagonal chip on levels `0, ..., N`. -/
structure Chip (R : Type*) (N : ℕ) where
  diagonal : Fin (N + 1) → R
  subdiagonal : Fin N → R

namespace Chip

/-- All transfer weights of a chip are nonnegative. -/
def IsNonnegative {R : Type*} [Zero R] [LE R] (c : Chip R N) : Prop :=
  (∀ i, 0 ≤ c.diagonal i) ∧ ∀ i, 0 ≤ c.subdiagonal i

/-- The transfer matrix of a chip. -/
def matrix {R : Type*} [Zero R] (c : Chip R N) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j ↦
    if i = j then c.diagonal i
    else if hsub : i.val = j.val + 1 then
      c.subdiagonal ⟨j.val, by lia⟩
    else 0

/-- The identity transfer chip. -/
def one {R : Type*} [Zero R] [One R] : Chip R N where
  diagonal := fun _ ↦ 1
  subdiagonal := fun _ ↦ 0

@[simp]
theorem matrix_one {R : Type*} [Semiring R] :
    (one : Chip R N).matrix = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [matrix, one]
  · simp [matrix, one, hij]

/-- Every lower-bidiagonal chip matrix is lower triangular. -/
theorem matrix_apply_eq_zero_of_lt {R : Type*} [Zero R]
    (c : Chip R N) {i j : Fin (N + 1)} (hij : i < j) :
    c.matrix i j = 0 := by
  have hne : i ≠ j := ne_of_lt hij
  have hsub : i.val ≠ j.val + 1 := by lia
  simp [matrix, hne, hsub]

end Chip

/-- Matrix product of a finite chip word, in traversal order. -/
def wordMatrix {R : Type*} [Semiring R] (word : List (Chip R N)) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  (word.map Chip.matrix).prod

@[simp]
theorem wordMatrix_nil {R : Type*} [Semiring R] :
    wordMatrix ([] : List (Chip R N)) = 1 :=
  rfl

@[simp]
theorem wordMatrix_append {R : Type*} [Semiring R]
    (u v : List (Chip R N)) :
    wordMatrix (u ++ v) = wordMatrix u * wordMatrix v := by
  simp [wordMatrix]

@[simp]
theorem wordMatrix_singleton {R : Type*} [Semiring R] (c : Chip R N) :
    wordMatrix [c] = c.matrix := by
  simp [wordMatrix]

/-- The transfer matrix of every chip word is lower triangular. -/
theorem wordMatrix_apply_eq_zero_of_lt {R : Type*} [Semiring R]
    (word : List (Chip R N)) {i j : Fin (N + 1)} (hij : i < j) :
    wordMatrix word i j = 0 := by
  induction word generalizing i j with
  | nil => simp [hij.ne]
  | cons c word ih =>
      rw [show wordMatrix (c :: word) = c.matrix * wordMatrix word by
        simp [wordMatrix]]
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i < k
      · rw [c.matrix_apply_eq_zero_of_lt hik, zero_mul]
      · have hkj : k < j := (le_of_not_gt hik).trans_lt hij
        rw [ih hkj, mul_zero]

/-- Diagonal edge weights read from a finite chip word. -/
def wordDiagonal {R : Type*} (word : List (Chip R N)) :
    Fin word.length → Fin (N + 1) → R :=
  fun s ↦ (word.get s).diagonal

/-- Subdiagonal edge weights read from a finite chip word. -/
def wordSubdiagonal {R : Type*} (word : List (Chip R N)) :
    Fin word.length → Fin N → R :=
  fun s ↦ (word.get s).subdiagonal

theorem wordDiagonal_nonneg {R : Type*} [Zero R] [LE R]
    (word : List (Chip R N))
    (hword : ∀ c ∈ word, c.IsNonnegative)
    (s : Fin word.length) (i : Fin (N + 1)) :
    0 ≤ wordDiagonal word s i :=
  (hword (word.get s) (List.get_mem word s)).1 i

theorem wordSubdiagonal_nonneg {R : Type*} [Zero R] [LE R]
    (word : List (Chip R N))
    (hword : ∀ c ∈ word, c.IsNonnegative)
    (s : Fin word.length) (i : Fin N) :
    0 ≤ wordSubdiagonal word s i :=
  (hword (word.get s) (List.get_mem word s)).2 i

theorem chipMatrix_word {R : Type*} [Zero R]
    (word : List (Chip R N)) (s : Fin word.length) :
    chipMatrix (wordDiagonal word) (wordSubdiagonal word) s =
      (word.get s).matrix := by
  rfl

/-- A valid stage in a word has the transfer matrix of the chip at that
position. -/
theorem chipMatrixNat_word {R : Type*} [Semiring R]
    (word : List (Chip R N)) (s : ℕ) (hs : s < word.length) :
    chipMatrixNat (wordDiagonal word) (wordSubdiagonal word) s =
      (word.get ⟨s, hs⟩).matrix := by
  simp [chipMatrixNat, chipMatrix_word, hs]

/-- Interval transfer products are products of the corresponding word slice. -/
theorem intervalProduct_word_eq_wordMatrix_take_drop
    {R : Type*} [Semiring R] (word : List (Chip R N))
    (a n : ℕ) (hbound : a + n ≤ word.length) :
    intervalProduct (wordDiagonal word) (wordSubdiagonal word) a n =
      wordMatrix ((word.drop a).take n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : a + n ≤ word.length := by lia
      have hindex : n < (word.drop a).length := by
        simp only [List.length_drop]
        lia
      rw [intervalProduct_succ, ih hprev,
        ← List.take_concat_get' (word.drop a) n hindex,
        wordMatrix_append]
      congr 1
      rw [wordMatrix_singleton]
      rw [chipMatrixNat_word word (a + n) (by lia)]
      apply congrArg Chip.matrix
      simp

/-- The chip path sum across a word interval is the corresponding sliced word
matrix entry. -/
theorem pathWeightSum_word_eq_wordMatrix_take_drop
    {R : Type*} [Semiring R] (word : List (Chip R N))
    (a b : Fin (word.length + 1)) (i j : Fin (N + 1)) (n : ℕ)
    (hstage : b.val = a.val + n) :
    pathWeightSum (wordDiagonal word) (wordSubdiagonal word) a b i j =
      wordMatrix ((word.drop a.val).take n) i j := by
  rw [pathWeightSum_eq_intervalProduct _ _ _ _ _ _ _ hstage,
    intervalProduct_word_eq_wordMatrix_take_drop]
  have hb := b.isLt
  lia

/-- `n` consecutive copies of a chip word. -/
def repeatWord {R : Type*} (word : List (Chip R N)) : ℕ → List (Chip R N)
  | 0 => []
  | n + 1 => word ++ repeatWord word n

@[simp]
theorem repeatWord_zero {R : Type*} (word : List (Chip R N)) :
    repeatWord word 0 = [] :=
  rfl

@[simp]
theorem repeatWord_succ {R : Type*} (word : List (Chip R N)) (n : ℕ) :
    repeatWord word (n + 1) = word ++ repeatWord word n :=
  rfl

theorem repeatWord_add {R : Type*} (word : List (Chip R N)) (m n : ℕ) :
    repeatWord word (m + n) = repeatWord word m ++ repeatWord word n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, repeatWord_succ, ih, repeatWord_succ,
        List.append_assoc]

@[simp]
theorem length_repeatWord {R : Type*} (word : List (Chip R N)) (n : ℕ) :
    (repeatWord word n).length = n * word.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

@[simp]
theorem wordMatrix_repeatWord {R : Type*} [Semiring R]
    (word : List (Chip R N)) (n : ℕ) :
    wordMatrix (repeatWord word n) = wordMatrix word ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [repeatWord, ih, pow_succ']

/-- Dropping a whole number of leading blocks leaves the requested trailing
number of blocks and the final tail. -/
theorem drop_repeatWord_append {R : Type*}
    (word tail : List (Chip R N)) {r total : ℕ} (hr : r ≤ total) :
    (repeatWord word total ++ tail).drop ((total - r) * word.length) =
      repeatWord word r ++ tail := by
  have htotal : total = (total - r) + r := by lia
  have hrepeated :
      repeatWord word total =
        repeatWord word (total - r) ++ repeatWord word r := by
    calc
      repeatWord word total = repeatWord word ((total - r) + r) :=
        congrArg (repeatWord word) htotal
      _ = repeatWord word (total - r) ++ repeatWord word r :=
        repeatWord_add word (total - r) r
  rw [hrepeated, List.append_assoc, ← length_repeatWord]
  simp

/-- In a repeated `(G ++ K)` word followed by `G`, the prefix ending after
the next `G` block has the expected form. -/
theorem take_repeatWord_append_left
    {R : Type*} (G K : List (Chip R N)) {q r : ℕ} (hqr : q ≤ r) :
    (repeatWord (G ++ K) r ++ G).take
        (q * (G.length + K.length) + G.length) =
      repeatWord (G ++ K) q ++ G := by
  have hr : r = q + (r - q) := by lia
  have hprefix : repeatWord (G ++ K) q ++ G <+:
      repeatWord (G ++ K) r ++ G := by
    rw [hr, repeatWord_add, List.append_assoc]
    cases r - q with
    | zero => simp
    | succ t =>
        refine ⟨K ++ repeatWord (G ++ K) t ++ G, ?_⟩
        simp [repeatWord, List.append_assoc]
  have htake := List.prefix_iff_eq_take.mp hprefix
  rw [htake]
  congr 1
  simp [Nat.mul_add]

/-- The finite strip containing `total` repeated `(G,K)` blocks and one final
`G` block. -/
def repeatedStrip {R : Type*} (G K : List (Chip R N)) (total : ℕ) :
    List (Chip R N) :=
  repeatWord (G ++ K) total ++ G

theorem mem_repeatedStrip {R : Type*} (G K : List (Chip R N))
    (total : ℕ) {c : Chip R N} (hc : c ∈ repeatedStrip G K total) :
    c ∈ G ∨ c ∈ K := by
  induction total with
  | zero => simpa [repeatedStrip] using Or.inl hc
  | succ total ih =>
      simp only [repeatedStrip, repeatWord_succ, List.mem_append] at hc
      rcases hc with (hcBlock | hcRepeat) | hcG
      · exact hcBlock
      · apply ih
        simp [repeatedStrip, hcRepeat]
      · exact Or.inl hcG

@[simp]
theorem length_repeatedStrip {R : Type*}
    (G K : List (Chip R N)) (total : ℕ) :
    (repeatedStrip G K total).length =
      total * (G.length + K.length) + G.length := by
  simp [repeatedStrip, Nat.mul_add]

/-- The stage interval selected by row `r` and column `c` is exactly the word
`G,K,G,...,K,G` with `r-c` copies of `K`. -/
theorem repeatedStrip_slice {R : Type*}
    (G K : List (Chip R N)) {c r total : ℕ}
    (hr : r ≤ total) :
    ((repeatedStrip G K total).drop
        ((total - r) * (G.length + K.length))).take
          ((r - c) * (G.length + K.length) + G.length) =
      repeatWord (G ++ K) (r - c) ++ G := by
  have hlen : (G ++ K).length = G.length + K.length := by simp
  rw [repeatedStrip, ← hlen, drop_repeatWord_append (G ++ K) G hr]
  simpa using take_repeatWord_append_left G K (Nat.sub_le r c)

/-- Matrix form of the repeated-strip slice. -/
theorem wordMatrix_repeatedStrip_slice {R : Type*} [Semiring R]
    (G K : List (Chip R N)) {c r total : ℕ}
    (hr : r ≤ total) :
    wordMatrix (((repeatedStrip G K total).drop
        ((total - r) * (G.length + K.length))).take
          ((r - c) * (G.length + K.length) + G.length)) =
      wordMatrix G * (wordMatrix K * wordMatrix G) ^ (r - c) := by
  rw [repeatedStrip_slice G K hr, wordMatrix_append,
    wordMatrix_repeatWord, wordMatrix_append, mul_pow_mul]

end

end ChipNetwork
end LGV
end RealRooted
