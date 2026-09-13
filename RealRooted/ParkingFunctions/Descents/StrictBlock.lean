import RealRooted.ParkingFunctions.Descents.WordContent
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Strict word blocks

This module identifies the multivariate content enumerator of strictly
decreasing finite words with an elementary symmetric polynomial.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- A finite word whose letters strictly decrease from left to right. -/
abbrev StrictDecreasingWord (k m : ℕ) :=
  {w : Fin k → Fin m // StrictAnti w}

/-- Reversing positions identifies decreasing words with increasing order
embeddings. -/
def strictDecreasingWordEquivOrderEmbedding (k m : ℕ) :
    StrictDecreasingWord k m ≃ (Fin k ↪o Fin m) where
  toFun w := OrderEmbedding.ofStrictMono (fun i => w.1 (Fin.rev i))
    (w.2.comp Fin.rev_strictAnti)
  invFun f :=
    ⟨fun i => f (Fin.rev i), f.strictMono.comp_strictAnti Fin.rev_strictAnti⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    simp
  right_inv f := by
    ext i
    simp

/-- Increasing order embeddings are equivalent to subsets of the alphabet
with the prescribed cardinality. -/
def orderEmbeddingEquivFinsetCard (k m : ℕ) :
    (Fin k ↪o Fin m) ≃ {s : Finset (Fin m) // s.card = k} where
  toFun f :=
    ⟨Finset.univ.image f, by simp [Finset.card_image_of_injective _ f.injective]⟩
  invFun s := s.1.orderEmbOfFin s.2
  left_inv f := by
    symm
    apply Finset.orderEmbOfFin_unique'
    simp
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ s.1 s.2

/-- A decreasing word is determined by the subset of alphabet letters that
it uses. -/
def strictDecreasingWordEquivFinsetCard (k m : ℕ) :
    StrictDecreasingWord k m ≃ {s : Finset (Fin m) // s.card = k} :=
  (strictDecreasingWordEquivOrderEmbedding k m).trans
    (orderEmbeddingEquivFinsetCard k m)

/-- The content exponent of an injective word is the sum of the singleton
exponents over its image. -/
theorem wordExponent_eq_sum_image_of_injective {k m : ℕ}
    (w : Fin k → Fin m) (hw : Function.Injective w) :
    wordExponent w =
      ∑ a ∈ Finset.univ.image w, Finsupp.single a 1 := by
  unfold wordExponent
  rw [Finset.sum_image]
  exact hw.injOn

/-- Reversing a finite word does not change the set of letters that it uses. -/
theorem image_comp_rev_univ {k m : ℕ} (w : Fin k → Fin m) :
    Finset.univ.image (fun i => w (Fin.rev i)) =
      Finset.univ.image w := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.rev i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.rev i, by simp⟩

/-- The universal content enumerator of strictly decreasing words. -/
def strictDecreasingWordEnumerator (k m : ℕ) : MvPolynomial (Fin m) ℤ :=
  ∑ w : StrictDecreasingWord k m,
    MvPolynomial.monomial (wordExponent w.1) 1

/-- Strictly decreasing blocks are enumerated by the corresponding elementary
symmetric polynomial, including the empty-word and empty-alphabet cases. -/
theorem strictDecreasingWordEnumerator_eq_esymm (k m : ℕ) :
    strictDecreasingWordEnumerator k m = MvPolynomial.esymm (Fin m) ℤ k := by
  rw [MvPolynomial.esymm_eq_sum_subtype]
  apply Fintype.sum_equiv (strictDecreasingWordEquivFinsetCard k m)
  intro w
  change MvPolynomial.monomial (wordExponent w.1) 1 =
    ∏ i ∈ Finset.univ.image (fun j => w.1 (Fin.rev j)), MvPolynomial.X i
  rw [wordExponent_eq_sum_image_of_injective w.1 w.2.injective]
  rw [image_comp_rev_univ]
  rw [MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X]

@[simp]
theorem strictDecreasingWordEnumerator_zero (m : ℕ) :
    strictDecreasingWordEnumerator 0 m = 1 := by
  rw [strictDecreasingWordEnumerator_eq_esymm]
  exact MvPolynomial.esymm_zero (Fin m) ℤ

@[simp]
theorem strictDecreasingWordEnumerator_zero_alphabet (k : ℕ) :
    strictDecreasingWordEnumerator k 0 =
      if k = 0 then 1 else 0 := by
  rw [strictDecreasingWordEnumerator_eq_esymm]
  cases k with
  | zero => simp
  | succ k =>
      rw [if_neg (Nat.succ_ne_zero k)]
      unfold MvPolynomial.esymm
      rw [(Finset.powersetCard_eq_empty).2]
      · simp
      · simp

/-- The strict-block enumerator is invariant under alphabet renaming. -/
theorem rename_strictDecreasingWordEnumerator (k m : ℕ)
    (e : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (strictDecreasingWordEnumerator k m) =
      strictDecreasingWordEnumerator k m := by
  rw [strictDecreasingWordEnumerator_eq_esymm,
    MvPolynomial.rename_esymm]

end

end RealRooted.ParkingFunctions
