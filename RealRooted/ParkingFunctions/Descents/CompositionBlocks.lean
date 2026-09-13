import RealRooted.ParkingFunctions.Descents.StrictBlock
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Strict blocks indexed by a composition

This module assembles finite words from the canonical blocks of a Mathlib
`Composition` and factors the content enumerator for independently strict
blocks.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Words which decrease strictly within every consecutive block of a
composition. -/
abbrev BlockwiseStrictWord {N : ℕ} (c : Composition N) (m : ℕ) :=
  {w : Fin N → Fin m //
    ∀ i : Fin c.length, StrictAnti (w ∘ c.embedding i)}

/-- A word is equivalently a dependent family of its restrictions to the
canonical blocks of a composition. -/
def wordEquivCompositionBlocks {N : ℕ} (c : Composition N) (m : ℕ) :
    (Fin N → Fin m) ≃
      ((i : Fin c.length) → Fin (c.blocksFun i) → Fin m) :=
  (c.blocksFinEquiv.symm.arrowCongr (Equiv.refl (Fin m))).trans
    (Equiv.piCurry fun _ _ => Fin m)

@[simp]
theorem wordEquivCompositionBlocks_apply {N m : ℕ} (c : Composition N)
    (w : Fin N → Fin m) (i : Fin c.length)
    (j : Fin (c.blocksFun i)) :
    wordEquivCompositionBlocks c m w i j = w (c.embedding i j) := rfl

/-- The `i`-th canonical split of the ordered positions is the list of
positions in the `i`-th composition embedding. -/
theorem getElem_splitWrtComposition_ofFn {N : ℕ} (c : Composition N)
    (i : Fin c.length) :
    ((List.ofFn (id : Fin N → Fin N)).splitWrtComposition c)[i.val]'(by
      rw [List.length_splitWrtComposition]
      exact i.isLt) = List.ofFn (c.embedding i) := by
  rw [List.getElem_splitWrtComposition]
  apply List.ext_getElem
  · have hle : c.sizeUpTo (i + 1) ≤ N := c.sizeUpTo_le (i + 1)
    simp only [List.length_drop, List.length_take, List.length_ofFn]
    rw [Nat.min_eq_left hle, c.sizeUpTo_succ' i,
      Nat.add_sub_cancel_left]
  · intro j hj₁ hj₂
    simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn]
    apply Fin.ext
    simp [Composition.coe_embedding]

/-- Restriction to composition blocks identifies a blockwise strict word
with a dependent family of strictly decreasing words. -/
def blockwiseStrictWordEquiv {N m : ℕ} (c : Composition N) :
    BlockwiseStrictWord c m ≃
      ((i : Fin c.length) → StrictDecreasingWord (c.blocksFun i) m) :=
  ((wordEquivCompositionBlocks c m).subtypeEquiv fun _ => by rfl).trans
    Equiv.subtypePiEquivPi

/-- Content is additive under the canonical decomposition of positions into
the blocks of a composition. -/
theorem wordExponent_eq_sum_wordExponent_blocks {N m : ℕ}
    (c : Composition N) (w : Fin N → Fin m) :
    wordExponent w =
      ∑ i : Fin c.length, wordExponent (w ∘ c.embedding i) := by
  unfold wordExponent
  calc
    (∑ i, Finsupp.single (w i) 1) =
        ∑ x : (Σ i : Fin c.length, Fin (c.blocksFun i)),
          Finsupp.single (w (c.blocksFinEquiv x)) 1 :=
      (c.blocksFinEquiv.sum_comp
        (fun j => Finsupp.single (w j) 1)).symm
    _ = ∑ i : Fin c.length,
        ∑ j : Fin (c.blocksFun i),
          Finsupp.single (w (c.embedding i j)) 1 := by
      rw [Fintype.sum_sigma]
      rfl

/-- Reindex blockwise strict words by dependent strict blocks, and split each
content monomial across the blocks. -/
theorem sum_monomial_blockwiseStrictWord_eq_sum_product {N m : ℕ}
    (c : Composition N) :
    (∑ w : BlockwiseStrictWord c m,
      MvPolynomial.monomial (wordExponent w.1) (1 : ℤ)) =
      ∑ v : ((i : Fin c.length) →
          StrictDecreasingWord (c.blocksFun i) m),
        ∏ i : Fin c.length,
          MvPolynomial.monomial (wordExponent (v i).1) (1 : ℤ) := by
  apply Fintype.sum_equiv (blockwiseStrictWordEquiv c)
  intro w
  change MvPolynomial.monomial (wordExponent w.1) (1 : ℤ) =
    ∏ i : Fin c.length,
      MvPolynomial.monomial
        (wordExponent (w.1 ∘ c.embedding i)) (1 : ℤ)
  rw [wordExponent_eq_sum_wordExponent_blocks]
  simpa using
    (MvPolynomial.monomial_sum_one Finset.univ
      (fun i : Fin c.length =>
        wordExponent (w.1 ∘ c.embedding i)))

/-- The dependent sum of strict-block products factors into the product of
the individual block enumerators. -/
theorem sum_product_strictDecreasingWord_eq_prod_enumerator {N m : ℕ}
    (c : Composition N) :
    (∑ v : ((i : Fin c.length) →
        StrictDecreasingWord (c.blocksFun i) m),
      ∏ i : Fin c.length,
        MvPolynomial.monomial (wordExponent (v i).1) (1 : ℤ)) =
      ∏ i : Fin c.length,
        strictDecreasingWordEnumerator (c.blocksFun i) m := by
  symm
  simpa only [strictDecreasingWordEnumerator] using
    (Fintype.prod_sum fun i
      (v : StrictDecreasingWord (c.blocksFun i) m) =>
        MvPolynomial.monomial (wordExponent v.1) (1 : ℤ))

/-- The multivariate content enumerator of words which decrease strictly on
every block of a composition. -/
def strictCompositionBlockEnumerator {N : ℕ}
    (c : Composition N) (m : ℕ) : MvPolynomial (Fin m) ℤ :=
  ∑ w : BlockwiseStrictWord c m,
    MvPolynomial.monomial (wordExponent w.1) (1 : ℤ)

/-- Independent strict blocks factor as the product of their elementary
symmetric content enumerators. -/
theorem strictCompositionBlockEnumerator_eq_prod_esymm {N : ℕ}
    (c : Composition N) (m : ℕ) :
    strictCompositionBlockEnumerator c m =
      ∏ i : Fin c.length,
        MvPolynomial.esymm (Fin m) ℤ (c.blocksFun i) := by
  unfold strictCompositionBlockEnumerator
  calc
    (∑ w : BlockwiseStrictWord c m,
        MvPolynomial.monomial (wordExponent w.1) (1 : ℤ)) =
        ∑ v : ((i : Fin c.length) →
            StrictDecreasingWord (c.blocksFun i) m),
          ∏ i : Fin c.length,
            MvPolynomial.monomial (wordExponent (v i).1) (1 : ℤ) :=
      sum_monomial_blockwiseStrictWord_eq_sum_product c
    _ = ∏ i : Fin c.length,
        strictDecreasingWordEnumerator (c.blocksFun i) m :=
      sum_product_strictDecreasingWord_eq_prod_enumerator c
    _ = ∏ i : Fin c.length,
        MvPolynomial.esymm (Fin m) ℤ (c.blocksFun i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact strictDecreasingWordEnumerator_eq_esymm (c.blocksFun i) m

@[simp]
theorem strictCompositionBlockEnumerator_single (N m : ℕ) (hN : 0 < N) :
    strictCompositionBlockEnumerator (Composition.single N hN) m =
      MvPolynomial.esymm (Fin m) ℤ N := by
  rw [strictCompositionBlockEnumerator_eq_prod_esymm]
  simp

@[simp]
theorem strictCompositionBlockEnumerator_ones (N m : ℕ) :
    strictCompositionBlockEnumerator (Composition.ones N) m =
      (∑ a : Fin m, MvPolynomial.X a) ^ N := by
  rw [strictCompositionBlockEnumerator_eq_prod_esymm]
  simp [MvPolynomial.esymm_one]

/-- The composition-block enumerator is invariant under alphabet renaming. -/
theorem rename_strictCompositionBlockEnumerator {N : ℕ}
    (c : Composition N) (m : ℕ) (e : Equiv.Perm (Fin m)) :
    MvPolynomial.rename e (strictCompositionBlockEnumerator c m) =
      strictCompositionBlockEnumerator c m := by
  simp_rw [strictCompositionBlockEnumerator_eq_prod_esymm,
    map_prod, MvPolynomial.rename_esymm]

end

end RealRooted.ParkingFunctions
