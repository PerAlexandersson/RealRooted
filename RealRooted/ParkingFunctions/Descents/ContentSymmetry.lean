import RealRooted.BrandenVecchi.SmirnovChow
import RealRooted.ParkingFunctions.Descents.WordContent
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Fixed-content symmetry for Smirnov descents

This file extracts labeled-content coefficients from the universal
multivariate weighted Smirnov polynomial.  Its symmetry comes from the checked
finite elementary-Toeplitz Chow identity, not from a pointwise relabeling of
words, since relabeling an ordered alphabet need not preserve descents.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The literal Smirnov words having one prescribed labeled content. -/
def fixedContentSmirnovWords {n m : ℕ} (μ : Multiset (Fin m)) :
    Finset (Fin n → Fin m) := by
  classical
  exact (BrandenVecchi.smirnovWords m n).filter fun w => wordContent w = μ

@[simp]
theorem mem_fixedContentSmirnovWords_iff {n m : ℕ}
    {μ : Multiset (Fin m)} {w : Fin n → Fin m} :
    w ∈ fixedContentSmirnovWords μ ↔
      BrandenVecchi.IsSmirnovWord n w ∧ wordContent w = μ := by
  simp [fixedContentSmirnovWords]

/-- The integral descent enumerator in one labeled content fiber. -/
def fixedContentSmirnovPolynomial {n m : ℕ}
    (μ : Multiset (Fin m)) : ℤ[X] :=
  ∑ w ∈ fixedContentSmirnovWords (n := n) μ,
    X ^ BrandenVecchi.smirnovDescentNumber w

/-- The exponent vector recording the multiplicity of every letter in a
word. -/
def wordExponent {n m : ℕ} (w : Fin n → Fin m) : Fin m →₀ ℕ :=
  ∑ i, Finsupp.single (w i) 1

@[simp]
theorem card_wordContent {n m : ℕ} (w : Fin n → Fin m) :
    (wordContent w).card = n := by
  simp [wordContent]

/-- The exponent vector and value-multiset presentations of content agree. -/
theorem wordExponent_eq_toFinsupp_wordContent {n m : ℕ}
    (w : Fin n → Fin m) :
    wordExponent w = (wordContent w).toFinsupp := by
  classical
  ext a
  unfold wordExponent wordContent
  simp only [Multiset.toFinsupp_apply]
  rw [Multiset.count_map]
  have hfilter :
      Multiset.filter (fun i => a = w i) Finset.univ.val =
        (Finset.univ.filter fun i => a = w i).val := rfl
  rw [hfilter]
  change (∑ i, Finsupp.single (w i) 1) a =
    (Finset.univ.filter fun i => a = w i).card
  rw [Finset.card_filter]
  change (Finsupp.applyAddHom a) (∑ i, Finsupp.single (w i) 1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : w i = a
  · subst a
    simp
  · simp [Ne.symm h]

/-- The universal monomial weight of a word is the monomial of its content
exponent. -/
theorem smirnovWordWeight_X_eq_monomial {n m : ℕ}
    (w : Fin n → Fin m) :
    BrandenVecchi.smirnovWordWeight
        (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X w =
      MvPolynomial.monomial (wordExponent w) 1 := by
  classical
  unfold BrandenVecchi.smirnovWordWeight wordExponent
  simpa [MvPolynomial.X] using
    (MvPolynomial.monomial_sum_prod (R := ℤ) Finset.univ
      (fun i => Finsupp.single (w i) 1) (fun _ => 1)).symm

/-- A labeled-content descent coefficient is the corresponding multivariate
coefficient of the universal weighted Smirnov polynomial. -/
theorem coeff_fixedContentSmirnovPolynomial {n m k : ℕ}
    (μ : Multiset (Fin m)) :
    (fixedContentSmirnovPolynomial (n := n) μ).coeff k =
      MvPolynomial.coeff μ.toFinsupp
        ((BrandenVecchi.weightedSmirnovPolynomial
          (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X n).coeff k) := by
  classical
  unfold fixedContentSmirnovPolynomial fixedContentSmirnovWords
    BrandenVecchi.weightedSmirnovPolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul, smirnovWordWeight_X_eq_monomial,
    MvPolynomial.coeff_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hc : wordContent w = μ
  · have he : wordExponent w = μ.toFinsupp := by
      rw [wordExponent_eq_toFinsupp_wordContent, hc]
    by_cases hk : k = BrandenVecchi.smirnovDescentNumber w
    · simp [hc, hk, he, MvPolynomial.coeff_monomial]
    · simp [hc, hk]
  · have he : wordExponent w ≠ μ.toFinsupp := by
      rw [wordExponent_eq_toFinsupp_wordContent]
      exact fun h => hc (Multiset.toFinsupp.injective h)
    by_cases hk : k = BrandenVecchi.smirnovDescentNumber w
    · simp [hc, hk, he, MvPolynomial.coeff_monomial]
    · simp [hc, hk]

/-- Renaming the variables of the universal weighted Smirnov polynomial by
an alphabet permutation leaves it unchanged. -/
theorem map_universalWeightedSmirnovPolynomial {n m : ℕ}
    (e : Equiv.Perm (Fin m)) :
    (BrandenVecchi.weightedSmirnovPolynomial
        (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X n).map
        (MvPolynomial.rename e).toRingHom =
      BrandenVecchi.weightedSmirnovPolynomial
        (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X n := by
  rw [BrandenVecchi.map_weightedSmirnovPolynomial]
  simpa [Function.comp_def] using
    (BrandenVecchi.weightedSmirnovPolynomial_comp_equiv
      (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X e n)

/-- Mapping a multiset by an alphabet permutation maps its multiplicity
vector along the same permutation. -/
theorem toFinsupp_map_equiv {m : ℕ} (μ : Multiset (Fin m))
    (e : Equiv.Perm (Fin m)) :
    (μ.map e).toFinsupp = Finsupp.mapDomain e μ.toFinsupp := by
  apply Multiset.toFinsupp_eq_iff.mpr
  simpa using Finsupp.toMultiset_map μ.toFinsupp e

/-- Coefficients of the universal weighted Smirnov polynomial are invariant
under simultaneous permutation of their exponent vector. -/
theorem coeff_universalWeightedSmirnovPolynomial_mapDomain
    {n m k : ℕ} (e : Equiv.Perm (Fin m)) (d : Fin m →₀ ℕ) :
    MvPolynomial.coeff (Finsupp.mapDomain e d)
        ((BrandenVecchi.weightedSmirnovPolynomial
          (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X n).coeff k) =
      MvPolynomial.coeff d
        ((BrandenVecchi.weightedSmirnovPolynomial
          (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X n).coeff k) := by
  have hmap := congrArg (fun p : Polynomial (MvPolynomial (Fin m) ℤ) =>
      p.coeff k) (map_universalWeightedSmirnovPolynomial (n := n) e)
  rw [Polynomial.coeff_map] at hmap
  change (MvPolynomial.rename e)
      ((BrandenVecchi.weightedSmirnovPolynomial
        (R := MvPolynomial (Fin m) ℤ) MvPolynomial.X n).coeff k) = _
    at hmap
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.mapDomain e d)) hmap
  rw [MvPolynomial.coeff_rename_mapDomain e e.injective] at hcoeff
  exact hcoeff.symm

/-- Fixed-content Smirnov descent polynomials depend only on the multiplicity
type, not on the chosen alphabet labels. -/
theorem fixedContentSmirnovPolynomial_map_equiv {n m : ℕ}
    (μ : Multiset (Fin m)) (e : Equiv.Perm (Fin m)) :
    fixedContentSmirnovPolynomial (n := n) (μ.map e) =
      fixedContentSmirnovPolynomial (n := n) μ := by
  ext k
  rw [coeff_fixedContentSmirnovPolynomial,
    coeff_fixedContentSmirnovPolynomial, toFinsupp_map_equiv]
  exact coeff_universalWeightedSmirnovPolynomial_mapDomain e μ.toFinsupp

/-- A content realization has the same fixed-content descent polynomial as
the multiplicity type that it realizes. -/
theorem fixedContentSmirnovPolynomial_eq_of_hasContentType
    {n m : ℕ} {μ : Multiset (Fin m)} {w : Fin n → Fin m}
    (h : HasContentType μ w) :
    fixedContentSmirnovPolynomial (n := n) (wordContent w) =
      fixedContentSmirnovPolynomial (n := n) μ := by
  obtain ⟨e, he⟩ := h
  rw [he, fixedContentSmirnovPolynomial_map_equiv]

/-- A prescribed content of the wrong total size has no words. -/
theorem fixedContentSmirnovPolynomial_eq_zero_of_card_ne
    {n m : ℕ} (μ : Multiset (Fin m)) (hμ : μ.card ≠ n) :
    fixedContentSmirnovPolynomial (n := n) μ = 0 := by
  classical
  unfold fixedContentSmirnovPolynomial
  apply Finset.sum_eq_zero
  intro w hw
  have hc := (mem_fixedContentSmirnovWords_iff.mp hw).2
  exfalso
  apply hμ
  rw [← hc]
  exact card_wordContent w

/-- The empty word is the unique Smirnov word with empty content, for every
ambient alphabet (including the empty alphabet). -/
@[simp]
theorem fixedContentSmirnovPolynomial_zero (m : ℕ) :
    fixedContentSmirnovPolynomial
      (n := 0) (0 : Multiset (Fin m)) = 1 := by
  simp [fixedContentSmirnovPolynomial, fixedContentSmirnovWords,
    BrandenVecchi.smirnovWords, BrandenVecchi.IsSmirnovWord, wordContent]

end

end RealRooted.ParkingFunctions
