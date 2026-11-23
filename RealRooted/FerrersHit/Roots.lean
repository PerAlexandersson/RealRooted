module

public import RealRooted.FerrersHit.Basic
import RealRooted.Transforms.BrandenE.IntegerFactors
import TauCeti.Order.SuccPred.IntermediateValue
import Mathlib.Order.SuccPred.Int
import Mathlib.Tactic

/-!
# Real-rooted hit polynomials of Ferrers boards

This is Haglund--Ono--Wagner (1999), Theorem 1 (page 3). We use an algebraic
proof through the Goldman--Joichi--White product. Its integer parameters have
no gaps between their extrema: the first is nonnegative, the last is at most
one, and each downward step has size at most one. Tau Ceti's discrete
intermediate value theorem supplies the consecutive block. The E transform
is then rooted in `[-1, 0]`, by endpoint multiplicity. Reversal and a shift
give the standard rook-to-hit transform.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted.FerrersHit

noncomputable section

private def parameters {n : ℕ} (h : Fin n → ℕ) : Multiset ℤ :=
  Finset.univ.val.map fun i => (h i : ℤ) - (i : ℕ)

private theorem mem_parameters {n : ℕ} (h : Fin n → ℕ) (c : ℤ) :
    c ∈ parameters h ↔ ∃ i, (h i : ℤ) - (i : ℕ) = c := by
  simp [parameters]

private theorem integerFactorProduct_parameters {n : ℕ} (h : Fin n → ℕ) :
    integerFactorProduct (parameters h) = factorialPolynomial h := by
  simp [integerFactorProduct, parameters, Function.comp_def,
    factorialPolynomial, Finset.prod]

/-- A finite descending crossing of a level by the GJW parameters attains
that level: monotone heights permit downward jumps of size at most one. -/
private theorem parameter_crossing {n : ℕ} (h : Fin n → ℕ) (hh : Monotone h)
    (i j : Fin n) (hij : i ≤ j) (c : ℤ)
    (hi : c ≤ (h i : ℤ) - (i : ℕ)) (hj : (h j : ℤ) - (j : ℕ) ≤ c) :
    c ∈ parameters h := by
  let f : ℕ → ℤ := fun k => if hk : k < n then -((h ⟨k, hk⟩ : ℤ) - k) else 0
  have hstep : ∀ k, (i : ℕ) ≤ k → k < (j : ℕ) → f (k + 1) ≤ Order.succ (f k) := by
    intro k _ hk
    have hk' : k < n := lt_trans hk j.isLt
    have hks : k + 1 < n := by lia
    have hmono := hh (show (⟨k, hk'⟩ : Fin n) ≤ ⟨k + 1, hks⟩ by simp)
    have hmono' : (h ⟨k, hk'⟩ : ℤ) ≤ (h ⟨k + 1, hks⟩ : ℤ) := by
      exact_mod_cast hmono
    dsimp [f]
    simp only [dite_eq_left hk', dite_eq_left hks]
    change -((h ⟨k + 1, hks⟩ : ℤ) - (k + 1 : ℕ)) ≤
      -((h ⟨k, hk'⟩ : ℤ) - k) + 1
    push_cast
    lia
  obtain ⟨k, hk, heq⟩ := Nat.exists_mem_Icc_eq_of_le_succ
    (f := f) (y := -c) hij hstep (by simpa [f, i.isLt] using neg_le_neg hi)
      (by simpa [f, j.isLt] using neg_le_neg hj)
  have hkn : k < n := lt_of_le_of_lt hk.2 j.isLt
  apply (mem_parameters h c).mpr
  refine ⟨⟨k, hkn⟩, ?_⟩
  simpa [f, hkn] using congrArg Neg.neg heq

private theorem parameters_no_gaps {n : ℕ} (h : Fin n → ℕ) (hh : IsFerrers h)
    (hn : n ≠ 0) (c : ℤ)
    (hlo : ∃ i, (h i : ℤ) - (i : ℕ) ≤ c)
    (hhi : ∃ i, c ≤ (h i : ℤ) - (i : ℕ)) :
    c ∈ parameters h := by
  let first : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let last : Fin n := ⟨n - 1, by lia⟩
  by_cases hc : c ≤ 0
  · obtain ⟨i, hi⟩ := hlo
    exact parameter_crossing h hh.1 first i
      (by change (0 : ℕ) ≤ (i : ℕ); exact Nat.zero_le _) c
      (by dsimp [first]; simp only [sub_zero]; lia) hi
  · obtain ⟨i, hi⟩ := hhi
    apply parameter_crossing h hh.1 i last (by dsimp [last]; exact_mod_cast (by lia)) c hi
    have hh_last := hh.2 last
    have hc' : 1 ≤ c := by lia
    dsimp [last] at hh_last ⊢
    exact_mod_cast (show (h ⟨n - 1, by lia⟩ : ℤ) - (n - 1 : ℕ) ≤ c by
      have hh' : (h ⟨n - 1, by lia⟩ : ℤ) ≤ (n : ℤ) := by exact_mod_cast hh_last
      have hn' : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by lia
      lia)

private theorem integerFactorInterval_nodup (m b : ℕ) :
    (integerFactorInterval m b).Nodup := by
  rw [integerFactorInterval, Multiset.nodup_add]
  refine ⟨Multiset.Nodup.map (by intro i j hij; exact_mod_cast neg_injective hij)
    (Multiset.nodup_range m),
    Multiset.Nodup.map (by intro i j hij; exact_mod_cast (by lia : (i : ℤ) = j))
      (Multiset.nodup_range b), ?_⟩
  rw [Multiset.disjoint_left]
  intro c hc hc'
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hc
  obtain ⟨j, -, hji⟩ := Multiset.mem_map.mp hc'
  lia

private theorem exists_parameter_block {n : ℕ} (h : Fin n → ℕ) (hh : IsFerrers h)
    (hn : n ≠ 0) :
    ∃ m b : ℕ, integerFactorInterval m b ≤ parameters h ∧
      ∀ c ∈ parameters h, 1 - (m : ℤ) ≤ c ∧ c ≤ b := by
  classical
  let s := (parameters h).toFinset
  have hne : s.Nonempty := by
    refine ⟨(h ⟨0, Nat.pos_of_ne_zero hn⟩ : ℤ), ?_⟩
    simpa [s, mem_parameters] using
      (show ∃ i : Fin n, (h i : ℤ) - (i : ℕ) = h ⟨0, Nat.pos_of_ne_zero hn⟩ from
        ⟨⟨0, Nat.pos_of_ne_zero hn⟩, by simp⟩)
  let l := s.min' hne
  let u := s.max' hne
  have hl : l ∈ parameters h := by simpa [s, l] using s.min'_mem hne
  have hu : u ∈ parameters h := by simpa [s, u] using s.max'_mem hne
  have hl_one : l ≤ 1 := by
    have hm : (h ⟨n - 1, by lia⟩ : ℤ) - (n - 1 : ℕ) ∈ s := by
      simp only [s, Multiset.mem_toFinset, mem_parameters]
      exact ⟨⟨n - 1, by lia⟩, rfl⟩
    have hmin := s.min'_le _ hm
    have hb := hh.2 ⟨n - 1, by lia⟩
    have hb' : (h ⟨n - 1, by lia⟩ : ℤ) ≤ (n : ℤ) := by exact_mod_cast hb
    have hn' : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by lia
    dsimp [l]
    lia
  have hu_zero : 0 ≤ u := by
    have hm : (h ⟨0, Nat.pos_of_ne_zero hn⟩ : ℤ) ∈ s := by
      simp only [s, Multiset.mem_toFinset, mem_parameters]
      exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩, by simp⟩
    exact le_trans (by positivity) (s.le_max' _ hm)
  let m := (1 - l).toNat
  let b := u.toNat
  have hm : (m : ℤ) = 1 - l := Int.toNat_of_nonneg (by lia)
  have hb : (b : ℤ) = u := Int.toNat_of_nonneg hu_zero
  refine ⟨m, b, ?_, ?_⟩
  · apply (Multiset.le_iff_subset (integerFactorInterval_nodup m b)).mpr
    intro c hc
    have hc_bounds : l ≤ c ∧ c ≤ u := by
      rw [integerFactorInterval, Multiset.mem_add] at hc
      rcases hc with hc | hc
      · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hc
        have hi' : i < m := Multiset.mem_range.mp hi
        have hi'' : (i : ℤ) < m := by exact_mod_cast hi'
        constructor <;> lia
      · obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hc
        have hi' : i < b := Multiset.mem_range.mp hi
        have hi'' : (i : ℤ) < b := by exact_mod_cast hi'
        constructor <;> lia
    apply parameters_no_gaps h hh hn c
    · obtain ⟨i, hi⟩ := (mem_parameters h l).mp hl
      exact ⟨i, hi.symm ▸ hc_bounds.1⟩
    · obtain ⟨i, hi⟩ := (mem_parameters h u).mp hu
      exact ⟨i, hi.symm ▸ hc_bounds.2⟩
  · intro c hc
    have hc' : c ∈ s := Multiset.mem_toFinset.mpr hc
    have hlo := s.min'_le c hc'
    have hhi := s.le_max' c hc'
    constructor <;> dsimp [l, u] at * <;> lia

/-- The E transform of the GJW product of a square Ferrers board is nonzero,
splits over the reals, and has all roots in `[-1, 0]`. -/
theorem brandenE_factorialPolynomial_roots_mem_Icc {n : ℕ} (h : Fin n → ℕ)
    (hh : IsFerrers h) :
    HasPosLeadingCoeff (brandenE (factorialPolynomial h)) ∧
      (brandenE (factorialPolynomial h)).Splits ∧
      ∀ r ∈ (brandenE (factorialPolynomial h)).roots, r ∈ Set.Icc (-1 : ℝ) 0 := by
  by_cases hn : n = 0
  · subst n
    simpa [factorialPolynomial, integerFactorProduct] using
      brandenE_integerFactorProduct_roots_mem_Icc 0 0 0
        (by simp [integerFactorInterval]) (by simp)
  · obtain ⟨m, b, hblock, hbound⟩ := exists_parameter_block h hh hn
    simpa [integerFactorProduct_parameters] using
      brandenE_integerFactorProduct_roots_mem_Icc (parameters h) m b hblock hbound

/-- **Haglund--Ono--Wagner, Theorem 1 (1999).** The hit polynomial, defined
by the standard rook-to-hit transform of the GJW rook numbers of a Ferrers
board in the square, is nonzero and has only real zeros. -/
theorem hitPolynomial_ne_zero_and_splits {n : ℕ} (h : Fin n → ℕ)
    (hh : IsFerrers h) : hitPolynomial h ≠ 0 ∧ (hitPolynomial h).Splits := by
  obtain ⟨hlc, hs, -⟩ := brandenE_factorialPolynomial_roots_mem_Icc h hh
  have hd : (brandenE (factorialPolynomial h)).natDegree ≤ n := by
    change (basisTransform orderedBellPolynomial (factorialPolynomial h)).natDegree ≤ n
    rw [basisTransform_natDegree_eq orderedBellPolynomial_natDegree
      orderedBellPolynomial_ne_zero (factorialPolynomial_monic_natDegree h).1.ne_zero]
    exact (factorialPolynomial_monic_natDegree h).2.le
  rw [hitPolynomial_eq_reflect_comp]
  refine ⟨?_, (hs.reflect hd).comp_X_sub_C 1⟩
  intro hz
  have hz' := congrArg (fun p : ℝ[X] => p.comp (X + 1)) hz
  simp only [comp_assoc, zero_comp] at hz'
  have hinv : (X - 1 : ℝ[X]).comp (X + 1) = X := by simp
  rw [hinv, comp_X] at hz'
  exact hlc.ne_zero (reflect_eq_zero_iff.mp hz')

end

end RealRooted.FerrersHit
