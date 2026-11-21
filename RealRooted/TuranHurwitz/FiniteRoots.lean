module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Multiset.Basic

/-!
# A finite indexing of polynomial roots with multiplicity

We use a list representative of the root multiset and extend it by zero.
The extension gives a natural-number sequence suitable for the disk kernel.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The roots of a real polynomial, with multiplicity, extended by zero after the list ends. -/
@[expose] noncomputable def indexedRoots (p : ℝ[X]) (j : ℕ) : ℝ :=
  if hj : j < p.roots.toList.length then p.roots.toList[j] else 0

/-- Every indexed root before the degree is an actual root of a split polynomial. -/
theorem indexedRoots_mem {p : ℝ[X]} (hs : p.Splits) {j : ℕ} (hj : j < p.natDegree) :
    indexedRoots p j ∈ p.roots := by
  have hlen : j < p.roots.toList.length := by
    rwa [Multiset.length_toList, ← hs.natDegree_eq_card_roots]
  rw [indexedRoots, dite_eq_left hlen]
  exact Multiset.mem_toList.mp (List.getElem_mem hlen)

/-- Extending the root list by zero preserves the interval `[-1, 1]`. -/
theorem indexedRoots_mem_Icc {p : ℝ[X]} (hs : p.Splits)
    (hr : ∀ r ∈ p.roots, r ∈ Set.Icc (-1 : ℝ) 1) (j : ℕ) :
    indexedRoots p j ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases hj : j < p.natDegree
  · exact hr _ (indexedRoots_mem hs hj)
  · have hlen : ¬j < p.roots.toList.length := by
      rwa [Multiset.length_toList, ← hs.natDegree_eq_card_roots]
    simp only [indexedRoots, dite_eq_right hlen, Set.mem_Icc]
    exact ⟨neg_nonpos.mpr zero_le_one, zero_le_one⟩

/-- A product over indexed roots is a product over the root multiset. -/
theorem prod_indexedRoots {M : Type*} [CommMonoid M] {p : ℝ[X]} (hs : p.Splits)
    (f : ℝ → M) :
    ∏ j ∈ Finset.range p.natDegree, f (indexedRoots p j) = (p.roots.map f).prod := by
  rw [hs.natDegree_eq_card_roots, ← Multiset.length_toList, Finset.prod_range]
  have hprod : (∏ i : Fin p.roots.toList.length, f (indexedRoots p i)) =
      ∏ i : Fin p.roots.toList.length, f p.roots.toList[i.1] := by
    apply Finset.prod_congr rfl
    intro i _
    rw [indexedRoots, dite_eq_left i.isLt]
  rw [hprod, Fin.prod_univ_fun_getElem]
  change (((p.roots.toList : Multiset ℝ).map f).prod) = _
  rw [Multiset.coe_toList]

/-- A split polynomial factors over the indexed roots with its leading coefficient. -/
theorem eq_prod_indexedRoots {p : ℝ[X]} (hs : p.Splits) :
    p = C p.leadingCoeff * ∏ j ∈ Finset.range p.natDegree, (X - C (indexedRoots p j)) := by
  rw [prod_indexedRoots hs (fun r : ℝ => X - C r)]
  exact hs.eq_prod_roots

end RealRooted.TuranHurwitz
