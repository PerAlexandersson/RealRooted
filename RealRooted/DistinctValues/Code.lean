module

public import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize
public import Mathlib.Basic.Real.Basic
public import RealRooted.Mathlib.Algebra.MvPolynomial.Diagonal
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-!
# Monomials marking distinct positive code values

A zero code entry receives its own null weight; each distinct positive value
is marked once. These are actual finite products, for use in the chordal
acyclic-orientation sum of RealRooted issue #2640.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted.DistinctValues

noncomputable section

/-- Zero-based marker indices of the distinct positive values of a finite code. -/
def codeValues {V : Type*} [Fintype V] (e : V → ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ.filter fun v => e v ≠ 0).image fun v => e v - 1

/-- A marker index occurs exactly when its positive code value occurs. -/
@[simp] theorem mem_codeValues {V : Type*} [Fintype V] (e : V → ℕ) (i : ℕ) :
    i ∈ codeValues e ↔ ∃ v, e v = i + 1 := by
  classical
  constructor
  · intro hi
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hi
    have hv0 := (Finset.mem_filter.mp hv).2
    exact ⟨v, by lia⟩
  · rintro ⟨v, hv⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, by lia⟩,
      by lia⟩

/-- The weighted monomial of a finite code: zeros weighted individually,
positive values marked once each. Marker `X i` represents code value `i+1`. -/
def codeMonomial {V : Type*} [Fintype V] (a : V → ℝ) (e : V → ℕ) :
    MvPolynomial ℕ ℝ :=
  MvPolynomial.C (∏ v, if e v = 0 then a v else 1) *
    ∏ i ∈ codeValues e, MvPolynomial.X i

/-- The value-one specialization removes the chosen variable from a squarefree product. -/
theorem specializeAt_prod_X (s : Finset ℕ) (i : ℕ) :
    MvPolynomial.specializeAt i 1 (∏ j ∈ s, MvPolynomial.X j : MvPolynomial ℕ ℝ) =
      ∏ j ∈ s.erase i, MvPolynomial.X j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.specializeAt]
  | @insert j s hj ih =>
      by_cases hji : j = i
      · subst j
        simp [Finset.prod_insert hj, MvPolynomial.specializeAt_mul, ih, hj,
          MvPolynomial.specializeAt_X]
      · have hjerase : j ∉ s.erase i := fun h => hj (Finset.erase_subset i s h)
        simp [Finset.prod_insert hj, MvPolynomial.specializeAt_mul, ih, hji, hjerase,
          Finset.erase_insert_of_ne hji, MvPolynomial.specializeAt_X]

/-- Marking a value adjoins its index to the set of existing markers. -/
theorem X_mul_specializeAt_prod_X (s : Finset ℕ) (i : ℕ) :
    MvPolynomial.X i *
        MvPolynomial.specializeAt i 1 (∏ j ∈ s, MvPolynomial.X j : MvPolynomial ℕ ℝ) =
      ∏ j ∈ insert i s, MvPolynomial.X j := by
  classical
  rw [specializeAt_prod_X]
  by_cases hi : i ∈ s
  · rw [Finset.insert_eq_of_mem hi]
    exact Finset.mul_prod_erase s _ hi
  · simp [hi]

/-- Adjoining a final zero adds no marker. -/
theorem codeValues_succ_zero {n : ℕ} (e : Fin (n + 1) → ℕ)
    (h : e (Fin.last n) = 0) : codeValues e = codeValues (fun i : Fin n => e i.castSucc) := by
  ext i
  simp only [mem_codeValues, Fin.exists_fin_succ', h]
  simp

/-- Adjoining a final positive value adjoins its marker. -/
theorem codeValues_succ_pos {n k : ℕ} (e : Fin (n + 1) → ℕ)
    (h : e (Fin.last n) = k + 1) :
    codeValues e = insert k (codeValues (fun i : Fin n => e i.castSucc)) := by
  ext i
  simp only [mem_codeValues, Fin.exists_fin_succ', h, Finset.mem_insert]
  grind

/-- A final code entry acts by null-weight multiplication or by value marking. -/
theorem codeMonomial_succ {n : ℕ} (a : Fin (n + 1) → ℝ) (e : Fin (n + 1) → ℕ) :
    codeMonomial a e =
      if e (Fin.last n) = 0 then
        MvPolynomial.C (a (Fin.last n)) * codeMonomial (fun i : Fin n => a i.castSucc)
          (fun i : Fin n => e i.castSucc)
      else MvPolynomial.X (e (Fin.last n) - 1) *
        MvPolynomial.specializeAt (e (Fin.last n) - 1) 1
          (codeMonomial (fun i : Fin n => a i.castSucc) (fun i : Fin n => e i.castSucc)) := by
  classical
  cases he : e (Fin.last n) with
  | zero =>
      simp only [he, ite_true, codeMonomial, Fin.prod_univ_castSucc,
        codeValues_succ_zero e he, MvPolynomial.C_mul]
      ring
  | succ k =>
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, codeMonomial,
        Fin.prod_univ_castSucc, he, ite_false, mul_one,
        codeValues_succ_pos e he, MvPolynomial.specializeAt_mul, MvPolynomial.specializeAt_C]
      rw [mul_left_comm, X_mul_specializeAt_prod_X]

/-- Relabeling the positions of a code preserves its weighted monomial. -/
theorem codeMonomial_equiv {V W : Type*} [Fintype V] [Fintype W]
    (f : V ≃ W) (a : W → ℝ) (e : W → ℕ) :
    codeMonomial (a ∘ f) (e ∘ f) = codeMonomial a e := by
  classical
  have hvalues : codeValues (e ∘ f) = codeValues e := by
    ext i
    simp only [mem_codeValues, Function.comp_apply]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨f v, hv⟩
    · rintro ⟨w, hw⟩
      exact ⟨f.symm w, by simpa using hw⟩
  have hprod : (∏ v, if (e ∘ f) v = 0 then (a ∘ f) v else 1) =
      ∏ w, if e w = 0 then a w else 1 := by
    simpa only [Function.comp_apply] using f.prod_comp (fun w => if e w = 0 then a w else 1)
  simp only [codeMonomial, hvalues, hprod]

/-- On the diagonal, the monomial records the number of distinct positive code values. -/
theorem diagonal_codeMonomial {V : Type*} [Fintype V] (a : V → ℝ) (e : V → ℕ) :
    MvPolynomial.diagonal (codeMonomial a e) =
      Polynomial.C (∏ v, if e v = 0 then a v else 1) *
        Polynomial.X ^ (codeValues e).card := by
  classical
  simp [codeMonomial, MvPolynomial.diagonal]

end

end RealRooted.DistinctValues
