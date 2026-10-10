import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.IntervalCases

/-!
# Generating polynomials of finite statistics

For a finite set and a natural-valued statistic, `Finset.genPoly` records the
distribution of the statistic as a polynomial.  This is deliberately stated
in the `Finset` namespace so that the definition is suitable for Mathlib.
-/

open scoped BigOperators Polynomial
open Polynomial

namespace Finset

variable {ι κ α β R : Type*}

/-- The generating polynomial of a natural-valued statistic on a finite set. -/
noncomputable def genPoly [CommSemiring R] (s : Finset ι) (stat : ι → ℕ) : R[X] :=
  ∑ a ∈ s, X ^ stat a

/-- The coefficient of `X ^ k` in `genPoly s stat` counts the `k`-fibre. -/
@[simp]
theorem coeff_genPoly [CommSemiring R] (s : Finset ι) (stat : ι → ℕ) (k : ℕ) :
    (genPoly s stat : R[X]).coeff k = (s.filter (stat · = k)).card := by
  simp [genPoly, Polynomial.coeff_X_pow, eq_comm, Finset.sum_boole]

/-- The generating polynomial of the empty set is zero. -/
@[simp]
theorem genPoly_empty [CommSemiring R] (stat : ι → ℕ) :
    genPoly (∅ : Finset ι) stat = (0 : R[X]) := by
  simp [genPoly]

/-- Inserting a new element adds its monomial to the generating polynomial. -/
@[simp]
theorem genPoly_insert [CommSemiring R] [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (stat : ι → ℕ) :
    genPoly (insert a s) stat = (X : R[X]) ^ stat a + genPoly s stat := by
  simp [genPoly, ha]

/-- Evaluating a generating polynomial at one gives the cardinality of its set. -/
@[simp]
theorem eval_one_genPoly [CommSemiring R] (s : Finset ι) (stat : ι → ℕ) :
    (genPoly s stat : R[X]).eval 1 = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [genPoly]
  | @insert a s ha ih =>
      rw [genPoly_insert a s ha stat, eval_add, eval_X_pow]
      simp [ih, ha, add_comm]

/-- The generating polynomial is additive over a disjoint union. -/
theorem genPoly_union [CommSemiring R] [DecidableEq ι] (s t : Finset ι) (h : Disjoint s t)
    (stat : ι → ℕ) :
    (genPoly (s ∪ t) stat : R[X]) = genPoly s stat + genPoly t stat := by
  simp only [genPoly]
  rw [Finset.sum_union h]

/-- Injective maps transport generating polynomials by transporting the statistic. -/
theorem genPoly_map [CommSemiring R] (e : ι ↪ κ) (s : Finset ι) (stat : κ → ℕ) :
    (genPoly (s.map e) stat : R[X]) = genPoly s (stat ∘ e) := by
  simp [genPoly, Finset.sum_map, Function.comp_apply]

/-- A ring homomorphism maps a generating polynomial to the generating polynomial of the same
statistic. -/
@[simp]
theorem map_genPoly {S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (s : Finset ι)
    (stat : ι → ℕ) : (genPoly s stat : R[X]).map f = genPoly s stat := by
  simp [genPoly, Polynomial.map_sum]

/-- An equivalence transports a statistic through its inverse on a mapped set. -/
theorem genPoly_equiv [CommSemiring R] (e : ι ≃ κ) (s : Finset κ) (stat : ι → ℕ) :
    (genPoly (s.map e.symm.toEmbedding) stat : R[X]) = genPoly s (stat ∘ e.symm) := by
  simp [genPoly, Function.comp_apply, Finset.sum_map]

/-- Generating polynomials multiply on products for an additive statistic. -/
theorem genPoly_product [CommSemiring R] (s : Finset ι) (t : Finset κ)
    (stat : ι → ℕ) (stat' : κ → ℕ) :
    (genPoly (s ×ˢ t) (fun p => stat p.1 + stat' p.2) : R[X]) =
      genPoly s stat * genPoly t stat' := by
  simp only [genPoly]
  rw [Finset.sum_product s t]
  simp_rw [pow_add]
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]

/-- The degree of a generating polynomial is at most the largest statistic. -/
theorem natDegree_genPoly_le [CommSemiring R] (s : Finset ι) (stat : ι → ℕ) :
    (genPoly s stat : R[X]).natDegree ≤ s.sup stat := by
  change (∑ a ∈ s, (X ^ stat a : R[X])).natDegree ≤ s.sup stat
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  exact (Polynomial.natDegree_X_pow_le _).trans (Finset.le_sup ha)

/-- Equal fibre cardinalities imply equal generating polynomials. -/
theorem genPoly_congr [CommSemiring R] (s t : Finset ι) (stat : ι → ℕ)
    (h : ∀ k, (s.filter (stat · = k)).card = (t.filter (stat · = k)).card) :
    (genPoly s stat : R[X]) = genPoly t stat := by
  apply Polynomial.ext
  intro k
  rw [coeff_genPoly, coeff_genPoly, h]

/-- A statistic-preserving bijection identifies the corresponding generating polynomials. -/
theorem genPoly_eq_of_bij [CommSemiring R] (s : Finset ι) (t : Finset κ)
    (stat : ι → ℕ) (stat' : κ → ℕ) (f : ι → κ) (hf : Function.Bijective f)
    (hst : ∀ x, x ∈ s ↔ f x ∈ t) (hstat : ∀ x ∈ s, stat x = stat' (f x)) :
    (genPoly s stat : R[X]) = genPoly t stat' := by
  unfold genPoly
  apply Finset.sum_bijective f hf hst
  intro x hx
  simp [hstat x hx]

/-- Coefficients of a generating polynomial are nonnegative in an ordered semiring. -/
theorem coeff_genPoly_nonneg [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (s : Finset ι) (stat : ι → ℕ) (k : ℕ) :
    0 ≤ (genPoly s stat : R[X]).coeff k := by
  rw [coeff_genPoly]
  positivity

private def fixedPoints (σ : Equiv.Perm (Fin 3)) : ℕ :=
  (Finset.univ.filter (fun i => σ i = i)).card

/-- For permutations of three letters, fixed-point enumeration is `2 + 3 X + X ^ 3`. -/
example :
    (genPoly (Finset.univ : Finset (Equiv.Perm (Fin 3))) fixedPoints : ℕ[X]) =
      (2 + 3 * X + X ^ 3 : ℕ[X]) := by
  have h0 :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => fixedPoints σ = 0)).card = 2 := by
    decide
  have h1 :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => fixedPoints σ = 1)).card = 3 := by
    decide
  have h2 :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => fixedPoints σ = 2)).card = 0 := by
    decide
  have h3 :
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => fixedPoints σ = 3)).card = 1 := by
    decide
  have hcoeff (k : ℕ) :
      ((2 + 3 * X + X ^ 3 : ℕ[X]).coeff k) =
        (if k = 0 then 2 else 0) + 3 * (if k = 1 then 1 else 0) +
          (if k = 3 then 1 else 0) := by
    change (Nat.cast 2 : ℕ[X]).coeff k + (3 * X).coeff k + (X ^ 3).coeff k = _
    rw [coeff_natCast_ite]
    simp [coeff_X, coeff_X_pow, eq_comm]
  apply Polynomial.ext
  intro k
  rw [coeff_genPoly]
  rw [hcoeff]
  by_cases hk : k ≤ 3
  · interval_cases k <;> simp [h0, h1, h2, h3]
  · have hk' : 3 < k := Nat.lt_of_not_ge hk
    have hzero :
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => fixedPoints σ = k)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro σ hσ
      have hle : fixedPoints σ ≤ 3 := by
        dsimp [fixedPoints]
        exact (Finset.card_filter_le _ _).trans_eq (by decide)
      exact by lia
    have hk0 : k ≠ 0 := by lia
    have hk1 : k ≠ 1 := by lia
    have hk3 : k ≠ 3 := by lia
    simp [hzero, hk0, hk1, hk3]

end Finset
