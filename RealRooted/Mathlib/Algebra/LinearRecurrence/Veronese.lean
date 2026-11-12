/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Veronese
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Operator
import Mathlib.Tactic

/-!
# Constant-coefficient recurrences for Veronese sections

The determinant norm of a forward characteristic polynomial is a monic annihilator
for every Veronese section of every solution. Thus the same recurrence of order
`r * E.order` works for all solutions and all residues. The coefficients must be
independent of the sequence index. The section modulus can be any positive natural
number, over an arbitrary commutative ring and in every characteristic.
-/

@[expose] public section

open Polynomial Finset

namespace LinearRecurrence

noncomputable section

variable {A : Type*} [CommRing A]

/-- Taking a section commutes with the shift action of a polynomial with expanded coefficients. -/
theorem veroneseSection_shiftAction_map_expand {r i : ℕ} (hr : 0 < r) (hi : i < r)
    (p : A[X][X]) (R : ℕ → A[X]) (n : ℕ) :
    (shiftAction (p.map (expand A r).toRingHom) R n).veroneseSection r i =
      shiftAction p (fun m => (R m).veroneseSection r i) n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, shiftAction, map_add, LinearMap.add_apply, Pi.add_apply,
        veroneseSection_add] at hp hq ⊢
      rw [hp, hq]
  | monomial k a =>
      simp only [Polynomial.map_monomial, shiftAction_monomial_apply, Pi.smul_apply,
        smul_eq_mul, forwardShift_pow_apply]
      exact veroneseSection_expand_mul hr hi a (R (n + k))

/-- Every annihilator of a polynomial sequence induces a norm annihilator for each section. -/
theorem shiftAction_veroneseNorm_eq_zero {r : ℕ} (hr : 0 < r)
    {p : A[X][X]} {R : ℕ → A[X]} (hR : shiftAction p R = 0)
    {i : ℕ} (hi : i < r) :
    shiftAction (veroneseNorm r p) (fun n => (R n).veroneseSection r i) = 0 := by
  have hann : shiftAction ((veroneseNorm r p).map (expand A r).toRingHom) R = 0 := by
    rw [← mul_veroneseAdjugateCoeffs hr p, mul_comm p, shiftAction_mul_apply, hR]
    exact map_zero _
  funext n
  rw [← veroneseSection_shiftAction_map_expand hr hi, hann]
  simp

/-- The recurrence with characteristic polynomial given by the explicit section determinant.
Its prescribed order remains meaningful over the trivial ring. -/
def veronese (r : ℕ) (E : LinearRecurrence A[X]) : LinearRecurrence A[X] where
  order := r * E.order
  coeffs i := -(veroneseNorm r E.charPoly).coeff i

/-- The order of the section recurrence is the modulus times the original order. -/
@[simp] theorem veronese_order (r : ℕ) (E : LinearRecurrence A[X]) :
    (E.veronese r).order = r * E.order := rfl

/-- The section recurrence has precisely the determinant norm as characteristic polynomial. -/
@[simp] theorem charPoly_veronese {r : ℕ} (hr : 0 < r) (E : LinearRecurrence A[X]) :
    (E.veronese r).charPoly = veroneseNorm r E.charPoly := by
  nontriviality A
  have hdeg : (veroneseNorm r E.charPoly).natDegree = r * E.order := by
    rw [E.charPoly_monic.natDegree_veroneseNorm hr,
      natDegree_eq_of_degree_eq_some E.charPoly_degree_eq_order]
  rw [LinearRecurrence.charPoly]
  dsimp only [veronese]
  rw [monomial_one_right_eq_X_pow]
  change X ^ (r * E.order) -
    ∑ i : Fin (r * E.order), monomial i (-(veroneseNorm r E.charPoly).coeff i) = _
  calc
    _ = X ^ (r * E.order) +
        ∑ i ∈ range (r * E.order), C ((veroneseNorm r E.charPoly).coeff i) * X ^ i := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i => monomial i (-(veroneseNorm r E.charPoly).coeff i)) (r * E.order)]
      simp [← C_mul_X_pow_eq_monomial]
    _ = veroneseNorm r E.charPoly := by
      rw [← hdeg]
      exact (E.charPoly_monic.veroneseNorm hr).as_sum.symm

/-- Veronese sections of solutions satisfy the common determinant-norm recurrence. -/
theorem IsSolution.veronese {E : LinearRecurrence A[X]} {R : ℕ → A[X]}
    (hR : E.IsSolution R) {r : ℕ} (hr : 0 < r) {i : ℕ} (hi : i < r) :
    (E.veronese r).IsSolution (fun n => (R n).veroneseSection r i) := by
  rw [isSolution_iff_aeval_charPoly_eq_zero, charPoly_veronese hr]
  exact shiftAction_veroneseNorm_eq_zero hr
    ((E.isSolution_iff_aeval_charPoly_eq_zero R).mp hR) hi

/-- One recurrence of order `r * E.order` works for every solution and every residue. -/
theorem exists_veroneseSection (E : LinearRecurrence A[X]) {r : ℕ} (hr : 0 < r) :
    ∃ T : LinearRecurrence A[X], T.order = r * E.order ∧
      T.charPoly = veroneseNorm r E.charPoly ∧
      ∀ (R : ℕ → A[X]), E.IsSolution R → ∀ i, i < r →
        T.IsSolution (fun n => (R n).veroneseSection r i) :=
  ⟨E.veronese r, rfl, charPoly_veronese hr E, fun _ hR _ hi => hR.veronese hr hi⟩

/-- An eventual source recurrence gives an eventual section recurrence with the same offset.
The source equation first determines row `s + E.order`; the section equation first
determines row `s + r * E.order`. Thus a source starting at row `N ≥ E.order`
gives a section recurrence starting at `N + (r - 1) * E.order`. -/
theorem veronese_recurrence_of_eventually (E : LinearRecurrence A[X])
    {r : ℕ} (hr : 0 < r) {R : ℕ → A[X]} {s : ℕ}
    (hR : ∀ n, s ≤ n → R (n + E.order) = ∑ j, E.coeffs j * R (n + j))
    {i : ℕ} (hi : i < r) {n : ℕ} (hn : s ≤ n) :
    (R (n + r * E.order)).veroneseSection r i =
      ∑ j : Fin (r * E.order), (E.veronese r).coeffs j *
        (R (n + j)).veroneseSection r i := by
  have hshift : E.IsSolution (fun m => R (s + m)) := by
    intro m
    simpa only [Nat.add_assoc] using hR (s + m) (Nat.le_add_right s m)
  have hsection := hshift.veronese hr hi (n - s)
  change (R (s + (n - s + r * E.order))).veroneseSection r i =
    ∑ j : Fin (r * E.order), (E.veronese r).coeffs j *
      (R (s + (n - s + j))).veroneseSection r i at hsection
  have hns : s + (n - s) = n := by lia
  simpa only [← Nat.add_assoc, hns] using hsection

end

end LinearRecurrence
