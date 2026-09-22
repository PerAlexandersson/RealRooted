import RealRooted.JacobiDeformation.KernelSignRestriction
import RealRooted.JacobiDeformation.SpectralKernelBridge

/-!
# Weighted signs of the Jacobi spectral kernel

This specializes the dimension-restricted Newton sign to the actual
quasi-Jacobi collocation matrix, then transports it through its spectral
kernel expansion.
-/

open Finset Matrix Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- A degree-`m` Newton weight has strictly positive entries on the actual
quasi-Jacobi collocation matrix whenever its degree is at least the matrix
dimension. -/
theorem aeval_weightNewtonPolynomial_quasiJacobiCollocationMatrix_entry_pos_of_le
    {N m : ℕ} (hN : 1 ≤ N) (hm : N + 1 ≤ m) {α β τ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : Fin (N + 1) → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial (N + 1) α β τ).IsRoot (x i))
    (i j : Fin (N + 1)) :
    0 < (aeval (quasiJacobiCollocationMatrix (N + 1) α β τ x)
      (weightNewtonPolynomial m δ (α + β + 2))) i j := by
  have hq : 2 ≤ N + 1 := by lia
  let A := quasiJacobiCollocationMatrix (N + 1) α β τ x
  let hA : A.IsHermitian :=
    quasiJacobiCollocationMatrix_isHermitian hq hα hβ x hx hroot
  have hs : 0 < α + β + 2 := by linarith
  apply aeval_weightNewtonPolynomial_entry_pos_of_dimension_le A hA
    (fun a b =>
      (quasiJacobiCollocationMatrix_entry_pos hq hα hβ x hx hroot a b).le)
    (quasiJacobiCollocationMatrix_sortedEigenvalues_strictAnti
      hq hα hβ x hx hroot)
    hm hδ hδ1 hs
    (fun k => quasiJacobiCollocationMatrix_increasingEigenvalues
      hq hα hβ x hx hroot k)
    i j
  exact quasiJacobiCollocationMatrix_entry_pos hq hα hβ x hx hroot i j

private theorem eval_weightNewtonPolynomial_eq_kernelWeight_div_zero
    {m q : ℕ} {δ s : ℝ} (hm : q ≤ m) (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 0 < s)
    (n : Fin q) :
    (weightNewtonPolynomial m δ s).eval (eigenvalue s n) =
      kernelWeight m δ s n / kernelWeight m δ s 0 := by
  rw [eval_weightNewtonPolynomial_eq_sum_newtonExpansionTerm
    (show (n : ℕ) ≤ m by exact le_trans n.isLt.le hm)]
  exact sum_newtonExpansionTerm_eq_kernelWeight_div_kernelWeight_zero
    (le_trans n.isLt.le hm) hδ hδ1 hs

/-- The actual weighted Jacobi spectral kernel is strictly positive after
division by the two preceding Jacobi evaluations.  The result allows the
Newton degree to exceed the collocation dimension. -/
theorem kernelWeight_quasiJacobi_sum_div_eval_prev_pos
    {N m : ℕ} (hN : 1 ≤ N) (hm : N + 1 ≤ m) {α β τ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (x : Fin (N + 1) → ℝ) (hx : Function.Injective x)
    (hroot : ∀ i, (quasiJacobiPolynomial (N + 1) α β τ).IsRoot (x i))
    (i j : Fin (N + 1)) :
    0 <
      (∑ l : Fin (N + 1),
          kernelWeight m δ (α + β + 2) l *
            (shiftedJacobiMonic l α β).eval (x i) *
            (shiftedJacobiMonic l α β).eval (x j) /
              shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic N α β).eval (x i) *
          (shiftedJacobiMonic N α β).eval (x j)) := by
  have hq : 2 ≤ N + 1 := by lia
  have hs : 0 < α + β + 2 := by linarith
  let A := quasiJacobiCollocationMatrix (N + 1) α β τ x
  let H := shiftedJacobiMonicNorm N α β
  let wi := kernelWeight m δ (α + β + 2) 0
  let ηi := quasiJacobiEta (N + 1) α β τ x i
  let ηj := quasiJacobiEta (N + 1) α β τ x j
  let pi := (shiftedJacobiMonic N α β).eval (x i)
  let pj := (shiftedJacobiMonic N α β).eval (x j)
  let S := ∑ l : Fin (N + 1),
    kernelWeight m δ (α + β + 2) l *
      (shiftedJacobiMonic l α β).eval (x i) *
      (shiftedJacobiMonic l α β).eval (x j) /
        shiftedJacobiMonicNorm l α β
  let T := ∑ l : Fin (N + 1),
    (weightNewtonPolynomial m δ (α + β + 2)).eval
        (eigenvalue (α + β + 2) l) *
      (shiftedJacobiMonic l α β).eval (x i) *
      (shiftedJacobiMonic l α β).eval (x j) /
        shiftedJacobiMonicNorm l α β
  have hentry : 0 <
      (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j := by
    simpa only [A] using
      aeval_weightNewtonPolynomial_quasiJacobiCollocationMatrix_entry_pos_of_le
        hN hm hα hβ hδ hδ1 x hx hroot i j
  have hηi : 0 < ηi :=
    quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot i
  have hηj : 0 < ηj :=
    quasiJacobiEta_pos_of_roots hq hα hβ x hx hroot j
  have hpi : pi ≠ 0 :=
    shiftedJacobiMonic_eval_prev_ne_zero_of_roots hq hα hβ x hx hroot i
  have hpj : pj ≠ 0 :=
    shiftedJacobiMonic_eval_prev_ne_zero_of_roots hq hα hβ x hx hroot j
  have hH : 0 < H := shiftedJacobiMonicNorm_pos hα hβ N
  have hwi : 0 < wi := kernelWeight_pos (j := 0) (by simp) hδ hs
  have hsum : T = S / wi := by
    apply Finset.sum_congr rfl
    intro l _
    rw [eval_weightNewtonPolynomial_eq_kernelWeight_div_zero hm hδ hδ1 hs l]
    ring
  have hspectral := aeval_quasiJacobiCollocationMatrix_apply_eq_kernel_sum
    hq hα hβ x hx hroot (weightNewtonPolynomial m δ (α + β + 2)) i j
  change (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j = H /
      (quasiJacobiCollocationScale (N + 1) α β τ x i *
        quasiJacobiCollocationScale (N + 1) α β τ x j) * T at hspectral
  rw [hsum] at hspectral
  have hformula : S / (pi * pj) =
      (aeval A (weightNewtonPolynomial m δ (α + β + 2))) i j * wi *
        Real.sqrt ηi * Real.sqrt ηj / H := by
    rw [quasiJacobiCollocationScale, quasiJacobiCollocationScale] at hspectral
    field_simp [hpi, hpj, hwi.ne', hH.ne', (Real.sqrt_pos.2 hηi).ne',
      (Real.sqrt_pos.2 hηj).ne'] at hspectral ⊢
    nlinarith [hspectral]
  change 0 < S / (pi * pj)
  rw [hformula]
  exact div_pos
    (mul_pos (mul_pos (mul_pos hentry hwi) (Real.sqrt_pos.2 hηi))
      (Real.sqrt_pos.2 hηj)) hH

end RealRooted.JacobiDeformation
