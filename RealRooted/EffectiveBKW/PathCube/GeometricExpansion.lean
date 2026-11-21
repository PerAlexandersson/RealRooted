module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite geometric expansions of a rational quartic series

Four distinct nonzero reciprocal roots determine the residues by interpolation.
The coefficient identity is formal: it uses neither analytic convergence nor a
real-rootedness assumption on the coefficient polynomials.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube.RationalSeries

open scoped BigOperators

/-- The factor with reciprocal root `z`. -/
noncomputable def linearPolynomial (z : ℂ) : Polynomial ℂ :=
  1 - Polynomial.C z * Polynomial.X

/-- A denominator with four prescribed reciprocal roots. -/
noncomputable def denominatorPolynomial (z : Fin 4 → ℂ) : Polynomial ℂ :=
  ∏ i, linearPolynomial (z i)

/-- The denominator with one factor omitted. -/
noncomputable def cofactorPolynomial (z : Fin 4 → ℂ) (i : Fin 4) : Polynomial ℂ :=
  ∏ j, if j = i then 1 else linearPolynomial (z j)

/-- The coefficient of the geometric mode belonging to a reciprocal root. -/
noncomputable def residue (z : Fin 4 → ℂ) (N : Polynomial ℂ) (i : Fin 4) : ℂ :=
  N.eval (z i)⁻¹ / (cofactorPolynomial z i).eval (z i)⁻¹

/-- The formal geometric series, without any convergence condition. -/
noncomputable def geometricSeries (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n ↦ z ^ n)

private theorem natDegree_linearPolynomial_le (z : ℂ) :
    (linearPolynomial z).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))

private theorem natDegree_cofactorPolynomial_le (z : Fin 4 → ℂ) (i : Fin 4) :
    (cofactorPolynomial z i).natDegree ≤ 3 := by
  classical
  apply (Polynomial.natDegree_prod_le _ _).trans
  have h (j : Fin 4) :
      (if j = i then (1 : Polynomial ℂ) else linearPolynomial (z j)).natDegree ≤
        if j = i then 0 else 1 := by
    split_ifs
    · simp
    · exact natDegree_linearPolynomial_le _
  calc
    _ ≤ ∑ j : Fin 4, if j = i then 0 else 1 := Finset.sum_le_sum (fun j _ ↦ h j)
    _ = 3 := by fin_cases i <;> norm_num [Fin.sum_univ_succ]

private theorem linear_mul_cofactor (z : Fin 4 → ℂ) (i : Fin 4) :
    linearPolynomial (z i) * cofactorPolynomial z i = denominatorPolynomial z := by
  fin_cases i <;>
    simp [cofactorPolynomial, denominatorPolynomial, Fin.prod_univ_succ] <;> ring

private theorem cofactor_eval_ne_zero {z : Fin 4 → ℂ}
    (hz : ∀ i, z i ≠ 0) (hinj : Function.Injective z) (i : Fin 4) :
    (cofactorPolynomial z i).eval (z i)⁻¹ ≠ 0 := by
  classical
  rw [cofactorPolynomial, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · simp only [ite_eq_right hji, linearPolynomial, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    intro h
    have he : z j / z i = 1 := (sub_eq_zero.mp h).symm
    have heq : z j = z i := by simpa using (div_eq_iff (hz i)).mp he
    exact hji (hinj heq)

private theorem cofactor_eval_other {z : Fin 4 → ℂ} (hz : ∀ i, z i ≠ 0)
    {i j : Fin 4} (hij : i ≠ j) : (cofactorPolynomial z j).eval (z i)⁻¹ = 0 := by
  classical
  rw [cofactorPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hij, linearPolynomial, hz i]

/-- The four residue numerators reconstruct any numerator of degree at most three. -/
theorem sum_residue_mul_cofactor {z : Fin 4 → ℂ} (hz : ∀ i, z i ≠ 0)
    (hinj : Function.Injective z) (N : Polynomial ℂ) (hN : N.natDegree ≤ 3) :
    N = ∑ i, Polynomial.C (residue z N i) * cofactorPolynomial z i := by
  classical
  have hv : Set.InjOn (fun i ↦ (z i)⁻¹) (Finset.univ : Finset (Fin 4)) := by
    intro i _ j _ he
    exact hinj (inv_injective he)
  have hsum :
      (∑ i, Polynomial.C (residue z N i) * cofactorPolynomial z i).natDegree ≤ 3 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ ↦
      (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_cofactorPolynomial_le z i))
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
  · have h : (N.natDegree : WithBot ℕ) < 4 := by exact_mod_cast (show N.natDegree < 4 by lia)
    exact Polynomial.degree_le_natDegree.trans_lt (by simpa using h)
  · have h :
        ((∑ i, Polynomial.C (residue z N i) * cofactorPolynomial z i).natDegree : WithBot ℕ)
          < 4 := by
      have hlt :
          (∑ i, Polynomial.C (residue z N i) * cofactorPolynomial z i).natDegree < 4 := by lia
      exact_mod_cast hlt
    exact Polynomial.degree_le_natDegree.trans_lt (by simpa using h)
  · intro i _
    rw [Polynomial.eval_finsetSum]
    symm
    calc
      _ = (Polynomial.C (residue z N i) * cofactorPolynomial z i).eval (z i)⁻¹ := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          simp [Polynomial.eval_mul, Polynomial.eval_C, cofactor_eval_other hz hji.symm]
        · simp
      _ = N.eval (z i)⁻¹ := by
        simp only [Polynomial.eval_mul, Polynomial.eval_C, residue]
        exact div_mul_cancel₀ _ (cofactor_eval_ne_zero hz hinj i)

/-- The formal geometric series inverts its corresponding linear factor. -/
theorem linear_mul_geometricSeries (z : ℂ) :
    (linearPolynomial z : PowerSeries ℂ) * geometricSeries z = 1 := by
  ext n
  cases n <;>
    simp [linearPolynomial, geometricSeries, sub_mul, mul_assoc,
      PowerSeries.coeff_C_mul, pow_succ']

/-- A rational series with four distinct nonzero reciprocal roots is the finite
sum of its geometric modes, with the exact interpolation residues. -/
theorem eq_sum_residue_geometricSeries {z : Fin 4 → ℂ} (hz : ∀ i, z i ≠ 0)
    (hinj : Function.Injective z) (N : Polynomial ℂ) (hN : N.natDegree ≤ 3)
    (p : PowerSeries ℂ)
    (hp : (denominatorPolynomial z : PowerSeries ℂ) * p = N) :
    p = ∑ i, PowerSeries.C (residue z N i) * geometricSeries (z i) := by
  classical
  have hDpoly : denominatorPolynomial z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ he
    have hh := congrArg (fun f : Polynomial ℂ ↦ f.eval 0) he
    simp [linearPolynomial] at hh
  have hD : (denominatorPolynomial z : PowerSeries ℂ) ≠ 0 := by
    intro he
    exact hDpoly (Polynomial.coe_eq_zero_iff.mp he)
  have hidentity := congrArg
    (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
    (sum_residue_mul_cofactor hz hinj N hN)
  have hidentity' : (N : PowerSeries ℂ) =
      ∑ i, PowerSeries.C (residue z N i) * (cofactorPolynomial z i : PowerSeries ℂ) := by
    simpa only [map_sum, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C] using hidentity
  apply mul_left_cancel₀ hD
  rw [hp, Finset.mul_sum, hidentity']
  apply Finset.sum_congr rfl
  intro i _
  have hfactor : (linearPolynomial (z i) : PowerSeries ℂ) *
      (cofactorPolynomial z i : PowerSeries ℂ) = denominatorPolynomial z := by
    simpa only [Polynomial.coe_mul] using congrArg
      (fun f : Polynomial ℂ ↦ (f : PowerSeries ℂ)) (linear_mul_cofactor z i)
  symm
  calc
    _ = PowerSeries.C (residue z N i) * (cofactorPolynomial z i : PowerSeries ℂ) *
        ((linearPolynomial (z i) : PowerSeries ℂ) * geometricSeries (z i)) := by
      rw [← hfactor]
      ring
    _ = _ := by rw [linear_mul_geometricSeries, mul_one]

/-- Extract the exact geometric-mode formula for every coefficient. -/
theorem coeff_eq_sum_residue_mul_pow {z : Fin 4 → ℂ} (hz : ∀ i, z i ≠ 0)
    (hinj : Function.Injective z) (N : Polynomial ℂ) (hN : N.natDegree ≤ 3)
    (p : PowerSeries ℂ)
    (hp : (denominatorPolynomial z : PowerSeries ℂ) * p = N) (n : ℕ) :
    PowerSeries.coeff n p = ∑ i, residue z N i * z i ^ n := by
  rw [eq_sum_residue_geometricSeries hz hinj N hN p hp]
  simp only [map_sum, PowerSeries.coeff_C_mul, geometricSeries, PowerSeries.coeff_mk]

end RealRooted.EffectiveBKW.PathCube.RationalSeries
