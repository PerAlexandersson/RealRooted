module

public import RealRooted.TuranHurwitz.Recurrence
public import Mathlib.Topology.Algebra.Polynomial
import RealRooted.DerivativeRecurrence.Degree
import Mathlib.Tactic.ComputeDegree

/-!
# Continuity and degree bounds for a small-b₁ perturbation

We prove coefficient continuity directly from finite coefficient convolutions.
Uniform degree bounds then give continuity of every complex evaluation.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- Replace `b₁` by a real perturbation parameter. -/
@[expose] noncomputable def perturbB₁ (c : Parameters) (eps : ℝ) : Parameters :=
  {c with b₁ := eps}

/-- Addition preserves continuity of every polynomial coefficient. -/
theorem continuous_coeff_add (f g : ℝ → ℝ[X])
    (hf : ∀ k, Continuous fun e => (f e).coeff k)
    (hg : ∀ k, Continuous fun e => (g e).coeff k) (k : ℕ) :
    Continuous fun e => (f e + g e).coeff k := by
  simpa only [coeff_add, Function.comp_def] using continuous_add.comp ((hf k).prodMk (hg k))

/-- Multiplication preserves coefficient continuity by a finite Cauchy convolution. -/
theorem continuous_coeff_mul (f g : ℝ → ℝ[X])
    (hf : ∀ k, Continuous fun e => (f e).coeff k)
    (hg : ∀ k, Continuous fun e => (g e).coeff k) (k : ℕ) :
    Continuous fun e => (f e * g e).coeff k := by
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun ij _ => (hf ij.1).mul (hg ij.2)

/-- Differentiation preserves coefficient continuity. -/
theorem continuous_coeff_derivative (f : ℝ → ℝ[X])
    (hf : ∀ k, Continuous fun e => (f e).coeff k) (k : ℕ) :
    Continuous fun e => (f e).derivative.coeff k := by
  simpa only [coeff_derivative, Function.comp_def] using continuous_mul.comp
    ((hf (k + 1)).prodMk (continuous_const (y := (k : ℝ) + 1)))

/-- A continuously varying scalar constant has continuously varying polynomial coefficients. -/
theorem continuous_coeff_C (f : ℝ → ℝ) (hf : Continuous f) (k : ℕ) :
    Continuous fun e => (C (f e)).coeff k := by
  by_cases hk : k = 0
  · subst k
    simpa only [coeff_C_zero] using hf
  · simpa only [coeff_C, hk, ite_false] using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

/-- With `tau = 0`, every perturbed family row has continuous coefficients. -/
theorem continuous_coeff_family_perturb (c : Parameters) (ht : c.tau = 0) (j k : ℕ) :
    Continuous fun e => (family (perturbB₁ c e) j).coeff k := by
  induction j generalizing k with
  | zero => simpa only [family_zero] using
      (continuous_const : Continuous fun _ : ℝ => (1 : ℝ[X]).coeff k)
  | succ j ih =>
      let q := shiftedVariable c
      have hrec (e : ℝ) : family (perturbB₁ c e) (j + 1) =
          (C c.a₂ + C (e + c.b₂) * q) * family (perturbB₁ c e) j +
            (q * (C c.a₁ + C e * q)) * (family (perturbB₁ c e) j).derivative := by
        simp only [family, perturbB₁, ht, zero_mul, map_zero, add_zero, sub_zero, mul_one,
          q, shiftedVariable]
      simp only [hrec]
      apply continuous_coeff_add
      · apply continuous_coeff_mul _ _ _ ih
        apply continuous_coeff_add _ _ (fun _ => continuous_const)
        apply continuous_coeff_mul
        · exact continuous_coeff_C _ (continuous_id.add continuous_const)
        · exact fun _ => continuous_const
      · apply continuous_coeff_mul
        · apply continuous_coeff_mul _ _ (fun _ => continuous_const)
          apply continuous_coeff_add _ _ (fun _ => continuous_const)
          apply continuous_coeff_mul
          · exact continuous_coeff_C _ continuous_id
          · exact fun _ => continuous_const
        · exact continuous_coeff_derivative _ ih

/-- With `tau = 0`, every row has degree at most its index uniformly in the perturbation. -/
theorem natDegree_family_perturb_le (c : Parameters) (ht : c.tau = 0) (e : ℝ) (j : ℕ) :
    (family (perturbB₁ c e) j).natDegree ≤ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      let q := shiftedVariable c
      have hrec : family (perturbB₁ c e) (j + 1) =
          (q * (C c.a₁ + C e * q)) * (family (perturbB₁ c e) j).derivative +
            (C c.a₂ + C (e + c.b₂) * q) * family (perturbB₁ c e) j := by
        simp only [family, perturbB₁, ht, zero_mul, map_zero, add_zero, sub_zero, mul_one,
          q, shiftedVariable]
        exact add_comm _ _
      have hA : (q * (C c.a₁ + C e * q)).natDegree ≤ 1 + 1 := by
        dsimp [q, shiftedVariable]
        compute_degree
      have hB : (C c.a₂ + C (e + c.b₂) * q).natDegree ≤ 1 := by
        dsimp [q, shiftedVariable]
        compute_degree
      rw [hrec]
      exact Polynomial.natDegree_add_le_of_degree_le
        (RealRooted.natDegree_mul_iterate_derivative_le (d := 1) (j := 1) hA ih)
        (RealRooted.natDegree_mul_iterate_derivative_le (d := 1) (j := 0) hB ih)

/-- The perturbed Turán expression has continuous coefficients. -/
theorem continuous_coeff_turan_perturb (c : Parameters) (ht : c.tau = 0) (m n k : ℕ) :
    Continuous fun e => (turan m n (family (perturbB₁ c e))).coeff k := by
  simp only [turan, finsetSum_coeff]
  apply continuous_finsetSum
  intro j _
  apply continuous_coeff_mul _ _ (fun _ => continuous_const)
  exact continuous_coeff_mul _ _ (continuous_coeff_family_perturb c ht _)
    (continuous_coeff_family_perturb c ht _)

/-- The same degree box contains every perturbed Turán expression. -/
theorem natDegree_turan_perturb_le (c : Parameters) (ht : c.tau = 0)
    (e : ℝ) (m n : ℕ) :
    (turan m n (family (perturbB₁ c e))).natDegree ≤ 2 * m + 2 * n := by
  rw [turan]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ 2 * n := by simpa using Finset.mem_range.mp hj
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_mul_le.trans
  have h₁ := natDegree_family_perturb_le c ht e (m + j)
  have h₂ := natDegree_family_perturb_le c ht e (m + 2 * n - j)
  lia

/-- Complex evaluation varies continuously with the perturbation parameter. -/
theorem continuous_aeval_turan_perturb (c : Parameters) (ht : c.tau = 0)
    (m n : ℕ) (z : ℂ) :
    Continuous fun e => Polynomial.aeval z (turan m n (family (perturbB₁ c e))) := by
  have hsum (e : ℝ) : Polynomial.aeval z (turan m n (family (perturbB₁ c e))) =
      ∑ k ∈ Finset.range (2 * m + 2 * n + 1),
        ((turan m n (family (perturbB₁ c e))).coeff k : ℂ) * z ^ k := by
    rw [← Polynomial.eval_map_algebraMap,
      eval_eq_sum_range' (n := 2 * m + 2 * n + 1)
        (by rw [natDegree_map]; exact Nat.lt_succ_of_le (natDegree_turan_perturb_le c ht e m n))]
    have hc (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
    simp only [coeff_map, hc]
  simp only [hsum]
  exact continuous_finsetSum _ fun k _ =>
    (Complex.continuous_ofReal.comp (continuous_coeff_turan_perturb c ht m n k)).mul
      continuous_const

end RealRooted.TuranHurwitz
