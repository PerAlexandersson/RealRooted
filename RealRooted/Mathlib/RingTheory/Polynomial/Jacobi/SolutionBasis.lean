/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.CompleteSolutions
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.Multiplicity
import Mathlib.Tactic

/-!
# Explicit bases at exceptional Jacobi parameters

The lower Jacobi polynomial and the left-endpoint conjugate of a shifted Jacobi
polynomial form a basis even when the standard degree-`u` polynomial is zero.
Source: unpublished proof notes, RealRooted issue #2345, equations (7) and (8).
-/

public section

namespace Polynomial

/-- The standard Jacobi model is always a solution, including when it is zero. -/
theorem shiftedJacobi_mem_jacobiSolutionSpace (n : ℕ) (α β : ℝ) :
    shiftedJacobi n α β ∈ jacobiSolutionSpace n α β := by
  apply (mem_jacobiSolutionSpace_iff n α β _).mpr
  simpa only [jacobiDifferentialOperator] using shiftedJacobi_differential_equation n α β

/-- The lower-degree standard model has a nonzero highest coefficient even at
exceptional endpoint parameters. -/
theorem coeff_shiftedJacobi_ne_zero_of_degree_sum (ℓ u : ℕ) (α β : ℝ)
    (hℓu : ℓ ≤ u) (hs : (ℓ : ℝ) + u + α + β + 1 = 0) :
    (shiftedJacobi ℓ α β).coeff ℓ ≠ 0 := by
  rw [coeff_shiftedJacobi]
  simp only [le_refl, ite_true, Nat.sub_self, Ring.choose_zero_right, mul_one]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  intro hz
  have harg : (ℓ : ℝ) + α + β + ℓ = ℓ + (α + β + ℓ) := by ring
  rw [harg, choose_add_nat_eq_zero_iff] at hz
  obtain ⟨p, _, hpℓ, hα⟩ := hz
  have : (p : ℝ) ≤ ℓ := by exact_mod_cast hpℓ
  have : (ℓ : ℝ) ≤ u := by exact_mod_cast hℓu
  linarith

/-- Exact degree of the lower standard model. -/
theorem natDegree_shiftedJacobi_of_degree_sum (ℓ u : ℕ) (α β : ℝ)
    (hℓu : ℓ ≤ u) (hs : (ℓ : ℝ) + u + α + β + 1 = 0) :
    (shiftedJacobi ℓ α β).natDegree = ℓ := by
  exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_shiftedJacobi_le ℓ α β)
    (coeff_shiftedJacobi_ne_zero_of_degree_sum ℓ u α β hℓu hs)

/-- The endpoint-conjugated model solves the exceptional upper-degree equation. -/
theorem X_pow_mul_shiftedJacobi_mem_jacobiSolutionSpace
    (u p : ℕ) (β : ℝ) (hpu : p ≤ u) :
    X ^ p * shiftedJacobi (u - p) p β ∈ jacobiSolutionSpace u (-(p : ℝ)) β := by
  apply (mem_jacobiSolutionSpace_iff u (-(p : ℝ)) β _).mpr
  have ht : ((u - p : ℕ) : ℝ) = u - p := Nat.cast_sub hpu
  rw [show -(p : ℝ) + 1 = 1 - (p : ℝ) by ring,
    jacobiDifferentialOperator_X_pow_mul]
  have hc : -(p : ℝ) + β + 2 + 2 * p = (p : ℝ) + β + 2 := by ring
  have hD : (u : ℝ) * (u + -(p : ℝ) + β + 1) -
      p * (p + (-(p : ℝ) + β + 2) - 1) =
        (u - p : ℕ) * ((u - p : ℕ) + (p : ℝ) + β + 1) := by
    rw [ht]
    ring
  rw [hc, hD]
  have h := (mem_jacobiSolutionSpace_iff (u - p) p β _).mp
    (shiftedJacobi_mem_jacobiSolutionSpace (u - p) p β)
  rw [h, mul_zero]

/-- The exceptional upper model has a nonzero highest coefficient. -/
theorem coeff_X_pow_mul_shiftedJacobi_ne_zero
    (ℓ u p : ℕ) (β : ℝ) (hℓp : ℓ < p) (hpu : p ≤ u)
    (hs : (ℓ : ℝ) + u - p + β + 1 = 0) :
    (X ^ p * shiftedJacobi (u - p) p β).coeff u ≠ 0 := by
  rw [coeff_X_pow_mul', ite_eq_left hpu, coeff_shiftedJacobi]
  simp only [le_refl, ite_true, Nat.sub_self, Ring.choose_zero_right, mul_one]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  apply ne_of_gt
  apply ring_choose_pos
  rw [Nat.cast_sub hpu]
  have : (ℓ : ℝ) < p := by exact_mod_cast hℓp
  linarith

/-- Exact degree of the exceptional upper model. -/
theorem natDegree_X_pow_mul_shiftedJacobi
    (ℓ u p : ℕ) (β : ℝ) (hℓp : ℓ < p) (hpu : p ≤ u)
    (hs : (ℓ : ℝ) + u - p + β + 1 = 0) :
    (X ^ p * shiftedJacobi (u - p) p β).natDegree = u := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · have h := natDegree_mul_le (p := (X : ℝ[X]) ^ p)
      (q := shiftedJacobi (u - p) p β)
    rw [natDegree_X_pow] at h
    have := natDegree_shiftedJacobi_le (u - p) (p : ℝ) β
    lia
  · exact coeff_X_pow_mul_shiftedJacobi_ne_zero ℓ u p β hℓp hpu hs

/-- The upper model has exactly the indicated multiplicity at zero. -/
theorem rootMultiplicity_X_pow_mul_shiftedJacobi
    (u p : ℕ) (β : ℝ) :
    (X ^ p * shiftedJacobi (u - p) p β).rootMultiplicity 0 = p := by
  have heval : (shiftedJacobi (u - p) p β).eval 0 ≠ 0 := by
    rw [shiftedJacobi_eval_zero]
    apply ne_of_gt
    apply ring_choose_pos
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hne : shiftedJacobi (u - p) p β ≠ 0 := by
    intro hz
    simp [hz] at heval
  have hx : (X ^ p : ℝ[X]).rootMultiplicity 0 = p := by
    simpa using rootMultiplicity_X_sub_C_pow (0 : ℝ) p
  rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hne), hx,
    rootMultiplicity_eq_zero (by simpa [IsRoot.def] using heval), add_zero]

/-- The explicit exceptional pair spans the entire polynomial solution space. -/
theorem mem_jacobiSolutionSpace_iff_exists_eq_sum
    (ℓ u p : ℕ) (β : ℝ) (hℓp : ℓ < p) (hpu : p ≤ u)
    (hs : (ℓ : ℝ) + u - p + β + 1 = 0) (f : ℝ[X]) :
    f ∈ jacobiSolutionSpace u (-(p : ℝ)) β ↔
      ∃ c d : ℝ, f = C c * shiftedJacobi ℓ (-(p : ℝ)) β +
        C d * (X ^ p * shiftedJacobi (u - p) p β) := by
  have hℓu : ℓ < u := hℓp.trans_le hpu
  have hs' : (ℓ : ℝ) + u + -(p : ℝ) + β + 1 = 0 := by linarith
  have heq := jacobiSolutionSpace_eq ℓ u (-(p : ℝ)) β hs'
  have hlow : shiftedJacobi ℓ (-(p : ℝ)) β ∈
      jacobiSolutionSpace u (-(p : ℝ)) β := by
    rw [← heq]
    exact shiftedJacobi_mem_jacobiSolutionSpace _ _ _
  have hhigh := X_pow_mul_shiftedJacobi_mem_jacobiSolutionSpace u p β hpu
  have hlowc := coeff_shiftedJacobi_ne_zero_of_degree_sum ℓ u (-(p : ℝ)) β hℓu.le hs'
  have hhighc := coeff_X_pow_mul_shiftedJacobi_ne_zero ℓ u p β hℓp hpu hs
  have hlowu : (shiftedJacobi ℓ (-(p : ℝ)) β).coeff u = 0 :=
    coeff_eq_zero_of_natDegree_lt ((natDegree_shiftedJacobi_le _ _ _).trans_lt hℓu)
  have hhighℓ : (X ^ p * shiftedJacobi (u - p) p β).coeff ℓ = 0 := by
    simp [coeff_X_pow_mul', not_le.mpr hℓp]
  constructor
  · intro hf
    refine ⟨f.coeff ℓ / (shiftedJacobi ℓ (-(p : ℝ)) β).coeff ℓ,
      f.coeff u / (X ^ p * shiftedJacobi (u - p) p β).coeff u, ?_⟩
    apply eq_of_mem_jacobiSolutionSpace_of_two_coeff_eq u ℓ u (-(p : ℝ)) β
      (Or.inr rfl) hs' hf
    · simpa only [smul_eq_C_mul] using
        (jacobiSolutionSpace u (-(p : ℝ)) β).add_mem
          ((jacobiSolutionSpace u (-(p : ℝ)) β).smul_mem _ hlow)
          ((jacobiSolutionSpace u (-(p : ℝ)) β).smul_mem _ hhigh)
    · simp [coeff_C_mul, hhighℓ, hlowc]
    · simp [coeff_C_mul, hlowu, hhighc]
  · rintro ⟨c, d, rfl⟩
    simpa only [smul_eq_C_mul] using
      (jacobiSolutionSpace u (-(p : ℝ)) β).add_mem
        ((jacobiSolutionSpace u (-(p : ℝ)) β).smul_mem c hlow)
        ((jacobiSolutionSpace u (-(p : ℝ)) β).smul_mem d hhigh)

/-- The standard polynomial vanishes exactly when its index is the upper
candidate and the full solution space is two-dimensional. -/
theorem shiftedJacobi_eq_zero_iff_finrank_eq_two (n m : ℕ) (α β : ℝ)
    (hs : (n : ℝ) + m + α + β + 1 = 0) :
    shiftedJacobi n α β = 0 ↔
      m < n ∧ Module.finrank ℝ (jacobiSolutionSpace n α β) = 2 := by
  constructor
  · intro hz
    obtain ⟨p, q, hp, hpn, hq, hqn, hα, hβ, hsum⟩ :=
      (shiftedJacobi_eq_zero_iff n α β).mp hz
    have hsum' : p + q = n + m + 1 := by
      have hreal : (p : ℝ) + q = n + m + 1 := by rw [hα, hβ] at hs; linarith
      exact_mod_cast hreal
    have hmn : m < n := by lia
    refine ⟨hmn, ?_⟩
    rw [finrank_jacobiSolutionSpace_of_two_degrees n m n α β hmn (Or.inr rfl)
      (by linarith), ite_eq_left]
    exact ⟨p, by lia, hpn, hα⟩
  · rintro ⟨hmn, hdim⟩
    have hs' : (m : ℝ) + n + α + β + 1 = 0 := by linarith
    rw [finrank_jacobiSolutionSpace_of_two_degrees n m n α β hmn (Or.inr rfl) hs'] at hdim
    have hexc : ∃ p : ℕ, m < p ∧ p ≤ n ∧ α = -(p : ℝ) := by
      split_ifs at hdim with h
      · exact h
      · norm_num at hdim
    obtain ⟨p, q, hmp, hpn, hmq, hqn, hα, hβ, hsum⟩ :=
      (jacobi_exceptional_parameters_iff m n α β hs').mp hexc
    exact (shiftedJacobi_eq_zero_iff n α β).mpr
      ⟨p, q, by lia, hpn, by lia, hqn, hα, hβ, by lia⟩

/-- The explicit spanning pair is linearly independent, hence is a basis
of the two-dimensional solution space described above. -/
theorem linearIndependent_shiftedJacobi_endpoint_pair
    (ℓ u p : ℕ) (β : ℝ) (hℓp : ℓ < p) (hpu : p ≤ u)
    (hs : (ℓ : ℝ) + u - p + β + 1 = 0) :
    LinearIndependent ℝ ![shiftedJacobi ℓ (-(p : ℝ)) β,
      X ^ p * shiftedJacobi (u - p) p β] := by
  apply linearIndependent_fin2.mpr
  constructor
  · change X ^ p * shiftedJacobi (u - p) p β ≠ 0
    intro hz
    have h := coeff_X_pow_mul_shiftedJacobi_ne_zero ℓ u p β hℓp hpu hs
    apply h
    rw [hz, coeff_zero]
  · intro c hc
    change c • (X ^ p * shiftedJacobi (u - p) p β) =
      shiftedJacobi ℓ (-(p : ℝ)) β at hc
    have hlow := coeff_shiftedJacobi_ne_zero_of_degree_sum ℓ u (-(p : ℝ)) β
      (hℓp.trans_le hpu).le (by linarith)
    apply hlow
    have h := congrArg (fun f : ℝ[X] => f.coeff ℓ) hc
    simpa [AddMonoidAlgebra.coeff_smul_apply, coeff_X_pow_mul', not_le.mpr hℓp] using h.symm

/-- The explicit exceptional Jacobi basis, indexed by its lower and upper
solution degrees. The spanning and independence theorems above identify its vectors. -/
noncomputable def jacobiEndpointBasis (ℓ u p : ℕ) (β : ℝ)
    (hℓp : ℓ < p) (hpu : p ≤ u) (hs : (ℓ : ℝ) + u - p + β + 1 = 0) :
    Module.Basis (Fin 2) ℝ (jacobiSolutionSpace u (-(p : ℝ)) β) := by
  have hs' : (ℓ : ℝ) + u + -(p : ℝ) + β + 1 = 0 := by linarith
  have hlow : shiftedJacobi ℓ (-(p : ℝ)) β ∈
      jacobiSolutionSpace u (-(p : ℝ)) β := by
    rw [← jacobiSolutionSpace_eq ℓ u (-(p : ℝ)) β hs']
    exact shiftedJacobi_mem_jacobiSolutionSpace _ _ _
  let v : Fin 2 → jacobiSolutionSpace u (-(p : ℝ)) β :=
    ![⟨shiftedJacobi ℓ (-(p : ℝ)) β, hlow⟩,
      ⟨X ^ p * shiftedJacobi (u - p) p β,
        X_pow_mul_shiftedJacobi_mem_jacobiSolutionSpace u p β hpu⟩]
  have hli : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp (jacobiSolutionSpace u (-(p : ℝ)) β).subtype
    have hv : (jacobiSolutionSpace u (-(p : ℝ)) β).subtype ∘ v =
        ![shiftedJacobi ℓ (-(p : ℝ)) β, X ^ p * shiftedJacobi (u - p) p β] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact linearIndependent_shiftedJacobi_endpoint_pair ℓ u p β hℓp hpu hs
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    intro f _
    obtain ⟨c, d, hf⟩ := (mem_jacobiSolutionSpace_iff_exists_eq_sum ℓ u p β hℓp hpu hs f).mp
      f.property
    have heq : f = c • v 0 + d • v 1 := by
      apply Subtype.ext
      simpa only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Submodule.coe_add, Submodule.coe_smul, smul_eq_C_mul] using hf
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  exact Module.Basis.mk hli hspan

end Polynomial
