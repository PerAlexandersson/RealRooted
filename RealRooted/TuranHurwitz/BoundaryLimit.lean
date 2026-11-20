module

public import RealRooted.TuranHurwitz.OpenStability
public import RealRooted.TuranHurwitz.TuranLowerBound
public import RealRooted.TuranHurwitz.ParameterContinuity
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# The exponential boundary by bounded-degree root closure

The perturbations remain admissible and converge coefficientwise. A uniform
positive evaluation bound excludes the zero polynomial. We then use the
library's algebraic bounded-degree closure theorem for closed root regions.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.TuranHurwitz

/-- A small positive perturbation satisfying the admissibility product inequality. -/
@[expose] noncomputable def boundaryEpsilon (c : Parameters) (k : ℕ) : ℝ :=
  (c.a₁ * c.b₂ / (c.a₁ + c.a₂ + 1)) / ((k : ℝ) + 1)

/-- Every chosen perturbation is positive and bounded by its initial value. -/
theorem boundaryEpsilon_pos_and_le {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb₂ : 0 < c.b₂) (k : ℕ) :
    0 < boundaryEpsilon c k ∧
      boundaryEpsilon c k ≤ c.a₁ * c.b₂ / (c.a₁ + c.a₂ + 1) := by
  have hden : 0 < c.a₁ + c.a₂ + 1 := by linarith [hc.a₂_nonneg]
  have hdelta : 0 < c.a₁ * c.b₂ / (c.a₁ + c.a₂ + 1) := div_pos (mul_pos ha hb₂) hden
  refine ⟨div_pos hdelta (by positivity), ?_⟩
  exact div_le_self hdelta.le (by linarith [Nat.cast_nonneg (α := ℝ) k])

/-- Every member of the chosen perturbation sequence is admissible. -/
theorem admissible_perturb_boundaryEpsilon {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb₂ : 0 < c.b₂) (ht : c.tau = 0) (k : ℕ) :
    (perturbB₁ c (boundaryEpsilon c k)).Admissible := by
  obtain ⟨hpos, hle⟩ := boundaryEpsilon_pos_and_le hc ha hb₂ k
  let delta := c.a₁ * c.b₂ / (c.a₁ + c.a₂ + 1)
  have hden : 0 < c.a₁ + c.a₂ + 1 := by linarith [hc.a₂_nonneg]
  have hdelta : 0 < delta := div_pos (mul_pos ha hb₂) hden
  have hproduct : delta * (c.a₁ + c.a₂ + 1) = c.a₁ * c.b₂ :=
    div_mul_cancel₀ _ hden.ne'
  have hcross : c.a₂ * boundaryEpsilon c k ≤ c.a₁ * (boundaryEpsilon c k + c.b₂) := by
    have hmul := mul_le_mul_of_nonneg_left hle hc.a₂_nonneg
    have hapos := mul_pos ha hpos
    have hadelta := mul_pos ha hdelta
    change c.a₂ * boundaryEpsilon c k ≤ c.a₂ * delta at hmul
    nlinarith
  refine ⟨hc.a₁_nonneg, hc.a₂_nonneg, hpos.le, hc.b₂_nonneg, hc.lam_nonneg,
    hc.tau_nonneg, hcross, ?_, ?_⟩
  · simpa only [perturbB₁, ht, zero_mul, add_zero] using add_pos hpos hb₂
  · exact add_pos ha hpos

/-- The perturbation sequence tends to zero. -/
theorem tendsto_boundaryEpsilon (c : Parameters) :
    Tendsto (boundaryEpsilon c) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (c.a₁ * c.b₂ / (c.a₁ + c.a₂ + 1))
  change Tendsto (fun k : ℕ => (c.a₁ * c.b₂ / (c.a₁ + c.a₂ + 1)) /
    ((k : ℝ) + 1)) atTop (𝓝 0)
  simpa only [mul_zero, div_eq_mul_inv, one_mul] using h

/-- The zero perturbation recovers an original tuple with `b₁ = 0`. -/
theorem perturbB₁_zero {c : Parameters} (hb : c.b₁ = 0) : perturbB₁ c 0 = c := by
  cases c
  simp_all [perturbB₁]

/-- Every complex Turán evaluation converges along the chosen perturbations. -/
theorem tendsto_aeval_turan_boundary {c : Parameters} (hb : c.b₁ = 0) (ht : c.tau = 0)
    (m n : ℕ) (z : ℂ) :
    Tendsto (fun k => Polynomial.aeval z
      (turan m n (family (perturbB₁ c (boundaryEpsilon c k))))) atTop
        (𝓝 (Polynomial.aeval z (turan m n (family c)))) := by
  have h := (continuous_aeval_turan_perturb c ht m n z).continuousAt.tendsto.comp
    (tendsto_boundaryEpsilon c)
  simpa only [perturbB₁_zero hb, Function.comp_def] using h

/-- The exponential-boundary Turán polynomial has a strictly positive norm at `1 - lambda`. -/
theorem family_turan_boundary_norm_lower {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb : c.b₁ = 0) (ht : c.tau = 0) (hb₂ : 0 < c.b₂) (m n : ℕ) :
    c.a₁ ^ n * c.b₂ ^ (2 * m + n) / ((2 * n).factorial : ℝ) ≤
      ‖Polynomial.aeval (1 - (c.lam : ℂ)) (turan m n (family c))‖ := by
  apply ge_of_tendsto (tendsto_aeval_turan_boundary hb ht m n (1 - (c.lam : ℂ))).norm
  apply Eventually.of_forall
  intro k
  have hk := admissible_perturb_boundaryEpsilon hc ha hb₂ ht k
  exact family_turan_norm_lower_of_tau_eq_zero hk ha
    (boundaryEpsilon_pos_and_le hc ha hb₂ k).1 ht hb₂ m n

/-- The exponential-boundary Turán polynomial is nonzero. -/
theorem family_turan_boundary_ne_zero {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb : c.b₁ = 0) (ht : c.tau = 0) (hb₂ : 0 < c.b₂) (m n : ℕ) :
    turan m n (family c) ≠ 0 := by
  have hlower := family_turan_boundary_norm_lower hc ha hb ht hb₂ m n
  have hpos : 0 < c.a₁ ^ n * c.b₂ ^ (2 * m + n) / ((2 * n).factorial : ℝ) :=
    div_pos (mul_pos (pow_pos ha _) (pow_pos hb₂ _)) (by exact_mod_cast Nat.factorial_pos _)
  intro heq
  rw [heq, map_zero, norm_zero] at hlower
  linarith

/-- Theorem 1.1(i) on the exponential boundary, by bounded-degree closed-root limits. -/
theorem family_turan_stable_boundary {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb : c.b₁ = 0) (ht : c.tau = 0) (hb₂ : 0 < c.b₂) (m n : ℕ) :
    turan m n (family c) ≠ 0 ∧
      ∀ z : ℂ, -c.lam < z.re → Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  have hne := family_turan_boundary_ne_zero hc ha hb ht hb₂ m n
  refine ⟨hne, ?_⟩
  let P := fun k => (turan m n (family (perturbB₁ c (boundaryEpsilon c k)))).map
    (algebraMap ℝ ℂ)
  let P₀ := (turan m n (family c)).map (algebraMap ℝ ℂ)
  have hdeg : ∀ k, (P k).natDegree ≤ 2 * m + 2 * n := by
    intro k
    dsimp [P]
    rw [natDegree_map]
    exact natDegree_turan_perturb_le c ht _ m n
  have hroots : ∀ k, ∀ r ∈ (P k).roots, r.re ≤ -c.lam := by
    intro k r hr
    by_contra hre
    have hk := admissible_perturb_boundaryEpsilon hc ha hb₂ ht k
    have hzero := (Polynomial.mem_roots'.mp hr).2
    dsimp [P] at hzero
    rw [IsRoot.def, Polynomial.eval_map_algebraMap] at hzero
    exact aeval_family_turan_ne_zero_of_tau_eq_zero hk ha
      (boundaryEpsilon_pos_and_le hc ha hb₂ k).1 ht m n r (lt_of_not_ge hre) hzero
  have hlim : ∀ z : ℂ, Tendsto (fun k => (P k).eval z) atTop (𝓝 (P₀.eval z)) := by
    intro z
    simpa only [P, P₀, Polynomial.eval_map_algebraMap] using
      tendsto_aeval_turan_boundary hb ht m n z
  have hclosed : IsClosed {z : ℂ | z.re ≤ -c.lam} :=
    isClosed_le Complex.continuous_re continuous_const
  have hrootlimit := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
    hclosed hdeg hroots hlim
  intro z hz heval
  have hzroot : z ∈ P₀.roots := by
    apply (Polynomial.mem_roots (Polynomial.map_ne_zero hne)).mpr
    rw [IsRoot.def, Polynomial.eval_map_algebraMap]
    exact heval
  exact (not_le_of_gt hz) (hrootlimit z hzroot)

end RealRooted.TuranHurwitz
