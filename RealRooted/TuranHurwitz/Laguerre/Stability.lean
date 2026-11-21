module

import RealRooted.TuranHurwitz.Laguerre.ApproximantLimit
public import RealRooted.TuranHurwitz.Laguerre.LeadingCoefficient
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import Mathlib.Tactic.Linarith

/-!
# Shi's Theorem 1.1(ii)

The finite Laguerre approximants have a common degree bound. Pointwise
evaluation convergence and closed-root preservation give the excluded
half-plane. The exact positive top coefficient excludes the zero limit.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.TuranHurwitz

/-- The complete all-index nonzero and half-plane conclusion of Theorem 1.1(ii). -/
theorem laguerreFamily_turan_stable {c : LaguerreParameters} (hc : c.Admissible) (m n : ℕ) :
    turan m n (laguerreFamily c) ≠ 0 ∧
      ∀ z : ℂ, -c.lam < z.re → Polynomial.aeval z (turan m n (laguerreFamily c)) ≠ 0 := by
  have hne := turan_laguerreFamily_ne_zero hc m n
  refine ⟨hne, ?_⟩
  let Q := fun k =>
    (turan m n (laguerreApproxFamily c (k + (m + n + 1)))).map (algebraMap ℝ ℂ)
  let Q₀ := (turan m n (laguerreFamily c)).map (algebraMap ℝ ℂ)
  have hdeg : ∀ k, (Q k).natDegree ≤ 2 * m + 2 * n := by
    intro k
    dsimp [Q]
    rw [natDegree_map]
    exact natDegree_turan_laguerreApproxFamily_le c _ m n
  have hroots : ∀ k, ∀ r ∈ (Q k).roots, r.re ≤ -c.lam := by
    intro k r hr
    by_contra hre
    have hzero := (Polynomial.mem_roots'.mp hr).2
    dsimp [Q] at hzero
    rw [IsRoot.def, Polynomial.eval_map_algebraMap] at hzero
    exact aeval_turan_laguerreApproxFamily_ne_zero hc (by lia) m n (by lia)
      (lt_of_not_ge hre) hzero
  have hlim : ∀ z : ℂ, Tendsto (fun k => (Q k).eval z) atTop (𝓝 (Q₀.eval z)) := by
    intro z
    simpa only [Q, Q₀, Polynomial.eval_map_algebraMap, Function.comp_def] using
      (tendsto_aeval_turan_laguerreApproxFamily hc m n z).comp
        (tendsto_add_atTop_nat (m + n + 1))
  have hclosed : IsClosed {z : ℂ | z.re ≤ -c.lam} :=
    isClosed_le Complex.continuous_re continuous_const
  have hrootlimit := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
    hclosed hdeg hroots hlim
  intro z hz heval
  have hzroot : z ∈ Q₀.roots := by
    apply (Polynomial.mem_roots (Polynomial.map_ne_zero hne)).mpr
    rw [IsRoot.def, Polynomial.eval_map_algebraMap]
    exact heval
  exact (not_le_of_gt hz) (hrootlimit z hzroot)

/-- Every admissible part (ii) Turán polynomial excludes the stated open half-plane. -/
theorem aeval_laguerreFamily_turan_ne_zero {c : LaguerreParameters} (hc : c.Admissible)
    (m n : ℕ) (z : ℂ) (hz : -c.lam < z.re) :
    Polynomial.aeval z (turan m n (laguerreFamily c)) ≠ 0 :=
  (laguerreFamily_turan_stable hc m n).2 z hz

end RealRooted.TuranHurwitz
