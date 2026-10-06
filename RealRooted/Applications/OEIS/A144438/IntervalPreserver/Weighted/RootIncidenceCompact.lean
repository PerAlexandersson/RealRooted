import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ParameterContinuity
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Compact root incidence for the weighted parameter family

We package the uniform root bound needed by the global first-contact argument.
The proof uses the Cauchy bound for monic polynomials whose coefficients vary
continuously over a compact parameter set.
-/

open Polynomial Set Topology

noncomputable section

namespace RealRooted.Applications.OEIS

private theorem isCompact_root_incidence_of_continuous_monic
    {T : Type*} [TopologicalSpace T] (K : Set T) (hK : IsCompact K)
    (p : T → ℝ[X]) {d : ℕ} (hd : d ≠ 0)
    (hmonic : ∀ t, (p t).Monic)
    (hdegree : ∀ t, (p t).natDegree = d)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i) :
    IsCompact {z : T × ℝ | z.1 ∈ K ∧ (p z.1).IsRoot z.2} := by
  have hB : ∀ i, ∃ C, ∀ t ∈ K, ‖(p t).coeff i‖ ≤ C := fun i =>
    hK.exists_bound_of_continuousOn (hcoeff i).continuousOn
  choose B hB using hB
  set M : ℝ := ∑ i ∈ Finset.range d, |B i| + 1
  have hcont : Continuous fun z : T × ℝ => (p z.1).eval z.2 := by
    have : (fun z : T × ℝ => (p z.1).eval z.2) =
        fun z => ∑ i ∈ Finset.range (d + 1), (p z.1).coeff i * z.2 ^ i := by
      funext z
      exact eval_eq_sum_range' (by rw [hdegree]; lia) _
    rw [this]
    exact continuous_finsetSum _ fun i _ =>
      ((hcoeff i).comp continuous_fst).mul (continuous_snd.pow i)
  convert (hK.prod (isCompact_closedBall (0 : ℝ) M)).inter_right
    (isClosed_eq hcont continuous_const) using 1
  · ext ⟨t, a⟩
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Metric.mem_closedBall,
      dist_zero_right, IsRoot.def]
    constructor
    · rintro ⟨ht, hroot⟩
      refine ⟨⟨ht, ?_⟩, hroot⟩
      have h1 := (IsRoot.def.mpr hroot).norm_lt_cauchyBound (hmonic t).ne_zero
      have h2 : ‖a‖ < (cauchyBound (p t) : ℝ) := by
        rw [← coe_nnnorm]
        exact_mod_cast h1
      refine h2.le.trans ?_
      simp only [cauchyBound, (hmonic t).leadingCoeff, nnnorm_one, div_one, hdegree,
        NNReal.coe_add, NNReal.coe_one, M]
      gcongr
      obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.range d)
        (Finset.nonempty_range_iff.mpr hd) fun i => ‖(p t).coeff i‖₊
      rw [heq, coe_nnnorm]
      exact (hB i t ht).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |B j|) (fun j _ => abs_nonneg _) hi))
    · rintro ⟨⟨ht, -⟩, hroot⟩
      exact ⟨ht, hroot⟩

/-- Over the full parameter cube, all roots of the weighted transformed
products form a compact incidence set. -/
theorem isCompact_weightedDecoParameterRootIncidence
    (w : ℝ) (n : ℕ) (hn : n ≠ 0) :
    IsCompact {z : (Fin n → ℝ) × ℝ |
      z.1 ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) ∧
        (weightedDecoParameterImage w Finset.univ z.1).IsRoot z.2} := by
  apply isCompact_root_incidence_of_continuous_monic
    (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1)
    (isCompact_univ_pi fun _ => isCompact_Icc)
    (fun a => weightedDecoParameterImage w Finset.univ a) hn
  · exact weightedDecoParameterImage_monic w Finset.univ
  · intro a
    simp
  · exact continuous_weightedDecoParameterImage_coeff w Finset.univ

end RealRooted.Applications.OEIS
