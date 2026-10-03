import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.FirstContactCompact
import RealRooted.Mathlib.Analysis.Normed.Field.Approximation

/-!
# Local topology for the weighted first-contact argument

A strictly negative companion-residue sign persists under small parameter
perturbations inside the parameter cube.  The nearby root is supplied by
coefficientwise root continuity for monic split polynomials.
-/

open Filter Polynomial Set Topology

noncomputable section

namespace RealRooted.Applications.OEIS

def weightedDecoParameterCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1

def weightedDecoResidueSign (w : ℝ) (n : ℕ)
    (a : Fin n → ℝ) (r : ℝ) : ℝ :=
  (weightedDecoParameterCompanion w Finset.univ a).eval r *
    (weightedDecoParameterImage w Finset.univ a).derivative.eval r

theorem continuous_weightedDecoResidueSign (w : ℝ) (n : ℕ) :
    Continuous fun z : (Fin n → ℝ) × ℝ =>
      weightedDecoResidueSign w n z.1 z.2 := by
  exact (continuous_weightedDecoParameterCompanion_eval_prod w Finset.univ).mul
    (continuous_weightedDecoParameterImage_derivative_eval_prod w Finset.univ)

/-- A strictly negative residue sign at a root persists at some nearby root
for every sufficiently close parameter vector in the cube. -/
theorem eventually_exists_weightedDeco_root_residueSign_neg
    {w : ℝ} {n : ℕ} (hn : n ≠ 0) {a : Fin n → ℝ} {r : ℝ}
    (hr : (weightedDecoParameterImage w Finset.univ a).IsRoot r)
    (hneg : weightedDecoResidueSign w n a r < 0)
    (hsplits : ∀ b ∈ weightedDecoParameterCube n,
      (weightedDecoParameterImage w Finset.univ b).Splits) :
    ∀ᶠ b in nhdsWithin a (weightedDecoParameterCube n),
      ∃ s, (weightedDecoParameterImage w Finset.univ b).IsRoot s ∧
        weightedDecoResidueSign w n b s < 0 := by
  let p : (Fin n → ℝ) → ℝ[X] := fun b =>
    weightedDecoParameterImage w Finset.univ b
  have hsign : ∀ᶠ z in nhds (a, r), weightedDecoResidueSign w n z.1 z.2 < 0 :=
    (continuous_weightedDecoResidueSign w n).continuousAt.eventually_lt
      continuousAt_const hneg
  rw [nhds_prod_eq] at hsign
  obtain ⟨U, hU, η, hη, hUV⟩ := Metric.eventually_prod_nhds_iff.mp hsign
  obtain ⟨δ, hδ, hpersist⟩ :=
    Polynomial.exists_coeff_radius_root_near
      (weightedDecoParameterImage_monic w Finset.univ a)
      (by simpa only [weightedDecoParameterImage_natDegree,
        Finset.card_univ, Fintype.card_fin] using hn) hr hη
  have hclose : ∀ᶠ b in nhds a,
      ∀ i : ℕ, ‖(p b).coeff i - (p a).coeff i‖ < δ :=
    Polynomial.eventually_forall_norm_coeff_sub_lt p (d := n)
      (fun b => by simp only [p, weightedDecoParameterImage_natDegree,
        Finset.card_univ, Fintype.card_fin])
      (fun i => continuous_weightedDecoParameterImage_coeff w Finset.univ i)
      a hδ
  have hU' : ∀ᶠ b in nhdsWithin a (weightedDecoParameterCube n), U b :=
    hU.filter_mono inf_le_left
  have hclose' : ∀ᶠ b in nhdsWithin a (weightedDecoParameterCube n),
      ∀ i : ℕ, ‖(p b).coeff i - (p a).coeff i‖ < δ :=
    hclose.filter_mono inf_le_left
  filter_upwards [hU', hclose', self_mem_nhdsWithin] with b hbU hbclose hbCube
  obtain ⟨s, hsroot, hrs⟩ := hpersist (p b)
    (weightedDecoParameterImage_monic w Finset.univ b)
    (by simp only [p, weightedDecoParameterImage_natDegree, Finset.card_univ,
      Fintype.card_fin])
    hbclose (hsplits b hbCube)
  refine ⟨s, hsroot, hUV hbU ?_⟩
  simpa only [dist_comm, dist_eq_norm] using hrs

end RealRooted.Applications.OEIS
