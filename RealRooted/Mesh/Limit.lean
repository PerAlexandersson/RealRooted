module

public import RealRooted.Mesh.Basic
public import RealRooted.NarayanaTransformation.RootGeometry
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.Mesh.FiniteDifference
import RealRooted.PFPolynomial.Closure

/-!
# Coefficientwise limits of polynomials with a mesh bound

A coefficientwise limit of polynomials of uniformly bounded degree, each with mesh at least `α > 0`
(respectively with only nonnegative roots), again has mesh at least `α` (respectively only
nonnegative roots).  The zero limit is allowed.  The proof is Hurwitz's theorem applied to the
stable pencils `q_k(z - α) + w q_k(z)` that characterize the mesh bound
(`Polynomial.MeshGE.iff_eq_zero_or_stablePencil`).  See RealRooted issue #2070.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

private theorem natDegree_le_of_tendsto_coeff {q : ℕ → ℝ[X]} {q₀ : ℝ[X]} {N : ℕ}
    (hdeg : ∀ k, (q k).natDegree ≤ N)
    (hcoeff : ∀ i, Tendsto (fun k => (q k).coeff i) atTop (𝓝 (q₀.coeff i))) :
    q₀.natDegree ≤ N := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  have h0 : Tendsto (fun k => (q k).coeff i) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun k => ?_
    exact (coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg k) hi)).symm
  exact tendsto_nhds_unique (hcoeff i) h0

private theorem tendsto_eval_complexify_of_tendsto_coeff {q : ℕ → ℝ[X]} {q₀ : ℝ[X]} {N : ℕ}
    (hdeg : ∀ k, (q k).natDegree ≤ N)
    (hcoeff : ∀ i, Tendsto (fun k => (q k).coeff i) atTop (𝓝 (q₀.coeff i))) (z : ℂ) :
    Tendsto (fun k => (complexify (q k)).eval z) atTop (𝓝 ((complexify q₀).eval z)) := by
  refine Polynomial.tendsto_eval_of_coeff_tendsto_of_natDegree_le
    (p := fun k => complexify (q k)) (N := N)
    (fun k => natDegree_map_le.trans (hdeg k))
    (natDegree_map_le.trans (natDegree_le_of_tendsto_coeff hdeg hcoeff)) (fun i => ?_) z
  simp only [complexify, coeff_map, Complex.ofRealHom_eq_coe]
  exact (Complex.continuous_ofReal.tendsto _).comp (hcoeff i)

/-- A coefficientwise limit of polynomials of uniformly bounded degree with mesh at least `α > 0`
has mesh at least `α`. -/
theorem _root_.Polynomial.MeshGE.of_tendsto_coeff {q : ℕ → ℝ[X]} {q₀ : ℝ[X]} {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hmesh : ∀ k, (q k).MeshGE α) (hdeg : ∀ k, (q k).natDegree ≤ N)
    (hcoeff : ∀ i, Tendsto (fun k => (q k).coeff i) atTop (𝓝 (q₀.coeff i))) :
    q₀.MeshGE α := by
  by_cases hq₀ : q₀ = 0
  · subst hq₀
    exact Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) hα.le
  obtain ⟨i₀, hi₀⟩ : ∃ i, q₀.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hq₀ (Polynomial.ext h)
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((hcoeff i₀).eventually (isOpen_ne.mem_nhds hi₀))
  have hne : ∀ k, q (k + K) ≠ 0 := fun k h => by
    have := hK (k + K) (by lia)
    rw [h, coeff_zero] at this
    exact this rfl
  have hshift : ∀ i, Tendsto (fun k => (q (k + K)).coeff i) atTop (𝓝 (q₀.coeff i)) :=
    fun i => (hcoeff i).comp (tendsto_add_atTop_nat K)
  have hdeg' : ∀ k, (q (k + K)).natDegree ≤ N := fun k => hdeg _
  have hev := tendsto_eval_complexify_of_tendsto_coeff hdeg' hshift
  have hcomp (p : ℝ[X]) (z : ℂ) : (complexify (p.comp (X - C α))).eval z =
      (complexify p).eval (z - (α : ℂ)) := by
    simp [complexify, Polynomial.map_comp, eval_comp]
  have hlim := IsUpperHalfPlaneStablePencil.of_tendsto_eval_of_natDegree_le
    (f := fun k => (q (k + K)).comp (X - C α)) (g := fun k => q (k + K))
    (f₀ := q₀.comp (X - C α)) (g₀ := q₀) (N := N)
    (fun k => ((Polynomial.MeshGE.iff_eq_zero_or_stablePencil hα).1 (hmesh _)).resolve_left
      (hne k))
    (fun k => natDegree_comp_le.trans (by simpa using hdeg' k)) hdeg'
    (fun z => by simpa only [hcomp] using hev (z - (α : ℂ))) hev hq₀
  exact (Polynomial.MeshGE.iff_eq_zero_or_stablePencil hα).2 (Or.inr hlim)

/-- A coefficientwise limit of polynomials of uniformly bounded degree with only nonnegative roots
has only nonnegative roots. -/
theorem HasOnlyNonnegRoots.of_tendsto_coeff {q : ℕ → ℝ[X]} {q₀ : ℝ[X]} {N : ℕ}
    (hnn : ∀ k, HasOnlyNonnegRoots (q k)) (hdeg : ∀ k, (q k).natDegree ≤ N)
    (hcoeff : ∀ i, Tendsto (fun k => (q k).coeff i) atTop (𝓝 (q₀.coeff i))) :
    HasOnlyNonnegRoots q₀ := by
  have hev := tendsto_eval_complexify_of_tendsto_coeff hdeg hcoeff
  rcases Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le (p := q) (p₀ := q₀)
    hdeg (fun k => (hnn k).imp_right And.left) hev with h | h
  · exact Or.inl h
  · exact HasOnlyNonnegRoots.of_tendsto_eval_of_natDegree_le hnn hdeg hev h

end RealRooted

end
