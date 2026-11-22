module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Examples
import TauCeti.Analysis.Complex.CanonicalProduct.Convergence

/-!
# Genus-one canonical products in the Laguerre--Pólya class

Real elementary factors and their natural powers belong to the class. Locally
uniform products preserve membership, so square-summable real slopes give
Laguerre--Pólya canonical products without an entire growth hypothesis.
-/

public section

open Complex Polynomial Filter Metric Topology

namespace RealRooted

/-- A real polynomial that splits over the reals belongs to the Laguerre--Pólya class. -/
theorem isLaguerrePolya_eval_map {p : ℝ[X]} (hp : p.Splits) :
    IsLaguerrePolya (fun z => (p.map ofRealHom).eval z) := by
  apply IsLaguerrePolya.of_forall_approx
  intro R ε hε
  exact ⟨p, Or.inr hp, fun _ _ => by simpa using hε⟩

/-- The constant function one belongs to the Laguerre--Pólya class. -/
theorem IsLaguerrePolya.one : IsLaguerrePolya (fun _ : ℂ => 1) := by
  simpa using isLaguerrePolya_eval_map (p := 1) Splits.one

/-- Natural powers preserve the Laguerre--Pólya class. -/
theorem IsLaguerrePolya.pow {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (n : ℕ) :
    IsLaguerrePolya (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using IsLaguerrePolya.one
  | succ n ih => simpa only [pow_succ, Pi.mul_def] using ih.mul hf

/-- Finite products preserve the Laguerre--Pólya class. -/
theorem IsLaguerrePolya.finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsLaguerrePolya (f i)) :
    IsLaguerrePolya (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsLaguerrePolya.one
  | @insert i s hi ih =>
      simpa [Finset.prod_insert hi, Pi.mul_def] using (hf i (by simp)).mul
        (ih fun j hj => hf j (by simp [hj]))

/-- A locally uniformly convergent product of Laguerre--Pólya functions belongs
to the class. The index type need not be countable. -/
theorem IsLaguerrePolya.of_hasProdLocallyUniformly {ι : Type*} {g : ι → ℂ → ℂ}
    {f : ℂ → ℂ} (hg : ∀ i, IsLaguerrePolya (g i))
    (hprod : HasProdLocallyUniformlyOn g f Set.univ) : IsLaguerrePolya f := by
  classical
  apply IsLaguerrePolya.of_forall_approx
  intro R ε hε
  have hlim := tendstoLocallyUniformlyOn_univ.mp
    (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod)
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp hlim _
    (isCompact_closedBall (0 : ℂ) R)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨s, hs⟩ := (hU (ε / 2) (half_pos hε)).exists
  obtain ⟨p, hp, hpd⟩ := (IsLaguerrePolya.finsetProd s g (fun i _ => hg i)).exists_approx
    R (half_pos hε)
  refine ⟨p, hp, fun z hz => ?_⟩
  calc
    dist (f z) ((p.map ofRealHom).eval z) ≤ dist (f z) (∏ i ∈ s, g i z) +
        dist (∏ i ∈ s, g i z) ((p.map ofRealHom).eval z) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hs z (mem_closedBall_zero_iff.mpr hz)) (hpd z hz)
    _ = ε := add_halves ε

/-- The real genus-one elementary factor belongs to the Laguerre--Pólya class. -/
theorem isLaguerrePolya_weierstrassFactor_one (a : ℝ) :
    IsLaguerrePolya (fun z => weierstrassFactor 1 ((a : ℂ) * z)) := by
  have hlin : IsLaguerrePolya (fun z : ℂ => 1 - (a : ℂ) * z) := by
    have hp : (1 - C a * X : ℝ[X]).Splits :=
      Splits.of_natDegree_le_one ((natDegree_sub_le _ _).trans
        (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp))))
    simpa using isLaguerrePolya_eval_map hp
  simpa only [weierstrassFactor_one_left, Pi.mul_def, ofReal_zero, add_zero] using
    hlin.mul (isLaguerrePolya_exp.comp_affine_real a 0)

/-- Square-summable real genus-one factors, with their natural multiplicities,
form a Laguerre--Pólya function. This includes finite and empty products. -/
theorem isLaguerrePolya_tprod_weierstrassFactor_one_pow {ι : Type*}
    (a : ι → ℝ) (m : ι → ℕ) (hs : Summable (fun i => (m i : ℝ) * a i ^ 2)) :
    IsLaguerrePolya (fun z => ∏' i, weierstrassFactor 1 ((a i : ℂ) * z) ^ m i) := by
  have hsum : Summable (fun i => (m i : ℝ) * ‖(a i : ℂ)‖ ^ 2) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hs
  exact IsLaguerrePolya.of_hasProdLocallyUniformly
    (fun i => (isLaguerrePolya_weierstrassFactor_one (a i)).pow (m i))
    (hasProdLocallyUniformlyOn_weierstrassFactor_one_pow _ _ hsum)

end RealRooted
