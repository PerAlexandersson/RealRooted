module

public import RealRooted.Mesh.DiscreteMultiplierSequence
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
import RealRooted.Mesh.Limit

/-!
# Laguerre--Pólya functions give discrete multiplier sequences

Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in finite difference setting*,
Proc. AMS 144 (2016), Corollary 2: if `f` is a Type-I Laguerre--Pólya function (the class `LP⁺` of
locally uniform limits of Pólya-frequency polynomials), then `i ↦ f(i)` is a discrete multiplier
sequence.

The polynomial case is `isDiscreteMultiplierSequence_eval`.  For a limit, the diagonal operators
of the approximating polynomials converge coefficientwise on every fixed polynomial, and the mesh
class is closed under such limits (`Polynomial.MeshGE.of_tendsto_coeff`,
`HasOnlyNonnegRoots.of_tendsto_coeff`).  See RealRooted issue #2070.
-/

public section

open Polynomial Filter Topology Module

noncomputable section

namespace RealRooted

/-- A diagonal operator on the falling factorials, applied to a polynomial of degree at most `N`,
is the corresponding finite combination of falling factorials. -/
private theorem apply_eq_sum_of_natDegree_le {S : ℝ[X] →ₗ[ℝ] ℝ[X]} {b : ℕ → ℝ}
    (hS : ∀ i, S (descPochhammer ℝ i) = b i • descPochhammer ℝ i) {p : ℝ[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) :
    S p = ∑ j ∈ Finset.range (N + 1),
      (b j * (descPochhammerBasis ℝ).repr p j) • descPochhammer ℝ j := by
  have e : ∀ k, descPochhammerBasis ℝ k = descPochhammer ℝ k := fun k =>
    descPochhammerBasis_apply k
  have hsum : ∑ j ∈ Finset.range (N + 1),
      (b j * (descPochhammerBasis ℝ).repr p j) • descPochhammer ℝ j =
      ∑ j ∈ Finset.range (N + 1),
        (b j * (descPochhammerBasis ℝ).repr p j) • descPochhammerBasis ℝ j :=
    Finset.sum_congr rfl fun j _ => by rw [e]
  rw [hsum]
  apply (descPochhammerBasis ℝ).repr.injective
  ext k
  rw [descPochhammerBasis_repr_apply_eq_mul_repr hS, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases hk : k ≤ N
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 (by lia))]
    · simp
    · intro j _ hjk
      simp [hjk]
  · rw [Finset.sum_eq_zero, natDegree_le_iff_repr_descPochhammerBasis.mp hp k (by lia), mul_zero]
    intro j hj
    have : j ≠ k := by
      have := Finset.mem_range.1 hj
      lia
    simp [this]

/-- BKS 2016, Corollary 2: if `f` is a Type-I Laguerre--Pólya function, then `i ↦ Re f(i)` is a
discrete multiplier sequence. -/
theorem isDiscreteMultiplierSequence_of_isLaguerrePolyaTypeI {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) : IsDiscreteMultiplierSequence fun i : ℕ => (f i).re := by
  obtain ⟨φ, hφ, hlim⟩ := hf
  intro T hT p hp hpnn
  set N := p.natDegree with hN
  choose Tk hTk using fun k => exists_linearMap_descPochhammer (fun i : ℕ => (φ k).eval (i : ℝ))
  have hclass : ∀ k, (Tk k p).MeshGE 1 ∧ HasOnlyNonnegRoots (Tk k p) := by
    intro k
    by_cases h0 : φ k = 0
    · have : Tk k p = 0 := by
        rw [apply_eq_sum_of_natDegree_le (hTk k) (le_refl N)]
        simp [h0]
      rw [this]
      exact ⟨Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) zero_le_one, Or.inl rfl⟩
    · have hpf := hφ k
      exact isDiscreteMultiplierSequence_eval h0 (hpf.2.1.resolve_left h0) hpf.2.2 _ (hTk k) p
        hp hpnn
  have hdeg : ∀ k, (Tk k p).natDegree ≤ N := by
    intro k
    rw [apply_eq_sum_of_natDegree_le (hTk k) (le_refl N)]
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_smul_le _ _).trans ?_
    rw [descPochhammer_natDegree]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hval : ∀ j : ℕ, Tendsto (fun k => (φ k).eval (j : ℝ)) atTop (𝓝 (f j).re) := by
    intro j
    have h1 := (hlim.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ (j : ℂ))
    have h2 : ∀ k, (((φ k).map Complex.ofRealHom).eval (j : ℂ)) = (((φ k).eval (j : ℝ) : ℝ) : ℂ)
      := fun k => by
      simp
    simp only [h2] at h1
    have h3 := (Complex.continuous_re.tendsto _).comp h1
    simpa [Function.comp_def] using h3
  have hcoeff : ∀ i, Tendsto (fun k => (Tk k p).coeff i) atTop (𝓝 ((T p).coeff i)) := by
    intro i
    rw [apply_eq_sum_of_natDegree_le hT (le_refl N)]
    simp only [apply_eq_sum_of_natDegree_le (hTk _) (le_refl N), finsetSum_coeff, coeff_smul,
      smul_eq_mul]
    refine tendsto_finsetSum _ fun j _ => ?_
    exact ((hval j).mul_const _).mul_const _
  exact ⟨Polynomial.MeshGE.of_tendsto_coeff one_pos (fun k => (hclass k).1) hdeg hcoeff,
    HasOnlyNonnegRoots.of_tendsto_coeff (fun k => (hclass k).2) hdeg hcoeff⟩

end RealRooted

end
