module

public import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic
public import RealRooted.MultivariateStability
public import Mathlib.Algebra.Order.Antidiag.Finsupp

/-!
# Closed limits of multivariate stable polynomials

This file isolates the bounded-degree closure step needed when a sequence of
stability-preserving operators converges coefficientwise.  The proof restricts
to a complex affine line and applies the existing closed-root limit theorem.
-/

public noncomputable section

open Filter Polynomial Topology

namespace RealRooted

/-- Uniform total-degree bounds turn coefficientwise convergence into
pointwise convergence of multivariate polynomial evaluations. -/
theorem MvPolynomial.tendsto_eval_of_coeff_tendsto_of_totalDegree_le
    {σ : Type*} [Finite σ] {P : ℕ → MvPolynomial σ ℂ}
    {P₀ : MvPolynomial σ ℂ} {N : ℕ}
    (hdeg : ∀ k, (P k).totalDegree ≤ N) (hdeg₀ : P₀.totalDegree ≤ N)
    (hcoeff : ∀ m : σ →₀ ℕ,
      Tendsto (fun k => (P k).coeff m) atTop (𝓝 (P₀.coeff m)))
    (z : σ → ℂ) :
    Tendsto (fun k => MvPolynomial.eval z (P k)) atTop
      (𝓝 (MvPolynomial.eval z P₀)) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let S : Finset (σ →₀ ℕ) :=
    (Finset.range (N + 1)).biUnion fun d =>
      Finset.finsuppAntidiag Finset.univ d
  have support_subset (Q : MvPolynomial σ ℂ) (hQ : Q.totalDegree ≤ N) :
      Q.support ⊆ S := by
    intro m hm
    let d := m.sum fun _ e => e
    have hd : d ≤ N := (MvPolynomial.le_totalDegree hm).trans hQ
    apply Finset.mem_biUnion.mpr
    refine ⟨d, Finset.mem_range.mpr (by lia), ?_⟩
    simp [d, Finsupp.sum_fintype]
  have eval_eq_sum (Q : MvPolynomial σ ℂ) (hQ : Q.totalDegree ≤ N) :
      MvPolynomial.eval z Q =
        ∑ m ∈ S, Q.coeff m * ∏ i, z i ^ m i := by
    rw [MvPolynomial.eval_eq']
    apply Finset.sum_subset (support_subset Q hQ)
    intro m hmS hmQ
    simp [MvPolynomial.notMem_support_iff.mp hmQ]
  have hsum : Tendsto
      (fun k => ∑ m ∈ S, (P k).coeff m * ∏ i, z i ^ m i)
      atTop
      (𝓝 (∑ m ∈ S, P₀.coeff m * ∏ i, z i ^ m i)) := by
    refine tendsto_finsetSum _ fun m _ => ?_
    exact (hcoeff m).mul_const (∏ i, z i ^ m i)
  convert hsum using 1
  · funext k
    exact eval_eq_sum (P k) (hdeg k)
  · exact congrArg 𝓝 (eval_eq_sum P₀ hdeg₀)

/-- A pointwise evaluation limit of uniformly bounded-degree stable
multivariate polynomials on finitely many variables is stable or zero. -/
theorem MvUpperHalfPlaneStableOrZero.of_tendsto_eval_of_totalDegree_le
    {σ : Type*} [Finite σ] {P : ℕ → MvPolynomial σ ℂ}
    {P₀ : MvPolynomial σ ℂ} {N : ℕ}
    (hstable : ∀ k, MvUpperHalfPlaneStable (P k))
    (hdeg : ∀ k, (P k).totalDegree ≤ N)
    (heval : ∀ z : σ → ℂ,
      Tendsto (fun k => MvPolynomial.eval z (P k)) atTop
        (𝓝 (MvPolynomial.eval z P₀))) :
    MvUpperHalfPlaneStableOrZero P₀ := by
  classical
  by_cases hP₀ : P₀ = 0
  · exact Or.inl hP₀
  right
  intro a ha hP₀a
  obtain ⟨b, hb, hP₀b⟩ := exists_upperHalfPlane_eval_ne_zero hP₀
  let v : σ → ℂ := fun i => b i - a i
  let A : ℂ[X] := MvPolynomial.affineLineRestriction a v P₀
  let p : ℕ → ℂ[X] := fun k =>
    MvPolynomial.affineLineRestriction a v (P k)
  let U : Set ℂ := {t | ∀ i, 0 < (a i + v i * t).im}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ i, {t : ℂ | 0 < (a i + v i * t).im} by
      ext t
      simp [U]]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (by fun_prop)
  have hzeroU : (0 : ℂ) ∈ U := by
    intro i
    simpa using ha i
  have hA0 : A.eval 0 = 0 := by
    simpa [A] using hP₀a
  have hA1 : A.eval 1 ≠ 0 := by
    simpa [A, v] using hP₀b
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hA1
    exact hA1 rfl
  have hpdeg (k : ℕ) : (p k).natDegree ≤ N :=
    (MvPolynomial.natDegree_affineLineRestriction_le a v (P k)).trans
      (hdeg k)
  have hproots (k : ℕ) (r : ℂ) (hr : r ∈ (p k).roots) : r ∈ Uᶜ := by
    intro hrU
    apply hstable k (fun i => a i + v i * r) hrU
    rw [← MvPolynomial.eval_affineLineRestriction]
    exact (Polynomial.mem_roots'.mp hr).2
  have hpeval (t : ℂ) :
      Tendsto (fun k => (p k).eval t) atTop (𝓝 (A.eval t)) := by
    simpa only [p, A, MvPolynomial.eval_affineLineRestriction] using
      heval (fun i => a i + v i * t)
  have hroot : (0 : ℂ) ∈ A.roots :=
    Polynomial.mem_roots'.mpr ⟨hA, hA0⟩
  have hclosed := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
    hUopen.isClosed_compl hpdeg hproots hpeval 0 hroot
  exact hclosed hzeroU

/-- Uniformly bounded-degree coefficientwise limits of stable multivariate
polynomials on finitely many variables are stable or zero. -/
theorem MvUpperHalfPlaneStableOrZero.of_coeff_tendsto_of_totalDegree_le
    {σ : Type*} [Finite σ] {P : ℕ → MvPolynomial σ ℂ}
    {P₀ : MvPolynomial σ ℂ} {N : ℕ}
    (hstable : ∀ k, MvUpperHalfPlaneStable (P k))
    (hdeg : ∀ k, (P k).totalDegree ≤ N) (hdeg₀ : P₀.totalDegree ≤ N)
    (hcoeff : ∀ m : σ →₀ ℕ,
      Tendsto (fun k => (P k).coeff m) atTop (𝓝 (P₀.coeff m))) :
    MvUpperHalfPlaneStableOrZero P₀ := by
  apply MvUpperHalfPlaneStableOrZero.of_tendsto_eval_of_totalDegree_le
    hstable hdeg
  exact MvPolynomial.tendsto_eval_of_coeff_tendsto_of_totalDegree_le
    hdeg hdeg₀ hcoeff

/-- Complexification preserves the total degree of a real multivariate
polynomial. -/
@[simp] theorem totalDegree_complexifyMv {σ : Type*}
    (P : MvPolynomial σ ℝ) :
    (complexifyMv P).totalDegree = P.totalDegree := by
  unfold complexifyMv MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective _ Complex.ofRealHom.injective]

/-- Uniformly bounded-degree coefficientwise limits of real-stable
multivariate polynomials on finitely many variables are real stable or zero. -/
theorem MvRealStableOrZero.of_coeff_tendsto_of_totalDegree_le
    {σ : Type*} [Finite σ] {P : ℕ → MvPolynomial σ ℝ}
    {P₀ : MvPolynomial σ ℝ} {N : ℕ}
    (hstable : ∀ k, MvRealStable (P k))
    (hdeg : ∀ k, (P k).totalDegree ≤ N) (hdeg₀ : P₀.totalDegree ≤ N)
    (hcoeff : ∀ m : σ →₀ ℕ,
      Tendsto (fun k => (P k).coeff m) atTop (𝓝 (P₀.coeff m))) :
    MvRealStableOrZero P₀ := by
  rw [mvRealStableOrZero_iff_complexifyMv]
  apply MvUpperHalfPlaneStableOrZero.of_coeff_tendsto_of_totalDegree_le
    hstable
  · intro k
    simpa using hdeg k
  · simpa using hdeg₀
  · intro m
    simp only [complexifyMv, MvPolynomial.coeff_map,
      Complex.ofRealHom_eq_coe]
    convert (Complex.continuous_ofReal.tendsto (P₀.coeff m)).comp
      (hcoeff m) using 1
    rfl

/-- A nonzero, uniformly bounded-degree coefficientwise limit of real-stable
multivariate polynomials is real stable. -/
theorem MvRealStable.of_coeff_tendsto_of_totalDegree_le
    {sigma : Type*} [Finite sigma] {P : ℕ → MvPolynomial sigma ℝ}
    {P₀ : MvPolynomial sigma ℝ} {N : ℕ}
    (hstable : ∀ k, MvRealStable (P k))
    (hdeg : ∀ k, (P k).totalDegree ≤ N) (hdeg₀ : P₀.totalDegree ≤ N)
    (hcoeff : ∀ m : sigma →₀ ℕ,
      Tendsto (fun k => (P k).coeff m) atTop (nhds (P₀.coeff m)))
    (hne : P₀ ≠ 0) :
    MvRealStable P₀ := by
  rcases MvRealStableOrZero.of_coeff_tendsto_of_totalDegree_le
      hstable hdeg hdeg₀ hcoeff with hzero | hstable₀
  · exact (hne hzero).elim
  · exact hstable₀

/-- A coefficientwise limit of stability-preserving linear operators is
stability preserving at a stable input, provided the limit operator is
injective and all outputs have a common total-degree bound. This is the
closure step used after a finite-dimensional Trotter product formula. -/
theorem MvRealStable.of_linearMap_coeff_tendsto_of_totalDegree_le
    {sigma : Type*} [Finite sigma] {P : MvPolynomial sigma ℝ} {N : ℕ}
    (T : MvPolynomial sigma ℝ →ₗ[ℝ] MvPolynomial sigma ℝ)
    (Tn : ℕ → MvPolynomial sigma ℝ →ₗ[ℝ] MvPolynomial sigma ℝ)
    (hP : MvRealStable P) (hstable : ∀ k, MvRealStable (Tn k P))
    (hdeg : ∀ k, (Tn k P).totalDegree ≤ N)
    (hdegT : (T P).totalDegree ≤ N)
    (hcoeff : ∀ m : sigma →₀ ℕ,
      Tendsto (fun k => (Tn k P).coeff m) atTop (nhds ((T P).coeff m)))
    (hinj : Function.Injective T) :
    MvRealStable (T P) := by
  apply MvRealStable.of_coeff_tendsto_of_totalDegree_le
    hstable hdeg hdegT hcoeff
  intro hzero
  apply hP.ne_zero
  apply hinj
  simpa using hzero

end RealRooted
