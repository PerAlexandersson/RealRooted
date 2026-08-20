import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import RealRooted.MultivariateStability

open Matrix MvPolynomial
open scoped ComplexOrder

noncomputable section

namespace RealRooted

/-!
# Determinantal stability

Borcea--Branden's determinantal criterion: for a Hermitian matrix `A` and
positive semidefinite matrices `B i`, the multivariate determinant

```text
P (z) = det (A + ∑ i, z i • B i)
```

is either stable, meaning nonvanishing whenever every coordinate lies in the
open upper half-plane, or identically zero.

Reference: J. Borcea and P. Branden, *Multivariate Polya--Schur classification
problems in the Weyl algebra*, Proposition 1.12 (arXiv:math/0606360); repeated
as Proposition 2.4 of *Applications of stable polynomials to mixed
determinants*, Duke Math. J. 143 (2008) (arXiv:math/0607755).

The printed proof perturbs the positive semidefinite data to positive definite
and then applies Hurwitz's theorem together with a Hermitian characteristic
polynomial.  The proof below is instead a direct kernel argument, which needs no
analysis at all: if some upper half-plane specialization is singular, a kernel
vector `v` of it satisfies `star v ⬝ᵥ M *ᵥ v = 0`, and taking imaginary parts
kills every `star v ⬝ᵥ B i *ᵥ v` because the Hermitian part contributes nothing
imaginary while the semidefinite parts contribute with strictly positive
weights `(z i).im`.  Semidefiniteness then upgrades this to `B i *ᵥ v = 0` and
hence `A *ᵥ v = 0`, so *every* specialization is singular.
-/

variable {m sigma : Type*} [Fintype m] [DecidableEq m] [Fintype sigma]

/-- The determinant of the affine matrix pencil `A + ∑ i, X i • B i`, as a
multivariate polynomial. -/
def detPencil (A : Matrix m m ℂ) (B : sigma → Matrix m m ℂ) : MvPolynomial sigma ℂ :=
  Matrix.det fun i j => C (A i j) + ∑ k : sigma, X k * C (B k i j)

/-- Evaluating the pencil determinant is the determinant of the evaluated
pencil. -/
theorem eval_detPencil (A : Matrix m m ℂ) (B : sigma → Matrix m m ℂ) (z : sigma → ℂ) :
    MvPolynomial.eval z (detPencil A B) = (A + ∑ k : sigma, z k • B k).det := by
  classical
  rw [detPencil, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, mul_comm]

omit [DecidableEq m] in
/-- The evaluated pencil applied to a vector, expanded. -/
private theorem pencil_mulVec (A : Matrix m m ℂ) (B : sigma → Matrix m m ℂ)
    (z : sigma → ℂ) (v : m → ℂ) :
    (A + ∑ k : sigma, z k • B k) *ᵥ v = A *ᵥ v + ∑ k : sigma, z k • (B k *ᵥ v) := by
  simp [Matrix.add_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec]

omit [DecidableEq m] in
/-- **The kernel step.**  If an upper half-plane specialization of the pencil
annihilates `v`, then `A` and every `B k` annihilate `v` separately. -/
theorem mulVec_eq_zero_of_pencil_mulVec_eq_zero
    {A : Matrix m m ℂ} {B : sigma → Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : ∀ k, (B k).PosSemidef)
    {z : sigma → ℂ} (hz : ∀ k, 0 < (z k).im) {v : m → ℂ}
    (hv : (A + ∑ k : sigma, z k • B k) *ᵥ v = 0) :
    A *ᵥ v = 0 ∧ ∀ k, B k *ᵥ v = 0 := by
  classical
  set q : sigma → ℂ := fun k => star v ⬝ᵥ (B k *ᵥ v) with hq
  -- each `q k` is a nonnegative real
  have hq_nonneg : ∀ k, 0 ≤ q k := fun k => (hB k).dotProduct_mulVec_nonneg v
  have hq_im : ∀ k, (q k).im = 0 := by
    intro k
    have := (Complex.le_def.mp (hq_nonneg k)).2
    simpa using this.symm
  have hq_re : ∀ k, 0 ≤ (q k).re := fun k => (Complex.le_def.mp (hq_nonneg k)).1
  -- pair the kernel relation with `star v`
  have hdot : star v ⬝ᵥ ((A + ∑ k : sigma, z k • B k) *ᵥ v) = 0 := by
    rw [hv, dotProduct_zero]
  rw [pencil_mulVec, dotProduct_add] at hdot
  have hsum : star v ⬝ᵥ (∑ k : sigma, z k • (B k *ᵥ v)) = ∑ k : sigma, z k * q k := by
    rw [dotProduct_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [dotProduct_smul]; rfl
  rw [hsum] at hdot
  -- imaginary parts: the Hermitian part contributes nothing
  have hAim : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    simpa using hA.im_star_dotProduct_mulVec_self v
  have himsum : ∑ k : sigma, (z k).im * (q k).re = 0 := by
    have h := congrArg Complex.im hdot
    simp only [Complex.add_im, Complex.zero_im, hAim, zero_add, Complex.im_sum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Complex.mul_im, hq_im k, mul_zero, zero_add]
  -- every summand is nonnegative, hence zero
  have hterm : ∀ k ∈ Finset.univ, (0 : ℝ) ≤ (z k).im * (q k).re := fun k _ =>
    mul_nonneg (hz k).le (hq_re k)
  have hzero : ∀ k ∈ Finset.univ, (z k).im * (q k).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm).mp himsum
  have hq_eq_zero : ∀ k, q k = 0 := by
    intro k
    have hk := hzero k (Finset.mem_univ k)
    have hre : (q k).re = 0 := by
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h (ne_of_gt (hz k))
      · exact h
    exact Complex.ext hre (hq_im k)
  -- semidefiniteness upgrades this to the kernel
  have hBv : ∀ k, B k *ᵥ v = 0 := fun k =>
    ((hB k).dotProduct_mulVec_zero_iff v).mp (hq_eq_zero k)
  refine ⟨?_, hBv⟩
  have : A *ᵥ v + ∑ k : sigma, z k • (B k *ᵥ v) = 0 := by
    rw [← pencil_mulVec]; exact hv
  simpa [hBv] using this

/-- **Borcea--Branden determinantal stability.**  For a Hermitian `A` and
positive semidefinite `B k`, the pencil determinant is stable or identically
zero. -/
theorem mvUpperHalfPlaneStableOrZero_detPencil
    (A : Matrix m m ℂ) (B : sigma → Matrix m m ℂ)
    (hA : A.IsHermitian) (hB : ∀ k, (B k).PosSemidef) :
    MvUpperHalfPlaneStableOrZero (detPencil A B) := by
  classical
  by_cases hP : detPencil A B = 0
  · exact Or.inl hP
  refine Or.inr ?_
  intro z hz hzero
  -- a kernel vector at `z`
  have hdet : (A + ∑ k : sigma, z k • B k).det = 0 := by
    rw [← eval_detPencil]; exact hzero
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨hAv, hBv⟩ :=
    mulVec_eq_zero_of_pencil_mulVec_eq_zero hA hB (fun k => hz k) hv
  -- then every specialization is singular, contradicting `detPencil ≠ 0`
  obtain ⟨w, _hw, hwne⟩ := exists_upperHalfPlane_eval_ne_zero hP
  refine hwne ?_
  rw [eval_detPencil]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
  rw [pencil_mulVec, hAv]
  simp [hBv]

end RealRooted
