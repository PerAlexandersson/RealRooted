module

public import RealRooted.Hadamard.RootIntervals
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# Schur--Szegő operations on polynomial sequences

Fixed-factor Schur--Szegő composition of a polynomial sequence is postcomposition of its
basis transform.  Termwise scalar multiplication is precomposition by a diagonal map.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

private theorem basisTransform_linearMap (L : ℝ[X] →ₗ[ℝ] ℝ[X])
    (P : ℕ → ℝ[X]) (p : ℝ[X]) :
    basisTransform (fun n => L (P n)) p = L (basisTransform P p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [basisTransform_add, hp, hq, LinearMap.map_add]
  | monomial n a =>
      simp only [basisTransform_monomial, linearMap_C_mul]

private theorem basisTransform_C_mul_X_pow (γ : ℕ → ℝ) (p : ℝ[X]) :
    basisTransform (fun n => C (γ n) * X ^ n) p = diagonalOperator γ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [basisTransform_add, diagonalOperator_add, hp, hq]
  | monomial n a =>
      rw [basisTransform_monomial, diagonalOperator_monomial]
      rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, ← C_mul]
      congr 2
      ring

/-- Applying a fixed Schur--Szegő factor to every row postcomposes the basis transform. -/
theorem basisTransform_schurSzegoComp (D : ℕ) (G : ℝ[X])
    (P : ℕ → ℝ[X]) (p : ℝ[X]) :
    basisTransform (fun n => schurSzegoComp D (P n) G) p =
      schurSzegoComp D (basisTransform P p) G := by
  exact basisTransform_linearMap (schurSzegoCompRightLinearMap D G) P p

/-- Linear-map form of fixed-factor postcomposition. -/
theorem basisTransformₗ_schurSzegoComp (D : ℕ) (G : ℝ[X]) (P : ℕ → ℝ[X]) :
    basisTransformₗ (fun n => schurSzegoComp D (P n) G) =
      schurSzegoCompRightLinearMap D G ∘ₗ basisTransformₗ P := by
  apply LinearMap.ext
  intro p
  exact basisTransform_schurSzegoComp D G P p

/-- Scaling row `n` by `γ n` precomposes its basis transform by the diagonal map `γ`. -/
theorem basisTransform_C_mul (γ : ℕ → ℝ) (P : ℕ → ℝ[X]) (p : ℝ[X]) :
    basisTransform (fun n => C (γ n) * P n) p =
      basisTransform P (diagonalOperator γ p) := by
  rw [← basisTransform_C_mul_X_pow γ p, basisTransform_basisTransform]
  congr 1
  funext n
  rw [show C (γ n) * X ^ n = γ n • X ^ n by simp [smul_eq_C_mul],
    basisTransform_smul, basisTransform_X_pow]

/-- Linear-map form of termwise sequence scaling. -/
theorem basisTransformₗ_C_mul (γ : ℕ → ℝ) (P : ℕ → ℝ[X]) :
    basisTransformₗ (fun n => C (γ n) * P n) =
      basisTransformₗ P ∘ₗ diagonalLinearMap γ := by
  apply LinearMap.ext
  intro p
  exact basisTransform_C_mul γ P p

/-- Simultaneous termwise scaling and fixed-factor Schur--Szegő composition. -/
theorem basisTransform_schurSzegoComp_C_mul (D : ℕ) (G : ℝ[X])
    (γ : ℕ → ℝ) (P : ℕ → ℝ[X]) (p : ℝ[X]) :
    basisTransform (fun n => schurSzegoComp D (P n) (C (γ n) * G)) p =
      schurSzegoComp D (basisTransform P (diagonalOperator γ p)) G := by
  simp_rw [schurSzegoComp_C_mul_right]
  rw [basisTransform_C_mul, basisTransform_schurSzegoComp]

/-- Linear-map form of the combined sequence operation. -/
theorem basisTransformₗ_schurSzegoComp_C_mul (D : ℕ) (G : ℝ[X])
    (γ : ℕ → ℝ) (P : ℕ → ℝ[X]) :
    basisTransformₗ (fun n => schurSzegoComp D (P n) (C (γ n) * G)) =
      schurSzegoCompRightLinearMap D G ∘ₗ
        basisTransformₗ P ∘ₗ diagonalLinearMap γ := by
  apply LinearMap.ext
  intro p
  exact basisTransform_schurSzegoComp_C_mul D G γ P p

/-- Root-location preservation inherited by postcomposition with a fixed Schur--Szegő map. -/
theorem MapsRealRootedIn.basisTransform_schurSzegoComp
    {D n m : ℕ} {I J K : Set ℝ} {G : ℝ[X]} {P : ℕ → ℝ[X]}
    (hG : MapsRealRootedIn (schurSzegoCompRightLinearMap D G) m J K)
    (hP : MapsRealRootedIn (basisTransformₗ P) n I J)
    (hdeg : ∀ p : ℝ[X], p.natDegree ≤ n → (basisTransform P p).natDegree ≤ m) :
    MapsRealRootedIn
      (basisTransformₗ (fun k => schurSzegoComp D (P k) G)) n I K := by
  rw [basisTransformₗ_schurSzegoComp]
  exact hG.comp hP hdeg

/-- Root-location preservation inherited by precomposition with a diagonal map. -/
theorem MapsRealRootedIn.basisTransform_C_mul
    {n : ℕ} {I J K : Set ℝ} {γ : ℕ → ℝ} {P : ℕ → ℝ[X]}
    (hP : MapsRealRootedIn (basisTransformₗ P) n J K)
    (hγ : MapsRealRootedIn (diagonalLinearMap γ) n I J) :
    MapsRealRootedIn (basisTransformₗ (fun k => C (γ k) * P k)) n I K := by
  rw [basisTransformₗ_C_mul]
  exact hP.comp hγ fun p hp => (natDegree_diagonalOperator_le γ p).trans hp

/-- Root-location preservation inherited by the combined sequence operation. -/
theorem MapsRealRootedIn.basisTransform_schurSzegoComp_C_mul
    {D n m : ℕ} {I J K L : Set ℝ} {G : ℝ[X]}
    {γ : ℕ → ℝ} {P : ℕ → ℝ[X]}
    (hG : MapsRealRootedIn (schurSzegoCompRightLinearMap D G) m K L)
    (hP : MapsRealRootedIn (basisTransformₗ P) n J K)
    (hγ : MapsRealRootedIn (diagonalLinearMap γ) n I J)
    (hdeg : ∀ p : ℝ[X], p.natDegree ≤ n → (basisTransform P p).natDegree ≤ m) :
    MapsRealRootedIn
      (basisTransformₗ (fun k => schurSzegoComp D (P k) (C (γ k) * G))) n I L := by
  rw [basisTransformₗ_schurSzegoComp_C_mul]
  apply hG.comp (hP.comp hγ fun p hp => (natDegree_diagonalOperator_le γ p).trans hp)
  intro p hp
  exact hdeg (diagonalOperator γ p) ((natDegree_diagonalOperator_le γ p).trans hp)

end RealRooted
