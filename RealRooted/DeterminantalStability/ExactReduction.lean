module

public import RealRooted.DeterminantalStability
public import RealRooted.Hyperbolicity
import RealRooted.Hyperbolicity.SignFree
import Mathlib.Algebra.MvPolynomial.Funext
import RealRooted.HomogeneousComponentStability
import RealRooted.RootContinuity

/-!
# Exact coordinate reduction for bivariate stable polynomials

This file formalizes the exact polynomial substitutions of item C of issue #954, which reduce the
bivariate determinantal representation theorem to the normalized ternary (Helton--Vinnikov)
statement: a real stable bivariate `p` gives a homogeneous ternary `q` that is hyperbolic at
`(0, 1, 0)` with `q(0, 1, 0) = 1`, and every symmetric representation
`q = det (T I + X M + Y N)` gives back `p = c · det (N + z (I + M) / 2 + w (I - M) / 2)`.
The ternary coordinates are indexed by `Option (Fin 2)`: `none` is `Y`,
`some 0` is `T`, and `some 1` is `X`.
-/

@[expose] public section

open Matrix MvPolynomial Polynomial

namespace RealRooted.BivariateDetRep

noncomputable section

/-- The linear map `(Y, T, X) ↦ (Y, T + X, T - X)` on coordinate values. -/
def exactReductionMap (z : Option (Fin 2) → ℝ) : Option (Fin 2) → ℝ :=
  fun o => Option.elim o (z none) ![z (some 0) + z (some 1),
    z (some 0) - z (some 1)]

/-- The three linear polynomials used by the exact coordinate reduction. -/
def exactReductionPolynomialMap :
    Option (Fin 2) → MvPolynomial (Option (Fin 2)) ℝ
  | none => X none
  | some i => if i = 0 then X (some 0) + X (some 1)
      else X (some 0) - X (some 1)

/-- The polynomial substitution `(Y, T, X) ↦ (Y, T + X, T - X)`. -/
def exactReduction (H : MvPolynomial (Option (Fin 2)) ℝ) :
    MvPolynomial (Option (Fin 2)) ℝ :=
  MvPolynomial.aeval exactReductionPolynomialMap H

/-- The `T`-axis direction `(Y, T, X) = (0, 1, 0)`. -/
def exactReductionDirection : Option (Fin 2) → ℝ :=
  fun o => Option.elim o 0 ![1, 0]

/-- The boundary direction `(Y, z, w) = (0, 1, 1)` for homogenization. -/
def homogenizationBoundary : Option (Fin 2) → ℝ :=
  fun o => Option.elim o 0 (fun _ => 1)

/-- The boundary value `H(0, 1, 1)` of the ordinary homogenization. -/
def homogenizationBoundaryValue (p : MvPolynomial (Fin 2) ℝ) : ℝ :=
  MvPolynomial.eval homogenizationBoundary
    (MvPolynomial.ordinaryHomogenization p p.totalDegree)

/-- The normalized polynomial `c⁻¹ H(Y, T + X, T - X)`, where
`H` is the ordinary homogenization and `c = H(0, 1, 1)`. -/
def normalizedExactReduction (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Option (Fin 2)) ℝ :=
  MvPolynomial.C (homogenizationBoundaryValue p)⁻¹ *
    exactReduction (MvPolynomial.ordinaryHomogenization p p.totalDegree)

/-- Evaluation commutes with the exact coordinate reduction. -/
@[simp] theorem eval_exactReduction
    (H : MvPolynomial (Option (Fin 2)) ℝ) (z : Option (Fin 2) → ℝ) :
    MvPolynomial.eval z (exactReduction H) =
      MvPolynomial.eval (exactReductionMap z) H := by
  change MvPolynomial.aeval z (MvPolynomial.aeval _ H) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun w : Option (Fin 2) → ℝ => MvPolynomial.eval w H)
  funext o
  cases o with
  | none => simp [exactReductionMap, exactReductionPolynomialMap]
  | some i =>
      fin_cases i <;> simp [exactReductionMap, exactReductionPolynomialMap]

/-- Exact coordinate reduction preserves the homogeneous degree. -/
theorem exactReduction_isHomogeneous
    {H : MvPolynomial (Option (Fin 2)) ℝ} {d : ℕ}
    (hH : H.IsHomogeneous d) : (exactReduction H).IsHomogeneous d := by
  unfold exactReduction
  have h := hH.aeval exactReductionPolynomialMap fun o => by
        cases o with
        | none => exact MvPolynomial.isHomogeneous_X ℝ (none : Option (Fin 2))
        | some i =>
            fin_cases i
            · simpa [exactReductionPolynomialMap] using
                (MvPolynomial.isHomogeneous_X ℝ (some 0)).add
                  (MvPolynomial.isHomogeneous_X ℝ (some 1))
            · simpa [exactReductionPolynomialMap] using
                (MvPolynomial.isHomogeneous_X ℝ (some 0)).sub
                  (MvPolynomial.isHomogeneous_X ℝ (some 1))
  rw [one_mul] at h
  exact h

/-- The normalized coordinate reduction is homogeneous of the total degree. -/
theorem normalizedExactReduction_isHomogeneous
    (p : MvPolynomial (Fin 2) ℝ) :
    (normalizedExactReduction p).IsHomogeneous p.totalDegree := by
  unfold normalizedExactReduction
  exact (exactReduction_isHomogeneous
    (MvPolynomial.ordinaryHomogenization_isHomogeneous p p.totalDegree)).C_mul _

/-- The exact reduction sends the `T`-axis direction to `(0, 1, 1)`. -/
@[simp] theorem exactReductionMap_exactReductionDirection :
    exactReductionMap exactReductionDirection = homogenizationBoundary := by
  funext o
  cases o with
  | none => rfl
  | some i => fin_cases i <;> norm_num [exactReductionMap,
      exactReductionDirection, homogenizationBoundary]

/-- The normalized coordinate reduction has value one on the `T`-axis. -/
theorem eval_normalizedExactReduction_eq_one
    {p : MvPolynomial (Fin 2) ℝ} (hc : homogenizationBoundaryValue p ≠ 0) :
    MvPolynomial.eval exactReductionDirection (normalizedExactReduction p) = 1 := by
  simp only [normalizedExactReduction, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_exactReduction, exactReductionMap_exactReductionDirection]
  change (homogenizationBoundaryValue p)⁻¹ * homogenizationBoundaryValue p = 1
  exact inv_mul_cancel₀ hc

/-- Affine-line restriction commutes with the exact linear coordinate map. -/
theorem affineLineRestriction_exactReduction
    (H : MvPolynomial (Option (Fin 2)) ℝ)
    (x e : Option (Fin 2) → ℝ) :
    MvPolynomial.affineLineRestriction x e (exactReduction H) =
      MvPolynomial.affineLineRestriction (exactReductionMap x)
        (exactReductionMap e) H := by
  apply Polynomial.funext
  intro t
  simp only [MvPolynomial.eval_affineLineRestriction, eval_exactReduction]
  apply congrArg (fun w : Option (Fin 2) → ℝ => MvPolynomial.eval w H)
  funext o
  cases o with
  | none => simp [exactReductionMap]
  | some i => fin_cases i <;> simp [exactReductionMap] <;> ring

/-- A real-stable bivariate polynomial gives a normalized homogeneous
polynomial hyperbolic on the `T`-axis after the exact coordinate reduction. -/
theorem _root_.RealRooted.MvRealStable.normalizedExactReduction_hyperbolicAt
    {p : MvPolynomial (Fin 2) ℝ} (hst : MvRealStable p)
    (hc : homogenizationBoundaryValue p ≠ 0) :
    (normalizedExactReduction p).HyperbolicAt exactReductionDirection := by
  let H := MvPolynomial.ordinaryHomogenization p p.totalDegree
  have hH : H.HyperbolicAt homogenizationBoundary :=
    hst.ordinaryHomogenization_hyperbolicAt_boundary_fin (fun _ => 1) (fun _ => by positivity)
  refine ⟨(eval_normalizedExactReduction_eq_one hc).trans_ne one_ne_zero, ?_⟩
  intro x
  have hsplits := hH.2 (exactReductionMap x)
  rw [← exactReductionMap_exactReductionDirection] at hsplits
  have hscaled : (Polynomial.C (homogenizationBoundaryValue p)⁻¹ *
      MvPolynomial.affineLineRestriction x exactReductionDirection
        (exactReduction H)).Splits := by
    rw [affineLineRestriction_exactReduction]
    exact hsplits.C_mul _
  have hnormalize :
      MvPolynomial.affineLineRestriction x exactReductionDirection
          (normalizedExactReduction p) =
        Polynomial.C (homogenizationBoundaryValue p)⁻¹ *
          MvPolynomial.affineLineRestriction x exactReductionDirection
            (exactReduction H) := by
    apply Polynomial.funext
    intro t
    simp [MvPolynomial.eval_affineLineRestriction,
      normalizedExactReduction, H]
  rw [hnormalize]
  exact hscaled

/-- The polynomial substitution `Y = 1`, `T = (z + w) / 2`,
`X = (z - w) / 2`. -/
def exactBackSubstitutionPolynomialMap :
    Option (Fin 2) → MvPolynomial (Fin 2) ℝ
  | none => 1
  | some i => if i = 0 then
      MvPolynomial.C (1 / 2 : ℝ) * (X (0 : Fin 2) + X (1 : Fin 2))
    else MvPolynomial.C (1 / 2 : ℝ) * (X (0 : Fin 2) - X (1 : Fin 2))

/-- Apply `Y = 1`, `T = (z + w) / 2`, `X = (z - w) / 2` to a ternary
polynomial. -/
def exactBackSubstitution (Q : MvPolynomial (Option (Fin 2)) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval exactBackSubstitutionPolynomialMap Q

/-- Evaluation commutes with exact back-substitution. -/
@[simp] theorem eval_exactBackSubstitution
    (Q : MvPolynomial (Option (Fin 2)) ℝ) (z : Fin 2 → ℝ) :
    MvPolynomial.eval z (exactBackSubstitution Q) =
      MvPolynomial.eval
        (fun o => MvPolynomial.eval z (exactBackSubstitutionPolynomialMap o)) Q := by
  unfold exactBackSubstitution
  change MvPolynomial.aeval z (MvPolynomial.aeval _ Q) = _
  rw [MvPolynomial.comp_aeval_apply]
  rfl

/-- Back-substitution after exact reduction is dehomogenization. -/
theorem exactBackSubstitution_exactReduction
    (H : MvPolynomial (Option (Fin 2)) ℝ) :
    exactBackSubstitution (exactReduction H) = MvPolynomial.dehomogenize H := by
  apply MvPolynomial.funext
  intro z
  rw [eval_exactBackSubstitution, eval_exactReduction,
    MvPolynomial.eval_dehomogenize]
  apply congrArg (fun f : Option (Fin 2) → ℝ => MvPolynomial.eval f H)
  funext o
  cases o with
  | none => simp [exactReductionMap, exactBackSubstitutionPolynomialMap]
  | some i =>
      fin_cases i <;>
        simp [exactReductionMap, exactBackSubstitutionPolynomialMap] <;> ring

/-- Back-substitution of the normalized reduction is `c⁻¹ p`. -/
theorem exactBackSubstitution_normalizedExactReduction
    (p : MvPolynomial (Fin 2) ℝ) :
    exactBackSubstitution (normalizedExactReduction p) =
      MvPolynomial.C (homogenizationBoundaryValue p)⁻¹ * p := by
  unfold normalizedExactReduction
  change MvPolynomial.aeval exactBackSubstitutionPolynomialMap
      (MvPolynomial.C (homogenizationBoundaryValue p)⁻¹ *
        exactReduction
          (MvPolynomial.ordinaryHomogenization p p.totalDegree)) = _
  rw [map_mul, MvPolynomial.aeval_C,
    show MvPolynomial.aeval exactBackSubstitutionPolynomialMap
        (exactReduction
          (MvPolynomial.ordinaryHomogenization p p.totalDegree)) =
        MvPolynomial.dehomogenize
          (MvPolynomial.ordinaryHomogenization p p.totalDegree) from
      exactBackSubstitution_exactReduction _,
    MvPolynomial.dehomogenize_ordinaryHomogenization]
  rfl

/-- Coefficient matrices for `det(T I + X M + Y N)` in the coordinate order
`none = Y`, `some 0 = T`, `some 1 = X`. -/
def ternaryDetPencilMatrices {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) :
    Option (Fin 2) → Matrix (Fin d) (Fin d) ℝ
  | none => N
  | some i => if i = 0 then 1 else M

/-- Coefficient matrices `((I + M) / 2, (I - M) / 2)` of the bivariate
back-substituted pencil. -/
def bivariateDetPencilMatrices {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Fin 2 → Matrix (Fin d) (Fin d) ℝ :=
  fun k i j => if k = 0 then ((1 + M) i j) / 2 else ((1 - M) i j) / 2

/-- Exact back-substitution of `det(T I + X M + Y N)` is the affine
bivariate determinant pencil with coefficient matrices `(I ± M) / 2`. -/
theorem exactBackSubstitution_realDetPencil
    {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) :
    exactBackSubstitution
        (realDetPencil (0 : Matrix (Fin d) (Fin d) ℝ)
          (ternaryDetPencilMatrices M N)) =
      realDetPencil N (bivariateDetPencilMatrices M) := by
  classical
  apply MvPolynomial.funext
  intro z
  rw [eval_exactBackSubstitution, eval_realDetPencil,
    eval_realDetPencil]
  congr 1
  apply Matrix.ext
  intro i j
  simp [exactBackSubstitutionPolynomialMap, ternaryDetPencilMatrices,
    bivariateDetPencilMatrices, Fintype.sum_option, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.add_apply]
  split_ifs <;> ring

/-- If the normalized reduction equals `det(T I + X M + Y N)`, then the
original polynomial is exactly `c` times the back-substituted determinant
pencil. -/
theorem eq_C_mul_realDetPencil_of_normalizedExactReduction_eq
    {p : MvPolynomial (Fin 2) ℝ} (hc : homogenizationBoundaryValue p ≠ 0)
    {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ)
    (hq : normalizedExactReduction p =
      realDetPencil (0 : Matrix (Fin d) (Fin d) ℝ)
        (ternaryDetPencilMatrices M N)) :
    p = MvPolynomial.C (homogenizationBoundaryValue p) *
      realDetPencil N (bivariateDetPencilMatrices M) := by
  have hback := congrArg exactBackSubstitution hq
  rw [exactBackSubstitution_normalizedExactReduction,
    exactBackSubstitution_realDetPencil] at hback
  calc
    p = MvPolynomial.C (homogenizationBoundaryValue p) *
        (MvPolynomial.C (homogenizationBoundaryValue p)⁻¹ * p) := by
      rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hc,
        MvPolynomial.C_1, one_mul]
    _ = MvPolynomial.C (homogenizationBoundaryValue p) *
        realDetPencil N (bivariateDetPencilMatrices M) := by rw [hback]

/-- For `M = diag(-1, 1)`, both endpoint coefficient matrices are singular,
so the reduction correctly allows positive semidefinite endpoint degeneracy. -/
example :
    let M : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]
    (bivariateDetPencilMatrices M 0).det = 0 ∧
      (bivariateDetPencilMatrices M 1).det = 0 := by
  norm_num [bivariateDetPencilMatrices, Matrix.det_fin_two,
    Matrix.one_apply, Matrix.add_apply]

end

end RealRooted.BivariateDetRep
