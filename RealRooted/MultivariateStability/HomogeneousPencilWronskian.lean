import RealRooted.HermiteBiehler.StablePencil
import RealRooted.Multiaffine.AffineLineRestriction
import RealRooted.SamePhaseInterlacing
import RealRooted.Wronskian.WeakForward

/-!
# Wronskian orientation for homogeneous stable pencils

This file extracts coordinatewise Wronskian signs from a stable affine
extension.  Homogeneity and coefficientwise nonnegativity provide the
positive leading coefficients needed to orient its univariate restrictions.
-/

namespace RealRooted

open scoped BigOperators

noncomputable section

/-- Restricting the old variables of a stable affine extension along a
strictly positive direction gives a stable univariate pencil. -/
theorem MvRealStable.isUpperHalfPlaneStablePencil_realAffineLineRestriction
    {σ : Type*} {P Q : MvPolynomial σ ℝ}
    (hPQ : MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some Q))
    (a b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    IsUpperHalfPlaneStablePencil
      (realAffineLineRestriction a b P)
      (realAffineLineRestriction a b Q) := by
  intro z w hz hw
  have h := hPQ (fun o => o.elim w
    (fun i => (a i : ℂ) + (b i : ℂ) * z)) (by
      intro o
      cases o with
      | none => exact hw
      | some i =>
          change 0 < ((a i : ℂ) + (b i : ℂ) * z).im
          simpa using mul_pos (hb i) hz)
  unfold complexify
  have hmap : Complex.ofRealHom = algebraMap ℝ ℂ := by
    ext r
    rfl
  rw [hmap]
  rw [eval_complexify_realAffineLineRestriction,
    eval_complexify_realAffineLineRestriction]
  simpa [complexifyMv, MvPolynomial.map_rename,
    MvPolynomial.eval_rename, MvPolynomial.eval_map,
    Function.comp_def] using h

/-- The Wronskian of two affine-line restrictions is the restriction of the
corresponding weighted sum of coordinate Wronskians. -/
theorem wronskian_realAffineLineRestriction
    {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (Q P : MvPolynomial σ ℝ) :
    Polynomial.wronskian
        (realAffineLineRestriction a b Q)
        (realAffineLineRestriction a b P) =
      realAffineLineRestriction a b
        (∑ i, MvPolynomial.C (b i) *
          MvPolynomial.coordinateWronskian Q P i) := by
  rw [Polynomial.wronskian, derivative_realAffineLineRestriction,
    derivative_realAffineLineRestriction]
  unfold realAffineLineRestriction
  rw [← map_mul, ← map_mul, ← map_sub]
  congr 1
  rw [directionalPDeriv, directionalPDeriv, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.coordinateWronskian]
  ring

/-- A positive-direction restriction of a nonzero homogeneous polynomial
with nonnegative coefficients has positive leading coefficient. -/
theorem MvPolynomial.IsHomogeneous.hasPosLeadingCoeff_realAffineLineRestriction
    {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hhom : P.IsHomogeneous d) (hnn : P.HasNonnegCoeffs)
    (hP0 : P ≠ 0) (a b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    HasPosLeadingCoeff (realAffineLineRestriction a b P) := by
  have hcoeff : 0 < (realAffineLineRestriction a b P).coeff d := by
    rw [MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction
      hhom]
    exact hnn.eval_pos hP0 hb
  have hdegree : (realAffineLineRestriction a b P).natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
        hhom a b) hcoeff.ne'
  rw [HasPosLeadingCoeff, Polynomial.leadingCoeff, hdegree]
  exact hcoeff

/-- A stable homogeneous affine extension orients the Wronskian of every
strictly positive affine-line restriction of its endpoints. -/
theorem MvRealStable.wronskian_eval_realAffineLineRestriction_nonneg_of_homogeneous
    {σ : Type*} {P Q : MvPolynomial σ ℝ} {d e : ℕ}
    (hPQ : MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some Q))
    (hPhom : P.IsHomogeneous d) (hQhom : Q.IsHomogeneous e)
    (hPnn : P.HasNonnegCoeffs) (hQnn : Q.HasNonnegCoeffs)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (a b : σ → ℝ) (hb : ∀ i, 0 < b i) (t : ℝ) :
    0 ≤ (Polynomial.wronskian
      (realAffineLineRestriction a b Q)
      (realAffineLineRestriction a b P)).eval t := by
  let p := realAffineLineRestriction a b P
  let q := realAffineLineRestriction a b Q
  have hp : HasPosLeadingCoeff p :=
    MvPolynomial.IsHomogeneous.hasPosLeadingCoeff_realAffineLineRestriction
      hPhom hPnn hP0 a b hb
  have hq : HasPosLeadingCoeff q :=
    MvPolynomial.IsHomogeneous.hasPosLeadingCoeff_realAffineLineRestriction
      hQhom hQnn hQ0 a b hb
  have hpencil : IsUpperHalfPlaneStablePencil p q :=
    hPQ.isUpperHalfPlaneStablePencil_realAffineLineRestriction a b hb
  have hHB : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial p q) := by
    intro z hz
    simpa using hpencil z Complex.I hz (by simp)
  exact wronskian_eval_nonneg_of_prec hp hq
    (prec_of_upperHalfPlaneStable_hermiteBiehler hp hq hHB) t

/-- A stable affine extension of two nonzero homogeneous polynomials with
nonnegative coefficients orients every coordinate Wronskian of its direction
against its base. -/
theorem MvRealStable.eval_coordinateWronskian_nonneg_of_homogeneous_affineExtension
    {σ : Type*} [Finite σ] {P Q : MvPolynomial σ ℝ} {d e : ℕ}
    (hPQ : MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some Q))
    (hPhom : P.IsHomogeneous d) (hQhom : Q.IsHomogeneous e)
    (hPnn : P.HasNonnegCoeffs) (hQnn : Q.HasNonnegCoeffs)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian Q P i) := by
  classical
  letI := Fintype.ofFinite σ
  intro i x
  let A : σ → ℝ := fun j => MvPolynomial.eval x
    (MvPolynomial.coordinateWronskian Q P j)
  have hweighted (b : σ → ℝ) (hb : ∀ j, 0 < b j) :
      0 ≤ ∑ j, b j * A j := by
    have hw :=
      hPQ.wronskian_eval_realAffineLineRestriction_nonneg_of_homogeneous
        hPhom hQhom hPnn hQnn hP0 hQ0 x b hb 0
    rw [wronskian_realAffineLineRestriction,
      eval_realAffineLineRestriction, map_sum] at hw
    simpa [A] using hw
  change 0 ≤ A i
  apply le_of_forall_pos_le_add
  intro ε hε
  let S := (Finset.univ.erase i).sum A
  let δ := ε / (|S| + 1)
  have hden : 0 < |S| + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  let b : σ → ℝ := fun j => if j = i then 1 else δ
  have hb : ∀ j, 0 < b j := by
    intro j
    by_cases hji : j = i
    · simp [b, hji]
    · simp [b, hji, hδ]
  have hw := hweighted b hb
  have hsum : (∑ j, b j * A j) = A i + δ * S := by
    calc
      (∑ j, b j * A j) =
          (Finset.univ.erase i).sum (fun j => b j * A j) + b i * A i :=
        (Finset.sum_erase_add Finset.univ (fun j => b j * A j)
          (Finset.mem_univ i)).symm
      _ = δ * S + A i := by
        simp only [b, ite_eq_left, one_mul]
        rw [Finset.mul_sum]
        apply congrArg (fun y => y + A i)
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [ite_eq_right hji]
      _ = A i + δ * S := by ring
  rw [hsum] at hw
  have hδ_nonneg : 0 ≤ δ := hδ.le
  have hmul : δ * S ≤ δ * |S| :=
    mul_le_mul_of_nonneg_left (le_abs_self S) hδ_nonneg
  have hquot : δ * |S| < ε := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [abs_nonneg S]
  nlinarith

end

end RealRooted
