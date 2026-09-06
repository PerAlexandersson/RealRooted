import RealRooted.HermiteBiehler
import RealRooted.LiebSokalPointwise
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative
import RealRooted.PosCombo
import RealRooted.SamePhaseStability
import RealRooted.WagnerX

/-!
# Weighted common-phase interleaving

This file provides reusable proper-position consequences of multivariate real
stability for positive weighted common-phase restrictions.
-/

open Polynomial

namespace RealRooted

noncomputable section

private theorem mvHasNonnegCoeffs_monomial {σ : Type*}
    (d : σ →₀ ℕ) {c : ℝ} (hc : 0 ≤ c) :
    MvPolynomial.HasNonnegCoeffs (MvPolynomial.monomial d c) := by
  classical
  intro e
  rw [MvPolynomial.coeff_monomial]
  split <;> simp_all

theorem MvPolynomial.HasNonnegCoeffs.pderiv {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvPolynomial.HasNonnegCoeffs P)
    (i : σ) :
    MvPolynomial.HasNonnegCoeffs (MvPolynomial.pderiv i P) := by
  classical
  rw [MvPolynomial.as_sum P, map_sum]
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro d hd
  rw [MvPolynomial.pderiv_monomial]
  apply mvHasNonnegCoeffs_monomial
  exact mul_nonneg (hP d) (Nat.cast_nonneg _)

private theorem hasNonnegCoeffs_finsetProd {ι : Type*}
    (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    HasNonnegCoeffs (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNonnegCoeffs_one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem hasNonnegCoeffs_finsetSum' {ι : Type*}
    (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    HasNonnegCoeffs (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNonnegCoeffs_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Nonnegative weights and multivariate coefficients give a univariate
polynomial with nonnegative coefficients. -/
theorem commonPhaseRestriction_hasNonnegCoeffs {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvPolynomial.HasNonnegCoeffs P)
    (wt : σ → ℝ) (hwt : ∀ i, 0 ≤ wt i) :
    HasNonnegCoeffs (commonPhaseRestriction wt P) := by
  classical
  rw [MvPolynomial.as_sum P]
  unfold commonPhaseRestriction
  rw [map_sum]
  apply hasNonnegCoeffs_finsetSum'
  intro d hd
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (hasNonnegCoeffs_C (hP d)).mul
  unfold Finsupp.prod
  apply hasNonnegCoeffs_finsetProd
  intro i hi
  exact (nonnegCoeffs_C_mul (hwt i) hasNonnegCoeffs_X).pow (d i)

@[simp] theorem commonPhaseRestriction_add {σ : Type*}
    (wt : σ → ℝ) (P Q : MvPolynomial σ ℝ) :
    commonPhaseRestriction wt (P + Q) =
      commonPhaseRestriction wt P + commonPhaseRestriction wt Q := by
  exact map_add (MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (wt i) * Polynomial.X)) P Q

@[simp] theorem commonPhaseRestriction_mul {σ : Type*}
    (wt : σ → ℝ) (P Q : MvPolynomial σ ℝ) :
    commonPhaseRestriction wt (P * Q) =
      commonPhaseRestriction wt P * commonPhaseRestriction wt Q := by
  exact map_mul (MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (wt i) * Polynomial.X)) P Q

/-- A nonzero polynomial with nonnegative coefficients is positive at a
strictly positive point. -/
theorem mv_eval_pos_of_hasNonnegCoeffs {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvPolynomial.HasNonnegCoeffs P)
    (hP0 : P ≠ 0) (wt : σ → ℝ) (hwt : ∀ i, 0 < wt i) :
    0 < MvPolynomial.eval wt P := by
  classical
  rw [MvPolynomial.as_sum P, map_sum]
  apply Finset.sum_pos
  · intro d hd
    rw [MvPolynomial.eval_monomial]
    apply mul_pos
    · exact lt_of_le_of_ne (hP d)
        (Ne.symm (MvPolynomial.mem_support_iff.mp hd))
    · unfold Finsupp.prod
      exact Finset.prod_pos fun i _ => pow_pos (hwt i) _
  · exact MvPolynomial.support_nonempty.mpr hP0

/-- A positive common-phase restriction of a nonzero polynomial with
nonnegative coefficients is nonzero. -/
theorem commonPhaseRestriction_ne_zero {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvPolynomial.HasNonnegCoeffs P)
    (hP0 : P ≠ 0) (wt : σ → ℝ) (hwt : ∀ i, 0 < wt i) :
    commonPhaseRestriction wt P ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) hzero
  rw [commonPhaseRestriction_eval] at heval
  simp only [mul_one, Polynomial.eval_zero] at heval
  have hpos := mv_eval_pos_of_hasNonnegCoeffs hP hP0 wt hwt
  linarith

/-- Renaming variables preserves multivariate real stability. -/
theorem MvRealStable.rename
    {σ τ : Type*} {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (f : σ → τ) :
    MvRealStable (MvPolynomial.rename f P) := by
  unfold MvRealStable complexifyMv at hP ⊢
  rw [MvPolynomial.map_rename]
  exact hP.rename

@[simp] theorem eval_complexify_commonPhaseRestriction
    {σ : Type*} (wt : σ → ℝ) (P : MvPolynomial σ ℝ) (z : ℂ) :
    (complexify (commonPhaseRestriction wt P)).eval z =
      MvPolynomial.eval (fun i => (wt i : ℂ) * z) (complexifyMv P) := by
  unfold complexify commonPhaseRestriction complexifyMv
  rw [Polynomial.eval_map]
  change (Polynomial.eval₂RingHom Complex.ofRealHom z)
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun i => Polynomial.C (wt i) * Polynomial.X) P) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hC :
      (Polynomial.eval₂RingHom Complex.ofRealHom z).comp Polynomial.C =
        Complex.ofRealHom := by
    ext r
    simp
  rw [hC]
  rw [MvPolynomial.eval_map]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext i
  simp

/-- Hermite--Biehler stability gives proper position, including the
constant-degree boundary case. -/
theorem prec_of_upperHalfPlaneStable_hermiteBiehler
    {A D : ℝ[X]}
    (hA : HasPosLeadingCoeff A) (hD : HasPosLeadingCoeff D)
    (hHB : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial A D)) :
    Prec D A := by
  by_cases hAdeg : 1 ≤ A.natDegree
  · exact prec_of_stable_general hA hD hHB hAdeg
  · have hA0 : A.natDegree = 0 := by lia
    have hD0 : D.natDegree = 0 := by
      have hle := (natDegree_shape_of_stable hA hD hHB).1
      lia
    exact prec_degree_zero_degree_zero hD.ne_zero
      (isRealRooted_of_deg_zero hD.ne_zero hD0).2 hA.ne_zero
      (isRealRooted_of_deg_zero hA.ne_zero hA0).2 hD0 hA0

/-- A proper-position relation with `X * D` is closed under adding the left
polynomial to the right. -/
theorem prec_add_X_mul_of_prec
    {A D : ℝ[X]}
    (hAD : Prec A (X * D))
    (hApos : HasPosLeadingCoeff A)
    (hDpos : HasPosLeadingCoeff D) :
    Prec A (A + X * D) := by
  have hXDpos : HasPosLeadingCoeff (X * D) := hDpos.X_mul
  have hsum : Prec A ([A, X * D].sum) := by
    apply prec_sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact prec_refl hAD.1.1 hAD.1.2
      · exact hAD
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hApos
      · exact hXDpos
    · simp
  simpa using hsum

/-- A positive common-phase restriction of a multiaffine real stable
polynomial's distinguished derivative is in proper position with the
zero-specialized restriction. -/
theorem MvRealStable.prec_commonPhaseRestriction_pderiv
    {σ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (hma : MvPolynomial.IsMultiaffine P)
    (i : σ) (wt : σ → ℝ) (hwt : ∀ j, 0 < wt j)
    (hA : HasPosLeadingCoeff
      (commonPhaseRestriction (Function.update wt i 0) P))
    (hD : HasPosLeadingCoeff
      (Polynomial.C (wt i) *
        commonPhaseRestriction wt (MvPolynomial.pderiv i P))) :
    Prec
      (Polynomial.C (wt i) *
        commonPhaseRestriction wt (MvPolynomial.pderiv i P))
      (commonPhaseRestriction (Function.update wt i 0) P) := by
  let A := commonPhaseRestriction (Function.update wt i 0) P
  let D := Polynomial.C (wt i) *
    commonPhaseRestriction wt (MvPolynomial.pderiv i P)
  have hHB : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial A D) := by
    intro z hz
    have hstable := hP (Function.update (fun j => (wt j : ℂ) * z) i
      ((wt i : ℂ) * Complex.I)) (by
        intro j
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
          simpa using hwt i
        · rw [Function.update_of_ne hji]
          change 0 < ((wt j : ℂ) * z).im
          simpa only [Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, add_zero] using
              mul_pos (hwt j) hz)
    have haff := MvPolynomial.eval_update_eq_eval_pderiv_mul_add_of_degreeOf_le_one
      (p := complexifyMv P) (i := i)
      (by
        apply MvPolynomial.degreeOf_le_iff.mpr
        intro d hd
        apply MvPolynomial.degreeOf_le_iff.mp (hma i) d
        apply MvPolynomial.mem_support_iff.mpr
        intro hcoeff
        apply MvPolynomial.mem_support_iff.mp hd
        rw [complexifyMv, MvPolynomial.coeff_map, hcoeff, map_zero])
      (fun j => (wt j : ℂ) * z) ((wt i : ℂ) * Complex.I)
    rw [haff] at hstable
    have hderiv :
        MvPolynomial.eval (fun j => (wt j : ℂ) * z)
            (MvPolynomial.pderiv i (complexifyMv P)) =
          (complexify
            (commonPhaseRestriction wt (MvPolynomial.pderiv i P))).eval z := by
      rw [eval_complexify_commonPhaseRestriction]
      simp only [complexifyMv]
      rw [MvPolynomial.pderiv_map]
    have hconst :
        MvPolynomial.eval
            (Function.update (fun j => (wt j : ℂ) * z) i 0)
            (complexifyMv P) =
          (complexify
            (commonPhaseRestriction (Function.update wt i 0) P)).eval z := by
      rw [eval_complexify_commonPhaseRestriction]
      congr 2
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    rw [hderiv, hconst] at hstable
    rw [eval_hermiteBiehlerPolynomial]
    dsimp [A, D]
    unfold complexify
    unfold complexify at hstable
    have hcast : (wt i : ℂ) = Complex.ofRealHom (wt i) := rfl
    rw [hcast] at hstable
    rw [Polynomial.map_mul, Polynomial.eval_mul, Polynomial.map_C,
      Polynomial.eval_C]
    intro hzero
    apply hstable
    convert hzero using 1
    ring
  exact prec_of_upperHalfPlaneStable_hermiteBiehler hA hD hHB

/-- Common-phase restriction commutes with renaming variables. -/
theorem commonPhaseRestriction_rename {σ τ : Type*}
    (f : σ → τ) (wt : τ → ℝ) (P : MvPolynomial σ ℝ) :
    commonPhaseRestriction wt (MvPolynomial.rename f P) =
      commonPhaseRestriction (wt ∘ f) P := by
  simp [commonPhaseRestriction, MvPolynomial.eval₂Hom_rename,
    Function.comp_def]

/-- A multiaffine common-phase restriction is its zero specialization plus
`X` times its weighted distinguished derivative. -/
theorem commonPhaseRestriction_eq_constant_add_X_mul_pderiv
    {σ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℝ}
    (hma : MvPolynomial.IsMultiaffine P) (i : σ) (wt : σ → ℝ) :
    commonPhaseRestriction wt P =
      commonPhaseRestriction (Function.update wt i 0) P +
        Polynomial.X *
          (Polynomial.C (wt i) *
            commonPhaseRestriction wt (MvPolynomial.pderiv i P)) := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, commonPhaseRestriction_eval]
  have haff := hma.eval_update_eq_eval_pderiv_mul_add i
    (fun j => wt j * x) (wt i * x)
  have hfull :
      Function.update (fun j => wt j * x) i (wt i * x) =
        fun j => wt j * x := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  have hzero :
      Function.update (fun j => wt j * x) i 0 =
        fun j => Function.update wt i 0 j * x := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [hfull, hzero] at haff
  have hderiv := hma.eval_update_pderiv_eq i
    (fun j => wt j * x) (wt i * x)
  rw [hfull] at hderiv
  rw [hderiv]
  linarith

end

end RealRooted
