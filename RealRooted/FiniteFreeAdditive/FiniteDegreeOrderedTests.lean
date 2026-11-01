module

import RealRooted.BorceaBranden.FiniteSymbolClassification
public import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol
public import RealRooted.Hermite.PoulainInterlacing
public import RealRooted.PFPolynomial
public import RealRooted.FiniteFreeAdditive.FiniteDegreeTests
import RealRooted.HermiteBiehler.StablePencil
public import RealRooted.MultiplierSequence
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.HermiteBiehler.Converse
import RealRooted.HermiteBiehler.ConverseLowDegree
import RealRooted.Hadamard.Grace
import RealRooted.Linear
import RealRooted.LinearPowerFamily
import RealRooted.Mathlib.Algebra.MvPolynomial.Equiv
import RealRooted.Mathlib.Algebra.Polynomial.Taylor
import RealRooted.ReciprocalShift.ProperPosition

/-!
# Ordered finite-degree tests for differential operators

This file builds the bivariate finite-symbol bridge from an ordered pair of
monomial tests to the ordered images of every PF polynomial in the degree box.
-/

@[expose] public section

open Polynomial BigOperators

noncomputable section

namespace RealRooted.FiniteDegreeOrdered

open BorceaBranden HermitePoulain

/-- The degree-`N` monomial test for a constant-coefficient differential
symbol. -/
def differentialTest (N : ℕ) (h : ℝ[X]) : ℝ[X] :=
  applyAsDifferentialOperator h (X ^ N)

private theorem complexPolynomialInFirstMv_smul (c : ℂ) (p : ℂ[X]) :
    complexPolynomialInFirstMv (c • p) =
      c • complexPolynomialInFirstMv p := by
  ext m
  simp [complexPolynomialInFirstMv, Algebra.smul_def]

private def complexDifferentialOperator (h : ℝ[X]) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun p := ∑ j ∈ Finset.range (h.natDegree + 1),
    C (h.coeff j : ℂ) * (derivative^[j]) p
  map_add' p q := by
    simp [iterate_map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    simp [smul_eq_C_mul, iterate_derivative_C_mul, Finset.mul_sum,
      mul_left_comm]

private theorem complexify_iterate_derivative (j : ℕ) (p : ℝ[X]) :
    complexify ((derivative^[j]) p) =
      (derivative^[j]) (complexify p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hderivative (q : ℝ[X]) :
          complexify q.derivative = (complexify q).derivative := by
        ext n
        simp [complexify, coeff_derivative]
      rw [hderivative]
      exact congrArg derivative ih

private theorem complexDifferentialOperator_complexify
    (h p : ℝ[X]) :
    complexDifferentialOperator h (complexify p) =
      complexify (applyAsDifferentialOperator h p) := by
  rw [applyAsDifferentialOperator]
  change (∑ j ∈ Finset.range (h.natDegree + 1),
      C (h.coeff j : ℂ) * (derivative^[j]) (complexify p)) =
    (Polynomial.mapRingHom Complex.ofRealHom)
      (∑ j ∈ Finset.range (h.natDegree + 1),
        C (h.coeff j) * (derivative^[j]) p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change C (h.coeff j : ℂ) * (derivative^[j]) (complexify p) =
    Polynomial.map Complex.ofRealHom
      (C (h.coeff j) * (derivative^[j]) p)
  rw [Polynomial.map_mul, Polynomial.map_C]
  rw [show Polynomial.map Complex.ofRealHom ((derivative^[j]) p) =
      (derivative^[j]) (complexify p) from
    complexify_iterate_derivative j p]
  rfl

private theorem complexDifferentialOperator_taylor
    (h : ℝ[X]) (w : ℂ) (p : ℂ[X]) :
    complexDifferentialOperator h (Polynomial.taylor w p) =
      Polynomial.taylor w (complexDifferentialOperator h p) := by
  change (∑ j ∈ Finset.range (h.natDegree + 1),
      C (h.coeff j : ℂ) * (derivative^[j]) (Polynomial.taylor w p)) =
    Polynomial.taylor w
      (∑ j ∈ Finset.range (h.natDegree + 1),
        C (h.coeff j : ℂ) * (derivative^[j]) p)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Polynomial.taylor_iterate_derivative]
  simp [Polynomial.taylor_apply]

private def differentialPencilDegreeBoxMap (N : ℕ) (h k : ℝ[X]) :
    MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ ↦ N) →ₗ[ℂ]
      MvPolynomial (Fin 2) ℂ where
  toFun p :=
    complexPolynomialInFirstMv
        (complexDifferentialOperator k
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) p.1)) +
      MvPolynomial.X 1 *
        complexPolynomialInFirstMv
          (complexDifferentialOperator h
            (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) p.1))
  map_add' p q := by
    simp [complexPolynomialInFirstMv, mul_add, add_assoc, add_left_comm]
  map_smul' c p := by
    change complexPolynomialInFirstMv
          (complexDifferentialOperator k
            (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) (c • p).1)) +
        MvPolynomial.X 1 * complexPolynomialInFirstMv
          (complexDifferentialOperator h
            (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) (c • p).1)) = _
    rw [show MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) (c • p).1 =
        c • MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) p.1 by simp]
    rw [map_smul, map_smul, complexPolynomialInFirstMv_smul,
      complexPolynomialInFirstMv_smul]
    rw [mul_smul_comm]
    exact (smul_add c _ _).symm

private theorem uniqueAlgEquiv_shiftedBoxPolynomial
    (N : ℕ) (w : ℂ) :
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (shiftedBoxPolynomial (fun _ : Fin 1 ↦ N) (fun _ ↦ w)).1 =
      (X + C w) ^ N := by
  rw [shiftedBoxPolynomial_eq_prod]
  simp

private theorem eval_complexPolynomialInFirstMv
    (p : ℂ[X]) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (complexPolynomialInFirstMv p) = p.eval (z 0) := by
  have hC :
      (MvPolynomial.eval z).comp
          (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ) =
        RingHom.id ℂ := by
    ext a
    simp
  simp [complexPolynomialInFirstMv, Polynomial.hom_eval₂, hC]

private theorem eval_complexDifferentialOperator_X_add_C_pow
    (N : ℕ) (h : ℝ[X]) (x w : ℂ) :
    (complexDifferentialOperator h ((X + C w) ^ N)).eval x =
      (complexify (differentialTest N h)).eval (x + w) := by
  have hshift : (X + C w : ℂ[X]) ^ N =
      Polynomial.taylor w ((X : ℂ[X]) ^ N) := by
    simp [Polynomial.taylor_apply]
  rw [hshift, complexDifferentialOperator_taylor]
  have hpow : ((X : ℂ[X]) ^ N) = complexify ((X : ℝ[X]) ^ N) := by
    simp [complexify]
  rw [hpow, complexDifferentialOperator_complexify]
  simp [differentialTest, Polynomial.taylor_apply, Polynomial.eval_comp]

private theorem eval_differentialPencilDegreeBoxMap_shiftedBoxPolynomial
    (N : ℕ) (h k : ℝ[X]) (w : ℂ) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z
        (differentialPencilDegreeBoxMap N h k
          (shiftedBoxPolynomial (fun _ : Fin 1 ↦ N) (fun _ ↦ w))) =
      (complexify (differentialTest N k)).eval (z 0 + w) +
        z 1 * (complexify (differentialTest N h)).eval (z 0 + w) := by
  change MvPolynomial.eval z
      (complexPolynomialInFirstMv
          (complexDifferentialOperator k
            (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
              (shiftedBoxPolynomial (fun _ : Fin 1 ↦ N) (fun _ ↦ w)).1)) +
        MvPolynomial.X 1 * complexPolynomialInFirstMv
          (complexDifferentialOperator h
            (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
              (shiftedBoxPolynomial (fun _ : Fin 1 ↦ N) (fun _ ↦ w)).1))) = _
  rw [uniqueAlgEquiv_shiftedBoxPolynomial]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, eval_complexPolynomialInFirstMv]
  rw [eval_complexDifferentialOperator_X_add_C_pow,
    eval_complexDifferentialOperator_X_add_C_pow]

private theorem algebraicSymbol_differentialPencilDegreeBoxMap_stable
    {N : ℕ} {h k : ℝ[X]}
    (hcap : MvUpperHalfPlaneStable
      (bivariatePencil (differentialTest N k) (differentialTest N h))) :
    MvUpperHalfPlaneStable
      (MvPolynomial.algebraicSymbol (fun _ : Fin 1 ↦ N)
        (differentialPencilDegreeBoxMap N h k)) := by
  intro z hz
  let x : Fin 2 → ℂ := fun i ↦ z (Sum.inl i)
  let w : Fin 1 → ℂ := fun i ↦ z (Sum.inr i)
  have hzsplit : z = Sum.elim x w := by
    funext i
    rcases i with i | i <;> rfl
  rw [hzsplit, eval_algebraicSymbol_eq_eval_shiftedBoxPolynomial]
  have hw : w = fun _ : Fin 1 ↦ w 0 := by
    funext i
    rw [Subsingleton.elim i 0]
  rw [hw]
  rw [eval_differentialPencilDegreeBoxMap_shiftedBoxPolynomial]
  have himsum : 0 < (x 0 + w 0).im := by
    dsimp [x, w]
    exact add_pos (hz (Sum.inl 0)) (hz (Sum.inr 0))
  have hvalue := hcap ![x 0 + w 0, x 1] (by
    intro i
    fin_cases i
    · simpa using himsum
    · exact hz (Sum.inl 1))
  simpa [eval_bivariatePencil] using hvalue

private theorem capPencil_eq_zero_pair_or_stable
    {N : ℕ} {h k : ℝ[X]}
    (hh : IsPFPolynomial (differentialTest N h))
    (hk : IsPFPolynomial (differentialTest N k))
    (horder : Interl (differentialTest N h) (differentialTest N k)) :
    (differentialTest N h = 0 ∧ differentialTest N k = 0) ∨
      MvUpperHalfPlaneStable
        (bivariatePencil (differentialTest N k) (differentialTest N h)) := by
  rcases horder with hh0 | hk0 | hstrict
  · by_cases hkzero : differentialTest N k = 0
    · exact Or.inl ⟨hh0, hkzero⟩
    · right
      apply mvUpperHalfPlaneStable_bivariatePencil_iff.mpr
      simpa [hh0] using
        isUpperHalfPlaneStablePencil_zero_right hkzero
          (hk.eq_zero_or_splits.resolve_left hkzero)
  · by_cases hhzero : differentialTest N h = 0
    · exact Or.inl ⟨hhzero, hk0⟩
    · right
      apply mvUpperHalfPlaneStable_bivariatePencil_iff.mpr
      simpa [hk0] using
        isUpperHalfPlaneStablePencil_zero_left hhzero
          (hh.eq_zero_or_splits.resolve_left hhzero)
  · right
    apply mvUpperHalfPlaneStable_bivariatePencil_iff.mpr
    exact isUpperHalfPlaneStablePencil_of_strictInterl
      (hk.hasNonnegCoeffs.pos_leadingCoeff hstrict.2.1.1)
      (hh.hasNonnegCoeffs.pos_leadingCoeff hstrict.1.1) hstrict

private theorem coeff_differentialTest_of_le
    (N : ℕ) (h : ℝ[X]) {j : ℕ} (hj : j ≤ N) :
    (differentialTest N h).coeff (N - j) =
      (N.descFactorial j : ℝ) * h.coeff j := by
  rw [differentialTest, applyAsDifferentialOperator,
    Polynomial.finsetSum_coeff]
  by_cases hh : j ≤ h.natDegree
  · rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
      simp only [nsmul_eq_mul]
      rw [Nat.sub_add_cancel hj]
      simp
      ring
    · intro q hq hqj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
      simp only [nsmul_eq_mul]
      simp [coeff_X_pow, show N - j + q ≠ N by lia]
    · intro hjnot
      exact (hjnot (by simpa using Nat.lt_succ_of_le hh)).elim
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hh),
      mul_zero]
    apply Finset.sum_eq_zero
    intro q hq
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_iterate_derivative]
    simp only [nsmul_eq_mul]
    by_cases hqj : q = j
    · subst q
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hh)]
      simp
    · simp [coeff_X_pow, show N - j + q ≠ N by lia]

private theorem coeff_eq_zero_of_differentialTest_eq_zero
    {N : ℕ} {h : ℝ[X]} (htest : differentialTest N h = 0)
    {j : ℕ} (hj : j ≤ N) : h.coeff j = 0 := by
  have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff (N - j)) htest
  rw [coeff_differentialTest_of_le N h hj, Polynomial.coeff_zero] at hcoeff
  have hfall : (N.descFactorial j : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj)
  exact (mul_eq_zero.mp hcoeff).resolve_left hfall

private theorem differentialTest_coeff_nonneg
    {N : ℕ} {h : ℝ[X]} (htest : IsPFPolynomial (differentialTest N h))
    {j : ℕ} (hj : j ≤ N) : 0 ≤ h.coeff j := by
  have hcoeff := htest.hasNonnegCoeffs (N - j)
  rw [coeff_differentialTest_of_le N h hj] at hcoeff
  have hfall : 0 < (N.descFactorial j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hj
  nlinarith

private theorem applyAsDifferentialOperator_eq_zero_of_test_eq_zero
    {N : ℕ} {h p : ℝ[X]} (htest : differentialTest N h = 0)
    (hpdeg : p.natDegree ≤ N) :
    applyAsDifferentialOperator h p = 0 := by
  rw [applyAsDifferentialOperator_eq_sum_range_right]
  apply Finset.sum_eq_zero
  intro j hj
  have hjN : j ≤ N := by
    have := Finset.mem_range.mp hj
    lia
  rw [coeff_eq_zero_of_differentialTest_eq_zero htest hjN]
  simp

private theorem pf_pair_interl_of_stablePencil {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hstable : IsUpperHalfPlaneStablePencil g f) :
    IsPFPolynomial f ∧ IsPFPolynomial g ∧ Interl f g := by
  by_cases hf0 : f = 0
  · subst f
    by_cases hg0 : g = 0
    · subst g
      exact ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, interl_zero_left 0⟩
    · have hgstable : IsUpperHalfPlaneStable (complexify g) := by
        intro z hz
        simpa using hstable z Complex.I hz (by norm_num)
      exact ⟨IsPFPolynomial.zero,
        IsPFPolynomial.of_realRooted_nonneg hg hgstable.splits_complexify,
        interl_zero_left g⟩
  · by_cases hg0 : g = 0
    · subst g
      have hfstable : IsUpperHalfPlaneStable (complexify f) := by
        intro z hz hzero
        apply hstable z Complex.I hz (by norm_num)
        simp [hzero]
      exact ⟨IsPFPolynomial.of_realRooted_nonneg hf hfstable.splits_complexify,
        IsPFPolynomial.zero, interl_zero_right f⟩
    · have hfpos := hf.pos_leadingCoeff hf0
      have hgpos := hg.pos_leadingCoeff hg0
      have hhb := hstable.hermiteBiehler
      by_cases hgdeg : 1 ≤ g.natDegree
      · have hstrict : StrictInterl f g :=
          strictInterl_of_stable_general hgpos hfpos hhb hgdeg
        exact ⟨IsPFPolynomial.of_realRooted_nonneg hf hstrict.1.2,
          IsPFPolynomial.of_realRooted_nonneg hg hstrict.2.1.2,
          hstrict.toInterl⟩
      · have hgdeg0 : g.natDegree = 0 := by lia
        have hfdeg0 : f.natDegree = 0 := by
          have hshape := natDegree_shape_of_stable hgpos hfpos hhb
          lia
        obtain ⟨_, hfs⟩ := isRealRooted_of_deg_zero hf0 hfdeg0
        obtain ⟨_, hgs⟩ := isRealRooted_of_deg_zero hg0 hgdeg0
        have hstrict : StrictInterl f g :=
          StrictInterl.of_degree_zero_degree_zero hf0 hfs hg0 hgs hfdeg0 hgdeg0
        exact ⟨IsPFPolynomial.of_realRooted_nonneg hf hfs,
          IsPFPolynomial.of_realRooted_nonneg hg hgs, hstrict.toInterl⟩

private theorem differentialPencilDegreeBoxMap_complexify
    (N : ℕ) (h k p : ℝ[X]) (hpdeg : p.natDegree ≤ N) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ ↦ N) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        change (Polynomial.map Complex.ofRealHom p).natDegree ≤ N
        exact Polynomial.natDegree_map_le.trans hpdeg⟩
    differentialPencilDegreeBoxMap N h k f =
      bivariatePencil (applyAsDifferentialOperator k p)
        (applyAsDifferentialOperator h p) := by
  change complexPolynomialInFirstMv
        (complexDifferentialOperator k
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
            ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)))) +
      MvPolynomial.X 1 * complexPolynomialInFirstMv
        (complexDifferentialOperator h
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
            ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)))) = _
  rw [AlgEquiv.apply_symm_apply, complexDifferentialOperator_complexify,
    complexDifferentialOperator_complexify]
  rfl

/-- Ordered PF monomial tests suffice for ordered preservation throughout the
degree box. -/
theorem preservesOrderedPFUpTo_of_differentialTests
    {N : ℕ} {h k : ℝ[X]}
    (hh : IsPFPolynomial (differentialTest N h))
    (hk : IsPFPolynomial (differentialTest N k))
    (horder : Interl (differentialTest N h) (differentialTest N k)) :
    PreservesOrderedPFUpTo N h k := by
  rcases capPencil_eq_zero_pair_or_stable hh hk horder with hzero | hcap
  · intro p hp hpdeg
    have hhzero :=
      applyAsDifferentialOperator_eq_zero_of_test_eq_zero hzero.1 hpdeg
    have hkzero :=
      applyAsDifferentialOperator_eq_zero_of_test_eq_zero hzero.2 hpdeg
    rw [hhzero, hkzero]
    exact ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, interl_zero_left 0⟩
  · intro p hp hpdeg
    by_cases hp0 : p = 0
    · subst p
      simp [IsPFPolynomial.zero, interl_zero_left]
    have hhnn : HasNonnegCoeffs (applyAsDifferentialOperator h p) :=
      applyAsDifferentialOperator_hasNonnegCoeffs_of_test
        hh hp.hasNonnegCoeffs hpdeg
    have hknn : HasNonnegCoeffs (applyAsDifferentialOperator k p) :=
      applyAsDifferentialOperator_hasNonnegCoeffs_of_test
        hk hp.hasNonnegCoeffs hpdeg
    let fmv : MvPolynomial (Fin 1) ℂ :=
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p)
    have hfmem : fmv ∈ MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ ↦ N) := by
      rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
      intro i
      rw [Subsingleton.elim i default,
        MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
      change (Polynomial.map Complex.ofRealHom p).natDegree ≤ N
      exact Polynomial.natDegree_map_le.trans hpdeg
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ ↦ N) :=
      ⟨fmv, hfmem⟩
    have hfstable : MvUpperHalfPlaneStable f.1 := by
      simpa [f, fmv] using
        (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable (complexify p)).mp
          (Polynomial.Splits.isUpperHalfPlaneStable_complexify
            (hp.eq_zero_or_splits.resolve_left hp0) hp0)
    have hsymbol :=
      algebraicSymbol_differentialPencilDegreeBoxMap_stable hcap
    have hout := finiteSymbol_preserves_stability_general
      (fun _ : Fin 1 ↦ N) (differentialPencilDegreeBoxMap N h k)
      hsymbol f hfstable
    have hvalue : differentialPencilDegreeBoxMap N h k f =
        bivariatePencil (applyAsDifferentialOperator k p)
          (applyAsDifferentialOperator h p) := by
      simpa [f, fmv] using
        differentialPencilDegreeBoxMap_complexify N h k p hpdeg
    rw [hvalue] at hout
    rcases hout.eq_zero_pair_or_stablePencil with hboth | hstable
    · rw [hboth.1, hboth.2]
      exact ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, interl_zero_left 0⟩
    · exact pf_pair_interl_of_stablePencil hhnn hknn hstable

/-- Ordered preservation through degree `N` forces both monomial tests to be
PF and ordered. -/
theorem differentialTests_ordered_of_preservesOrderedPFUpTo
    {N : ℕ} {h k : ℝ[X]} (hpres : PreservesOrderedPFUpTo N h k) :
    IsPFPolynomial (differentialTest N h) ∧
      IsPFPolynomial (differentialTest N k) ∧
        Interl (differentialTest N h) (differentialTest N k) := by
  exact hpres (isPFPolynomial_X_pow N) (by simp)

/-- Two constant-coefficient differential operators preserve the ordered PF
pair through degree `N` exactly when their images of `X ^ N` are PF and have
the same order. -/
theorem preservesOrderedPFUpTo_iff_differentialTests
    (N : ℕ) (h k : ℝ[X]) :
    PreservesOrderedPFUpTo N h k ↔
      IsPFPolynomial (differentialTest N h) ∧
        IsPFPolynomial (differentialTest N k) ∧
          Interl (differentialTest N h) (differentialTest N k) := by
  constructor
  · exact differentialTests_ordered_of_preservesOrderedPFUpTo
  · rintro ⟨hh, hk, horder⟩
    exact preservesOrderedPFUpTo_of_differentialTests hh hk horder

/-- The degree-`N` Jensen polynomial of a differential symbol, normalized by
falling factorials. -/
def jensenDifferentialTest (N : ℕ) (h : ℝ[X]) : ℝ[X] :=
  (differentialTest N h).reflect N

/-- The coefficient of the degree-`N` Jensen polynomial is the corresponding
symbol coefficient multiplied by a falling factorial. -/
theorem coeff_jensenDifferentialTest_of_le
    (N : ℕ) (h : ℝ[X]) {j : ℕ} (hj : j ≤ N) :
    (jensenDifferentialTest N h).coeff j =
      (N.descFactorial j : ℝ) * h.coeff j := by
  rw [jensenDifferentialTest, Polynomial.coeff_reflect,
    Polynomial.revAt_le hj, coeff_differentialTest_of_le N h hj]

private theorem natDegree_differentialTest_le (N : ℕ) (h : ℝ[X]) :
    (differentialTest N h).natDegree ≤ N := by
  rw [differentialTest, applyAsDifferentialOperator]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_iterate_derivative (X ^ N) j).trans
      ((Nat.sub_le _ _).trans (by simp)))

private theorem reflect_reverses_interl_of_pf
    {N : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpdeg : p.natDegree ≤ N) (hqdeg : q.natDegree ≤ N)
    (hpq : Interl p q) : Interl (q.reflect N) (p.reflect N) := by
  rcases hpq with hpzero | hqzero | hpq
  · subst p
    simpa using interl_zero_right (q.reflect N)
  · subst q
    simpa using interl_zero_left (p.reflect N)
  · exact (reciprocalShift_reverses_strictInterl
      hp hq hpdeg hqdeg hpq).toInterl

/-- At a common cap, ordered monomial tests are equivalent to PF Jensen
polynomials in the reversed interlacing order. -/
theorem differentialTests_ordered_iff_jensenDifferentialTests
    (N : ℕ) (h k : ℝ[X]) :
    (IsPFPolynomial (differentialTest N h) ∧
        IsPFPolynomial (differentialTest N k) ∧
          Interl (differentialTest N h) (differentialTest N k)) ↔
      (IsPFPolynomial (jensenDifferentialTest N h) ∧
        IsPFPolynomial (jensenDifferentialTest N k) ∧
          Interl (jensenDifferentialTest N k)
            (jensenDifferentialTest N h)) := by
  constructor
  · rintro ⟨hh, hk, horder⟩
    have hhdeg := natDegree_differentialTest_le N h
    have hkdeg := natDegree_differentialTest_le N k
    exact ⟨isPFPolynomial_reflect hh hhdeg,
      isPFPolynomial_reflect hk hkdeg,
      reflect_reverses_interl_of_pf hh hk hhdeg hkdeg horder⟩
  · rintro ⟨hh, hk, horder⟩
    have hhdeg : (jensenDifferentialTest N h).natDegree ≤ N :=
      Polynomial.natDegree_reflect_le.trans
        (max_le le_rfl (natDegree_differentialTest_le N h))
    have hkdeg : (jensenDifferentialTest N k).natDegree ≤ N :=
      Polynomial.natDegree_reflect_le.trans
        (max_le le_rfl (natDegree_differentialTest_le N k))
    have hhback := isPFPolynomial_reflect hh hhdeg
    have hkback := isPFPolynomial_reflect hk hkdeg
    have hback := reflect_reverses_interl_of_pf hk hh hkdeg hhdeg horder
    simpa only [jensenDifferentialTest, Polynomial.reflect_reflect] using
      And.intro hhback (And.intro hkback hback)

/-- Ordered PF preservation through degree `N` is equivalent to the two Jensen
tests being PF in the reversed interlacing order. -/
theorem preservesOrderedPFUpTo_iff_jensenDifferentialTests
    (N : ℕ) (h k : ℝ[X]) :
    PreservesOrderedPFUpTo N h k ↔
      IsPFPolynomial (jensenDifferentialTest N h) ∧
        IsPFPolynomial (jensenDifferentialTest N k) ∧
          Interl (jensenDifferentialTest N k)
            (jensenDifferentialTest N h) := by
  rw [preservesOrderedPFUpTo_iff_differentialTests,
    differentialTests_ordered_iff_jensenDifferentialTests]

/-- Divide the `j`th coefficient by `(N)_j`; on polynomials of degree at
most `N`, this is the inverse of the Jensen normalization. -/
def capNormalizedDifferentialSymbol (N : ℕ) (q : ℝ[X]) : ℝ[X] :=
  diagonalOperator (fun j ↦ ((N.descFactorial j : ℝ)⁻¹)) q

/-- Coefficients of the inverse Jensen normalization. -/
@[simp] theorem coeff_capNormalizedDifferentialSymbol
    (N : ℕ) (q : ℝ[X]) (j : ℕ) :
    (capNormalizedDifferentialSymbol N q).coeff j =
      (N.descFactorial j : ℝ)⁻¹ * q.coeff j := by
  simp [capNormalizedDifferentialSymbol, coeff_diagonalOperator]

/-- Jensen normalization and coefficientwise division by `(N)_j` cancel on
the degree-`N` box. -/
theorem jensenDifferentialTest_capNormalizedDifferentialSymbol
    (N : ℕ) (q : ℝ[X]) (hqdeg : q.natDegree ≤ N) :
    jensenDifferentialTest N (capNormalizedDifferentialSymbol N q) = q := by
  ext j
  by_cases hj : j ≤ N
  · rw [coeff_jensenDifferentialTest_of_le N _ hj,
      coeff_capNormalizedDifferentialSymbol, ← mul_assoc]
    have hfall : (N.descFactorial j : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj)
    rw [mul_inv_cancel₀ hfall, one_mul]
  · have hjN : N < j := Nat.lt_of_not_ge hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hqdeg.trans_lt hjN)]
    exact (Polynomial.natDegree_reflect_le.trans
      (max_le le_rfl (natDegree_differentialTest_le N _))).trans_lt hjN

/-- Any PF pair in reversed Jensen order gives a finite-cap companion pair
after coefficientwise division by falling factorials. -/
theorem preservesOrderedPFUpTo_capNormalizedDifferentialSymbol
    {N : ℕ} {q r : ℝ[X]}
    (hqdeg : q.natDegree ≤ N) (hrdeg : r.natDegree ≤ N)
    (hq : IsPFPolynomial q) (hr : IsPFPolynomial r)
    (horder : Interl r q) :
    PreservesOrderedPFUpTo N
      (capNormalizedDifferentialSymbol N q)
      (capNormalizedDifferentialSymbol N r) := by
  apply (preservesOrderedPFUpTo_iff_jensenDifferentialTests N _ _).mpr
  rw [jensenDifferentialTest_capNormalizedDifferentialSymbol N q hqdeg,
    jensenDifferentialTest_capNormalizedDifferentialSymbol N r hrdeg]
  exact ⟨hq, hr, horder⟩

/-- The explicit order-`r` symbol whose Jensen polynomial is
`(1 + s X) ^ r`. -/
def binomialDifferentialSymbol (N r : ℕ) (s : ℝ) : ℝ[X] :=
  capNormalizedDifferentialSymbol N ((C s * X + 1) ^ r)

private theorem coeff_C_mul_X_pow_mul_natCast
    (a : ℝ) (i j n : ℕ) :
    (C a * X ^ i * (n : ℝ[X])).coeff j =
      if j = i then a * n else 0 := by
  rw [show (n : ℝ[X]) = C (n : ℝ) by norm_num]
  rw [show C a * X ^ i * C (n : ℝ) = C (a * n) * X ^ i by
    calc
      C a * X ^ i * C (n : ℝ) = (C a * C (n : ℝ)) * X ^ i := by ring
      _ = C (a * n) * X ^ i := by rw [C_mul]]
  rw [Polynomial.coeff_C_mul_X_pow]

private theorem coeff_C_mul_X_add_one_pow (r j : ℕ) (s : ℝ) :
    ((C s * X + 1) ^ r : ℝ[X]).coeff j =
      (r.choose j : ℝ) * s ^ j := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  by_cases hj : j ≤ r
  · rw [Finset.sum_eq_single j]
    · simp only [mul_pow, one_pow, mul_one]
      rw [← map_pow, coeff_C_mul_X_pow_mul_natCast]
      simp
      ring
    · intro i hi hij
      simp only [mul_pow, one_pow, mul_one]
      rw [← map_pow, coeff_C_mul_X_pow_mul_natCast]
      simp [hij.symm]
    · simp [hj]
  · rw [Finset.sum_eq_zero]
    · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)]
    · intro i hi
      simp only [mul_pow, one_pow, mul_one]
      have hij : j ≠ i := by
        have hir : i ≤ r := by simpa using Finset.mem_range.mp hi
        lia
      rw [← map_pow, coeff_C_mul_X_pow_mul_natCast]
      simp [hij]

/-- The coefficient formula for the explicit higher-order differential
symbol. -/
theorem coeff_binomialDifferentialSymbol
    (N r : ℕ) (s : ℝ) (j : ℕ) :
    (binomialDifferentialSymbol N r s).coeff j =
      (N.descFactorial j : ℝ)⁻¹ * (r.choose j : ℝ) * s ^ j := by
  rw [binomialDifferentialSymbol, coeff_capNormalizedDifferentialSymbol,
    coeff_C_mul_X_add_one_pow]
  ring

private theorem natDegree_C_mul_X_add_one_pow_le (r : ℕ) (s : ℝ) :
    ((C s * X + 1) ^ r : ℝ[X]).natDegree ≤ r := by
  have hlin : (C s * X + 1 : ℝ[X]).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have hpow : ((C s * X + 1) ^ r : ℝ[X]).natDegree ≤
      r * (C s * X + 1 : ℝ[X]).natDegree :=
    Polynomial.natDegree_pow_le
  exact hpow.trans (by
    simpa using Nat.mul_le_mul_left r hlin)

/-- The Jensen polynomial of the explicit order-`r` symbol is exactly
`(1 + s X) ^ r`. -/
theorem jensenDifferentialTest_binomialDifferentialSymbol
    {N r : ℕ} (s : ℝ) (hrN : r ≤ N) :
    jensenDifferentialTest N (binomialDifferentialSymbol N r s) =
      (C s * X + 1) ^ r := by
  exact jensenDifferentialTest_capNormalizedDifferentialSymbol N _
    ((natDegree_C_mul_X_add_one_pow_le r s).trans hrN)

private theorem reflect_one_C_mul_X_add_one (s : ℝ) :
    reflect 1 (C s * X + 1 : ℝ[X]) = X + C s := by
  rw [show (C s * X + 1 : ℝ[X]) = C s * X ^ 1 + C 1 * X ^ 0 by simp,
    Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  simp [Polynomial.revAt_le, add_comm]

private theorem reflect_C_mul_X_add_one_pow (s : ℝ) (r : ℕ) :
    reflect r ((C s * X + 1) ^ r : ℝ[X]) = (X + C s) ^ r := by
  induction r with
  | zero => simp [Polynomial.reflect_one]
  | succ r ih =>
      have hlin : (C s * X + 1 : ℝ[X]).natDegree ≤ 1 := by
        simpa using natDegree_C_mul_X_add_one_pow_le 1 s
      rw [pow_succ', show r + 1 = 1 + r by lia,
        Polynomial.reflect_mul (C s * X + 1) ((C s * X + 1) ^ r)
          hlin
          (natDegree_C_mul_X_add_one_pow_le r s),
        reflect_one_C_mul_X_add_one, ih, show 1 + r = r + 1 by lia, pow_succ]
      ring

private theorem reflect_C_mul_X_add_one_pow_at_cap
    {N r : ℕ} (s : ℝ) (hrN : r ≤ N) :
    reflect N ((C s * X + 1) ^ r : ℝ[X]) =
      X ^ (N - r) * (X + C s) ^ r := by
  calc
    reflect N ((C s * X + 1) ^ r : ℝ[X]) =
        reflect (r + (N - r)) (((C s * X + 1) ^ r) * 1) := by
          rw [Nat.add_sub_of_le hrN, mul_one]
    _ = reflect r ((C s * X + 1) ^ r) * reflect (N - r) 1 := by
      rw [Polynomial.reflect_mul _ _
        (natDegree_C_mul_X_add_one_pow_le r s) (by simp)]
    _ = X ^ (N - r) * (X + C s) ^ r := by
      rw [reflect_C_mul_X_add_one_pow, Polynomial.reflect_one]
      ring

/-- The monomial image of the explicit higher-order symbol is
`X ^ (N - r) * (X + s) ^ r`. -/
theorem differentialTest_binomialDifferentialSymbol
    {N r : ℕ} (s : ℝ) (hrN : r ≤ N) :
    differentialTest N (binomialDifferentialSymbol N r s) =
      X ^ (N - r) * (X + C s) ^ r := by
  have h := congrArg (reflect N)
    (jensenDifferentialTest_binomialDifferentialSymbol s hrN)
  simpa only [jensenDifferentialTest, Polynomial.reflect_reflect,
    reflect_C_mul_X_add_one_pow_at_cap s hrN] using h

private theorem isPFPolynomial_C_mul_X_add_one {s : ℝ} (hs : 0 ≤ s) :
    IsPFPolynomial (C s * X + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa using IsPFPolynomial.one
  have hfactor : (C s * X + 1 : ℝ[X]) = C s * (X + C s⁻¹) := by
    rw [mul_add, ← C_mul]
    simp [hs.ne']
  rw [hfactor]
  exact (isPFPolynomial_X_add_C (inv_nonneg.mpr hs.le)).const_mul hs

private theorem interl_binomialJensen_consecutive
    {r : ℕ} {s : ℝ} (hr : 1 ≤ r) (hs : 0 ≤ s) :
    Interl ((C s * X + 1) ^ (r - 1)) ((C s * X + 1) ^ r) := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa using IsPFPolynomial.one.interl_self
  have hstep := (interlaces_linear_pow 1 s hs (r - 1)).toStrictInterl.toInterl
  simpa [Nat.sub_add_cancel hr, add_comm] using hstep

/-- Consecutive members of the explicit higher-order family give ordered PF
images of every PF input in the degree-`N` box. -/
theorem preservesOrderedPFUpTo_binomialDifferentialSymbol
    {N r : ℕ} {s : ℝ} (hr : 1 ≤ r) (hrN : r ≤ N) (hs : 0 ≤ s) :
    PreservesOrderedPFUpTo N (binomialDifferentialSymbol N r s)
      (binomialDifferentialSymbol N (r - 1) s) := by
  apply (preservesOrderedPFUpTo_iff_jensenDifferentialTests N _ _).mpr
  rw [jensenDifferentialTest_binomialDifferentialSymbol s hrN,
    jensenDifferentialTest_binomialDifferentialSymbol s (by lia : r - 1 ≤ N)]
  exact ⟨(isPFPolynomial_C_mul_X_add_one hs).pow r,
    (isPFPolynomial_C_mul_X_add_one hs).pow (r - 1),
    interl_binomialJensen_consecutive hr hs⟩

/-- The explicit higher-order recurrence row is PF and is preceded by its
order-`r` differential image on every input in the cap. -/
theorem binomialDifferentialRecurrence_pf_and_interl
    {N r : ℕ} {s a : ℝ} (hr : 1 ≤ r) (hrN : r ≤ N)
    (hs : 0 ≤ s) (ha : 0 ≤ a) {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hpdeg : p.natDegree ≤ N) :
    IsPFPolynomial
        (X * applyAsDifferentialOperator
            (binomialDifferentialSymbol N r s) p +
          C a * applyAsDifferentialOperator
            (binomialDifferentialSymbol N (r - 1) s) p) ∧
      Interl
        (applyAsDifferentialOperator (binomialDifferentialSymbol N r s) p)
        (X * applyAsDifferentialOperator
            (binomialDifferentialSymbol N r s) p +
          C a * applyAsDifferentialOperator
            (binomialDifferentialSymbol N (r - 1) s) p) := by
  obtain ⟨hh, hk, horder⟩ :=
    preservesOrderedPFUpTo_binomialDifferentialSymbol hr hrN hs hp hpdeg
  exact ⟨isPFPolynomial_X_mul_add_C_mul hh hk horder ha,
    interl_X_mul_add_C_mul hh hk horder ha⟩

private theorem natDegree_applyAsDifferentialOperator_le (h p : ℝ[X]) :
    (applyAsDifferentialOperator h p).natDegree ≤ p.natDegree := by
  rw [applyAsDifferentialOperator]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_iterate_derivative p j).trans (Nat.sub_le _ _))

private theorem applyAsDifferentialOperator_ne_zero_of_coeff_zero_eq_one
    {h p : ℝ[X]} (hzero : h.coeff 0 = 1) (hp0 : p ≠ 0) :
    applyAsDifferentialOperator h p ≠ 0 := by
  intro houtput
  have htop := congrArg (fun q : ℝ[X] ↦ q.coeff p.natDegree) houtput
  rw [coeff_applyAsDifferentialOperator_natDegree, hzero, one_mul,
    Polynomial.coeff_zero] at htop
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp0) (by
    simpa [Polynomial.coeff_natDegree] using htop)

private theorem natDegree_applyAsDifferentialOperator_of_coeff_zero_eq_one
    {h p : ℝ[X]} (hzero : h.coeff 0 = 1) (hp0 : p ≠ 0) :
    (applyAsDifferentialOperator h p).natDegree = p.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_applyAsDifferentialOperator_le h p
  · rw [coeff_applyAsDifferentialOperator_natDegree, hzero, one_mul,
      Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0

/-- On a nonzero input, the explicit higher-order recurrence increases the
degree by exactly one. -/
theorem natDegree_binomialDifferentialRecurrence
    {N r : ℕ} {s a : ℝ} {p : ℝ[X]} (hp0 : p ≠ 0) :
    (X * applyAsDifferentialOperator
          (binomialDifferentialSymbol N r s) p +
        C a * applyAsDifferentialOperator
          (binomialDifferentialSymbol N (r - 1) s) p).natDegree =
      p.natDegree + 1 := by
  have hzero : (binomialDifferentialSymbol N r s).coeff 0 = 1 := by
    rw [coeff_binomialDifferentialSymbol]
    simp
  have hmain0 :=
    applyAsDifferentialOperator_ne_zero_of_coeff_zero_eq_one hzero hp0
  have hmainDegree :=
    natDegree_applyAsDifferentialOperator_of_coeff_zero_eq_one hzero hp0
  have hleftDegree :
      (X * applyAsDifferentialOperator
        (binomialDifferentialSymbol N r s) p).natDegree =
          p.natDegree + 1 := by
    rw [Polynomial.natDegree_X_mul hmain0, hmainDegree]
  have hrightDegree :
      (C a * applyAsDifferentialOperator
        (binomialDifferentialSymbol N (r - 1) s) p).natDegree ≤
          p.natDegree :=
    (Polynomial.natDegree_C_mul_le _ _).trans
      (natDegree_applyAsDifferentialOperator_le _ _)
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
    (hrightDegree.trans_lt (by rw [hleftDegree]; lia)), hleftDegree]

end RealRooted.FiniteDegreeOrdered
