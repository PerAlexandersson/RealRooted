import RealRooted.BorceaBranden.Applications.BidiagonalSymbol
import RealRooted.HermiteBiehler
import RealRooted.OperatorPreservesInterlacing

/-!
# Real PF consequences of genuine affine finite symbols

This module connects the proved multiaffine Borcea--Branden finite-symbol
theorem to the real `Splits` and `IsPFPolynomial` interfaces.  The symbol
below is the genuine affine algebraic symbol, not the
homogeneous Jensen-pencil interface `finiteSymbolBBStatement` (which is false).
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A real polynomial whose complexification has no upper-half-plane zero
splits over `ℝ`.  A nonreal zero would put either it or its conjugate in the
open upper half-plane. -/
lemma splits_of_complexify_upper_stable {p : ℝ[X]}
    (hstable : IsUpperHalfPlaneStable (complexify p)) : p.Splits := by
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    exact hstable Complex.I (by norm_num) (by simp)
  have hcs : (complexify p).Splits := IsAlgClosed.splits _
  apply Polynomial.Splits.of_splits_map Complex.ofRealHom hcs
  intro z hz
  have hzroot : (complexify p).IsRoot z :=
    (Polynomial.mem_roots (map_ne_zero hp0)).mp hz
  have hzim_nonpos : z.im ≤ 0 := by
    by_contra h
    exact hstable z (lt_of_not_ge h) hzroot
  have hzconjroot : (complexify p).IsRoot (starRingEnd ℂ z) := by
    have hmap := Polynomial.IsRoot.map (f := starRingEnd ℂ) hzroot
    have hcomp : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
      ext r
      exact Complex.conj_ofReal r
    simpa [complexify, Polynomial.map_map, hcomp] using hmap
  have hzim_nonneg : 0 ≤ z.im := by
    by_contra h
    have hcpos : 0 < (starRingEnd ℂ z).im := by
      simpa using (neg_pos.mpr (lt_of_not_ge h))
    exact hstable (starRingEnd ℂ z) hcpos hzconjroot
  have hzim : z.im = 0 := le_antisymm hzim_nonpos hzim_nonneg
  refine ⟨z.re, ?_⟩
  apply Complex.ext
  · simp
  · simp [hzim]

/-- A nonzero split real polynomial complexifies to an upper-half-plane
stable polynomial. -/
lemma complexify_upper_stable_of_splits {p : ℝ[X]}
    (hp : p.Splits) (hp0 : p ≠ 0) :
    IsUpperHalfPlaneStable (complexify p) := by
  intro z hz
  exact eval_complexify_ne_zero_of_splits_of_im_pos hp hp0 hz

namespace BorceaBranden

/-- Complex-linear extension of a real-linear polynomial operator.  This is
defined coefficientwise so that it is available for arbitrary finite-symbol
applications, not only bidiagonal operators. -/
def complexifyLinearMap (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  Polynomial.lsum fun n =>
    { toFun := fun z => C z * complexify (T (X ^ n))
      map_add' := by
        intro z w
        simp [add_mul]
      map_smul' := by
        intro z w
        rw [smul_eq_C_mul]
        simp [mul_assoc] }

@[simp] lemma complexifyLinearMap_monomial
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) (z : ℂ) :
    complexifyLinearMap T (Polynomial.monomial n z) =
      C z * complexify (T (X ^ n)) := by
  simp [complexifyLinearMap]

@[simp] lemma complexifyLinearMap_X_pow
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) :
    complexifyLinearMap T ((X : ℂ[X]) ^ n) = complexify (T ((X : ℝ[X]) ^ n)) := by
  rw [Polynomial.X_pow_eq_monomial, complexifyLinearMap_monomial]
  simp

private lemma complexify_add (p q : ℝ[X]) :
    complexify (p + q) = complexify p + complexify q := by
  unfold complexify
  exact Polynomial.map_add Complex.ofRealHom

private lemma complexify_smul (a : ℝ) (p : ℝ[X]) :
    complexify (a • p) = (a : ℂ) • complexify p := by
  unfold complexify
  exact Polynomial.map_smul Complex.ofRealHom a

private lemma complexify_X_pow_real (n : ℕ) :
    complexify ((X : ℝ[X]) ^ n) = (X : ℂ[X]) ^ n := by
  induction n with
  | zero => simp [complexify]
  | succ n ih =>
      unfold complexify at ih ⊢
      rw [pow_succ, Polynomial.map_mul, ih]
      simp [pow_succ]

lemma complexifyLinearMap_complexify
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (p : ℝ[X]) :
    complexifyLinearMap T (complexify p) = complexify (T p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [complexify_add]
      rw [LinearMap.map_add T]
      rw [complexify_add]
      rw [LinearMap.map_add, hp, hq]
  | monomial n a =>
      rw [show Polynomial.monomial n a = a • (X : ℝ[X]) ^ n by
        rw [Polynomial.X_pow_eq_monomial, Polynomial.smul_monomial]
        simp]
      rw [complexify_smul, LinearMap.map_smul T, complexify_smul,
        LinearMap.map_smul (complexifyLinearMap T), complexify_X_pow_real,
        complexifyLinearMap_X_pow]

private lemma complexPolynomialInFirstMv_complexify (p : ℝ[X]) :
    complexPolynomialInFirstMv (complexify p) =
      MvPolynomial.map Complex.ofRealHom
        (Challenges.BorceaBranden.polynomialInFirstMv p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [complexify_add]
      simpa only [complexPolynomialInFirstMv, Polynomial.eval₂_add,
        Challenges.BorceaBranden.polynomialInFirstMv, map_add] using
        congrArg₂ (· + ·) hp hq
  | monomial n a =>
      unfold complexify complexPolynomialInFirstMv
      simp [Challenges.BorceaBranden.polynomialInFirstMv,
        Polynomial.eval₂_monomial, Polynomial.map_monomial]

/-- The complex finite symbol of the coefficientwise complex extension is the
complexification of the genuine real affine algebraic symbol. -/
theorem complexFiniteAlgebraicSymbol_complexifyLinearMap
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (d : ℕ) :
    complexFiniteAlgebraicSymbol d (complexifyLinearMap T) =
      complexifyMv (Challenges.BorceaBranden.finiteAlgebraicSymbol d T) := by
  classical
  simp only [complexFiniteAlgebraicSymbol,
    Challenges.BorceaBranden.finiteAlgebraicSymbol, complexifyMv, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [map_mul, MvPolynomial.map_C, map_pow,
    complexifyLinearMap_X_pow,
    complexPolynomialInFirstMv_complexify, MvPolynomial.map_X]
  congr 2

/-- The algebraic symbol of the degree-box restriction of the complexified
operator is the renamed complexification of its real finite symbol. -/
theorem algebraicSymbol_complexifyLinearMapDegreeBox
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (d : ℕ) :
    MvPolynomial.algebraicSymbol (fun _ : Fin 1 => d)
        (complexUnivariateDegreeBoxOperator d (complexifyLinearMap T)) =
      MvPolynomial.rename finOneSumEquivFinTwo.symm
        (complexifyMv
          (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)) := by
  have h := congrArg (MvPolynomial.rename finOneSumEquivFinTwo.symm)
    (rename_algebraicSymbol_complexUnivariateDegreeBoxOperator d
      (complexifyLinearMap T))
  rw [complexFiniteAlgebraicSymbol_complexifyLinearMap] at h
  have hcomp : finOneSumEquivFinTwo.symm ∘ finOneSumToFinTwo = id := by
    funext i
    exact finOneSumEquivFinTwo.symm_apply_apply i
  rw [MvPolynomial.rename_rename, hcomp, MvPolynomial.rename_id] at h
  exact h

/-- Finite-symbol stability preservation for an arbitrary real-linear
univariate operator, after restriction to a degree box. -/
theorem complexifyLinearMapDegreeBox_preserves_stability
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (d : ℕ)
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)))
    (f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d))
    (hf : MvUpperHalfPlaneStable f.1) :
    MvUpperHalfPlaneStableOrZero
      (complexUnivariateDegreeBoxOperator d (complexifyLinearMap T) f) := by
  apply finiteSymbol_finOne_preserves_stability d _ ?_ f hf
  rw [algebraicSymbol_complexifyLinearMapDegreeBox]
  exact hSymbol.rename

private lemma complexifyLinearMapDegreeBox_value
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (d : ℕ) (p : ℝ[X])
    (hpdeg : p.natDegree ≤ d) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        simpa [complexify] using hpdeg⟩
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (complexUnivariateDegreeBoxOperator d (complexifyLinearMap T) f) =
      complexify (T p) := by
  simp only [complexUnivariateDegreeBoxOperator, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]
  exact complexifyLinearMap_complexify T p

/-- The unconditional real finite-symbol sufficiency theorem.  Unlike the
challenge `finiteSymbolTheoremStatement`, this is a proof term built from the
formalized multivariate degree-box theorem. -/
theorem linearMap_splits_of_finiteSymbol_stable
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)))
    (hpdeg : p.natDegree ≤ d) (hp : p.Splits) :
    T p = 0 ∨ (T p).Splits := by
  by_cases hp0 : p = 0
  · left
    subst p
    simp
  let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
    ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p), by
      rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
      intro i
      rw [Subsingleton.elim i default,
        MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
      simpa [complexify] using hpdeg⟩
  have hfstable : MvUpperHalfPlaneStable f.1 := by
    apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mp
    exact complexify_upper_stable_of_splits hp hp0
  have hout := complexifyLinearMapDegreeBox_preserves_stability
    T d hSymbol f hfstable
  have hvalue := complexifyLinearMapDegreeBox_value T d p hpdeg
  rcases hout with hzero | hstable
  · left
    have hz := congrArg (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)) hzero
    rw [hvalue] at hz
    simp only [map_zero] at hz
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
    simpa [complexify] using hz
  · right
    apply splits_of_complexify_upper_stable
    have hu : IsUpperHalfPlaneStable
        (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
          (complexUnivariateDegreeBoxOperator d (complexifyLinearMap T) f)) := by
      apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mpr
      rw [AlgEquiv.symm_apply_apply]
      exact hstable
    rw [hvalue] at hu
    exact hu

/-- A stable finite symbol transports the full real-rooted pencil generated
by any two inputs in the degree box.  This is the compatibility-level form of
`linearMap_splits_of_finiteSymbol_stable`: it is stronger than applying that
theorem only to the two endpoints, since every real linear combination is
covered simultaneously. -/
theorem linearMap_allComboRealRooted_of_finiteSymbol_stable
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {d : ℕ} {p q : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)))
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hall : AllComboRealRooted p q) :
    AllComboRealRooted (T p) (T q) := by
  apply allComboRealRooted_map_of_pencil hall
  intro a b hab
  apply linearMap_splits_of_finiteSymbol_stable hSymbol
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le
      ((Polynomial.natDegree_C_mul_le a p).trans hpdeg)
      ((Polynomial.natDegree_C_mul_le b q).trans hqdeg))
  · exact hab.2

/-- Order-insensitive interlacing preservation supplied by a genuine stable
finite symbol.  `Prec0` records the unavoidable possibility that an operator
annihilates an endpoint or reverses the chosen orientation. -/
theorem linearMap_prec0_or_revPrec0_of_finiteSymbol_stable
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {d : ℕ} {p q : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)))
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec p q) :
    Prec0 (T p) (T q) ∨ Prec0 (T q) (T p) := by
  apply prec0_or_revPrec0_of_allComboRealRooted
  exact linearMap_allComboRealRooted_of_finiteSymbol_stable
    hSymbol hpdeg hqdeg (allComboRealRooted_of_prec hpq)

private lemma hermiteBiehlerPolynomial_natDegree_le
    {p q : ℝ[X]} {d : ℕ} (hpdeg : p.natDegree ≤ d)
    (hqdeg : q.natDegree ≤ d) :
    (hermiteBiehlerPolynomial p q).natDegree ≤ d := by
  unfold hermiteBiehlerPolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simpa [complexify] using hpdeg
  · apply Polynomial.natDegree_mul_le.trans
    simpa [complexify] using hqdeg

lemma complexifyLinearMap_hermiteBiehler
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (p q : ℝ[X]) :
    complexifyLinearMap T (hermiteBiehlerPolynomial p q) =
      hermiteBiehlerPolynomial (T p) (T q) := by
  unfold hermiteBiehlerPolynomial
  rw [LinearMap.map_add]
  rw [show C Complex.I * complexify q =
      Complex.I • complexify q by rw [smul_eq_C_mul]]
  rw [LinearMap.map_smul, complexifyLinearMap_complexify,
    complexifyLinearMap_complexify, smul_eq_C_mul]

private lemma complexifyLinearMapDegreeBox_hermiteBiehler_value
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (d : ℕ) (p q : ℝ[X])
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
          (hermiteBiehlerPolynomial p q), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        simpa using
          hermiteBiehlerPolynomial_natDegree_le hpdeg hqdeg⟩
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (complexUnivariateDegreeBoxOperator d (complexifyLinearMap T) f) =
      hermiteBiehlerPolynomial (T p) (T q) := by
  simp only [complexUnivariateDegreeBoxOperator, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]
  exact complexifyLinearMap_hermiteBiehler T p q

/-- A genuine stable finite symbol preserves an oriented interlacing pair for
an arbitrary real-linear operator, provided the nonzero outputs retain
positive leading coefficients. -/
theorem linearMap_prec_of_finiteSymbol_stable
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {d : ℕ} {p q : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d T)))
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec q p)
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpout : HasPosLeadingCoeff (T p))
    (hqout : HasPosLeadingCoeff (T q))
    (hpoutdeg : 1 ≤ (T p).natDegree) :
    Prec (T q) (T p) := by
  let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
    ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
        (hermiteBiehlerPolynomial p q), by
      rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
      intro i
      rw [Subsingleton.elim i default,
        MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
      simpa using
        hermiteBiehlerPolynomial_natDegree_le hpdeg hqdeg⟩
  have hfstable : MvUpperHalfPlaneStable f.1 := by
    apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mp
    exact hermiteBiehlerForwardPos hp hq hpq
  have hout := complexifyLinearMapDegreeBox_preserves_stability
    T d hSymbol f hfstable
  have hvalue := complexifyLinearMapDegreeBox_hermiteBiehler_value
    T d p q hpdeg hqdeg
  rcases hout with hzero | hstable
  · exfalso
    have hz := congrArg (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)) hzero
    rw [hvalue] at hz
    simp only [map_zero] at hz
    apply hpout.ne_zero
    apply Polynomial.ext
    intro k
    have hz' := congrArg (fun r : ℂ[X] => r.coeff k) hz
    have hre := congrArg Complex.re hz'
    simpa [hermiteBiehlerPolynomial, complexify] using hre
  · apply prec_of_stable_general hpout hqout
    · have hu : IsUpperHalfPlaneStable
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
            (complexUnivariateDegreeBoxOperator d (complexifyLinearMap T) f)) := by
        apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mpr
        rw [AlgEquiv.symm_apply_apply]
        exact hstable
      rw [hvalue] at hu
      exact hu
    · exact hpoutdeg

/-- The complex degree-box bidiagonal operator is the complexification of the
real bidiagonal operator on a degree-bounded real input. -/
lemma complexBidiagonalDegreeBox_value
    (alpha beta : ℕ → ℝ) (d : ℕ) (p : ℝ[X])
    (hpdeg : p.natDegree ≤ d) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        simpa [complexify] using hpdeg⟩
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (complexUnivariateDegreeBoxOperator d
          (complexBidiagonalLinearMap alpha beta) f) =
      complexify (bidiagonalOperator alpha beta p) := by
  simp only [complexUnivariateDegreeBoxOperator, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]
  change complexBidiagonalLinearMap alpha beta (complexify p) = _
  apply Polynomial.ext
  intro k
  cases k with
  | zero => simp [complexBidiagonalLinearMap, bidiagonalOperator, complexify]
  | succ k =>
      simp [complexBidiagonalLinearMap, bidiagonalOperator, complexify,
        coeff_X_mul]

/-- The complex degree-box bidiagonal operator commutes with the
Hermite--Biehler combination of two real inputs. -/
lemma complexBidiagonalDegreeBox_hermiteBiehler_value
    (alpha beta : ℕ → ℝ) (d : ℕ) (p q : ℝ[X])
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
          (hermiteBiehlerPolynomial p q), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        simpa using
          hermiteBiehlerPolynomial_natDegree_le hpdeg hqdeg⟩
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (complexUnivariateDegreeBoxOperator d
          (complexBidiagonalLinearMap alpha beta) f) =
      hermiteBiehlerPolynomial
        (bidiagonalOperator alpha beta p)
        (bidiagonalOperator alpha beta q) := by
  simp only [complexUnivariateDegreeBoxOperator, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
      simp [complexBidiagonalLinearMap, bidiagonalOperator,
        hermiteBiehlerPolynomial, complexify]
      ring
  | succ k =>
      simp [complexBidiagonalLinearMap, bidiagonalOperator,
        hermiteBiehlerPolynomial, complexify, coeff_X_mul]
      ring

/-- A stable genuine affine algebraic symbol makes the associated real
bidiagonal operator preserve splitness up to the zero output. -/
theorem bidiagonalOperator_splits_of_affineSymbol_stable
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (hpdeg : p.natDegree ≤ d) (hp : p.Splits) :
    bidiagonalOperator alpha beta p = 0 ∨
      (bidiagonalOperator alpha beta p).Splits := by
  by_cases hp0 : p = 0
  · left
    subst p
    simp [bidiagonalOperator]
  let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
    ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p), by
      rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
      intro i
      rw [Subsingleton.elim i default,
        MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
      simpa [complexify] using hpdeg⟩
  have hfstable : MvUpperHalfPlaneStable f.1 := by
    apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mp
    exact complexify_upper_stable_of_splits hp hp0
  have hout := complexBidiagonalDegreeBox_preserves_stability
    alpha beta d hSymbol f hfstable
  have hvalue := complexBidiagonalDegreeBox_value alpha beta d p hpdeg
  rcases hout with hzero | hstable
  · left
    have hz := congrArg (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)) hzero
    rw [hvalue] at hz
    simp only [map_zero] at hz
    apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
    simpa [complexify] using hz
  · right
    apply splits_of_complexify_upper_stable
    have hu : IsUpperHalfPlaneStable
        (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
          (complexUnivariateDegreeBoxOperator d
            (complexBidiagonalLinearMap alpha beta) f)) := by
      apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mpr
      rw [AlgEquiv.symm_apply_apply]
      exact hstable
    rw [hvalue] at hu
    exact hu

/-- With nonnegative bidiagonal coefficients, affine-symbol stability gives a
PF-preserving operator on the chosen degree box. -/
theorem bidiagonalOperator_isPF_of_affineSymbol_stable
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (halpha : ∀ k, 0 ≤ alpha k) (hbeta : ∀ k, 0 ≤ beta k)
    (hpdeg : p.natDegree ≤ d) (hp : IsPFPolynomial p) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) := by
  by_cases hp0 : p = 0
  · subst p
    simpa [bidiagonalOperator] using IsPFPolynomial.zero
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact hp.hasNonnegCoeffs.bidiagonalOperator halpha hbeta
  · rcases bidiagonalOperator_splits_of_affineSymbol_stable
        hSymbol hpdeg (hp.eq_zero_or_splits.resolve_left hp0) with hzero | hsplits
    · simp [hzero]
    · exact hsplits

/-- A genuine stable affine symbol preserves an oriented interlacing pair,
provided the two nonzero outputs have positive leading coefficients.  This is
the real Hermite--Biehler consequence of complex stability preservation. -/
theorem bidiagonalOperator_prec_of_affineSymbol_stable
    {alpha beta : ℕ → ℝ} {d : ℕ} {p q : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec q p)
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpout : HasPosLeadingCoeff (bidiagonalOperator alpha beta p))
    (hqout : HasPosLeadingCoeff (bidiagonalOperator alpha beta q))
    (hpoutdeg : 1 ≤ (bidiagonalOperator alpha beta p).natDegree) :
    Prec (bidiagonalOperator alpha beta q)
      (bidiagonalOperator alpha beta p) := by
  let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
    ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
        (hermiteBiehlerPolynomial p q), by
      rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
      intro i
      rw [Subsingleton.elim i default,
        MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
      simpa using
        hermiteBiehlerPolynomial_natDegree_le hpdeg hqdeg⟩
  have hfstable : MvUpperHalfPlaneStable f.1 := by
    apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mp
    exact hermiteBiehlerForwardPos hp hq hpq
  have hout := complexBidiagonalDegreeBox_preserves_stability
    alpha beta d hSymbol f hfstable
  have hvalue := complexBidiagonalDegreeBox_hermiteBiehler_value
    alpha beta d p q hpdeg hqdeg
  rcases hout with hzero | hstable
  · exfalso
    have hz := congrArg (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)) hzero
    rw [hvalue] at hz
    simp only [map_zero] at hz
    apply hpout.ne_zero
    apply Polynomial.ext
    intro k
    have hz' := congrArg (fun r : ℂ[X] => r.coeff k) hz
    have hre := congrArg Complex.re hz'
    simpa [hermiteBiehlerPolynomial, complexify] using hre
  · apply prec_of_stable_general hpout hqout
    · have hu : IsUpperHalfPlaneStable
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
            (complexUnivariateDegreeBoxOperator d
              (complexBidiagonalLinearMap alpha beta) f)) := by
        apply (isUpperHalfPlaneStable_iff_mvUpperHalfPlaneStable _).mpr
        rw [AlgEquiv.symm_apply_apply]
        exact hstable
      rw [hvalue] at hu
      exact hu
    · exact hpoutdeg

end BorceaBranden

end RealRooted
