module

public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
public import RealRooted.BorceaBranden.RealFiniteClassification
public import RealRooted.FiniteFreeAdditive
public import RealRooted.LiebSokalOperator
public import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
public import RealRooted.MultivariateStability

import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol.Interlacing
import RealRooted.BorceaBranden.RealFiniteSymbolSufficiency
import RealRooted.FiniteFreeAdditive.RootWindow
import RealRooted.HermiteBiehler.Basic
import RealRooted.Mathlib.Algebra.MvPolynomial.EvalOnVars
import RealRooted.Mathlib.Algebra.MvPolynomial.Equiv
import RealRooted.MultivariateStability.LinearForm
import RealRooted.ObreschkoffConverse.DegreeGap

/-!
# Stability and interlacing for finite-free additive convolution

This file proves the lower-degree normalization for finite-free additive convolution and
develops its stability and interlacing consequences.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The normalized derivative which lowers a degree-`D` convolution factor to degree `m`. -/
def finiteFreeAdditiveDerivativeNormalization (D m : ℕ) (g : ℝ[X]) : ℝ[X] :=
  C ((m.factorial : ℝ) / D.factorial) * derivative^[D - m] g

private theorem normalization_differential_coefficient
    {D m i : ℕ} (hmD : m ≤ D) (him : i ≤ m) (g : ℝ[X]) :
    ((m - i).factorial : ℝ) / m.factorial *
        (finiteFreeAdditiveDerivativeNormalization D m g).coeff (m - i) =
      ((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i) := by
  rw [finiteFreeAdditiveDerivativeNormalization, coeff_C_mul,
    coeff_iterate_derivative]
  simp only [nsmul_eq_mul]
  have hindex : m - i + (D - m) = D - i := by lia
  rw [hindex]
  have hfactor := Nat.factorial_mul_descFactorial
    (n := D - i) (k := D - m) (by lia)
  have hsub : D - i - (D - m) = m - i := by lia
  rw [hsub] at hfactor
  have hfactorReal :
      (((m - i).factorial : ℕ) : ℝ) * (D - i).descFactorial (D - m) =
        ((D - i).factorial : ℕ) := by
    exact_mod_cast hfactor
  have hmfac : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hDfac : ((D.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← hfactorReal]
  ring

/-- Lower-degree normalization for finite-free additive convolution. If the first input has
degree at most `m ≤ D`, then the ambient degree can be lowered to `m` after replacing the
second input by its normalized `(D - m)`th derivative. -/
theorem finiteFreeAdditiveConvolution_eq_lowerDegree
    {D m : ℕ} (hmD : m ≤ D) {f : ℝ[X]} (hf : f.natDegree ≤ m) (g : ℝ[X]) :
    finiteFreeAdditiveConvolution D f g =
      finiteFreeAdditiveConvolution m f
        (finiteFreeAdditiveDerivativeNormalization D m g) := by
  rw [finiteFreeAdditiveConvolution_comm D,
    finiteFreeAdditiveConvolution_eq_sum_iterate_derivative D g (hf.trans hmD),
    finiteFreeAdditiveConvolution_comm m,
    finiteFreeAdditiveConvolution_eq_sum_iterate_derivative m
      (finiteFreeAdditiveDerivativeNormalization D m g) hf]
  let term : ℕ → ℝ[X] := fun i =>
    C (((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
      derivative^[i] f
  calc
    ∑ i ∈ Finset.range (D + 1),
          C (((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
            derivative^[i] f =
        ∑ i ∈ Finset.range (m + 1), term i := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by lia))
      intro i hiD him
      have hmi : m < i := by simpa using him
      dsimp [term]
      rw [iterate_derivative_eq_zero (hf.trans_lt hmi), mul_zero]
    _ = ∑ i ∈ Finset.range (m + 1),
          C (((m - i).factorial : ℝ) / m.factorial *
              (finiteFreeAdditiveDerivativeNormalization D m g).coeff (m - i)) *
            derivative^[i] f := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [term]
      rw [normalization_differential_coefficient hmD
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- The normalized derivative of a degree-`D` nonzero polynomial has degree `m`. -/
theorem natDegree_finiteFreeAdditiveDerivativeNormalization
    {D m : ℕ} (hmD : m ≤ D) {g : ℝ[X]} (hg : g ≠ 0)
    (hgdeg : g.natDegree = D) :
    (finiteFreeAdditiveDerivativeNormalization D m g).natDegree = m := by
  have hscale : ((m.factorial : ℝ) / D.factorial) ≠ 0 := by positivity
  rw [finiteFreeAdditiveDerivativeNormalization, natDegree_C_mul hscale,
    natDegree_iterate_derivative_eq_sub hg (by lia), hgdeg]
  lia

/-- The normalized derivative of a monic degree-`D` polynomial is monic of degree `m`. -/
theorem finiteFreeAdditiveDerivativeNormalization_monic
    {D m : ℕ} (hmD : m ≤ D) {g : ℝ[X]} (hg : g.Monic)
    (hgdeg : g.natDegree = D) :
    (finiteFreeAdditiveDerivativeNormalization D m g).Monic := by
  change (finiteFreeAdditiveDerivativeNormalization D m g).leadingCoeff = 1
  rw [leadingCoeff,
    natDegree_finiteFreeAdditiveDerivativeNormalization hmD hg.ne_zero hgdeg]
  have hcoeff := normalization_differential_coefficient hmD (show 0 ≤ m by lia) g
  simp only [Nat.sub_zero] at hcoeff
  rw [div_self (by positivity : (m.factorial : ℝ) ≠ 0), one_mul,
    div_self (by positivity : (D.factorial : ℝ) ≠ 0), one_mul] at hcoeff
  rw [hcoeff]
  simpa [← hgdeg] using hg.coeff_natDegree

/-- Convolution by a monic degree-`D` factor preserves the degree of every nonzero input in
the degree box. -/
theorem natDegree_finiteFreeAdditiveConvolution_right_eq
    {D : ℕ} {f g : ℝ[X]} (hfdeg : f.natDegree ≤ D) (hf : f ≠ 0)
    (hg : g.Monic) (hgdeg : g.natDegree = D) :
    (finiteFreeAdditiveConvolution D f g).natDegree = f.natDegree := by
  let m := f.natDegree
  have hnorm := finiteFreeAdditiveDerivativeNormalization_monic
    (D := D) (m := m) hfdeg hg hgdeg
  have hnormDegree := natDegree_finiteFreeAdditiveDerivativeNormalization
    (D := D) (m := m) hfdeg hg.ne_zero hgdeg
  rw [finiteFreeAdditiveConvolution_eq_lowerDegree hfdeg le_rfl]
  exact natDegree_finiteFreeAdditiveConvolution_eq m rfl
    (by simpa [m] using hnormDegree) hf hnorm.ne_zero

/-- Convolution by a monic degree-`D` factor preserves the leading coefficient of every
nonzero input in the degree box. -/
theorem leadingCoeff_finiteFreeAdditiveConvolution_right
    {D : ℕ} {f g : ℝ[X]} (hfdeg : f.natDegree ≤ D) (hf : f ≠ 0)
    (hg : g.Monic) (hgdeg : g.natDegree = D) :
    (finiteFreeAdditiveConvolution D f g).leadingCoeff = f.leadingCoeff := by
  let m := f.natDegree
  have hnorm := finiteFreeAdditiveDerivativeNormalization_monic
    (D := D) (m := m) hfdeg hg hgdeg
  have hnormDegree := natDegree_finiteFreeAdditiveDerivativeNormalization
    (D := D) (m := m) hfdeg hg.ne_zero hgdeg
  have hnormCoeff :
      (finiteFreeAdditiveDerivativeNormalization D m g).coeff m = 1 := by
    simpa only [hnormDegree] using hnorm.coeff_natDegree
  rw [leadingCoeff, natDegree_finiteFreeAdditiveConvolution_right_eq hfdeg hf hg hgdeg,
    finiteFreeAdditiveConvolution_eq_lowerDegree hfdeg le_rfl,
    coeff_finiteFreeAdditiveConvolution_top, hnormCoeff]
  simp only [mul_one]
  rfl

/-! ### The coordinate operator and its algebraic symbol -/

open scoped BigOperators

private theorem iteratedPDerivAt_smul_real {σ : Type*} (q : σ) (j : ℕ)
    (c : ℝ) (p : MvPolynomial σ ℝ) :
    iteratedPDerivAt q j (c • p) = c • iteratedPDerivAt q j p := by
  rw [← iteratedPDerivAt_eq_pow, ← iteratedPDerivAt_eq_pow]
  exact ((MvPolynomial.pderiv q).toLinearMap ^ j).map_smul c p

/-- Apply convolution by `g` in the coordinate `q`, using the differential formula. -/
def finiteFreeAdditiveConvolutionAt {σ : Type*} (D : ℕ) (g : ℝ[X]) (q : σ)
    (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : Fin (D + 1),
    MvPolynomial.C
        (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
      iteratedPDerivAt q i p

/-- The restriction of coordinate convolution to a coordinate-wise degree box. -/
def finiteFreeAdditiveConvolutionDegreeBox {σ : Type*}
    (D : ℕ) (g : ℝ[X]) (q : σ) (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun p := finiteFreeAdditiveConvolutionAt D g q p.1
  map_add' p r := by
    unfold finiteFreeAdditiveConvolutionAt
    change (∑ i : Fin (D + 1),
        MvPolynomial.C
            (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
          iteratedPDerivAt q i (p.1 + r.1)) =
      (∑ i : Fin (D + 1),
        MvPolynomial.C
            (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
          iteratedPDerivAt q i p.1) +
      ∑ i : Fin (D + 1),
        MvPolynomial.C
            (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
          iteratedPDerivAt q i r.1
    simp only [iteratedPDerivAt_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by
    unfold finiteFreeAdditiveConvolutionAt
    change (∑ i : Fin (D + 1),
        MvPolynomial.C
            (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
          iteratedPDerivAt q i (c • p.1)) =
      c • ∑ i : Fin (D + 1),
        MvPolynomial.C
            (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
          iteratedPDerivAt q i p.1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedPDerivAt_smul_real, MvPolynomial.smul_eq_C_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring_nf

private def realDegreeBoxInclusion {σ : Type*} (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun p := p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem complexification_realDegreeBoxInclusion
    {σ : Type*} (q : σ) (κ : σ → ℕ) :
    BorceaBranden.complexificationDegreeBoxLinearMap κ
        (realDegreeBoxInclusion κ) =
      BorceaBranden.coordinateDiagonalOperatorDegreeBox (fun _ => 1) q κ := by
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) κ).ext
  intro m
  rw [BorceaBranden.complexificationDegreeBoxLinearMap_basis,
    BorceaBranden.coordinateDiagonalOperatorDegreeBox_basis]
  simp [realDegreeBoxInclusion, complexifyMv]

private theorem coordinateJensenSymbol_one_real
    {σ : Type*} (D : ℕ) (q : σ) :
    BorceaBranden.coordinateJensenSymbol D (fun _ => 1) q =
      complexifyMv
        ((MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ D) := by
  unfold BorceaBranden.coordinateJensenSymbol
  rw [add_pow]
  simp only [complexifyMv]
  let term : ℕ → MvPolynomial (σ ⊕ σ) ℂ := fun i =>
    MvPolynomial.C (D.choose i : ℂ) *
      MvPolynomial.X (Sum.inl q) ^ i *
        MvPolynomial.X (Sum.inr q) ^ (D - i)
  simpa [term, mul_comm, mul_left_comm, mul_assoc] using
    Fin.sum_univ_eq_sum_range term (D + 1)

private theorem algebraicSymbol_realDegreeBoxInclusion
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ) (D : ℕ) (κ : σ → ℕ) (hκ : κ q = D) :
    MvPolynomial.algebraicSymbol κ (realDegreeBoxInclusion κ) =
      (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ D *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  change complexifyMv (MvPolynomial.algebraicSymbol κ (realDegreeBoxInclusion κ)) =
    complexifyMv
      ((MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ D *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i)
  rw [← BorceaBranden.algebraicSymbol_complexificationDegreeBoxLinearMap,
    complexification_realDegreeBoxInclusion q]
  rw [BorceaBranden.algebraicSymbol_coordinateDiagonalOperatorDegreeBox
    D (fun _ => 1) q κ hκ]
  rw [BorceaBranden.coordinateDiagonalSymbol, coordinateJensenSymbol_one_real]
  simp only [complexifyMv, map_mul, map_pow, map_add, MvPolynomial.map_X,
    map_prod]
  have he : @Finset.erase σ (Classical.decEq σ) Finset.univ q =
      @Finset.erase σ (inferInstance : DecidableEq σ) Finset.univ q := by
    ext i
    simp
  rw [he]

private def iteratedPDerivAtDegreeBoxReal {σ : Type*}
    (q : σ) (j : ℕ) (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun p := iteratedPDerivAt q j p.1
  map_add' p r := iteratedPDerivAt_add q j p.1 r.1
  map_smul' c p := by
    rw [← iteratedPDerivAt_eq_pow, ← iteratedPDerivAt_eq_pow]
    exact ((MvPolynomial.pderiv q).toLinearMap ^ j).map_smul c p.1

private def pderivAfterReal {σ τ : Type*}
    (q : τ) (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial τ ℝ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial τ ℝ where
  toFun p := MvPolynomial.pderiv q (T p)
  map_add' p r := by rw [T.map_add, map_add]
  map_smul' c p := by
    rw [T.map_smul, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.pderiv_C_mul]
    simp [MvPolynomial.smul_eq_C_mul]

private theorem pderiv_rightComplementMonomial_zero_real
    {σ τ : Type*} [Fintype σ] (q : τ) (κ : σ → ℕ) (d : σ →₀ ℕ) :
    MvPolynomial.pderiv (Sum.inl q)
        (MvPolynomial.rightComplementMonomial (R := ℝ) (τ := τ) κ d) = 0 := by
  rw [MvPolynomial.rightComplementMonomial_eq_prod]
  have hrename :
      (∏ i : σ, (MvPolynomial.X (Sum.inr i) : MvPolynomial (τ ⊕ σ) ℝ) ^
          (κ i - d i)) =
        MvPolynomial.rename (Sum.inr : σ → τ ⊕ σ)
          (∏ i : σ, MvPolynomial.X i ^ (κ i - d i)) := by
    simp only [map_prod, map_pow, MvPolynomial.rename_X]
  rw [hrename]
  exact MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (MvPolynomial.inl_notMem_vars_rename_inr q _)

private theorem algebraicSymbol_pderivAfterReal
    {σ τ : Type*} [Fintype σ] (q : τ) (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial τ ℝ) :
    MvPolynomial.algebraicSymbol κ (pderivAfterReal q κ T) =
      MvPolynomial.pderiv (Sum.inl q) (MvPolynomial.algebraicSymbol κ T) := by
  classical
  rw [MvPolynomial.algebraicSymbol_eq_sum,
    MvPolynomial.algebraicSymbol_eq_sum]
  simp only [pderivAfterReal, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_rename Sum.inl_injective,
    pderiv_rightComplementMonomial_zero_real, zero_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem algebraicSymbol_iteratedPDerivAtDegreeBoxReal
    {σ : Type*} [Fintype σ] (q : σ) (j : ℕ) (κ : σ → ℕ) :
    MvPolynomial.algebraicSymbol κ
        (iteratedPDerivAtDegreeBoxReal q j κ) =
      iteratedPDerivAt (Sum.inl q) j
        (MvPolynomial.algebraicSymbol κ (realDegreeBoxInclusion κ)) := by
  induction j with
  | zero =>
      have hzero : iteratedPDerivAtDegreeBoxReal q 0 κ =
          realDegreeBoxInclusion κ := by
        ext p
        rfl
      rw [hzero]
      rfl
  | succ j ih =>
      have hmap : iteratedPDerivAtDegreeBoxReal q (j + 1) κ =
          pderivAfterReal q κ (iteratedPDerivAtDegreeBoxReal q j κ) := by
        ext p
        rfl
      rw [hmap, algebraicSymbol_pderivAfterReal, ih]
      rfl

private theorem iteratedPDerivAt_linearForm_pow_real {σ : Type*}
    (q r : σ) (hqr : q ≠ r) (j n : ℕ) :
    iteratedPDerivAt q j
        ((MvPolynomial.X q + MvPolynomial.X r : MvPolynomial σ ℝ) ^ n) =
      MvPolynomial.C (n.descFactorial j : ℝ) *
        (MvPolynomial.X q + MvPolynomial.X r) ^ (n - j) := by
  classical
  induction j generalizing n with
  | zero => simp [iteratedPDerivAt]
  | succ j ih =>
      rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, map_add,
        MvPolynomial.pderiv_X_self,
        MvPolynomial.pderiv_X_of_ne (Ne.symm hqr)]
      simp only [add_zero, mul_one, Nat.descFactorial_succ]
      by_cases hjn : j < n
      · rw [← Nat.sub_sub, Nat.cast_mul]
        simp only [map_mul]
        norm_num
        ring_nf
      · have hnj : n ≤ j := Nat.le_of_not_gt hjn
        by_cases hEq : n = j
        · subst n
          simp
        · have hlt : n < j := lt_of_le_of_ne hnj hEq
          simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]

private theorem pderiv_spectatorProduct_zero_real
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ) (κ : σ → ℕ) :
    MvPolynomial.pderiv (Sum.inl q)
        (∏ i ∈ Finset.univ.erase q,
          ((MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ σ) ℝ) +
            MvPolynomial.X (Sum.inr i)) ^ κ i) = 0 := by
  classical
  have hprod : ∀ (s : Finset σ), (∀ i ∈ s, i ≠ q) →
      MvPolynomial.pderiv (Sum.inl q)
        (∏ i ∈ s,
          ((MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ σ) ℝ) +
            MvPolynomial.X (Sum.inr i)) ^ κ i) = 0 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have hiq : i ≠ q := hs i (by simp)
        rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, ih (by simp_all),
          MvPolynomial.pderiv_pow, map_add,
          MvPolynomial.pderiv_X_of_ne (by simpa using hiq),
          MvPolynomial.pderiv_X_of_ne Sum.inr_ne_inl]
        simp
  exact hprod (Finset.univ.erase q) fun i hi => (Finset.mem_erase.mp hi).1

private theorem iteratedPDerivAt_mul_of_pderiv_zero_real {σ : Type*}
    (q : σ) (j : ℕ) (a b : MvPolynomial σ ℝ)
    (hb : MvPolynomial.pderiv q b = 0) :
    iteratedPDerivAt q j (a * b) = iteratedPDerivAt q j a * b := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_mul, hb, mul_zero,
        add_zero, iteratedPDerivAt]

private theorem algebraicSymbol_iteratedPDerivAtDegreeBoxReal_explicit
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ) (j D : ℕ) (κ : σ → ℕ) (hκ : κ q = D) :
    MvPolynomial.algebraicSymbol κ
        (iteratedPDerivAtDegreeBoxReal q j κ) =
      MvPolynomial.C (D.descFactorial j : ℝ) *
          (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ (D - j) *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  rw [algebraicSymbol_iteratedPDerivAtDegreeBoxReal,
    algebraicSymbol_realDegreeBoxInclusion q D κ hκ,
    iteratedPDerivAt_mul_of_pderiv_zero_real]
  · rw [iteratedPDerivAt_linearForm_pow_real (Sum.inl q) (Sum.inr q)
      Sum.inl_ne_inr j D]
  · exact pderiv_spectatorProduct_zero_real q κ

private theorem finiteFreeAdditiveConvolutionDegreeBox_eq_sum_linearMap
    {σ : Type*} (D : ℕ) (g : ℝ[X]) (q : σ) (κ : σ → ℕ) :
    finiteFreeAdditiveConvolutionDegreeBox D g q κ =
      ∑ i : Fin (D + 1),
        (((D - (i : ℕ)).factorial : ℝ) / D.factorial * g.coeff (D - i)) •
          iteratedPDerivAtDegreeBoxReal q i κ := by
  ext p m
  simp only [finiteFreeAdditiveConvolutionDegreeBox,
    finiteFreeAdditiveConvolutionAt, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.coeff_sum, iteratedPDerivAtDegreeBoxReal]

private theorem algebraicSymbol_finiteFreeAdditiveConvolutionDegreeBox_explicit
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ) (D : ℕ) (g : ℝ[X]) (κ : σ → ℕ) (hκ : κ q = D) :
    MvPolynomial.algebraicSymbol κ
        (finiteFreeAdditiveConvolutionDegreeBox D g q κ) =
      (∑ i : Fin (D + 1),
        MvPolynomial.C
            ((((D - (i : ℕ)).factorial : ℝ) / D.factorial *
                g.coeff (D - i)) * D.descFactorial i) *
          (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^
            (D - (i : ℕ))) *
        ∏ j ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j)) ^ κ j := by
  rw [finiteFreeAdditiveConvolutionDegreeBox_eq_sum_linearMap]
  have hsum : ∀ s : Finset (Fin (D + 1)),
      MvPolynomial.algebraicSymbol κ
          (s.sum fun i =>
            (((D - (i : ℕ)).factorial : ℝ) / D.factorial *
              g.coeff (D - i)) • iteratedPDerivAtDegreeBoxReal q i κ) =
        s.sum fun i =>
          MvPolynomial.algebraicSymbol κ
            ((((D - (i : ℕ)).factorial : ℝ) / D.factorial *
              g.coeff (D - i)) • iteratedPDerivAtDegreeBoxReal q i κ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, ih,
        MvPolynomial.algebraicSymbol_add]
  rw [hsum Finset.univ]
  simp_rw [MvPolynomial.algebraicSymbol_smul,
    algebraicSymbol_iteratedPDerivAtDegreeBoxReal_explicit q _ D κ hκ,
    MvPolynomial.smul_eq_C_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [MvPolynomial.C_mul]
  ring

/-- The bivariate factor `g(x_q + y_q)` in the algebraic symbol. -/
def finiteFreeAdditiveConvolutionSymbol {σ : Type*}
    (g : ℝ[X]) (q : σ) : MvPolynomial (σ ⊕ σ) ℝ :=
  g.eval₂ MvPolynomial.C
    (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q))

private theorem finiteFreeAdditive_symbol_sum
    {σ : Type*} (q : σ) (D : ℕ) {g : ℝ[X]} (hgdeg : g.natDegree ≤ D) :
    (∑ i : Fin (D + 1),
      MvPolynomial.C
          ((((D - (i : ℕ)).factorial : ℝ) / D.factorial *
              g.coeff (D - i)) * D.descFactorial i) *
        (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^
          (D - (i : ℕ))) =
      finiteFreeAdditiveConvolutionSymbol g q := by
  let L : MvPolynomial (σ ⊕ σ) ℝ :=
    MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)
  have hcoefficient : ∀ i : Fin (D + 1),
      (((D - (i : ℕ)).factorial : ℝ) / D.factorial *
          g.coeff (D - i)) * D.descFactorial i = g.coeff (D - i) := by
    intro i
    have hi : (i : ℕ) ≤ D := Nat.le_of_lt_succ i.isLt
    have hfactor := Nat.factorial_mul_descFactorial hi
    have hDfac : (D.factorial : ℝ) ≠ 0 := by positivity
    have hfactorReal :
        (((D - (i : ℕ)).factorial : ℕ) : ℝ) * D.descFactorial i =
          (D.factorial : ℕ) := by
      exact_mod_cast hfactor
    calc
      ((D - (i : ℕ)).factorial : ℝ) / D.factorial *
            g.coeff (D - i) * D.descFactorial i =
          (((D - (i : ℕ)).factorial : ℝ) / D.factorial *
            D.descFactorial i) * g.coeff (D - i) := by ring
      _ = g.coeff (D - i) := by
        rw [show ((D - (i : ℕ)).factorial : ℝ) / D.factorial *
            D.descFactorial i = 1 by
          field_simp
          exact hfactorReal]
        simp
  simp_rw [hcoefficient]
  let term : ℕ → MvPolynomial (σ ⊕ σ) ℝ := fun k =>
    MvPolynomial.C (g.coeff k) * L ^ k
  rw [show (∑ i : Fin (D + 1),
      MvPolynomial.C (g.coeff (D - (i : ℕ))) * L ^ (D - (i : ℕ))) =
      ∑ k ∈ Finset.range (D + 1), term k by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => MvPolynomial.C (g.coeff (D - i)) * L ^ (D - i)) (D + 1)]
    rw [← Finset.sum_range_reflect term (D + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [term]]
  rw [← Polynomial.eval₂_eq_sum_range' MvPolynomial.C (by lia) L]
  rfl

/-- The algebraic symbol of coordinate convolution is `g(x_q + y_q)` times the usual
spectator factors. -/
theorem algebraicSymbol_finiteFreeAdditiveConvolutionDegreeBox
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ) (D : ℕ) {g : ℝ[X]} (hgdeg : g.natDegree ≤ D)
    (κ : σ → ℕ) (hκ : κ q = D) :
    MvPolynomial.algebraicSymbol κ
        (finiteFreeAdditiveConvolutionDegreeBox D g q κ) =
      finiteFreeAdditiveConvolutionSymbol g q *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  rw [algebraicSymbol_finiteFreeAdditiveConvolutionDegreeBox_explicit q D g κ hκ,
    finiteFreeAdditive_symbol_sum q D hgdeg]

private theorem finiteFreeAdditiveConvolutionSymbol_realStable
    {σ : Type*} {g : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits) (q : σ) :
    MvRealStable (finiteFreeAdditiveConvolutionSymbol g q) := by
  unfold MvRealStable
  intro z hz hzero
  have hgstable := Polynomial.Splits.isUpperHalfPlaneStable_complexify hgs hg0
  apply hgstable (z (Sum.inl q) + z (Sum.inr q))
  · simpa only [Complex.add_im] using
      add_pos (hz (Sum.inl q)) (hz (Sum.inr q))
  · have hC :
        (MvPolynomial.eval z).comp
            ((MvPolynomial.C : ℂ →+* MvPolynomial (σ ⊕ σ) ℂ).comp
              Complex.ofRealHom) =
          Complex.ofRealHom := by
      ext r
      simp
    simpa [finiteFreeAdditiveConvolutionSymbol, complexifyMv, complexify,
      Polynomial.hom_eval₂, hC, Polynomial.eval_map] using hzero

private theorem mvRealStable_pow {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (n : ℕ) : MvRealStable (P ^ n) := by
  induction n with
  | zero => simpa using (MvRealStable.one (sigma := σ))
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hP

/-- Coordinate convolution by a nonzero split factor preserves real stability on every
degree box whose selected coordinate has degree bound `D`. The output may be zero. -/
theorem finiteFreeAdditiveConvolutionDegreeBox_preservesRealStability
    {σ : Type*} [Finite σ]
    (q : σ) (D : ℕ) {g : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits)
    (hgdeg : g.natDegree ≤ D) (κ : σ → ℕ) (hκ : κ q = D) :
    BorceaBranden.PreservesRealStabilityOnDegreeBox κ
      (finiteFreeAdditiveConvolutionDegreeBox D g q κ) := by
  classical
  let _ := Fintype.ofFinite σ
  apply BorceaBranden.preservesRealStabilityOnDegreeBox_of_algebraicSymbol_realStable
  rw [algebraicSymbol_finiteFreeAdditiveConvolutionDegreeBox q D hgdeg κ hκ]
  apply (finiteFreeAdditiveConvolutionSymbol_realStable hg0 hgs q).mul
  apply MvRealStable.finset_prod
  intro i hi
  exact mvRealStable_pow (MvRealStable.X_add_X (Sum.inl i) (Sum.inr i)) (κ i)

/-- Coordinate convolution preserves real stability with arbitrary spectator variables. Only
the selected coordinate is required to have degree at most `D`; the output may be zero. -/
theorem finiteFreeAdditiveConvolutionAt_realStableOrZero
    {σ : Type*} [Finite σ] (q : σ) (D : ℕ) {g : ℝ[X]}
    (hg0 : g ≠ 0) (hgs : g.Splits) (hgdeg : g.natDegree ≤ D)
    {p : MvPolynomial σ ℝ} (hpq : p.degreeOf q ≤ D) (hp : MvRealStable p) :
    MvRealStableOrZero (finiteFreeAdditiveConvolutionAt D g q p) := by
  classical
  let _ := Fintype.ofFinite σ
  let κ : σ → ℕ := fun i => if i = q then D else p.degreeOf i
  have hκ : κ q = D := by simp [κ]
  have hpκ : p ∈ MvPolynomial.degreeOfLE σ ℝ κ := by
    rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
    intro i
    by_cases hi : i = q
    · simpa [κ, hi] using hpq
    · simp [κ, hi]
  let pκ : MvPolynomial.degreeOfLE σ ℝ κ := ⟨p, hpκ⟩
  exact finiteFreeAdditiveConvolutionDegreeBox_preservesRealStability
    q D hg0 hgs hgdeg κ hκ pκ hp

/-! ### Directed interlacing -/

private theorem finiteFreeAdditiveConvolution_add_left
    (D : ℕ) (f h g : ℝ[X]) :
    finiteFreeAdditiveConvolution D (f + h) g =
      finiteFreeAdditiveConvolution D f g +
        finiteFreeAdditiveConvolution D h g := by
  ext j
  simp only [coeff_add, coeff_finiteFreeAdditiveConvolution]
  split_ifs
  · simp only [finiteFreeAdditiveConvolutionCoeff, coeff_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp

private def finiteFreeAdditiveConvolutionLinearMap
    (D : ℕ) (g : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun f := finiteFreeAdditiveConvolution D f g
  map_add' f h := finiteFreeAdditiveConvolution_add_left D f h g
  map_smul' c f := by
    simpa [smul_eq_C_mul] using
      finiteFreeAdditiveConvolution_C_mul_left D c f g

private theorem uniqueAlgEquiv_pderiv_finOne (p : MvPolynomial (Fin 1) ℝ) :
    MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) (MvPolynomial.pderiv 0 p) =
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p).derivative := by
  ext n
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.coeff_pderiv,
    Polynomial.coeff_derivative, MvPolynomial.coeff_uniqueAlgEquiv]
  congr 2 <;> simp

private theorem uniqueAlgEquiv_iteratedPDerivAt_finOne
    (j : ℕ) (p : MvPolynomial (Fin 1) ℝ) :
    MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) (iteratedPDerivAt 0 j p) =
      (Polynomial.derivative^[j])
        (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      change MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
          (MvPolynomial.pderiv 0 (iteratedPDerivAt 0 j p)) =
        Polynomial.derivative ((Polynomial.derivative^[j])
          (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p))
      rw [uniqueAlgEquiv_pderiv_finOne, ih]

private theorem univariateDegreeBoxOperator_finiteFreeAdditiveConvolution
    (D : ℕ) (g : ℝ[X]) :
    BorceaBranden.univariateDegreeBoxOperator D
        (finiteFreeAdditiveConvolutionLinearMap D g) =
      finiteFreeAdditiveConvolutionDegreeBox D g 0 (fun _ => D) := by
  apply LinearMap.ext
  intro p
  apply (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective
  simp only [BorceaBranden.univariateDegreeBoxOperator,
    finiteFreeAdditiveConvolutionLinearMap,
    finiteFreeAdditiveConvolutionDegreeBox, LinearMap.coe_mk, AddHom.coe_mk,
    AlgEquiv.apply_symm_apply]
  change finiteFreeAdditiveConvolution D
      (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p.1) g =
    MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
      (finiteFreeAdditiveConvolutionAt D g 0 p.1)
  rw [finiteFreeAdditiveConvolution_comm,
    finiteFreeAdditiveConvolution_eq_sum_iterate_derivative D g]
  · unfold finiteFreeAdditiveConvolutionAt
    rw [map_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
        (MvPolynomial.C
            (((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
          iteratedPDerivAt 0 i p.1)) (D + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      C (((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
            (Polynomial.derivative^[i])
              (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p.1) =
          MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
              (MvPolynomial.C
                (((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i))) *
            MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
              (iteratedPDerivAt 0 i p.1) := by
        rw [uniqueAlgEquiv_iteratedPDerivAt_finOne]
        simp
      _ = MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)
            (MvPolynomial.C
                (((D - i).factorial : ℝ) / D.factorial * g.coeff (D - i)) *
              iteratedPDerivAt 0 i p.1) :=
        ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).map_mul _ _).symm
  · rw [show (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p.1).natDegree =
        p.1.degreeOf default by
      simpa only [AlgEquiv.symm_apply_apply] using
        (MvPolynomial.degreeOf_uniqueAlgEquiv_symm (σ := Fin 1)
          (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p.1)).symm]
    exact (MvPolynomial.mem_degreeOfLE_iff_degreeOf p.1).mp p.2 default

private theorem finiteAlgebraicSymbol_finiteFreeAdditiveConvolution_realStable
    {D : ℕ} {g : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits)
    (hgdeg : g.natDegree = D) :
    MvRealStable
      (BorceaBranden.finiteAlgebraicSymbol D
        (finiteFreeAdditiveConvolutionLinearMap D g)) := by
  rw [← BorceaBranden.rename_algebraicSymbol_univariateDegreeBoxOperator,
    univariateDegreeBoxOperator_finiteFreeAdditiveConvolution,
    algebraicSymbol_finiteFreeAdditiveConvolutionDegreeBox 0 D hgdeg.le
      (fun _ => D) rfl]
  simpa using
    (finiteFreeAdditiveConvolutionSymbol_realStable hg0 hgs (0 : Fin 1)).rename
      BorceaBranden.finOneSumToFinTwo

/-- Convolution by a monic split degree-`D` factor preserves directed interlacing in the
zero-aware convention. The inputs may have any degrees at most `D`. -/
theorem interl_finiteFreeAdditiveConvolution_right
    {D : ℕ} {g f h : ℝ[X]} (hg : g.Monic) (hgs : g.Splits)
    (hgdeg : g.natDegree = D) (hfdeg : f.natDegree ≤ D)
    (hhdeg : h.natDegree ≤ D) (hhf : StrictInterl h f)
    (hf : HasPosLeadingCoeff f) (hh : HasPosLeadingCoeff h) :
    Interl (finiteFreeAdditiveConvolution D h g)
      (finiteFreeAdditiveConvolution D f g) := by
  apply BorceaBranden.linearMap_interl_of_finiteSymbol_stable
    (d := D) (T := finiteFreeAdditiveConvolutionLinearMap D g)
  · exact finiteAlgebraicSymbol_finiteFreeAdditiveConvolution_realStable
      hg.ne_zero hgs hgdeg
  · exact hfdeg
  · exact hhdeg
  · exact hhf
  · exact hf
  · exact hh
  · right
    change 0 < (finiteFreeAdditiveConvolution D f g).leadingCoeff
    rw [leadingCoeff_finiteFreeAdditiveConvolution_right hfdeg hf.ne_zero hg hgdeg]
    exact hf
  · right
    change 0 < (finiteFreeAdditiveConvolution D h g).leadingCoeff
    rw [leadingCoeff_finiteFreeAdditiveConvolution_right hhdeg hh.ne_zero hg hgdeg]
    exact hh

/-- In the nonzero `StrictInterl` convention, the same hypotheses give a directed
interlacing pair. Root inequalities in `StrictInterl` remain weak. -/
theorem strictInterl_finiteFreeAdditiveConvolution_right
    {D : ℕ} {g f h : ℝ[X]} (hg : g.Monic) (hgs : g.Splits)
    (hgdeg : g.natDegree = D) (hfdeg : f.natDegree ≤ D)
    (hhdeg : h.natDegree ≤ D) (hhf : StrictInterl h f)
    (hf : HasPosLeadingCoeff f) (hh : HasPosLeadingCoeff h) :
    StrictInterl (finiteFreeAdditiveConvolution D h g)
      (finiteFreeAdditiveConvolution D f g) := by
  apply (interl_finiteFreeAdditiveConvolution_right hg hgs hgdeg hfdeg hhdeg
    hhf hf hh).toStrictInterl_of_ne
  · intro hout
    have hlc := leadingCoeff_finiteFreeAdditiveConvolution_right
      hhdeg hh.ne_zero hg hgdeg
    have hzero : h.leadingCoeff = 0 := by simpa [hout] using hlc.symm
    exact (ne_of_gt hh) hzero
  · intro fout
    have hlc := leadingCoeff_finiteFreeAdditiveConvolution_right
      hfdeg hf.ne_zero hg hgdeg
    have fzero : f.leadingCoeff = 0 := by simpa [fout] using hlc.symm
    exact (ne_of_gt hf) fzero

end

end RealRooted
