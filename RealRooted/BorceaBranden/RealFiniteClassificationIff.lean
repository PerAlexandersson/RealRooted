module

import Mathlib.Data.FunLike.Fintype
import RealRooted.BorceaBranden.RealFiniteHomotopy
import RealRooted.BorceaBranden.RealFiniteNecessity
public import RealRooted.BorceaBranden.RealFiniteClassification
public import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol

@[expose] public section

open scoped BigOperators

noncomputable section

namespace RealRooted
namespace BorceaBranden

/-- The ring endomorphism of `MvPolynomial σ R` negating every variable, `X i ↦ -X i`. -/
def negVariablesHom {σ R : Type*} [CommRing R] :
    MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i => -MvPolynomial.X i

@[simp]
private theorem negVariablesHom_C {σ R : Type*} [CommRing R] (r : R) :
    negVariablesHom (σ := σ) (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [negVariablesHom]

@[simp]
private theorem negVariablesHom_X {σ R : Type*} [CommRing R] (i : σ) :
    negVariablesHom (R := R) (MvPolynomial.X i) = -MvPolynomial.X i := by
  simp [negVariablesHom]

private theorem eval_negVariablesHom {σ : Type*}
    (P : MvPolynomial σ ℂ) (z : σ → ℂ) :
    MvPolynomial.eval z (negVariablesHom P) =
      MvPolynomial.eval (fun i => -z i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hP]
      simp

private theorem complexifyMv_negVariablesHom {σ : Type*}
    (P : MvPolynomial σ ℝ) :
    complexifyMv (negVariablesHom P) = negVariablesHom (complexifyMv P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [complexifyMv]
  | add P Q hP hQ =>
      unfold complexifyMv at hP hQ ⊢
      rw [map_add, map_add, map_add, hP, hQ, map_add]
  | mul_X P i hP =>
      unfold complexifyMv at hP ⊢
      rw [map_mul, map_mul, map_mul, hP]
      simp

private theorem eval_complexifyMv_conj {σ : Type*}
    (P : MvPolynomial σ ℝ) (z : σ → ℂ) :
    MvPolynomial.eval z (complexifyMv P) =
      starRingEnd ℂ
        (MvPolynomial.eval (fun i => starRingEnd ℂ (z i)) (complexifyMv P)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [complexifyMv]
  | add P Q hP hQ =>
      unfold complexifyMv at hP hQ ⊢
      rw [map_add, MvPolynomial.eval_add, MvPolynomial.eval_add,
        map_add, hP, hQ]
  | mul_X P i hP =>
      unfold complexifyMv at hP ⊢
      rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
        map_mul, hP]
      simp

private theorem MvRealStable.negVariablesHom {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvRealStable P) :
    MvRealStable (negVariablesHom P) := by
  intro z hz
  rw [complexifyMv_negVariablesHom, eval_negVariablesHom]
  let w : σ → ℂ := fun i => -starRingEnd ℂ (z i)
  have hw : ∀ i, 0 < (w i).im := by
    intro i
    simp only [w, Complex.neg_im, Complex.conj_im, neg_neg]
    exact hz i
  have hne := hP w hw
  have hconj : starRingEnd ℂ
      (MvPolynomial.eval w (complexifyMv P)) ≠ 0 := by
    intro hzero
    apply hne
    have h := congrArg (starRingEnd ℂ) hzero
    simpa using h
  have heval := eval_complexifyMv_conj P (fun i => -z i)
  have hpoint : (fun i => starRingEnd ℂ (-z i)) = w := by
    funext i
    simp [w]
  rw [hpoint] at heval
  rw [heval]
  exact hconj

/-- Simultaneously negate all variables of a real multivariate polynomial. -/
def sourceNegation {σ : Type*} :
    MvPolynomial σ ℝ →+* MvPolynomial σ ℝ :=
  negVariablesHom

/-- Simultaneous source negation multiplies a monomial by its parity sign. -/
theorem sourceNegation_monomial_one {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) :
    sourceNegation (MvPolynomial.monomial m 1) =
      (∏ i, (-1 : ℝ) ^ m i) • MvPolynomial.monomial m 1 := by
  change negVariablesHom (MvPolynomial.monomial m 1) = _
  rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
  rw [map_mul, map_one, one_mul, map_prod]
  simp only [map_pow, negVariablesHom_X]
  have hpow (i : σ) :
      (-MvPolynomial.X i : MvPolynomial σ ℝ) ^ m i =
        ((-1 : ℝ) ^ m i) • MvPolynomial.X i ^ m i := by
    rw [neg_pow, MvPolynomial.smul_eq_C_mul]
    have hone : (-1 : MvPolynomial σ ℝ) = MvPolynomial.C (-1 : ℝ) := by
      simp
    rw [hone, map_pow]
  simp_rw [hpow]
  rw [show (∏ i, ((-1 : ℝ) ^ m i • MvPolynomial.X i ^ m i)) =
      MvPolynomial.C (∏ i, (-1 : ℝ) ^ m i) *
        ∏ i, MvPolynomial.X i ^ m i by
    simp only [MvPolynomial.smul_eq_C_mul, ← map_prod,
      Finset.prod_mul_distrib]]
  simp only [map_one, one_mul, MvPolynomial.smul_eq_C_mul]

/-- Simultaneous source negation preserves real stability. -/
theorem MvRealStable.sourceNegation {σ : Type*}
    {P : MvPolynomial σ ℝ} (hP : MvRealStable P) :
    MvRealStable (sourceNegation P) := by
  change MvRealStable (RealRooted.BorceaBranden.negVariablesHom P)
  exact MvRealStable.negVariablesHom hP

/-- Simultaneous source negation as a real linear map. -/
def sourceNegationLinear {σ : Type*} :
    MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ where
  toFun := sourceNegation
  map_add' p q := by simp
  map_smul' c p := by simp [sourceNegation, Algebra.smul_def]

/-- Simultaneous source negation is an involution. -/
@[simp]
theorem sourceNegation_involutive {σ : Type*} (p : MvPolynomial σ ℝ) :
    sourceNegation (sourceNegation p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sourceNegation, negVariablesHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, sourceNegation, negVariablesHom_X, map_neg, neg_neg]
      change negVariablesHom (negVariablesHom p) = p at hp
      rw [hp]

/-- The sign `(-1) ^ ∑ i, κ i` of the top monomial of the global degree box `κ`. -/
def globalBoxSign {σ : Type*} [Fintype σ] (κ : σ → ℕ) : ℝ :=
  ∏ i, (-1 : ℝ) ^ κ i

/-- The sign `(-1) ^ |m|` of the monomial `m`, where `|m| = ∑ i, m i`. -/
def monomialSign {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) : ℝ :=
  ∏ i, (-1 : ℝ) ^ m i

private theorem complement_sign_eq {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (m : σ →₀ ℕ) (hm : ∀ i, m i ≤ κ i) :
    (∏ i, (-1 : ℝ) ^ (κ i - m i)) =
      globalBoxSign κ * monomialSign m := by
  rw [globalBoxSign, monomialSign, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  have hsquare : ((-1 : ℝ) ^ m i) * ((-1 : ℝ) ^ m i) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ (κ i - m i) =
        (-1 : ℝ) ^ (κ i - m i) * 1 := by ring
    _ = (-1 : ℝ) ^ (κ i - m i) *
        (((-1 : ℝ) ^ m i) * ((-1 : ℝ) ^ m i)) := by rw [hsquare]
    _ = ((-1 : ℝ) ^ (κ i - m i) * (-1 : ℝ) ^ m i) *
        (-1 : ℝ) ^ m i := by ring
    _ = (-1 : ℝ) ^ ((κ i - m i) + m i) * (-1 : ℝ) ^ m i := by
      rw [pow_add]
    _ = (-1 : ℝ) ^ κ i * (-1 : ℝ) ^ m i := by
      rw [Nat.sub_add_cancel (hm i)]

/-- Simultaneous source reflection, normalized so its monomial factor is the
right-complement sign occurring in the negative algebraic symbol. -/
def sourceReflectionDegreeBox {σ : Type*} [Fintype σ] (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ]
      MvPolynomial.degreeOfLE σ ℝ κ :=
  (MvPolynomial.basisDegreeOfLE (R := ℝ) κ).constr ℝ fun m =>
    (globalBoxSign κ * monomialSign m.1) •
      MvPolynomial.basisDegreeOfLE κ m

@[simp]
private theorem sourceReflectionDegreeBox_basis
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    sourceReflectionDegreeBox κ (MvPolynomial.basisDegreeOfLE κ m) =
      (globalBoxSign κ * monomialSign m.1) •
        MvPolynomial.basisDegreeOfLE κ m := by
  simp [sourceReflectionDegreeBox]

/-- Explicit monomial formula for normalized simultaneous source reflection. -/
theorem sourceReflectionDegreeBox_basis_explicit
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    sourceReflectionDegreeBox κ (MvPolynomial.basisDegreeOfLE κ m) =
      ((∏ i, (-1 : ℝ) ^ κ i) * ∏ i, (-1 : ℝ) ^ m.1 i) •
        MvPolynomial.basisDegreeOfLE κ m := by
  rw [sourceReflectionDegreeBox_basis]
  rfl

private theorem negVariablesHom_basisDegreeOfLE
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    negVariablesHom (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m).1 =
      monomialSign m.1 •
        (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m).1 := by
  rw [MvPolynomial.coe_basisDegreeOfLE]
  simpa only [sourceNegation, monomialSign] using sourceNegation_monomial_one m.1

/-- The normalized reflection is a global sign times simultaneous variable
negation. -/
theorem coe_sourceReflectionDegreeBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℝ κ) :
    (sourceReflectionDegreeBox κ p).1 =
      globalBoxSign κ • negVariablesHom p.1 := by
  let lhs : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ :=
    (MvPolynomial.degreeOfLE σ ℝ κ).subtype.comp (sourceReflectionDegreeBox κ)
  let rhs : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ :=
    { toFun := fun q => globalBoxSign κ • negVariablesHom q.1
      map_add' := by
        intro q r
        simp only [Submodule.coe_add, map_add, smul_add]
      map_smul' := by
        intro c q
        simp only [Submodule.coe_smul, RingHom.id_apply, Algebra.smul_def,
          MvPolynomial.algebraMap_eq]
        rw [map_mul, negVariablesHom_C]
        ring }
  have hmaps : lhs = rhs := by
    apply (MvPolynomial.basisDegreeOfLE (R := ℝ) κ).ext
    intro m
    simp only [lhs, rhs, LinearMap.comp_apply, Submodule.coe_subtype,
      sourceReflectionDegreeBox_basis]
    change (globalBoxSign κ * monomialSign m.1) •
        (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m).1 =
      globalBoxSign κ •
        negVariablesHom (MvPolynomial.basisDegreeOfLE (R := ℝ) κ m).1
    rw [negVariablesHom_basisDegreeOfLE]
    simp only [smul_smul]
  exact LinearMap.congr_fun hmaps p

/-- The normalized simultaneous reflection preserves real stability. -/
theorem sourceReflectionDegreeBox_preserves_realStability
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    {p : MvPolynomial.degreeOfLE σ ℝ κ} (hp : MvRealStable p.1) :
    MvRealStable (sourceReflectionDegreeBox κ p).1 := by
  rw [coe_sourceReflectionDegreeBox]
  have hsign : globalBoxSign κ ≠ 0 := by
    unfold globalBoxSign
    positivity
  have hneg := MvRealStable.negVariablesHom hp
  simpa only [MvPolynomial.smul_eq_C_mul] using hneg.C_mul hsign

/-- Precompose a real degree-box operator with normalized simultaneous source
reflection. -/
def sourceReflectedOperator {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ :=
  T.comp (sourceReflectionDegreeBox κ)

private theorem negRightVariablesHom_rename_inl
    {σ τ R : Type*} [CommRing R] (P : MvPolynomial τ R) :
    MvPolynomial.negRightVariablesHom
        (MvPolynomial.rename (Sum.inl : τ → τ ⊕ σ) P) =
      MvPolynomial.rename Sum.inl P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, MvPolynomial.rename_X,
      MvPolynomial.negRightVariablesHom_X_inl, hP]

private theorem negRightVariablesHom_rightComplementMonomial
    {σ τ R : Type*} [CommRing R] [Fintype σ]
    (κ : σ → ℕ) (m : σ →₀ ℕ) :
    MvPolynomial.negRightVariablesHom
        (MvPolynomial.rightComplementMonomial (R := R) (τ := τ) κ m) =
      (∏ i, (-1 : R) ^ (κ i - m i)) •
        MvPolynomial.rightComplementMonomial κ m := by
  unfold MvPolynomial.rightComplementMonomial
  rw [map_prod]
  simp only [map_pow, MvPolynomial.negRightVariablesHom_X_inr]
  have hpow (i : σ) :
      (-MvPolynomial.X (Sum.inr i) : MvPolynomial (τ ⊕ σ) R) ^
          (κ i - m i) =
        ((-1 : R) ^ (κ i - m i)) •
          MvPolynomial.X (Sum.inr i) ^ (κ i - m i) := by
    rw [neg_pow, MvPolynomial.smul_eq_C_mul]
    have hone : (-1 : MvPolynomial (τ ⊕ σ) R) =
        MvPolynomial.C (-1 : R) := by simp
    rw [hone, map_pow]
  simp_rw [hpow]
  simp only [MvPolynomial.smul_eq_C_mul, ← map_prod,
    Finset.prod_mul_distrib]

/-- Source reflection converts the positive algebraic symbol into the
right-sign-reversed algebraic symbol. -/
theorem algebraicSymbol_sourceReflectedOperator
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) :
    MvPolynomial.algebraicSymbol κ (sourceReflectedOperator κ T) =
      MvPolynomial.algebraicSymbolNegRight κ T := by
  classical
  rw [MvPolynomial.algebraicSymbol_eq_sum,
    MvPolynomial.algebraicSymbolNegRight,
    MvPolynomial.algebraicSymbol_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  simp only [sourceReflectedOperator, LinearMap.comp_apply,
    sourceReflectionDegreeBox_basis, map_smul, MvPolynomial.rename_C,
    MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.negRightVariablesHom_C,
    negRightVariablesHom_rename_inl,
    negRightVariablesHom_rightComplementMonomial]
  rw [complement_sign_eq κ m.1 m.2]
  have hC : MvPolynomial.C (globalBoxSign κ) *
      MvPolynomial.C (monomialSign m.1) =
        (MvPolynomial.C (globalBoxSign κ * monomialSign m.1) :
          MvPolynomial (σ ⊕ σ) ℝ) := by
    rw [map_mul]
  rw [hC]
  ring

/-- The normalized simultaneous source reflection is an involution. -/
@[simp]
theorem sourceReflectionDegreeBox_involutive
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (p : MvPolynomial.degreeOfLE σ ℝ κ) :
    sourceReflectionDegreeBox κ (sourceReflectionDegreeBox κ p) = p := by
  let R := sourceReflectionDegreeBox κ
  have hR : R.comp R = LinearMap.id := by
    apply (MvPolynomial.basisDegreeOfLE (R := ℝ) κ).ext
    intro m
    simp only [R, LinearMap.comp_apply, sourceReflectionDegreeBox_basis,
      map_smul, smul_smul, LinearMap.id_apply]
    have sign_sq (e : σ → ℕ) :
        (∏ i, (-1 : ℝ) ^ e i) * ∏ i, (-1 : ℝ) ^ e i = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hglobal : globalBoxSign κ * globalBoxSign κ = 1 := by
      simpa only [globalBoxSign] using sign_sq κ
    have hmono : monomialSign m.1 * monomialSign m.1 = 1 := by
      simpa only [monomialSign] using sign_sq fun i => m.1 i
    rw [show (globalBoxSign κ * monomialSign m.1) *
        (globalBoxSign κ * monomialSign m.1) = 1 by
      rw [show (globalBoxSign κ * monomialSign m.1) *
          (globalBoxSign κ * monomialSign m.1) =
        (globalBoxSign κ * globalBoxSign κ) *
          (monomialSign m.1 * monomialSign m.1) by ring, hglobal, hmono, one_mul]]
    exact one_smul ℝ _
  exact LinearMap.congr_fun hR p

/-- The right-sign-reversed algebraic-symbol branch of Borcea--Brändén,
arXiv:0809.0401, Theorem 1.2 preserves real stability. -/
theorem preservesRealStabilityOnDegreeBox_of_algebraicSymbolNegRight_realStable
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ}
    (hSymbol : MvRealStable (MvPolynomial.algebraicSymbolNegRight κ T)) :
    PreservesRealStabilityOnDegreeBox κ T := by
  have hReflectedSymbol : MvRealStable
      (MvPolynomial.algebraicSymbol κ (sourceReflectedOperator κ T)) := by
    rw [algebraicSymbol_sourceReflectedOperator]
    exact hSymbol
  have hReflected :=
    preservesRealStabilityOnDegreeBox_of_algebraicSymbol_realStable
      hReflectedSymbol
  intro p hp
  have hpReflected := sourceReflectionDegreeBox_preserves_realStability κ hp
  have hout := hReflected (sourceReflectionDegreeBox κ p) hpReflected
  simpa only [sourceReflectedOperator, LinearMap.comp_apply,
    sourceReflectionDegreeBox_involutive] using hout

/-- Borcea--Brändén, arXiv:0809.0401, Theorem 1.2: the unconditional real
finite classification on a coordinate-wise degree box. -/
theorem preservesRealStabilityOnDegreeBox_iff_rankTwo_or_symbol_or_negRight
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℝ κ →ₗ[ℝ] MvPolynomial σ ℝ) :
    PreservesRealStabilityOnDegreeBox κ T ↔
      HasStableRankTwoRepresentation κ T ∨
        MvRealStable (MvPolynomial.algebraicSymbol κ T) ∨
        MvRealStable (MvPolynomial.algebraicSymbolNegRight κ T) := by
  constructor
  · intro hT
    rcases forall_realStableOrZero_or_symbol_or_negRight_of_preserves hT with
      hRange | hSymbol | hNegRight
    · exact Or.inl
        (hasStableRankTwoRepresentation_of_forall_realStableOrZero hRange)
    · exact Or.inr (Or.inl hSymbol)
    · exact Or.inr (Or.inr hNegRight)
  · rintro (hRank | hSymbol | hNegRight)
    · exact hRank.preservesRealStabilityOnDegreeBox
    · exact preservesRealStabilityOnDegreeBox_of_algebraicSymbol_realStable hSymbol
    · exact
        preservesRealStabilityOnDegreeBox_of_algebraicSymbolNegRight_realStable
          hNegRight

end BorceaBranden
end RealRooted
