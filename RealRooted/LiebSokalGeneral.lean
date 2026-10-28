module

import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier
import RealRooted.DifferentialBlocks
import RealRooted.ElementaryDifferential
import RealRooted.LiebSokal
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.LiebSokalOperator.Linearity
public import RealRooted.LiebSokalOperator
public import RealRooted.MultivariateStability

/-!
# The general Lieb--Sokal theorem

This file removes the multiaffine hypotheses from the constant-coefficient
differential form of the Lieb--Sokal theorem. We rescale by descending
factorials, polarize both inputs in a common degree box, apply the multiaffine
theorem, and identify the polarized differential action on the diagonal.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted

noncomputable section

private theorem iteratedPDerivAt_rename_mul_of_notMem
    {R sigma tau : Type*} [CommRing R]
    (f : sigma → tau) (hf : Function.Injective f)
    (i : sigma) (n : ℕ) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) (hK : f i ∉ K.vars) :
    iteratedPDerivAt (f i) n (MvPolynomial.rename f G * K) =
      MvPolynomial.rename f (iteratedPDerivAt i n G) * K := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iteratedPDerivAt, ih, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_rename hf,
        MvPolynomial.pderiv_eq_zero_of_notMem_vars hK]
      simp

private theorem applyMonomialDifferential_mapDomain_rename_mul
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (f : sigma → tau) (hf : Function.Injective f)
    (d : sigma →₀ ℕ) (G : MvPolynomial sigma R)
    (K : MvPolynomial tau R) (hK : ∀ i, f i ∉ K.vars) :
    applyMonomialDifferential (d.mapDomain f)
        (MvPolynomial.rename f G * K) =
      MvPolynomial.rename f (applyMonomialDifferential d G) * K := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i n d hi hn ih =>
      rw [Finsupp.mapDomain_add, applyMonomialDifferential_comp,
        Finsupp.mapDomain_single, applyMonomialDifferential_single_nat,
        ih, iteratedPDerivAt_rename_mul_of_notMem f hf i n _ K (hK i),
        ← applyMonomialDifferential_single_nat,
        ← applyMonomialDifferential_comp]

private theorem applyNegDifferential_rename_mul
    {R sigma tau : Type*} [CommRing R] [Fintype sigma] [Fintype tau]
    (f : sigma → tau) (hf : Function.Injective f)
    (F G : MvPolynomial sigma R) (K : MvPolynomial tau R)
    (hK : ∀ i, f i ∉ K.vars) :
    applyNegDifferential (MvPolynomial.rename f F)
        (MvPolynomial.rename f G * K) =
      MvPolynomial.rename f (applyNegDifferential F G) * K := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [MvPolynomial.rename_monomial, applyNegDifferential_monomial,
        Finsupp.sum_mapDomain_index_inj hf,
        applyMonomialDifferential_mapDomain_rename_mul f hf d G K hK,
        applyNegDifferential_monomial, map_mul, map_mul,
        MvPolynomial.rename_C]
      have hC :
          (MvPolynomial.C ((-1 : R) ^ (d.sum fun _ n ↦ n)) *
              MvPolynomial.C c : MvPolynomial tau R) =
            MvPolynomial.C (c * (-1 : R) ^ (d.sum fun _ n ↦ n)) := by
        rw [← map_mul]
        congr 1
        ring
      rw [hC]
      ac_rfl
  | add F H hF hH =>
      rw [map_add, applyNegDifferential_add_left, hF, hH,
        applyNegDifferential_add_left, map_add, add_mul]

private theorem notMem_vars_mul
    {R sigma : Type*} [CommRing R] {i : sigma}
    {P Q : MvPolynomial sigma R} (hP : i ∉ P.vars) (hQ : i ∉ Q.vars) :
    i ∉ (P * Q).vars := by
  classical
  exact fun hi => (Finset.mem_union.mp (MvPolynomial.vars_mul P Q hi)).elim hP hQ

private theorem blockEmbedding_injective
    {sigma : Type*} (kappa : sigma → ℕ) (i : sigma) :
    Function.Injective (fun j : Fin (kappa i) ↦
      (⟨i, j⟩ : BorceaBranden.PolarizedSource kappa)) := by
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2

private theorem blockEmbedding_notMem_vars_rename
    {sigma : Type*} (kappa : sigma → ℕ) {i j : sigma}
    (hij : i ≠ j) (x : Fin (kappa i))
    (P : MvPolynomial (Fin (kappa j)) ℂ) :
    (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa) ∉
      (MvPolynomial.rename
        (fun y : Fin (kappa j) ↦
          (⟨j, y⟩ : BorceaBranden.PolarizedSource kappa)) P).vars := by
  intro hx
  obtain ⟨y, _hy, hyx⟩ := MvPolynomial.mem_vars_rename
    (fun y : Fin (kappa j) ↦
      (⟨j, y⟩ : BorceaBranden.PolarizedSource kappa)) P hx
  exact hij (congrArg Sigma.fst hyx).symm

private theorem blockEmbedding_notMem_vars_prod
    {sigma : Type*} (kappa : sigma → ℕ)
    (s : Finset sigma) (P : (i : sigma) → MvPolynomial (Fin (kappa i)) ℂ)
    {i : sigma} (hi : i ∉ s) (x : Fin (kappa i)) :
    (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa) ∉
      (∏ j ∈ s, MvPolynomial.rename
        (fun y : Fin (kappa j) ↦
          (⟨j, y⟩ : BorceaBranden.PolarizedSource kappa)) (P j)).vars := by
  classical
  intro hx
  have hx' := MvPolynomial.vars_prod
    (fun j ↦ MvPolynomial.rename
      (fun y : Fin (kappa j) ↦
        (⟨j, y⟩ : BorceaBranden.PolarizedSource kappa)) (P j)) hx
  simp only [Finset.mem_biUnion] at hx'
  obtain ⟨j, hj, hxj⟩ := hx'
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  exact blockEmbedding_notMem_vars_rename kappa hji.symm x (P j) hxj

private theorem applyNegDifferential_blockProducts
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (s : Finset sigma)
    (F G : (i : sigma) → MvPolynomial (Fin (kappa i)) ℂ)
    (K : MvPolynomial (BorceaBranden.PolarizedSource kappa) ℂ)
    (hK : ∀ i ∈ s, ∀ x : Fin (kappa i),
      (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa) ∉ K.vars) :
    applyNegDifferential
        (∏ i ∈ s, MvPolynomial.rename
          (fun x : Fin (kappa i) ↦
            (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) (F i))
        ((∏ i ∈ s, MvPolynomial.rename
          (fun x : Fin (kappa i) ↦
            (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) (G i)) * K) =
      (∏ i ∈ s, MvPolynomial.rename
        (fun x : Fin (kappa i) ↦
          (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa))
            (applyNegDifferential (F i) (G i))) * K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using applyNegDifferential_C (1 : ℂ) K
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi, applyNegDifferential_mul]
      have hrest (j : sigma) (hj : j ∈ s) (x : Fin (kappa j)) :
          (⟨j, x⟩ : BorceaBranden.PolarizedSource kappa) ∉
            (MvPolynomial.rename
              (fun y : Fin (kappa i) ↦
                (⟨i, y⟩ : BorceaBranden.PolarizedSource kappa)) (G i) * K).vars :=
        notMem_vars_mul
          (blockEmbedding_notMem_vars_rename kappa (by
            intro hji
            subst j
            exact hi hj) x (G i))
          (hK j (Finset.mem_insert_of_mem hj) x)
      rw [show
          MvPolynomial.rename
                (fun x : Fin (kappa i) ↦
                  (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) (G i) *
              (∏ j ∈ s, MvPolynomial.rename
                (fun x : Fin (kappa j) ↦
                  (⟨j, x⟩ : BorceaBranden.PolarizedSource kappa)) (G j)) * K =
            (∏ j ∈ s, MvPolynomial.rename
                (fun x : Fin (kappa j) ↦
                  (⟨j, x⟩ : BorceaBranden.PolarizedSource kappa)) (G j)) *
              (MvPolynomial.rename
                (fun x : Fin (kappa i) ↦
                  (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) (G i) * K) by
            ring,
        ih _ hrest]
      have hiK (x : Fin (kappa i)) :
          (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa) ∉
            ((∏ j ∈ s, MvPolynomial.rename
              (fun y : Fin (kappa j) ↦
                (⟨j, y⟩ : BorceaBranden.PolarizedSource kappa))
                  (applyNegDifferential (F j) (G j))) * K).vars :=
        notMem_vars_mul
          (blockEmbedding_notMem_vars_prod kappa s
            (fun j ↦ applyNegDifferential (F j) (G j)) hi x)
          (hK i (Finset.mem_insert_self i s) x)
      rw [show
          (∏ j ∈ s, MvPolynomial.rename
              (fun x : Fin (kappa j) ↦
                (⟨j, x⟩ : BorceaBranden.PolarizedSource kappa))
                  (applyNegDifferential (F j) (G j))) *
              (MvPolynomial.rename
                (fun x : Fin (kappa i) ↦
                  (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) (G i) * K) =
            MvPolynomial.rename
                (fun x : Fin (kappa i) ↦
                  (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) (G i) *
              ((∏ j ∈ s, MvPolynomial.rename
                (fun x : Fin (kappa j) ↦
                  (⟨j, x⟩ : BorceaBranden.PolarizedSource kappa))
                    (applyNegDifferential (F j) (G j))) * K) by ring,
        applyNegDifferential_rename_mul _
          (blockEmbedding_injective kappa i) (F i) (G i) _ hiK]
      ring

private def descFactorialScale
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (P : MvPolynomial sigma ℂ) : MvPolynomial sigma ℂ :=
  P.coeff.sum fun m a =>
    MvPolynomial.monomial m ((∏ i, (kappa i).descFactorial (m i) : ℕ) * a)

@[simp] private theorem coeff_descFactorialScale
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (P : MvPolynomial sigma ℂ) (m : sigma →₀ ℕ) :
    (descFactorialScale kappa P).coeff m =
      ((∏ i, (kappa i).descFactorial (m i) : ℕ) : ℂ) * P.coeff m := by
  classical
  rw [descFactorialScale, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  by_cases hm : m ∈ P.support
  · simp [hm, MvPolynomial.coeff_monomial]
  · have hcoeff : P.coeff m = 0 := Finsupp.notMem_support_iff.mp hm
    simp [hm, hcoeff, MvPolynomial.coeff_monomial]

private theorem descFactorialScale_mem_degreeOfLE
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (P : MvPolynomial sigma ℂ) :
    descFactorialScale kappa P ∈ MvPolynomial.degreeOfLE sigma ℂ kappa := by
  classical
  rw [MvPolynomial.mem_degreeOfLE]
  intro m hm i
  by_contra hmi
  have hzero : (kappa i).descFactorial (m i) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hmi)
  have hprod : ∏ j, (kappa j).descFactorial (m j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hzero
  have hcoeff := Finsupp.mem_support_iff.mp hm
  rw [coeff_descFactorialScale, hprod, Nat.cast_zero, zero_mul] at hcoeff
  exact hcoeff rfl

private theorem coeff_fold_coordinateDiagonalOperator
    {sigma : Type*} (kappa : sigma → ℕ)
    (l : List sigma) (P : MvPolynomial sigma ℂ) (m : sigma →₀ ℕ) :
    (l.foldl (fun Q i =>
      BorceaBranden.coordinateDiagonalOperator
        (fun k ↦ ((kappa i).descFactorial k : ℝ)) i Q) P).coeff m =
      ((l.map fun i => ((kappa i).descFactorial (m i) : ℂ)).prod) *
        P.coeff m := by
  induction l generalizing P with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih,
        BorceaBranden.coeff_coordinateDiagonalOperator]
      simp only [List.map_cons, List.prod_cons, Complex.ofReal_natCast]
      ring

private theorem descFactorialScale_eq_fold
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (P : MvPolynomial sigma ℂ) :
    descFactorialScale kappa P =
      (differentialVariableOrder sigma).foldl (fun Q i =>
        BorceaBranden.coordinateDiagonalOperator
          (fun k ↦ ((kappa i).descFactorial k : ℝ)) i Q) P := by
  classical
  ext m
  rw [coeff_descFactorialScale,
    coeff_fold_coordinateDiagonalOperator]
  have hprod := List.prod_toFinset
    (fun i => ((kappa i).descFactorial (m i) : ℂ))
    (nodup_differentialVariableOrder sigma)
  have huniv : (differentialVariableOrder sigma).toFinset = Finset.univ := by
    ext i
    simp
  rw [huniv] at hprod
  simp only [Nat.cast_prod]
  rw [hprod]

private theorem coordinateDiagonalOperator_zero
    {sigma : Type*} (gamma : ℕ → ℝ) (i : sigma) :
    BorceaBranden.coordinateDiagonalOperator gamma i
        (0 : MvPolynomial sigma ℂ) = 0 := by
  classical
  ext
  simp

private theorem fold_coordinateDiagonalOperator_zero
    {sigma : Type*} (kappa : sigma → ℕ) (l : List sigma) :
    l.foldl (fun Q i =>
      BorceaBranden.coordinateDiagonalOperator
        (fun k ↦ ((kappa i).descFactorial k : ℝ)) i Q)
      (0 : MvPolynomial sigma ℂ) = 0 := by
  induction l <;> simp_all [coordinateDiagonalOperator_zero]

private theorem fold_coordinateDiagonalOperator_zero_or_stable
    {sigma : Type*} [Finite sigma] (kappa : sigma → ℕ)
    (l : List sigma) {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) :
    l.foldl (fun Q i =>
        BorceaBranden.coordinateDiagonalOperator
          (fun k ↦ ((kappa i).descFactorial k : ℝ)) i Q) P = 0 ∨
      MvUpperHalfPlaneStable
        (l.foldl (fun Q i =>
          BorceaBranden.coordinateDiagonalOperator
            (fun k ↦ ((kappa i).descFactorial k : ℝ)) i Q) P) := by
  induction l generalizing P with
  | nil => exact Or.inr hP
  | cons i l ih =>
      rw [List.foldl_cons]
      have hseq := BorceaBranden.isPFMultiplierSequence_descFactorial (kappa i)
      have hstep :=
        BorceaBranden.IsPFMultiplierSequence.coordinateDiagonalOperator_preserves_stability
          hseq (P.degreeOf i) i le_rfl hP
      rcases hstep with hzero | hstable
      · left
        rw [hzero, fold_coordinateDiagonalOperator_zero]
      · exact ih hstable

private theorem descFactorialScale_zero_or_stable
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    {P : MvPolynomial sigma ℂ} (hP : MvUpperHalfPlaneStable P) :
    descFactorialScale kappa P = 0 ∨
      MvUpperHalfPlaneStable (descFactorialScale kappa P) := by
  rw [descFactorialScale_eq_fold]
  exact fold_coordinateDiagonalOperator_zero_or_stable
    kappa (differentialVariableOrder sigma) hP

private def normalizedPolarizationFactors
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m : sigma →₀ ℕ) :
    MvPolynomial (BorceaBranden.PolarizedSource kappa) ℂ :=
  ∏ i, MvPolynomial.rename
    (fun x : Fin (kappa i) ↦
      (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa))
    (MvPolynomial.C ((kappa i).choose (m i) : ℂ)⁻¹ *
      MvPolynomial.esymm (Fin (kappa i)) ℂ (m i))

private def factorialPolarizationFactors
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m : sigma →₀ ℕ) :
    MvPolynomial (BorceaBranden.PolarizedSource kappa) ℂ :=
  ∏ i, MvPolynomial.rename
    (fun x : Fin (kappa i) ↦
      (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa))
    (MvPolynomial.C ((m i).factorial : ℂ) *
      MvPolynomial.esymm (Fin (kappa i)) ℂ (m i))

private theorem blockwisePolarizationBasis_eq_normalizedFactors
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ kappa i}) :
    BorceaBranden.blockwisePolarizationBasis kappa m =
      normalizedPolarizationFactors kappa m.1 := by
  classical
  unfold BorceaBranden.blockwisePolarizationBasis
  unfold normalizedPolarizationFactors
  apply Finset.prod_congr rfl
  intro i _hi
  rw [polarization_X_pow (m.2 i), map_mul, MvPolynomial.rename_C]
  change _ * MvPolynomial.rename
      (fun x : Fin (kappa i) ↦
        (⟨i, x⟩ : BorceaBranden.PolarizedSource kappa)) _ = _
  rw [map_mul, MvPolynomial.rename_C]

private theorem descFactorialScale_monomial
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m : sigma →₀ ℕ) (a : ℂ) :
    descFactorialScale kappa (MvPolynomial.monomial m a) =
      MvPolynomial.monomial m
        (((∏ i, (kappa i).descFactorial (m i) : ℕ) : ℂ) * a) := by
  classical
  ext n
  by_cases hnm : n = m
  · subst n
    simp [MvPolynomial.coeff_monomial]
  · simp [MvPolynomial.coeff_monomial, Ne.symm hnm]

private theorem descFactorial_mul_choose_inv
    {d k : ℕ} (hk : k ≤ d) :
    ((d.descFactorial k : ℕ) : ℂ) * ((d.choose k : ℂ)⁻¹) =
      (k.factorial : ℂ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hchoose : (d.choose k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  field_simp

private theorem scaled_blockwisePolarization_basis
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ kappa i}) :
    let p : MvPolynomial.degreeOfLE sigma ℂ kappa :=
      ⟨descFactorialScale kappa
          (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m).1,
        descFactorialScale_mem_degreeOfLE kappa _⟩
    (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa p).1 =
      factorialPolarizationFactors kappa m.1 := by
  classical
  dsimp only
  let c : ℂ := ((∏ i, (kappa i).descFactorial (m.1 i) : ℕ) : ℂ)
  let p : MvPolynomial.degreeOfLE sigma ℂ kappa :=
    ⟨descFactorialScale kappa
        (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m).1,
      descFactorialScale_mem_degreeOfLE kappa _⟩
  have hp :
      p =
        c • MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m := by
    apply Subtype.ext
    dsimp [p]
    rw [MvPolynomial.coe_basisDegreeOfLE, descFactorialScale_monomial]
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial]
  change (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa p).1 = _
  calc
    (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa p).1 =
        (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa
          (c • MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m)).1 := by
            exact congrArg (fun q =>
              (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa q).1) hp
    _ = factorialPolarizationFactors kappa m.1 := by
      rw [map_smul]
      simp only [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul,
        BorceaBranden.blockwisePolarizationDegreeBoxGeneral_basis]
      rw [blockwisePolarizationBasis_eq_normalizedFactors]
      unfold c normalizedPolarizationFactors factorialPolarizationFactors
      simp only [Nat.cast_prod, map_prod]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _hi
      simp only [map_mul, MvPolynomial.rename_C]
      rw [← mul_assoc, ← map_mul,
        descFactorial_mul_choose_inv (m.2 i)]

private theorem blockwisePolarization_basis
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m : {m : sigma →₀ ℕ // ∀ i, m i ≤ kappa i}) :
    (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa
      (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m)).1 =
        normalizedPolarizationFactors kappa m.1 := by
  rw [BorceaBranden.blockwisePolarizationDegreeBoxGeneral_basis]
  apply blockwisePolarizationBasis_eq_normalizedFactors

private theorem choose_differential_identity
    {d j k : ℕ} (hj : j ≤ d) (hk : k ≤ j) :
    k.factorial * (d + k - j).choose k * d.choose (j - k) =
      d.choose j * j.descFactorial k := by
  have hchoose := Nat.choose_mul (n := d) (k := j) (s := j - k)
    (Nat.sub_le j k)
  rw [Nat.choose_symm hk] at hchoose
  have hjsub : j - (j - k) = k := by lia
  rw [hjsub] at hchoose
  have hsub : d - (j - k) = d + k - j := by lia
  rw [hsub] at hchoose
  calc
    k.factorial * (d + k - j).choose k * d.choose (j - k) =
        k.factorial * (d.choose (j - k) * (d + k - j).choose k) := by ring
    _ = k.factorial * (d.choose j * j.choose k) := by rw [← hchoose]
    _ = d.choose j * (k.factorial * j.choose k) := by ring
    _ = d.choose j * j.descFactorial k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]

private theorem normalized_differential_coefficient
    {d j k : ℕ} (hj : j ≤ d) (hk : k ≤ j) :
    (k.factorial : ℂ) * ((d.choose j : ℂ)⁻¹) *
        ((d + k - j).choose k : ℂ) * (d.choose (j - k) : ℂ) =
      (j.descFactorial k : ℂ) := by
  have hchoose : (d.choose j : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
  have hnat := choose_differential_identity hj hk
  have hcast :
      (k.factorial : ℂ) * ((d + k - j).choose k : ℂ) *
          (d.choose (j - k) : ℂ) =
        (d.choose j : ℂ) * (j.descFactorial k : ℂ) := by
    exact_mod_cast hnat
  field_simp
  linear_combination hcast

private theorem diagonal_applyNegDifferential_factor
    {tau : Type*} (v : tau) (d j k : ℕ) (hj : j ≤ d) :
    MvPolynomial.rename (fun _ : Fin d => v)
        (applyNegDifferential
          (MvPolynomial.C (k.factorial : ℂ) *
            MvPolynomial.esymm (Fin d) ℂ k)
          (MvPolynomial.C ((d.choose j : ℂ)⁻¹) *
            MvPolynomial.esymm (Fin d) ℂ j)) =
      if k ≤ j then
        MvPolynomial.C ((-1 : ℂ) ^ k * (j.descFactorial k : ℂ)) *
          MvPolynomial.X v ^ (j - k)
      else 0 := by
  classical
  rw [applyNegDifferential_C_mul_left,
    applyNegDifferential_C_mul_right,
    applyNegDifferential_esymm]
  by_cases hk : k ≤ j
  · simp only [ite_eq_left hk, map_mul, map_nsmul,
      MvPolynomial.rename_C, MvPolynomial.rename_esymm_const,
      Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
    simp only [MvPolynomial.C_mul', smul_smul]
    have hc : (k.factorial : ℂ) * ((d.choose j : ℂ)⁻¹ *
        ((-1 : ℂ) ^ k * (((d + k - j).choose k : ℂ) *
          (d.choose (j - k) : ℂ)))) =
          (-1 : ℂ) ^ k * (j.descFactorial k : ℂ) := by
      rw [← normalized_differential_coefficient hj hk]
      ring
    rw [hc, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.smul_eq_C_mul, ← MvPolynomial.C_mul]
  · rw [ite_eq_right hk, mul_zero, mul_zero, map_zero,
      ite_eq_right hk]

private theorem iteratedPDerivAt_monomial'
    {R sigma : Type*} [CommSemiring R] (i : sigma) (k : ℕ)
    (m : sigma →₀ ℕ) (a : R) :
    iteratedPDerivAt i k (MvPolynomial.monomial m a) =
      MvPolynomial.monomial (m - Finsupp.single i k)
        ((m i).descFactorial k * a) := by
  induction k with
  | zero => simp [iteratedPDerivAt]
  | succ k ih =>
      rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_monomial]
      have hsub : m - Finsupp.single i k - Finsupp.single i 1 =
          m - Finsupp.single i (k + 1) := by
        ext j
        simp [Nat.sub_sub]
      rw [hsub]
      have hi : (m - Finsupp.single i k) i = m i - k := by simp
      rw [hi, Nat.descFactorial_succ, Nat.cast_mul]
      ring_nf

private theorem applyNegDifferential_X_pow
    {sigma : Type*} [Fintype sigma] (i : sigma) (j k : ℕ) :
    applyNegDifferential (MvPolynomial.X i ^ k) (MvPolynomial.X i ^ j) =
      MvPolynomial.C ((-1 : ℂ) ^ k * (j.descFactorial k : ℂ)) *
        MvPolynomial.X i ^ (j - k) := by
  rw [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial,
    applyNegDifferential_monomial,
    applyMonomialDifferential_single_nat,
    iteratedPDerivAt_monomial']
  have hsub : Finsupp.single i j - Finsupp.single i k =
      Finsupp.single i (j - k) := by
    ext x
    simp
  rw [hsub]
  simp only [Finsupp.sum_single_index, Finsupp.single_eq_same,
    mul_one]
  rw [MvPolynomial.X_pow_eq_monomial]
  simp only [MvPolynomial.C_mul_monomial, mul_one]

private theorem applyNegDifferential_rename
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    (f : sigma → tau) (hf : Function.Injective f)
    (F G : MvPolynomial sigma ℂ) :
    applyNegDifferential (MvPolynomial.rename f F)
        (MvPolynomial.rename f G) =
      MvPolynomial.rename f (applyNegDifferential F G) := by
  simpa using applyNegDifferential_rename_mul f hf F G 1 (by simp)

private theorem sigmaFst_finOne_injective {sigma : Type*} :
    Function.Injective
      (Sigma.fst : (Σ _ : sigma, Fin 1) → sigma) := by
  intro ⟨i, x⟩ ⟨j, y⟩ h
  dsimp at h
  subst j
  exact congrArg (Sigma.mk i) (Subsingleton.elim x y)

private theorem diagonal_polarized_apply_basis
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (m n : {a : sigma →₀ ℕ // ∀ i, a i ≤ kappa i}) :
    MvPolynomial.rename Sigma.fst
        (applyNegDifferential
          (factorialPolarizationFactors kappa m.1)
          (normalizedPolarizationFactors kappa n.1)) =
      applyNegDifferential
        (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m).1
        (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa n).1 := by
  classical
  let one : sigma → ℕ := fun _ => 1
  let A : (i : sigma) → MvPolynomial (Fin (one i)) ℂ :=
    fun i => MvPolynomial.X 0 ^ m.1 i
  let B : (i : sigma) → MvPolynomial (Fin (one i)) ℂ :=
    fun i => MvPolynomial.X 0 ^ n.1 i
  have hone := applyNegDifferential_blockProducts one Finset.univ A B 1
    (by simp)
  simp only [mul_one] at hone
  have hmonomial (a : sigma →₀ ℕ) :
      ∏ i, (MvPolynomial.X i ^ a i : MvPolynomial sigma ℂ) =
        MvPolynomial.monomial a 1 := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    symm
    apply Finset.prod_subset (Finset.subset_univ a.support)
    intro i _hi hi
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  have hcoordinates :
      applyNegDifferential
          (MvPolynomial.monomial m.1 1)
          (MvPolynomial.monomial n.1 1) =
        ∏ i, MvPolynomial.C
            ((-1 : ℂ) ^ m.1 i * ((n.1 i).descFactorial (m.1 i) : ℂ)) *
          MvPolynomial.X i ^ (n.1 i - m.1 i) := by
    calc
      _ = applyNegDifferential
          (MvPolynomial.rename Sigma.fst
            (∏ i, MvPolynomial.rename (fun x => ⟨i, x⟩) (A i)))
          (MvPolynomial.rename Sigma.fst
            (∏ i, MvPolynomial.rename (fun x => ⟨i, x⟩) (B i))) := by
        simp only [map_prod, A, B, map_pow, MvPolynomial.rename_X]
        congr 1
        · exact (hmonomial m.1).symm
        · exact (hmonomial n.1).symm
      _ = MvPolynomial.rename Sigma.fst
          (applyNegDifferential
            (∏ i, MvPolynomial.rename (fun x => ⟨i, x⟩) (A i))
            (∏ i, MvPolynomial.rename (fun x => ⟨i, x⟩) (B i))) :=
        applyNegDifferential_rename Sigma.fst sigmaFst_finOne_injective _ _
      _ = MvPolynomial.rename Sigma.fst
          (∏ i, MvPolynomial.rename (fun x => ⟨i, x⟩)
            (applyNegDifferential (A i) (B i))) := congrArg _ hone
      _ = _ := by
        simp only [map_prod, A, B, applyNegDifferential_X_pow,
          map_mul, MvPolynomial.rename_C, map_pow, MvPolynomial.rename_X]
  rw [MvPolynomial.coe_basisDegreeOfLE,
    MvPolynomial.coe_basisDegreeOfLE]
  unfold factorialPolarizationFactors normalizedPolarizationFactors
  have hblocks := applyNegDifferential_blockProducts kappa Finset.univ
    (fun i => MvPolynomial.C ((m.1 i).factorial : ℂ) *
      MvPolynomial.esymm (Fin (kappa i)) ℂ (m.1 i))
    (fun i => MvPolynomial.C ((kappa i).choose (n.1 i) : ℂ)⁻¹ *
      MvPolynomial.esymm (Fin (kappa i)) ℂ (n.1 i)) 1 (by simp)
  simp only [mul_one] at hblocks
  calc
    _ = MvPolynomial.rename Sigma.fst
        (∏ i, MvPolynomial.rename (fun x => ⟨i, x⟩)
          (applyNegDifferential
            (MvPolynomial.C ((m.1 i).factorial : ℂ) *
              MvPolynomial.esymm (Fin (kappa i)) ℂ (m.1 i))
            (MvPolynomial.C ((kappa i).choose (n.1 i) : ℂ)⁻¹ *
              MvPolynomial.esymm (Fin (kappa i)) ℂ (n.1 i)))) :=
      congrArg (MvPolynomial.rename Sigma.fst) hblocks
    _ = ∏ i, MvPolynomial.C
          ((-1 : ℂ) ^ m.1 i * ((n.1 i).descFactorial (m.1 i) : ℂ)) *
        MvPolynomial.X i ^ (n.1 i - m.1 i) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _hi
      rw [MvPolynomial.rename_rename]
      change MvPolynomial.rename (fun _ : Fin (kappa i) => i) _ = _
      rw [diagonal_applyNegDifferential_factor i (kappa i) (n.1 i) (m.1 i)
        (n.2 i)]
      by_cases hmn : m.1 i ≤ n.1 i
      · rw [ite_eq_left hmn]
      · rw [ite_eq_right hmn,
          Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hmn),
          Nat.cast_zero, mul_zero, MvPolynomial.C_0, zero_mul]
    _ = _ := hcoordinates.symm

private noncomputable def descFactorialScaleDegreeBox
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ) :
    MvPolynomial.degreeOfLE sigma ℂ kappa →ₗ[ℂ]
      MvPolynomial.degreeOfLE sigma ℂ kappa where
  toFun P := ⟨descFactorialScale kappa P.1,
    descFactorialScale_mem_degreeOfLE kappa P.1⟩
  map_add' P Q := by
    apply Subtype.ext
    ext m
    simp only [Submodule.coe_add]
    rw [show (descFactorialScale kappa P.1 +
        descFactorialScale kappa Q.1).coeff m =
          (descFactorialScale kappa P.1).coeff m +
            (descFactorialScale kappa Q.1).coeff m from
      (MvPolynomial.coeffAddMonoidHom m).map_add _ _]
    rw [coeff_descFactorialScale, coeff_descFactorialScale,
      coeff_descFactorialScale]
    rw [show (P.1 + Q.1).coeff m = P.1.coeff m + Q.1.coeff m from
      (MvPolynomial.coeffAddMonoidHom m).map_add _ _]
    ring
  map_smul' c P := by
    apply Subtype.ext
    ext m
    simp only [Submodule.coe_smul, coeff_descFactorialScale,
      MvPolynomial.coeff_smul, RingHom.id_apply]
    ring

private theorem diagonal_polarized_apply
    {sigma : Type*} [Fintype sigma] (kappa : sigma → ℕ)
    (P Q : MvPolynomial.degreeOfLE sigma ℂ kappa) :
    MvPolynomial.rename Sigma.fst
        (applyNegDifferential
          (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa
            (descFactorialScaleDegreeBox kappa P)).1
          (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa Q).1) =
      applyNegDifferential P.1 Q.1 := by
  let inc := Submodule.subtype (MvPolynomial.degreeOfLE sigma ℂ kappa)
  let pol := (Submodule.subtype
      (MvPolynomial.degreeOfLE
        (BorceaBranden.PolarizedSource kappa) ℂ (fun _ => 1))).comp
      (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa)
  let diag : MvPolynomial (BorceaBranden.PolarizedSource kappa) ℂ →ₗ[ℂ]
      MvPolynomial sigma ℂ := (MvPolynomial.rename Sigma.fst).toLinearMap
  let spol := pol.comp (descFactorialScaleDegreeBox kappa)
  let L := diag.comp ((applyNegDifferentialLeftLinearMap (pol Q)).comp spol)
  let R := (applyNegDifferentialLeftLinearMap (inc Q)).comp inc
  change L P = R P
  apply LinearMap.congr_fun ?_ P
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa).ext
  intro m
  let Lm := diag.comp
    ((applyNegDifferentialRightLinearMap (spol
      (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m))).comp pol)
  let Rm := (applyNegDifferentialRightLinearMap
    (inc (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m))).comp inc
  change Lm Q = Rm Q
  apply LinearMap.congr_fun ?_ Q
  apply (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa).ext
  intro n
  change MvPolynomial.rename Sigma.fst
      (applyNegDifferential
        (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa
          ⟨descFactorialScale kappa
              (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m).1,
            descFactorialScale_mem_degreeOfLE kappa _⟩).1
        (BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa
          (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa n)).1) =
      applyNegDifferential
        (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa m).1
        (MvPolynomial.basisDegreeOfLE (R := ℂ) kappa n).1
  rw [scaled_blockwisePolarization_basis,
    blockwisePolarization_basis]
  exact diagonal_polarized_apply_basis kappa m n

/-- The constant-coefficient differential action `F(-∂){G}` of two stable
polynomials is zero or stable. -/
theorem MvUpperHalfPlaneStable.liebSokal
    {sigma : Type*} [Fintype sigma]
    {F G : MvPolynomial sigma ℂ} (hF : MvUpperHalfPlaneStable F)
    (hG : MvUpperHalfPlaneStable G) :
    applyNegDifferential F G = 0 ∨
      MvUpperHalfPlaneStable (applyNegDifferential F G) := by
  let kappa : sigma → ℕ := fun i => max (F.degreeOf i) (G.degreeOf i)
  let f : MvPolynomial.degreeOfLE sigma ℂ kappa :=
    ⟨F, (MvPolynomial.mem_degreeOfLE_iff_degreeOf F).2 fun i =>
      le_max_left (F.degreeOf i) (G.degreeOf i)⟩
  let g : MvPolynomial.degreeOfLE sigma ℂ kappa :=
    ⟨G, (MvPolynomial.mem_degreeOfLE_iff_degreeOf G).2 fun i =>
      le_max_right (F.degreeOf i) (G.degreeOf i)⟩
  have hid := diagonal_polarized_apply kappa f g
  rcases descFactorialScale_zero_or_stable kappa hF with hzero | hscaled
  · left
    have hfzero : descFactorialScaleDegreeBox kappa f = 0 := Subtype.ext hzero
    rw [← hid, hfzero, map_zero]
    change MvPolynomial.rename Sigma.fst (applyNegDifferential 0 _) = 0
    rw [applyNegDifferential_zero_left, map_zero]
  · let pf := BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa
      (descFactorialScaleDegreeBox kappa f)
    let pg := BorceaBranden.blockwisePolarizationDegreeBoxGeneral kappa g
    have hpf : MvUpperHalfPlaneStable pf.1 :=
      BorceaBranden.mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral
        kappa _ hscaled
    have hpg : MvUpperHalfPlaneStable pg.1 :=
      BorceaBranden.mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral
        kappa _ hG
    have hpfma : MvPolynomial.IsMultiaffine pf.1 :=
      (MvPolynomial.mem_degreeOfLE_iff_degreeOf pf.1).mp pf.2
    have hpgma : MvPolynomial.IsMultiaffine pg.1 :=
      (MvPolynomial.mem_degreeOfLE_iff_degreeOf pg.1).mp pg.2
    rcases hpf.liebSokal_multiaffine hpg hpfma hpgma with hzero | hstable
    · left
      rw [← hid, show pf.1 = _ from rfl, show pg.1 = _ from rfl,
        hzero, map_zero]
    · right
      rw [← hid, show pf.1 = _ from rfl, show pg.1 = _ from rfl]
      exact hstable.rename

end

end RealRooted
