import RealRooted.MultivariateStability.Substitution
import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier
import RealRooted.LiebSokalOperator
import RealRooted.MultivariateStability.Inversion
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Finite-order Weyl-symbol preservers

A finite-order differential operator `∑_{j ≤ m} Q_j ∂_q^j` whose signed Weyl symbol
`∑_j Q_j (-w)^j` is upper-half-plane stable maps every stable polynomial, of any degree and
with any spectator variables, to a stable polynomial or zero.  On each degree box the operator
is the coordinate PF multiplier `n.descFactorial` applied to the symbol, followed by the
substitution `w ↦ -1 / (x_q + y_q)`, so the general finite-symbol theorem applies.  This is the
polynomial-symbol case of Borcea--Brändén, *The Lee--Yang and Pólya--Schur programs. I*,
Invent. Math. 177 (2009), Theorems 1.3--1.4 (arXiv:0809.0401).
-/

open scoped BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

open RealRooted

private theorem iteratedPDerivAt_smul {σ : Type*} (q : σ) (j : ℕ)
    (c : ℂ) (p : MvPolynomial σ ℂ) :
    iteratedPDerivAt q j (c • p) = c • iteratedPDerivAt q j p := by
  rw [← iteratedPDerivAt_eq_pow, ← iteratedPDerivAt_eq_pow]
  exact ((MvPolynomial.pderiv q).toLinearMap ^ j).map_smul c p

/-- A finite-order differential operator in the coordinate `q`. -/
def finiteOrderWeylOperator {σ : Type*} (q : σ) (m : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun p := ∑ j : Fin (m + 1), Q j * iteratedPDerivAt q j p
  map_add' p r := by
    simp only [iteratedPDerivAt_add, Finset.sum_add_distrib, mul_add]
  map_smul' c p := by
    simp only [iteratedPDerivAt_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [MvPolynomial.smul_eq_C_mul]
    simp only [RingHom.id_apply, MvPolynomial.smul_eq_C_mul]
    ring_nf

/-- The degree-box restriction of a finite-order differential operator. -/
def finiteOrderWeylOperatorDegreeBox {σ : Type*}
    (q : σ) (m : ℕ) (Q : Fin (m + 1) → MvPolynomial σ ℂ) (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ :=
  { toFun := fun p => finiteOrderWeylOperator q m Q p.1
    map_add' := fun p r => by
      exact (finiteOrderWeylOperator q m Q).map_add p.1 r.1
    map_smul' := fun c p => by
      exact (finiteOrderWeylOperator q m Q).map_smul c p.1 }

private def iteratedPDerivAtDegreeBox {σ : Type*}
    (q : σ) (j : ℕ) (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun p := iteratedPDerivAt q j p.1
  map_add' p r := iteratedPDerivAt_add q j p.1 r.1
  map_smul' c p := iteratedPDerivAt_smul q j c p.1

private def leftMultiply {σ : Type*} (a : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun p := a * p
  map_add' p r := by rw [mul_add]
  map_smul' c p := by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
    simp only [RingHom.id_apply]
    ring_nf

private theorem algebraicSymbol_leftMultiply {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (a : MvPolynomial σ ℂ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ) :
    MvPolynomial.algebraicSymbol κ (leftMultiply a ∘ₗ T) =
      MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ) a *
        MvPolynomial.algebraicSymbol κ T := by
  classical
  rw [MvPolynomial.algebraicSymbol_eq_sum,
    MvPolynomial.algebraicSymbol_eq_sum]
  simp only [LinearMap.coe_comp, Function.comp_apply, leftMultiply,
    LinearMap.coe_mk, AddHom.coe_mk, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring_nf

private theorem pderiv_rightComplementMonomial_zero {σ τ : Type*} [Fintype σ]
    (q : τ) (κ : σ → ℕ) (d : σ →₀ ℕ) :
    MvPolynomial.pderiv (Sum.inl q)
        (MvPolynomial.rightComplementMonomial (R := ℂ) (τ := τ) κ d) = 0 := by
  rw [MvPolynomial.rightComplementMonomial_eq_prod]
  have hrename :
      (∏ i : σ, (MvPolynomial.X (Sum.inr i) :
        MvPolynomial (τ ⊕ σ) ℂ) ^ (κ i - d i)) =
        MvPolynomial.rename (Sum.inr : σ → τ ⊕ σ)
          (∏ i : σ, MvPolynomial.X i ^ (κ i - d i)) := by
    simp only [map_prod, map_pow, MvPolynomial.rename_X]
  rw [hrename]
  exact MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (MvPolynomial.inl_notMem_vars_rename_inr q _)

private def pderivAfter {σ τ : Type*}
    (q : τ) (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ where
  toFun p := MvPolynomial.pderiv q (T p)
  map_add' p r := by
    rw [T.map_add]
    exact map_add _ _ _
  map_smul' c p := by
    rw [T.map_smul, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.pderiv_C_mul]
    simp only [RingHom.id_apply, MvPolynomial.smul_eq_C_mul]

private theorem algebraicSymbol_pderivAfter {σ τ : Type*} [Fintype σ]
    (q : τ) (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.algebraicSymbol κ (pderivAfter q κ T) =
      MvPolynomial.pderiv (Sum.inl q) (MvPolynomial.algebraicSymbol κ T) := by
  classical
  let D : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ :=
    { toFun p := MvPolynomial.pderiv q (T p)
      map_add' p r := by
        rw [T.map_add, map_add]
      map_smul' c p := by
        rw [T.map_smul, MvPolynomial.smul_eq_C_mul,
          MvPolynomial.pderiv_C_mul]
        simp only [RingHom.id_apply, MvPolynomial.smul_eq_C_mul] }
  change MvPolynomial.algebraicSymbol κ D = _
  rw [MvPolynomial.algebraicSymbol_eq_sum,
    MvPolynomial.algebraicSymbol_eq_sum]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_rename Sum.inl_injective, D,
    pderiv_rightComplementMonomial_zero, zero_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring_nf

private theorem coordinateJensenSymbol_one {σ : Type*} (n : ℕ) (q : σ) :
    coordinateJensenSymbol n (fun _ => 1) q =
      (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ n := by
  unfold coordinateJensenSymbol
  let g : ℕ → MvPolynomial (σ ⊕ σ) ℂ := fun k =>
    MvPolynomial.C (n.choose k : ℂ) *
      MvPolynomial.X (Sum.inl q) ^ k *
        MvPolynomial.X (Sum.inr q) ^ (n - k)
  calc
    (∑ k : Fin (n + 1),
        MvPolynomial.C (n.choose (k : ℕ) : ℂ) *
          MvPolynomial.C ((fun _ => 1) (k : ℕ) : ℂ) *
            MvPolynomial.X (Sum.inl q) ^ (k : ℕ) *
              MvPolynomial.X (Sum.inr q) ^ (n - (k : ℕ))) =
        ∑ k ∈ Finset.range (n + 1), g k := by
          simpa [g, mul_comm, mul_left_comm, mul_assoc] using
            (Fin.sum_univ_eq_sum_range g (n + 1))
    _ = (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ n := by
      rw [add_pow]
      simp [g, mul_comm, mul_assoc]

private def degreeBoxInclusion {σ : Type*} (κ : σ → ℕ) :
    MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun p := p.1
  map_add' p r := rfl
  map_smul' c p := by rfl

private theorem coordinateDiagonalOperatorDegreeBox_one_eq_inclusion
    {σ : Type*} (q : σ) (κ : σ → ℕ) :
    coordinateDiagonalOperatorDegreeBox (fun _ => 1) q κ =
      degreeBoxInclusion κ := by
  classical
  ext p m
  by_cases h : p.1.coeff m = 0 <;>
    simp [coordinateDiagonalOperatorDegreeBox, coordinateDiagonalOperator,
      degreeBoxInclusion, h]

private theorem algebraicSymbol_inclusion_eq_product
    {σ : Type*} [Fintype σ] [DecidableEq σ] (q : σ) (n : ℕ) (κ : σ → ℕ)
    (hκ : κ q = n) :
    MvPolynomial.algebraicSymbol κ (degreeBoxInclusion κ) =
      (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ n *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  rw [← coordinateDiagonalOperatorDegreeBox_one_eq_inclusion q κ,
    algebraicSymbol_coordinateDiagonalOperatorDegreeBox n (fun _ => 1) q κ hκ,
    coordinateDiagonalSymbol, coordinateJensenSymbol_one]
  have he : @Finset.erase σ (Classical.decEq σ) Finset.univ q =
      @Finset.erase σ (inferInstance : DecidableEq σ) Finset.univ q := by
    ext i
    simp
  rw [he]

private theorem algebraicSymbol_iteratedPDerivAtDegreeBox
    {σ : Type*} [Fintype σ] (q : σ) (j : ℕ) (κ : σ → ℕ) :
    MvPolynomial.algebraicSymbol κ
        (iteratedPDerivAtDegreeBox q j κ) =
      iteratedPDerivAt (Sum.inl q) j
        (MvPolynomial.algebraicSymbol κ (degreeBoxInclusion κ)) := by
  induction j with
  | zero =>
      have hzero : iteratedPDerivAtDegreeBox q 0 κ = degreeBoxInclusion κ := by
        ext p
        rfl
      rw [hzero]
      simp [iteratedPDerivAt]
  | succ j ih =>
      have hmap : iteratedPDerivAtDegreeBox q (j + 1) κ =
          pderivAfter q κ (iteratedPDerivAtDegreeBox q j κ) := by
        ext p
        rfl
      rw [hmap, algebraicSymbol_pderivAfter, ih]
      rfl

private theorem iteratedPDerivAt_linearForm_pow {σ : Type*}
    (q r : σ) (hqr : q ≠ r) (j n : ℕ) :
    iteratedPDerivAt q j
        ((MvPolynomial.X q + MvPolynomial.X r) ^ n) =
      MvPolynomial.C (n.descFactorial j : ℂ) *
        (MvPolynomial.X q + MvPolynomial.X r) ^ (n - j) := by
  classical
  induction j generalizing n with
  | zero =>
      simp only [iteratedPDerivAt, Nat.descFactorial_zero, Nat.cast_one,
        MvPolynomial.C_1, one_mul, Nat.sub_zero]
  | succ j ih =>
      rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, map_add,
        MvPolynomial.pderiv_X_self,
        MvPolynomial.pderiv_X_of_ne (Ne.symm hqr)]
      simp only [add_zero, mul_one, Nat.descFactorial_succ]
      by_cases hjn : j < n
      · rw [← Nat.sub_sub]
        rw [Nat.cast_mul]
        simp only [map_mul]
        norm_num
        ring_nf
      · have hnj : n ≤ j := Nat.le_of_not_gt hjn
        by_cases hEq : n = j
        · subst n
          simp
        · have hlt : n < j := lt_of_le_of_ne hnj hEq
          simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]

private theorem pderiv_spectatorProduct_zero {σ : Type*} [Fintype σ]
    [DecidableEq σ]
    (q : σ) (κ : σ → ℕ) :
    MvPolynomial.pderiv (Sum.inl q)
        (∏ i ∈ Finset.univ.erase q,
          ((MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ σ) ℂ) +
            MvPolynomial.X (Sum.inr i)) ^ κ i) = 0 := by
  classical
  have hprod : ∀ (s : Finset σ), (∀ i ∈ s, i ≠ q) →
      MvPolynomial.pderiv (Sum.inl q)
        (∏ i ∈ s,
          ((MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ σ) ℂ) +
            MvPolynomial.X (Sum.inr i)) ^ κ i) = 0 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        have hiq : i ≠ q := hs i (by simp)
        have hiq' : (Sum.inl i : σ ⊕ σ) ≠ Sum.inl q := by
          intro h
          exact hiq (Sum.inl.inj h)
        have hs' : ∀ j ∈ s, j ≠ q := by
          intro j hj
          exact hs j (by simp [hj])
        rw [Finset.prod_insert hi, MvPolynomial.pderiv_mul, ih hs']
        have hfactor :
            MvPolynomial.pderiv (Sum.inl q)
                ((MvPolynomial.X (Sum.inl i) : MvPolynomial (σ ⊕ σ) ℂ) +
                  MvPolynomial.X (Sum.inr i)) = 0 := by
          rw [map_add,
            MvPolynomial.pderiv_X_of_ne (i := Sum.inl q) (j := Sum.inl i)
              hiq',
            MvPolynomial.pderiv_X_of_ne (i := Sum.inl q) (j := Sum.inr i)
              (Ne.symm (Sum.inl_ne_inr : Sum.inl q ≠ Sum.inr i))]
          simp
        rw [MvPolynomial.pderiv_pow, hfactor]
        simp
  apply hprod (Finset.univ.erase q)
  intro i hi
  exact (Finset.mem_erase.mp hi).1

private theorem iteratedPDerivAt_mul_of_pderiv_zero {σ : Type*}
    (q : σ) (j : ℕ) (a b : MvPolynomial σ ℂ)
    (hb : MvPolynomial.pderiv q b = 0) :
    iteratedPDerivAt q j (a * b) = iteratedPDerivAt q j a * b := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [iteratedPDerivAt, ih, MvPolynomial.pderiv_mul, hb, mul_zero,
        add_zero, iteratedPDerivAt]

private theorem algebraicSymbol_iteratedPDerivAtDegreeBox_explicit
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ) (j n : ℕ) (κ : σ → ℕ)
    (hκ : κ q = n) :
    MvPolynomial.algebraicSymbol κ
        (iteratedPDerivAtDegreeBox q j κ) =
      MvPolynomial.C (n.descFactorial j : ℂ) *
          (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^ (n - j) *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  rw [algebraicSymbol_iteratedPDerivAtDegreeBox,
    algebraicSymbol_inclusion_eq_product q n κ hκ]
  rw [iteratedPDerivAt_mul_of_pderiv_zero]
  · rw [iteratedPDerivAt_linearForm_pow (Sum.inl q) (Sum.inr q)
      (Sum.inl_ne_inr : Sum.inl q ≠ Sum.inr q)
      j n]
  · exact pderiv_spectatorProduct_zero q κ

private theorem finiteOrderWeylOperatorDegreeBox_algebraicSymbol_explicit
    {σ : Type*} [Fintype σ] [DecidableEq σ] (q : σ) (m n : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) (κ : σ → ℕ)
    (hκ : κ q = n) :
    MvPolynomial.algebraicSymbol κ
        (finiteOrderWeylOperatorDegreeBox q m Q κ) =
      (∑ j : Fin (m + 1),
        MvPolynomial.C (n.descFactorial (j : ℕ) : ℂ) *
          MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ) (Q j) *
          (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^
            (n - (j : ℕ))) *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  have hmap : finiteOrderWeylOperatorDegreeBox q m Q κ =
      ∑ j : Fin (m + 1),
        leftMultiply (Q j) ∘ₗ iteratedPDerivAtDegreeBox q (j : ℕ) κ := by
    apply LinearMap.ext
    intro p
    change finiteOrderWeylOperator q m Q p.1 = _
    simp [finiteOrderWeylOperator, iteratedPDerivAtDegreeBox, leftMultiply]
  rw [hmap]
  have hsum : ∀ s : Finset (Fin (m + 1)),
      MvPolynomial.algebraicSymbol κ
          (s.sum (fun j =>
            leftMultiply (Q j) ∘ₗ iteratedPDerivAtDegreeBox q (j : ℕ) κ)) =
        s.sum (fun j => MvPolynomial.algebraicSymbol κ
          (leftMultiply (Q j) ∘ₗ iteratedPDerivAtDegreeBox q (j : ℕ) κ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.sum_insert hj, MvPolynomial.algebraicSymbol_add, ih,
          Finset.sum_insert hj]
  calc
    MvPolynomial.algebraicSymbol κ
        (∑ j : Fin (m + 1),
          leftMultiply (Q j) ∘ₗ iteratedPDerivAtDegreeBox q (j : ℕ) κ) =
        ∑ j : Fin (m + 1),
          MvPolynomial.algebraicSymbol κ
            (leftMultiply (Q j) ∘ₗ iteratedPDerivAtDegreeBox q (j : ℕ) κ) := by
      exact hsum Finset.univ
    _ = _ := by
      rw [show (∑ j : Fin (m + 1),
          MvPolynomial.algebraicSymbol κ
            (leftMultiply (Q j) ∘ₗ iteratedPDerivAtDegreeBox q (j : ℕ) κ)) =
          (∑ j : Fin (m + 1),
            MvPolynomial.C (n.descFactorial (j : ℕ) : ℂ) *
              MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ) (Q j) *
              (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^
                (n - (j : ℕ)) *
              ∏ i ∈ Finset.univ.erase q,
                (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i) by
            apply Finset.sum_congr rfl
            intro j hj
            rw [algebraicSymbol_leftMultiply,
              algebraicSymbol_iteratedPDerivAtDegreeBox_explicit q (j : ℕ)
                n κ hκ]
            ring_nf]
      rw [Finset.sum_mul]

/-- The signed Weyl symbol of a finite-order differential operator. -/
def signedWeylSymbol {σ : Type*} (m : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    MvPolynomial (Option σ) ℂ :=
  ∑ j : Fin (m + 1),
    MvPolynomial.rename some (Q j) *
      MvPolynomial.C ((-1 : ℂ) ^ (j : ℕ)) * MvPolynomial.X none ^ (j : ℕ)

private theorem optionEquivLeft_rename_some {σ : Type*}
    (P : MvPolynomial σ ℂ) :
    MvPolynomial.optionEquivLeft ℂ σ (MvPolynomial.rename some P) =
      Polynomial.C P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
      classical
      have hnone : Finsupp.mapDomain some d none = 0 := by
        rw [Finsupp.mapDomain_apply]
        simp
      have hsome : (Finsupp.mapDomain some d).some = d := by
        ext i
        exact Finsupp.mapDomain_apply_of_injective (Option.some_injective σ) d i
      rw [MvPolynomial.rename_monomial some d r,
        MvPolynomial.optionEquivLeft_monomial, hnone, hsome,
        Polynomial.monomial_zero_left]
  | add P R hP hR => simp only [map_add, hP, hR]

private theorem optionEquivLeft_signedWeylSymbol {σ : Type*} (m : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    MvPolynomial.optionEquivLeft ℂ σ (signedWeylSymbol m Q) =
      ∑ j : Fin (m + 1),
        Polynomial.C (Q j * MvPolynomial.C ((-1 : ℂ) ^ (j : ℕ))) *
          Polynomial.X ^ (j : ℕ) := by
  rw [signedWeylSymbol]
  simp only [map_sum, map_mul, map_pow, optionEquivLeft_rename_some,
    MvPolynomial.optionEquivLeft_C, MvPolynomial.optionEquivLeft_X_none]

private theorem optionEquivLeft_coordinateDiagonalOperator_coeff
    {σ : Type*} (gamma : ℕ → ℝ) (P : MvPolynomial (Option σ) ℂ) (k : ℕ) :
    (MvPolynomial.optionEquivLeft ℂ σ
      (coordinateDiagonalOperator gamma none P)).coeff k =
      MvPolynomial.C (gamma k : ℂ) *
        (MvPolynomial.optionEquivLeft ℂ σ P).coeff k := by
  classical
  ext d
  rw [MvPolynomial.optionEquivLeft_coeff_coeff,
    coeff_coordinateDiagonalOperator, Finsupp.optionElim_apply_none,
    MvPolynomial.coeff_C_mul, MvPolynomial.optionEquivLeft_coeff_coeff]

private theorem polynomial_coeff_fintype_sum {ι R : Type*} [Fintype ι]
    [CommSemiring R] (f : ι → Polynomial R) (k : ℕ) :
    Polynomial.coeff (∑ i, f i) k = ∑ i, Polynomial.coeff (f i) k := by
  change Polynomial.lcoeff R k (∑ i, f i) = _
  rw [map_sum]
  rfl

private theorem optionEquivLeft_descFactorialTerms {σ : Type*} (gamma : ℕ → ℝ)
    (m : ℕ) (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    MvPolynomial.optionEquivLeft ℂ σ
        (∑ j : Fin (m + 1),
          MvPolynomial.rename some (Q j) *
            MvPolynomial.C ((gamma (j : ℕ) : ℂ) * (-1 : ℂ) ^ (j : ℕ)) *
            MvPolynomial.X none ^ (j : ℕ)) =
      ∑ j : Fin (m + 1),
        Polynomial.C
          (Q j * MvPolynomial.C
            ((gamma (j : ℕ) : ℂ) * (-1 : ℂ) ^ (j : ℕ))) *
          Polynomial.X ^ (j : ℕ) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul, map_mul, map_pow, optionEquivLeft_rename_some,
    MvPolynomial.optionEquivLeft_C, MvPolynomial.optionEquivLeft_X_none,
    ← Polynomial.C_mul]

private theorem coordinateDiagonalOperator_signedWeylSymbol
    {σ : Type*} (gamma : ℕ → ℝ) (m : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    coordinateDiagonalOperator gamma none (signedWeylSymbol m Q) =
      ∑ j : Fin (m + 1),
        MvPolynomial.rename some (Q j) *
          MvPolynomial.C ((gamma (j : ℕ) : ℂ) * (-1 : ℂ) ^ (j : ℕ)) *
          MvPolynomial.X none ^ (j : ℕ) := by
  apply (MvPolynomial.optionEquivLeft ℂ σ).injective
  apply Polynomial.ext
  intro k
  rw [optionEquivLeft_coordinateDiagonalOperator_coeff,
    optionEquivLeft_signedWeylSymbol,
    optionEquivLeft_descFactorialTerms,
    polynomial_coeff_fintype_sum, polynomial_coeff_fintype_sum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hkj : k = (j : ℕ)
  · subst k
    simp only [ite_true]
    rw [map_mul]
    ring_nf
  · simp [hkj]

private theorem signedWeylSymbol_degreeOf_none_le {σ : Type*} (m : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    (signedWeylSymbol m Q).degreeOf none ≤ m := by
  rw [← MvPolynomial.natDegree_optionEquivLeft]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [optionEquivLeft_signedWeylSymbol]
  rw [polynomial_coeff_fintype_sum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro j _hj
  have hjle : (j : ℕ) ≤ m := Nat.le_of_lt_succ j.isLt
  have hkj : k ≠ (j : ℕ) := by lia
  simp only [hkj, ↓reduceIte]

private theorem descFactorialTransform_degreeOf_none_le
    {σ : Type*} (m n : ℕ) (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    (coordinateDiagonalOperator (fun k => (n.descFactorial k : ℝ)) none
      (signedWeylSymbol m Q)).degreeOf none ≤ n := by
  rw [← MvPolynomial.natDegree_optionEquivLeft]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [optionEquivLeft_coordinateDiagonalOperator_coeff,
    Nat.descFactorial_eq_zero_iff_lt.mpr hk]
  simp

private theorem invertVariable_add {σ : Type*} (n : ℕ)
    (P R : MvPolynomial (Option σ) ℂ) :
    invertVariable n (P + R) = invertVariable n P + invertVariable n R := by
  unfold invertVariable
  rw [map_add, Polynomial.add_comp, Polynomial.reflect_add, map_add]

private theorem invertVariable_zero {σ : Type*} (n : ℕ) :
    invertVariable n (0 : MvPolynomial (Option σ) ℂ) = 0 := by
  unfold invertVariable
  simp

private theorem invertVariable_fintype_sum {ι σ : Type*} [Fintype ι]
    (n : ℕ) (P : ι → MvPolynomial (Option σ) ℂ) :
    invertVariable n (∑ i, P i) = ∑ i, invertVariable n (P i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => exact invertVariable_zero n
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, invertVariable_add, ih]

private theorem mul_mul_mul_mul_self {R : Type*} [CommMonoid R]
    (A B u v : R) :
    A * (B * u) * (u * v) = A * B * (u * u) * v := by
  ac_rfl

private theorem invertVariable_signed_monomial {σ : Type*}
    (n j : ℕ) (hj : j ≤ n) (a : ℂ) (P : MvPolynomial σ ℂ) :
    invertVariable n
        (MvPolynomial.rename some P *
          MvPolynomial.C (a * (-1 : ℂ) ^ j) * MvPolynomial.X none ^ j) =
      MvPolynomial.C a * MvPolynomial.rename some P *
        MvPolynomial.X none ^ (n - j) := by
  apply (MvPolynomial.optionEquivLeft ℂ σ).injective
  unfold invertVariable
  rw [AlgEquiv.apply_symm_apply]
  have hcomp :
      (MvPolynomial.optionEquivLeft ℂ σ
        (MvPolynomial.rename some P *
          MvPolynomial.C (a * (-1 : ℂ) ^ j) *
          MvPolynomial.X none ^ j)).comp (-Polynomial.X) =
        Polynomial.C (P * MvPolynomial.C a) * Polynomial.X ^ j := by
    simp only [map_mul, map_pow, optionEquivLeft_rename_some,
      MvPolynomial.optionEquivLeft_C, MvPolynomial.optionEquivLeft_X_none,
      Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp,
      Polynomial.X_comp]
    simp only [map_neg, map_one]
    have hsign :
        ((-1 : Polynomial (MvPolynomial σ ℂ)) ^ j) *
          (-1 : Polynomial (MvPolynomial σ ℂ)) ^ j = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow (α := Polynomial (MvPolynomial σ ℂ))
        (Even.add_self j)
    rw [neg_pow (Polynomial.X : Polynomial (MvPolynomial σ ℂ)) j,
      mul_mul_mul_mul_self, hsign, mul_one]
  rw [hcomp, Polynomial.reflect_C_mul_X_pow, Polynomial.revAt_le hj]
  have hout :
      MvPolynomial.optionEquivLeft ℂ σ
          (MvPolynomial.C a * MvPolynomial.rename some P *
            MvPolynomial.X none ^ (n - j)) =
        Polynomial.C (MvPolynomial.C a) * Polynomial.C P *
          Polynomial.X ^ (n - j) := by
    rw [map_mul, map_mul, map_pow, MvPolynomial.optionEquivLeft_C,
      optionEquivLeft_rename_some, MvPolynomial.optionEquivLeft_X_none]
  rw [hout, map_mul]
  rw [mul_comm (Polynomial.C P)
    (Polynomial.C (MvPolynomial.C a))]

private theorem invertVariable_descFactorial_signedWeylSymbol
    {σ : Type*} (m n : ℕ) (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    invertVariable n
        (coordinateDiagonalOperator (fun k => (n.descFactorial k : ℝ)) none
          (signedWeylSymbol m Q)) =
      ∑ j : Fin (m + 1),
        MvPolynomial.C (n.descFactorial (j : ℕ) : ℂ) *
          MvPolynomial.rename some (Q j) *
          MvPolynomial.X none ^ (n - (j : ℕ)) := by
  rw [coordinateDiagonalOperator_signedWeylSymbol,
    invertVariable_fintype_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjn : (j : ℕ) ≤ n
  · exact invertVariable_signed_monomial n (j : ℕ) hjn
      (n.descFactorial (j : ℕ) : ℂ) (Q j)
  · have hnj : n < (j : ℕ) := Nat.lt_of_not_ge hjn
    have hzero : (n.descFactorial (j : ℕ) : ℝ) = 0 := by
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hnj]
      norm_num
    have htermzero :
        MvPolynomial.rename some (Q j) *
            MvPolynomial.C
              (((n.descFactorial (j : ℕ) : ℝ) : ℂ) * (-1 : ℂ) ^ (j : ℕ)) *
            MvPolynomial.X none ^ (j : ℕ) = 0 := by
      rw [hzero]
      norm_num
    rw [htermzero, invertVariable_zero,
      Nat.descFactorial_eq_zero_iff_lt.mpr hnj]
    norm_num

private def weylSymbolSubstitution {σ : Type*} (q : σ) :
    Option σ → MvPolynomial (σ ⊕ σ) ℂ :=
  fun o => o.elim
    (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q))
    (fun i => MvPolynomial.X (Sum.inl i))

private theorem bind₁_weylSymbolSubstitution_rename_some {σ : Type*}
    (q : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.bind₁ (weylSymbolSubstitution q) (MvPolynomial.rename some P) =
      MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ) P := by
  rw [MvPolynomial.bind₁_rename, MvPolynomial.rename_eq_aeval]
  rfl

private theorem bind₁_invertVariable_descFactorial_signedWeylSymbol
    {σ : Type*} (q : σ) (m n : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) :
    MvPolynomial.bind₁ (weylSymbolSubstitution q)
        (invertVariable n
          (coordinateDiagonalOperator (fun k => (n.descFactorial k : ℝ)) none
            (signedWeylSymbol m Q))) =
      ∑ j : Fin (m + 1),
        MvPolynomial.C (n.descFactorial (j : ℕ) : ℂ) *
          MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ) (Q j) *
          (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q)) ^
            (n - (j : ℕ)) := by
  rw [invertVariable_descFactorial_signedWeylSymbol, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul, map_mul, map_pow, MvPolynomial.bind₁_C_right,
    bind₁_weylSymbolSubstitution_rename_some,
    MvPolynomial.bind₁_X_right]
  rfl

private theorem finiteOrderWeylOperatorDegreeBox_algebraicSymbol
    {σ : Type*} [Fintype σ] [DecidableEq σ] (q : σ) (m n : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ) (κ : σ → ℕ)
    (hκ : κ q = n) :
    MvPolynomial.algebraicSymbol κ
        (finiteOrderWeylOperatorDegreeBox q m Q κ) =
      MvPolynomial.bind₁ (weylSymbolSubstitution q)
        (invertVariable n
          (coordinateDiagonalOperator (fun k => (n.descFactorial k : ℝ)) none
            (signedWeylSymbol m Q))) *
        ∏ i ∈ Finset.univ.erase q,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i := by
  rw [finiteOrderWeylOperatorDegreeBox_algebraicSymbol_explicit q m n Q κ hκ,
    bind₁_invertVariable_descFactorial_signedWeylSymbol]

private theorem signedWeylSymbol_descFactorial_eq_zero_imp
    {σ : Type*} (m n : ℕ) (Q : Fin (m + 1) → MvPolynomial σ ℂ)
    (hzero : coordinateDiagonalOperator
      (fun k => (n.descFactorial k : ℝ)) none (signedWeylSymbol m Q) = 0) :
    ∀ j : Fin (m + 1), (j : ℕ) ≤ n → Q j = 0 := by
  intro j hj
  have hcoeff := congrArg
    (fun P : MvPolynomial (Option σ) ℂ =>
      (MvPolynomial.optionEquivLeft ℂ σ P).coeff (j : ℕ)) hzero
  rw [optionEquivLeft_coordinateDiagonalOperator_coeff,
    optionEquivLeft_signedWeylSymbol, polynomial_coeff_fintype_sum,
    map_zero, Polynomial.coeff_zero] at hcoeff
  simp only [Polynomial.coeff_C_mul_X_pow] at hcoeff
  rw [Finset.sum_eq_single j] at hcoeff
  · simp only [ite_true] at hcoeff
    have hdescNat : n.descFactorial (j : ℕ) ≠ 0 :=
      Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj)
    have hdesc : (((n.descFactorial (j : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hdescNat
    have hCdesc :
        MvPolynomial.C (((n.descFactorial (j : ℕ) : ℝ) : ℂ)) ≠
          (0 : MvPolynomial σ ℂ) := MvPolynomial.C_ne_zero.mpr hdesc
    have hsign : MvPolynomial.C ((-1 : ℂ) ^ (j : ℕ)) ≠
        (0 : MvPolynomial σ ℂ) := by
      exact MvPolynomial.C_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    exact (mul_eq_zero.mp
      ((mul_eq_zero.mp hcoeff).resolve_left hCdesc)).resolve_right hsign
  · intro k _hk hkj
    have hval : (j : ℕ) ≠ (k : ℕ) := by
      intro h
      exact hkj (Fin.ext h.symm)
    simp only [hval, ↓reduceIte]
  · simp

private theorem degreeOf_pderiv_self_le {σ : Type*} (q : σ)
    (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv q P).degreeOf q ≤ P.degreeOf q - 1 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [map_sum]
  refine (MvPolynomial.degreeOf_sum_le q P.support fun d =>
    MvPolynomial.pderiv q (MvPolynomial.monomial d (P.coeff d))).trans ?_
  apply Finset.sup_le
  intro d hd
  rw [MvPolynomial.pderiv_monomial]
  by_cases hc : P.coeff d * d q = 0
  · simp [hc]
  · rw [MvPolynomial.degreeOf_monomial_eq _ q hc]
    simpa using Nat.sub_le_sub_right
      (MvPolynomial.degreeOf_le_iff.mp le_rfl d hd) 1

private theorem degreeOf_iteratedPDerivAt_le {σ : Type*} (q : σ)
    (j : ℕ) (P : MvPolynomial σ ℂ) :
    (iteratedPDerivAt q j P).degreeOf q ≤ P.degreeOf q - j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [iteratedPDerivAt]
      refine (degreeOf_pderiv_self_le q (iteratedPDerivAt q j P)).trans ?_
      calc
        (iteratedPDerivAt q j P).degreeOf q - 1 ≤
            (P.degreeOf q - j) - 1 := Nat.sub_le_sub_right ih 1
        _ = P.degreeOf q - (j + 1) := Nat.sub_sub _ _ _

private theorem iteratedPDerivAt_eq_zero_of_degreeOf_lt {σ : Type*}
    (q : σ) (j : ℕ) (P : MvPolynomial σ ℂ) (hdegree : P.degreeOf q < j) :
    iteratedPDerivAt q j P = 0 := by
  cases j with
  | zero => simp at hdegree
  | succ j =>
      rw [iteratedPDerivAt]
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
      have hPdegree : P.degreeOf q ≤ j := Nat.lt_succ_iff.mp hdegree
      have hdegreeZero : (iteratedPDerivAt q j P).degreeOf q = 0 := by
        apply Nat.eq_zero_of_le_zero
        exact (degreeOf_iteratedPDerivAt_le q j P).trans (by
          rw [Nat.sub_eq_zero_of_le hPdegree])
      exact not_ne_iff.mpr hdegreeZero

/-- The descending-factorial multiplier kills every coordinate exponent above
the chosen degree.  This is the `n < m` regression used by the finite proof. -/
theorem descFactorial_natCast_eq_zero_of_lt {n m : ℕ} (h : n < m) :
    (n.descFactorial m : ℝ) = 0 := by
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
  norm_num

/-- A zero Jensen polynomial makes the corresponding finite coordinate action
zero on every polynomial of bounded coordinate degree. -/
theorem coordinateDiagonalOperator_eq_zero_of_jensenPolynomial_eq_zero
    {σ : Type*} (d : ℕ) (gamma : ℕ → ℝ) (q : σ)
    (p : MvPolynomial σ ℂ) (hp : p.degreeOf q ≤ d)
    (hJ : jensenPolynomial d gamma = 0) :
    coordinateDiagonalOperator gamma q p = 0 := by
  classical
  ext m
  rw [coeff_coordinateDiagonalOperator]
  by_cases hm : m ∈ p.support
  · have hmle : m q ≤ d := (MvPolynomial.degreeOf_le_iff.mp hp) m hm
    rw [(jensenPolynomial_eq_zero_iff.mp hJ) (m q) hmle]
    simp
  · have hcoeff : p.coeff m = 0 := Finsupp.notMem_support_iff.mp hm
    simp [hcoeff]

/-- The descending-factorial transform of a stable Weyl symbol is stable or
zero after inversion and the positive substitution `w = x_q + y_q`. -/
theorem signedWeylSymbol_descFactorial_invert_bind_zero_or
    {σ : Type*} [Finite σ] (q : σ) (m n : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ)
    (hW : MvUpperHalfPlaneStable (signedWeylSymbol m Q)) :
    MvUpperHalfPlaneStableOrZero
      (MvPolynomial.bind₁
        (fun o : Option σ => o.elim
          (MvPolynomial.X (Sum.inl q) + MvPolynomial.X (Sum.inr q))
          (fun i => MvPolynomial.X (Sum.inl i)))
        (invertVariable n
          (coordinateDiagonalOperator (fun k => (n.descFactorial k : ℝ)) none
            (signedWeylSymbol m Q)))) := by
  have := Fintype.ofFinite σ
  have hdiag := coordinateDiagonalOperator_preserves_stability m
    (fun k => (n.descFactorial k : ℝ)) none
    (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
      (isPFMultiplierSequence_descFactorial n) m)
    (signedWeylSymbol_degreeOf_none_le m Q) hW
  rcases hdiag with hzero | hstable
  · left
    have hinvzero : invertVariable n
        (0 : MvPolynomial (Option σ) ℂ) = 0 := by
      unfold invertVariable
      simp
    rw [hzero, hinvzero]
    exact map_zero _
  · have hinv := MvUpperHalfPlaneStable.invertVariable
      (descFactorialTransform_degreeOf_none_le m n Q) hstable
    right
    apply hinv.bind₁_of_im_eval_pos
    intro o z hz
    cases o with
    | none =>
        simpa only [Option.elim, MvPolynomial.eval_add, MvPolynomial.eval_X,
          Complex.add_im] using
          add_pos (hz (Sum.inl q)) (hz (Sum.inr q))
    | some i =>
        simpa only [Option.elim, MvPolynomial.eval_X] using hz (Sum.inl i)

/-- A stable signed Weyl symbol makes the corresponding finite-order operator
preserve upper-half-plane stability on a coordinate-wise degree box. -/
theorem finiteOrderWeylOperatorDegreeBox_preserves_stability
    {σ : Type*} [Finite σ] (q : σ) (m n : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ)
    (κ : σ → ℕ)
    (hκ : κ q = n)
    (p : MvPolynomial.degreeOfLE σ ℂ κ)
    (hp : MvUpperHalfPlaneStable p.1)
    (hW : MvUpperHalfPlaneStable (signedWeylSymbol m Q)) :
    MvUpperHalfPlaneStableOrZero
      (finiteOrderWeylOperatorDegreeBox q m Q κ p) := by
  classical
  have := Fintype.ofFinite σ
  have hdiag := coordinateDiagonalOperator_preserves_stability m
    (fun k => (n.descFactorial k : ℝ)) none
    (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
      (isPFMultiplierSequence_descFactorial n) m)
    (signedWeylSymbol_degreeOf_none_le m Q) hW
  have hspect : MvUpperHalfPlaneStable
      (∏ i ∈ Finset.univ.erase q,
        (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)) ^ κ i) := by
    classical
    induction Finset.univ.erase q using Finset.induction_on with
    | empty =>
        simpa only [Finset.prod_empty] using
          (MvUpperHalfPlaneStable.one (sigma := σ ⊕ σ))
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi]
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (MvUpperHalfPlaneStable.mul_X_add_X_pow
          (MvUpperHalfPlaneStable.one (sigma := σ ⊕ σ))
          (Sum.inl i) (Sum.inr i) (κ i)).mul ih
  rcases hdiag with hdiagZero | hdiagStable
  · left
    have hQzero := signedWeylSymbol_descFactorial_eq_zero_imp m n Q hdiagZero
    change (∑ j : Fin (m + 1),
      Q j * iteratedPDerivAt q (j : ℕ) p.1) = 0
    apply Finset.sum_eq_zero
    intro j _hj
    by_cases hjn : (j : ℕ) ≤ n
    · rw [hQzero j hjn, zero_mul]
    · have hpDegree : p.1.degreeOf q ≤ n := by
        have hpκ := (MvPolynomial.mem_degreeOfLE_iff_degreeOf p.1).mp p.2 q
        simpa only [hκ] using hpκ
      have hdegree : p.1.degreeOf q < (j : ℕ) :=
        lt_of_le_of_lt hpDegree (Nat.lt_of_not_ge hjn)
      rw [iteratedPDerivAt_eq_zero_of_degreeOf_lt q (j : ℕ) p.1 hdegree,
        mul_zero]
  · have hinvStable := MvUpperHalfPlaneStable.invertVariable
      (descFactorialTransform_degreeOf_none_le m n Q) hdiagStable
    have hbaseStable : MvUpperHalfPlaneStable
        (MvPolynomial.bind₁ (weylSymbolSubstitution q)
          (invertVariable n
            (coordinateDiagonalOperator (fun k => (n.descFactorial k : ℝ)) none
              (signedWeylSymbol m Q)))) := by
      apply hinvStable.bind₁_of_im_eval_pos
      intro o z hz
      cases o with
      | none =>
          simpa only [weylSymbolSubstitution, Option.elim,
            MvPolynomial.eval_add, MvPolynomial.eval_X, Complex.add_im] using
            add_pos (hz (Sum.inl q)) (hz (Sum.inr q))
      | some i =>
          simpa only [weylSymbolSubstitution, Option.elim,
            MvPolynomial.eval_X] using hz (Sum.inl i)
    have hsymbol : MvUpperHalfPlaneStable
        (MvPolynomial.algebraicSymbol κ
          (finiteOrderWeylOperatorDegreeBox q m Q κ)) := by
      rw [finiteOrderWeylOperatorDegreeBox_algebraicSymbol q m n Q κ hκ]
      exact hbaseStable.mul hspect
    exact finiteSymbol_preserves_stability_general κ
      (finiteOrderWeylOperatorDegreeBox q m Q κ) hsymbol p hp

/-- A finite-order differential operator with stable signed Weyl symbol sends
every upper-half-plane stable polynomial to a stable polynomial or zero. -/
theorem finiteOrderWeylOperator_preserves_stability
    {σ : Type*} [Finite σ] (q : σ) (m : ℕ)
    (Q : Fin (m + 1) → MvPolynomial σ ℂ)
    (hW : MvUpperHalfPlaneStable (signedWeylSymbol m Q))
    {p : MvPolynomial σ ℂ} (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStableOrZero (finiteOrderWeylOperator q m Q p) := by
  classical
  let _ := Fintype.ofFinite σ
  let κ : σ → ℕ := fun i => p.degreeOf i
  have hpκ : p ∈ MvPolynomial.degreeOfLE σ ℂ κ := by
    rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
    intro i
    exact le_rfl
  let pκ : MvPolynomial.degreeOfLE σ ℂ κ := ⟨p, hpκ⟩
  have hresult := finiteOrderWeylOperatorDegreeBox_preserves_stability
    q m (κ q) Q κ rfl pκ hp hW
  exact hresult

end

end RealRooted.BorceaBranden
