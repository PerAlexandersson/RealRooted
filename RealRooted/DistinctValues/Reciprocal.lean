module

public import RealRooted.Multiaffine.Reciprocal
public import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative
public import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize
import RealRooted.Permanent.Stability.Fractional
import Mathlib.Algebra.MvPolynomial.Funext
import RealRooted.Multiaffine.AffineLineRestriction

/-!
# Positive multiaffine reciprocation

Complementation of exponents realizes `P(z) ↦ (∏ i, z_i) P(1/z)`.
For real multiaffine polynomials this preserves stability and nonnegative
coefficients. This is the change of variables used for the marked distinct-value
operator in RealRooted issue #2640.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted.DistinctValues

noncomputable section

/-- Positive reciprocation in the multiaffine exponent cube. -/
def reciprocal {σ R : Type*} [Fintype σ] [CommSemiring R]
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  P.coeff.sum fun d c => MvPolynomial.monomial (complementExponent d) c

/-- The reciprocal of zero is zero. -/
@[simp] theorem reciprocal_zero {σ R : Type*} [Fintype σ] [CommSemiring R] :
    reciprocal (0 : MvPolynomial σ R) = 0 := by simp [reciprocal]

/-- Positive reciprocation is additive. -/
theorem reciprocal_add {σ R : Type*} [Fintype σ] [CommSemiring R]
    (P Q : MvPolynomial σ R) : reciprocal (P + Q) = reciprocal P + reciprocal Q := by
  classical
  unfold reciprocal
  apply Finsupp.sum_add_index <;> simp

/-- Positive reciprocation commutes with finite sums. -/
theorem reciprocal_sum {σ R ι : Type*} [Fintype σ] [CommSemiring R]
    (s : Finset ι) (P : ι → MvPolynomial σ R) :
    reciprocal (∑ i ∈ s, P i) = ∑ i ∈ s, reciprocal (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reciprocal]
  | @insert i s hi ih => rw [Finset.sum_insert hi, reciprocal_add, ih, Finset.sum_insert hi]

/-- The reciprocal of a monomial complements its exponent. -/
@[simp] theorem reciprocal_monomial {σ R : Type*} [Fintype σ] [CommSemiring R]
    (d : σ →₀ ℕ) (c : R) :
    reciprocal (MvPolynomial.monomial d c) = MvPolynomial.monomial (complementExponent d) c := by
  unfold reciprocal
  exact MvPolynomial.sum_monomial_eq (by simp)

/-- Every reciprocal is multiaffine. -/
theorem reciprocal_isMultiaffine {σ R : Type*} [Fintype σ] [CommSemiring R]
    (P : MvPolynomial σ R) : MvPolynomial.IsMultiaffine (reciprocal P) := by
  classical
  intro i
  rw [reciprocal, MvPolynomial.sum_def]
  refine (MvPolynomial.degreeOf_sum_le i P.support _).trans ?_
  apply Finset.sup_le
  intro d hd
  by_cases hc : P.coeff d = 0
  · simp [hc]
  · rw [MvPolynomial.degreeOf_monomial_eq _ i hc]
    exact Nat.sub_le _ _

/-- Positive reciprocation preserves coefficientwise nonnegativity. -/
theorem reciprocal_hasNonnegCoeffs {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hP : P.HasNonnegCoeffs) :
    (reciprocal P).HasNonnegCoeffs := by
  classical
  rw [reciprocal, MvPolynomial.sum_def]
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro d hd m
  rw [MvPolynomial.coeff_monomial]
  split
  · exact hP d
  · exact le_rfl

/-- Complementing a squarefree monomial gives its reciprocal evaluation formula. -/
private theorem eval_reciprocal_monomial
    {σ K : Type*} [Fintype σ] [Field K]
    (d : σ →₀ ℕ) (hd : ∀ i, d i ≤ 1) (c : K)
    (z : σ → K) (hz : ∀ i, z i ≠ 0) :
    MvPolynomial.eval z (MvPolynomial.monomial (complementExponent d) c) =
      (∏ i, z i) * MvPolynomial.eval (fun i => (z i)⁻¹) (MvPolynomial.monomial d c) := by
  simp only [MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype (complementExponent d) (fun i e => z i ^ e) (by simp),
    Finsupp.prod_fintype d (fun i e => (z i)⁻¹ ^ e) (by simp)]
  have hprod : ∏ i, z i ^ (complementExponent d) i =
      ∏ i, (z i * ((z i)⁻¹ ^ d i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd i) with h | h <;> simp [h, hz i]
  rw [hprod, Finset.prod_mul_distrib]
  ring

/-- Evaluation of positive reciprocation away from the coordinate hyperplanes. -/
theorem eval_reciprocal {σ K : Type*} [Fintype σ] [Field K]
    {P : MvPolynomial σ K} (hP : MvPolynomial.IsMultiaffine P)
    (z : σ → K) (hz : ∀ i, z i ≠ 0) :
    MvPolynomial.eval z (reciprocal P) =
      (∏ i, z i) * MvPolynomial.eval (fun i => (z i)⁻¹) P := by
  classical
  rw [reciprocal, MvPolynomial.sum_def, MvPolynomial.eval_sum]
  conv_rhs => rw [MvPolynomial.as_sum P, MvPolynomial.eval_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_reciprocal_monomial d
    (fun i => MvPolynomial.degreeOf_le_iff.mp (hP i) d hd) (P.coeff d) z hz

/-- Positive reciprocation commutes with coefficient maps. -/
theorem reciprocal_map {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial σ R) :
    reciprocal (MvPolynomial.map f P) = MvPolynomial.map f (reciprocal P) := by
  classical
  rw [MvPolynomial.as_sum P, map_sum, reciprocal_sum]
  simp only [MvPolynomial.map_monomial, reciprocal_monomial, reciprocal_sum, map_sum]

/-- Complementing a multiaffine exponent twice recovers it. -/
theorem reciprocal_reciprocal {σ R : Type*} [Fintype σ] [CommSemiring R]
    {P : MvPolynomial σ R} (hP : MvPolynomial.IsMultiaffine P) :
    reciprocal (reciprocal P) = P := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P, reciprocal_sum, reciprocal_sum]
  simp only [reciprocal_monomial]
  conv_rhs => rw [MvPolynomial.as_sum P]
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg (fun e => MvPolynomial.monomial e (P.coeff d))
  ext i
  have hi := MvPolynomial.degreeOf_le_iff.mp (hP i) d hd
  simp only [complementExponent_apply]
  lia

/-- Positive reciprocation preserves real stability on multiaffine polynomials. -/
theorem reciprocal_mvRealStable {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    (hma : MvPolynomial.IsMultiaffine P) : MvRealStable (reciprocal P) := by
  intro z hz
  have hz0 : ∀ i, z i ≠ 0 := fun i h => by simpa [h] using hz i
  rw [complexifyMv, ← reciprocal_map]
  have hmap : MvPolynomial.IsMultiaffine (MvPolynomial.map Complex.ofRealHom P) := by
    intro i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact MvPolynomial.degreeOf_le_iff.mp (hma i) d
      (MvPolynomial.support_map_subset _ _ hd)
  rw [eval_reciprocal hmap z hz0]
  apply mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hz0 i)
  apply hP.eval_ne_zero_of_im_neg
  intro i
  rw [Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (hz i)) (Complex.normSq_pos.mpr (hz0 i))

/-- Positive reciprocation commutes with scalar multiplication. -/
theorem reciprocal_C_mul {σ : Type*} [Fintype σ]
    (a : ℝ) (P : MvPolynomial σ ℝ) :
    reciprocal (MvPolynomial.C a * P) = MvPolynomial.C a * reciprocal P := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P, Finset.mul_sum]
  rw [reciprocal_sum]
  conv_rhs => rw [MvPolynomial.as_sum P, reciprocal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [MvPolynomial.C_mul_monomial]

/-- Marking a coordinate after its value-one specialization is multiaffine. -/
theorem mark_isMultiaffine {σ : Type*} {P : MvPolynomial σ ℝ}
    (hP : P.IsMultiaffine) (i : σ) :
    (MvPolynomial.X i * MvPolynomial.specializeAt i 1 P).IsMultiaffine := by
  classical
  apply (RealRooted.MvPolynomial.IsMultiaffine.specializeAt_preserves hP i 1).X_mul_of_notMem_vars
  rw [RealRooted.MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv hP]
  intro hi
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hi) with hi | hi
  · exact (Finset.mem_erase.mp (MvPolynomial.vars_specializeZero_subset_erase P i hi)).1 rfl
  · exact hP.notMem_vars_pderiv_self i hi

/-- Positive reciprocation exchanges marking and value-one specialization. -/
theorem reciprocal_mark {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsMultiaffine) (i : σ) :
    reciprocal (MvPolynomial.X i * MvPolynomial.specializeAt i 1 P) =
      MvPolynomial.specializeAt i 1 (reciprocal P) := by
  classical
  apply MvPolynomial.funext_set (fun _ => {x : ℝ | x ≠ 0})
  · intro j
    have heq : {x : ℝ | x ≠ 0} = Set.univ \ {0} := by ext x; simp
    rw [heq]
    exact Set.infinite_univ.sdiff (Set.finite_singleton 0)
  · intro z hz
    have hz0 : ∀ j, z j ≠ 0 := fun j => hz j (Set.mem_univ j)
    have hu0 : ∀ j, Function.update z i 1 j ≠ 0 := by
      intro j
      by_cases hji : j = i <;> simp [hji, hz0 j]
    have hinv : (fun j => (Function.update z i 1 j)⁻¹) =
        Function.update (fun j => (z j)⁻¹) i 1 := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    rw [eval_reciprocal (mark_isMultiaffine hP i) z hz0,
      MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_specializeAt,
      MvPolynomial.eval_specializeAt, eval_reciprocal hP _ hu0, hinv]
    rw [Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
      ← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    field_simp [hz0 i]

/-- The total degree of a multiaffine polynomial is bounded by the number of coordinates. -/
theorem totalDegree_le_card {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : P.IsMultiaffine) : P.totalDegree ≤ Fintype.card σ := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro d hd
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i, d i ≤ ∑ _i : σ, 1 := Finset.sum_le_sum fun i _ =>
      MvPolynomial.degreeOf_le_iff.mp (hP i) d hd
    _ = Fintype.card σ := by simp

end

end RealRooted.DistinctValues
