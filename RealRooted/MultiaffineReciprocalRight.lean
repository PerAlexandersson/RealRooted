import RealRooted.MultiaffineReciprocal

/-!
# Signed multiaffine reciprocal in a right variable block

This file defines the signed reciprocal transform in only the right-hand
variables of a polynomial indexed by `Sum tau sigma`.  The variables indexed
by `tau` are left unchanged and need not have bounded degree.  This is the
reciprocal operation used in the proof of Borcea--Branden Lemma 2.2.
-/

open BigOperators

namespace RealRooted

noncomputable section

/-- The total exponent in the right-hand variable block. -/
def rightExponentSum {tau sigma : Type*} (d : Sum tau sigma ->₀ ℕ) : ℕ :=
  (Finsupp.sumFinsuppEquivProdFinsupp d).2.sum fun _ n => n

theorem rightExponentSum_eq {tau sigma : Type*} [Fintype sigma]
    (d : Sum tau sigma ->₀ ℕ) :
    rightExponentSum d = ∑ i : sigma, d (Sum.inr i) := by
  rw [rightExponentSum, Finsupp.sum_fintype _ _ (by simp)]
  rfl

/-- Complement exponents in the right-hand multiaffine cube while leaving all
left-hand exponents unchanged. -/
def complementRightExponent {tau sigma : Type*} [Fintype sigma]
    (d : Sum tau sigma ->₀ ℕ) : Sum tau sigma ->₀ ℕ :=
  let e := Finsupp.sumFinsuppEquivProdFinsupp d
  Finsupp.sumFinsuppEquivProdFinsupp.symm
    (e.1, complementExponent e.2)

@[simp] theorem complementRightExponent_inl
    {tau sigma : Type*} [Fintype sigma]
    (d : Sum tau sigma ->₀ ℕ) (i : tau) :
    complementRightExponent d (Sum.inl i) = d (Sum.inl i) := by
  rfl

@[simp] theorem complementRightExponent_inr
    {tau sigma : Type*} [Fintype sigma]
    (d : Sum tau sigma ->₀ ℕ) (i : sigma) :
    complementRightExponent d (Sum.inr i) = 1 - d (Sum.inr i) := by
  rfl

/-- The polynomial realization of signed reciprocal substitution in only the
right-hand block:
`P(z, w) -> (prod i, w i) * P(z, -w⁻¹)`.

This definition uses the exact reciprocal convention; it does not include the
additional global sign sometimes used to normalize the expansion in the
statement of Borcea--Branden Lemma 2.2. -/
def signedMultiaffineReciprocalRight
    {R tau sigma : Type*} [CommRing R] [Fintype sigma]
    (P : MvPolynomial (Sum tau sigma) R) :
    MvPolynomial (Sum tau sigma) R :=
  P.sum fun d c =>
    MvPolynomial.monomial (complementRightExponent d)
      ((-1 : R) ^ rightExponentSum d * c)

theorem signedMultiaffineReciprocalRight_add
    {R tau sigma : Type*} [CommRing R] [Fintype sigma]
    (P Q : MvPolynomial (Sum tau sigma) R) :
    signedMultiaffineReciprocalRight (P + Q) =
      signedMultiaffineReciprocalRight P +
        signedMultiaffineReciprocalRight Q := by
  classical
  unfold signedMultiaffineReciprocalRight
  apply Finsupp.sum_add_index
  · intro d hd
    simp
  · intro d hd a b
    simp [mul_add]

@[simp] theorem signedMultiaffineReciprocalRight_zero
    {R tau sigma : Type*} [CommRing R] [Fintype sigma] :
    signedMultiaffineReciprocalRight
      (0 : MvPolynomial (Sum tau sigma) R) = 0 := by
  classical
  rw [signedMultiaffineReciprocalRight, MvPolynomial.sum_def]
  simp

theorem signedMultiaffineReciprocalRight_sum
    {R tau sigma alpha : Type*} [CommRing R] [Fintype sigma]
    (s : Finset alpha) (P : alpha -> MvPolynomial (Sum tau sigma) R) :
    signedMultiaffineReciprocalRight (∑ i ∈ s, P i) =
      ∑ i ∈ s, signedMultiaffineReciprocalRight (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, signedMultiaffineReciprocalRight_add, ih,
        Finset.sum_insert ha]

@[simp] theorem signedMultiaffineReciprocalRight_monomial
    {R tau sigma : Type*} [CommRing R] [Fintype sigma]
    (d : Sum tau sigma ->₀ ℕ) (c : R) :
    signedMultiaffineReciprocalRight (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (complementRightExponent d)
        ((-1 : R) ^ rightExponentSum d * c) := by
  unfold signedMultiaffineReciprocalRight
  rw [MvPolynomial.sum_monomial_eq (by simp)]

/-- The reciprocal transform has degree at most one in every right-hand
coordinate, independently of the degrees in the left-hand block. -/
theorem degreeOf_signedMultiaffineReciprocalRight_inr_le_one
    {R tau sigma : Type*} [CommRing R] [Fintype sigma]
    (P : MvPolynomial (Sum tau sigma) R) (i : sigma) :
    (signedMultiaffineReciprocalRight P).degreeOf (Sum.inr i) <= 1 := by
  classical
  unfold signedMultiaffineReciprocalRight
  rw [MvPolynomial.sum_def]
  refine (MvPolynomial.degreeOf_sum_le (Sum.inr i) P.support fun d =>
    MvPolynomial.monomial (complementRightExponent d)
      ((-1 : R) ^ rightExponentSum d * MvPolynomial.coeff d P)).trans ?_
  apply Finset.sup_le
  intro d hd
  by_cases hc :
      (-1 : R) ^ rightExponentSum d * MvPolynomial.coeff d P = 0
  · simp [hc, MvPolynomial.degreeOf_zero]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ hc]
    simp

private theorem eval_signedMultiaffineReciprocalRight_term
    {R tau sigma : Type*} [Field R] [Fintype sigma]
    (d : Sum tau sigma ->₀ ℕ)
    (hd : ∀ i : sigma, d (Sum.inr i) <= 1) (c : R)
    (z : Sum tau sigma -> R) (hz : ∀ i : sigma, z (Sum.inr i) != 0) :
    MvPolynomial.eval z
        (MvPolynomial.monomial (complementRightExponent d)
          ((-1 : R) ^ rightExponentSum d * c)) =
      (∏ i : sigma, z (Sum.inr i)) *
        MvPolynomial.eval
          (Sum.elim
            (fun i => z (Sum.inl i))
            (fun i => -(z (Sum.inr i))⁻¹))
          (MvPolynomial.monomial d c) := by
  let dl : tau ->₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp d).1
  let dr : sigma ->₀ ℕ := (Finsupp.sumFinsuppEquivProdFinsupp d).2
  have hd_eq : d = Finsupp.sumElim dl dr := by
    change d = Finsupp.sumFinsuppEquivProdFinsupp.symm
      (Finsupp.sumFinsuppEquivProdFinsupp d)
    exact (Finsupp.sumFinsuppEquivProdFinsupp.symm_apply_apply d).symm
  have hdright : ∀ i : sigma, dr i <= 1 := by
    intro i
    exact hd i
  have hcomplement :
      (complementRightExponent d).prod (fun i n => z i ^ n) =
        dl.prod (fun i n => z (Sum.inl i) ^ n) *
          ∏ i : sigma, z (Sum.inr i) ^ (1 - dr i) := by
    change
      (Finsupp.sumElim dl (complementExponent dr)).prod
          (fun i n => z i ^ n) = _
    rw [Finsupp.prod_sumElim]
    change dl.prod (fun i n => z (Sum.inl i) ^ n) *
      (complementExponent dr).prod
        (fun i n => z (Sum.inr i) ^ n) = _
    rw [Finsupp.prod_fintype (complementExponent dr)
      (fun i n => z (Sum.inr i) ^ n) (by simp)]
    simp only [complementExponent_apply]
  have horiginal :
      d.prod
          (fun i n =>
            (Sum.elim
              (fun j => z (Sum.inl j))
              (fun j => -(z (Sum.inr j))⁻¹) i) ^ n) =
        dl.prod (fun i n => z (Sum.inl i) ^ n) *
          ∏ i : sigma, (-(z (Sum.inr i))⁻¹) ^ dr i := by
    rw [hd_eq, Finsupp.prod_sumElim]
    change dl.prod (fun i n => z (Sum.inl i) ^ n) *
      dr.prod (fun i n => (-(z (Sum.inr i))⁻¹) ^ n) = _
    rw [Finsupp.prod_fintype dr
      (fun i n => (-(z (Sum.inr i))⁻¹) ^ n) (by simp)]
  have hrightExponentSum :
      rightExponentSum d = ∑ i : sigma, dr i := by
    rw [rightExponentSum_eq]
    rfl
  have hprod :
      ∏ i : sigma,
          ((-1 : R) ^ dr i * z (Sum.inr i) ^ (1 - dr i)) =
        ∏ i : sigma,
          (z (Sum.inr i) * (-(z (Sum.inr i))⁻¹) ^ dr i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hdright i) with hdi | hdi
    · simp [hdi]
    · simp [hdi, hz i]
  simp only [MvPolynomial.eval_monomial]
  rw [hcomplement, horiginal, hrightExponentSum,
    ← Finset.prod_pow_eq_pow_sum Finset.univ dr (-1)]
  calc
    ((∏ i : sigma, (-1 : R) ^ dr i) * c) *
          (dl.prod (fun i n => z (Sum.inl i) ^ n) *
            ∏ i : sigma, z (Sum.inr i) ^ (1 - dr i)) =
        c * dl.prod (fun i n => z (Sum.inl i) ^ n) *
          ∏ i : sigma,
            ((-1 : R) ^ dr i * z (Sum.inr i) ^ (1 - dr i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = c * dl.prod (fun i n => z (Sum.inl i) ^ n) *
          ∏ i : sigma,
            (z (Sum.inr i) * (-(z (Sum.inr i))⁻¹) ^ dr i) := by
      rw [hprod]
    _ = (∏ i : sigma, z (Sum.inr i)) *
          (c * (dl.prod (fun i n => z (Sum.inl i) ^ n) *
            ∏ i : sigma, (-(z (Sum.inr i))⁻¹) ^ dr i)) := by
      rw [Finset.prod_mul_distrib]
      ring

/-- Evaluation of the right-block signed reciprocal away from the right
coordinate hyperplanes.  No condition is imposed on the left block. -/
theorem eval_signedMultiaffineReciprocalRight
    {R tau sigma : Type*} [Field R] [Fintype sigma]
    {P : MvPolynomial (Sum tau sigma) R}
    (hP : ∀ i : sigma, P.degreeOf (Sum.inr i) <= 1)
    (z : Sum tau sigma -> R)
    (hz : ∀ i : sigma, z (Sum.inr i) != 0) :
    MvPolynomial.eval z (signedMultiaffineReciprocalRight P) =
      (∏ i : sigma, z (Sum.inr i)) *
        MvPolynomial.eval
          (Sum.elim
            (fun i => z (Sum.inl i))
            (fun i => -(z (Sum.inr i))⁻¹)) P := by
  unfold signedMultiaffineReciprocalRight
  rw [MvPolynomial.sum_def, MvPolynomial.eval_sum]
  conv_rhs => rw [MvPolynomial.as_sum P, MvPolynomial.eval_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_signedMultiaffineReciprocalRight_term d
    (fun i => MvPolynomial.degreeOf_le_iff.mp (hP i) d hd)
    (MvPolynomial.coeff d P) z hz

/-- Signed reciprocal substitution in the right-hand block preserves
upper-half-plane stability while leaving all left-hand coordinates unchanged. -/
theorem MvUpperHalfPlaneStable.signedMultiaffineReciprocalRight
    {tau sigma : Type*} [Fintype sigma]
    {P : MvPolynomial (Sum tau sigma) ℂ}
    (hstable : MvUpperHalfPlaneStable P)
    (hP : ∀ i : sigma, P.degreeOf (Sum.inr i) <= 1) :
    MvUpperHalfPlaneStable (signedMultiaffineReciprocalRight P) := by
  intro z hz
  have hz0 : ∀ i : sigma, z (Sum.inr i) != 0 := fun i hzero => by
    have him := hz (Sum.inr i)
    rw [hzero] at him
    simp at him
  rw [eval_signedMultiaffineReciprocalRight hP z hz0]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i hi => hz0 i
  · apply hstable
    intro i
    rcases i with i | i
    · exact hz (Sum.inl i)
    · change 0 < -((z (Sum.inr i))⁻¹).im
      rw [Complex.inv_im]
      simpa only [neg_div, neg_neg] using
        div_pos (hz (Sum.inr i)) (Complex.normSq_pos.mpr (hz0 i))

end

end RealRooted
