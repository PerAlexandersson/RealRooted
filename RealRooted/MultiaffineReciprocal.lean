import RealRooted.Multiaffine
import RealRooted.MultivariateStability

/-!
# Multiaffine reciprocal transforms

This file defines the signed complement of a multiaffine multivariate
polynomial. On evaluation, it is the polynomial realization of
`P(z) ↦ ∏ i, z i * P(-1 / z)`, which preserves upper-half-plane stability.
-/

open BigOperators

namespace RealRooted

noncomputable section

/-- Complement every exponent inside the multiaffine cube. -/
def complementExponent {sigma : Type*} [Fintype sigma] (d : sigma →₀ ℕ) :
    sigma →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => 1 - d i

@[simp] theorem complementExponent_apply {sigma : Type*} [Fintype sigma]
    (d : sigma →₀ ℕ) (i : sigma) :
    complementExponent d i = 1 - d i := by
  rfl

/-- The polynomial realization of the signed reciprocal transform
`P(z) ↦ ∏ i, z i * P(-1 / z)`. -/
def signedMultiaffineReciprocal
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  P.sum fun d c =>
    MvPolynomial.monomial (complementExponent d)
      ((-1 : R) ^ (d.sum fun _ n => n) * c)

theorem signedMultiaffineReciprocal_add
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (P Q : MvPolynomial sigma R) :
    signedMultiaffineReciprocal (P + Q) =
      signedMultiaffineReciprocal P + signedMultiaffineReciprocal Q := by
  classical
  unfold signedMultiaffineReciprocal
  apply Finsupp.sum_add_index
  · intro d hd
    simp
  · intro d hd a b
    simp [mul_add]

@[simp] theorem signedMultiaffineReciprocal_zero
    {R sigma : Type*} [CommRing R] [Fintype sigma] :
    signedMultiaffineReciprocal (0 : MvPolynomial sigma R) = 0 := by
  classical
  rw [signedMultiaffineReciprocal, MvPolynomial.sum_def]
  simp

theorem signedMultiaffineReciprocal_sum
    {R sigma alpha : Type*} [CommRing R] [Fintype sigma]
    (s : Finset alpha) (P : alpha → MvPolynomial sigma R) :
    signedMultiaffineReciprocal (∑ i ∈ s, P i) =
      ∑ i ∈ s, signedMultiaffineReciprocal (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, signedMultiaffineReciprocal_add, ih,
        Finset.sum_insert ha]

@[simp] theorem signedMultiaffineReciprocal_monomial
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (d : sigma →₀ ℕ) (c : R) :
    signedMultiaffineReciprocal (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (complementExponent d)
        ((-1 : R) ^ (d.sum fun _ n => n) * c) := by
  unfold signedMultiaffineReciprocal
  rw [MvPolynomial.sum_monomial_eq (by simp)]

private theorem complementExponent_sum_single_one
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (t : Finset sigma) :
    complementExponent (∑ i ∈ t, Finsupp.single i 1) =
      ∑ i ∈ tᶜ, Finsupp.single i 1 := by
  classical
  rw [← Finsupp.indicator_eq_sum_single t (fun _ => 1),
    ← Finsupp.indicator_eq_sum_single tᶜ (fun _ => 1)]
  ext i
  by_cases hi : i ∈ t <;> simp [complementExponent_apply, hi]

private theorem sum_sum_single_one
    {sigma : Type*} (t : Finset sigma) :
    (∑ i ∈ t, Finsupp.single i 1).sum (fun _ n => n) = t.card := by
  classical
  rw [← Finsupp.indicator_eq_sum_single t (fun _ => 1),
    Finsupp.sum_indicator_index (fun _ => 1) (by simp)]
  simp

/-- Signed multiaffine reciprocation sends an elementary symmetric polynomial
to its complementary elementary symmetric polynomial, up to sign. -/
theorem signedMultiaffineReciprocal_esymm
    {R : Type*} [CommRing R] (N k : ℕ) (hk : k ≤ N) :
    signedMultiaffineReciprocal (MvPolynomial.esymm (Fin N) R k) =
      MvPolynomial.C ((-1 : R) ^ k) *
        MvPolynomial.esymm (Fin N) R (N - k) := by
  classical
  calc
    signedMultiaffineReciprocal (MvPolynomial.esymm (Fin N) R k) =
        ∑ t ∈ Finset.powersetCard k Finset.univ,
          MvPolynomial.monomial
            (∑ i ∈ tᶜ, Finsupp.single i 1) ((-1 : R) ^ k) := by
      rw [MvPolynomial.esymm_eq_sum_monomial,
        signedMultiaffineReciprocal_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [signedMultiaffineReciprocal_monomial,
        complementExponent_sum_single_one, sum_sum_single_one]
      rw [(Finset.mem_powersetCard.mp ht).2]
      simp
    _ = ∑ u ∈ Finset.powersetCard (N - k) Finset.univ,
          MvPolynomial.monomial
            (∑ i ∈ u, Finsupp.single i 1) ((-1 : R) ^ k) := by
      refine Finset.sum_bij (fun t _ => tᶜ) ?_ ?_ ?_ ?_
      · intro t ht
        rcases Finset.mem_powersetCard.mp ht with ⟨htsub, htcard⟩
        exact Finset.mem_powersetCard.mpr
          ⟨by simp, by simp [Finset.card_compl, htcard]⟩
      · intro t₁ ht₁ t₂ ht₂ hcompl
        exact compl_injective hcompl
      · intro u hu
        refine ⟨uᶜ, ?_, by simp⟩
        rcases Finset.mem_powersetCard.mp hu with ⟨husub, hucard⟩
        exact Finset.mem_powersetCard.mpr
          ⟨by simp, by simp [Finset.card_compl, hucard,
            Nat.sub_sub_self hk]⟩
      · intro t ht
        simp
    _ = MvPolynomial.C ((-1 : R) ^ k) *
          MvPolynomial.esymm (Fin N) R (N - k) := by
      rw [MvPolynomial.esymm_eq_sum_monomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [MvPolynomial.C_mul_monomial]
      simp

/-- The signed reciprocal transform is multiaffine. -/
theorem isMultiaffine_signedMultiaffineReciprocal
    {R sigma : Type*} [CommRing R] [Fintype sigma]
    (P : MvPolynomial sigma R) :
    MvPolynomial.IsMultiaffine (signedMultiaffineReciprocal P) := by
  intro i
  unfold signedMultiaffineReciprocal
  rw [MvPolynomial.sum_def]
  refine (MvPolynomial.degreeOf_sum_le i P.support fun d =>
    MvPolynomial.monomial (complementExponent d)
      ((-1 : R) ^ (d.sum fun _ n => n) * MvPolynomial.coeff d P)).trans ?_
  apply Finset.sup_le
  intro d hd
  by_cases hc :
      (-1 : R) ^ (d.sum fun _ n => n) * MvPolynomial.coeff d P = 0
  · simp [hc, MvPolynomial.degreeOf_zero]
  · rw [MvPolynomial.degreeOf_monomial_eq _ i hc]
    simp

private theorem eval_signedMultiaffineReciprocal_term
    {R sigma : Type*} [Field R] [Fintype sigma]
    (d : sigma →₀ ℕ) (hd : ∀ i, d i ≤ 1) (c : R)
    (z : sigma → R) (hz : ∀ i, z i ≠ 0) :
    MvPolynomial.eval z
        (MvPolynomial.monomial (complementExponent d)
          ((-1 : R) ^ (d.sum fun _ n => n) * c)) =
      (∏ i, z i) *
        MvPolynomial.eval (fun i => -(z i)⁻¹)
          (MvPolynomial.monomial d c) := by
  simp only [MvPolynomial.eval_monomial]
  rw [Finsupp.sum_fintype d (fun _ n => n) (by simp),
    Finsupp.prod_fintype (complementExponent d) (fun i e => z i ^ e)
      (by simp),
    Finsupp.prod_fintype d (fun i e => (-(z i)⁻¹) ^ e) (by simp),
    ← Finset.prod_pow_eq_pow_sum Finset.univ d (-1)]
  have hprod :
      ∏ i, ((-1 : R) ^ d i * z i ^ (complementExponent d) i) =
        ∏ i, (z i * (-(z i)⁻¹) ^ d i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp (hd i)) with hdi | hdi
    · simp [hdi]
    · simp [hdi, hz i]
  calc
    (∏ i, (-1 : R) ^ d i) * c *
          ∏ i, z i ^ (complementExponent d) i =
        c * ∏ i, ((-1 : R) ^ d i *
          z i ^ (complementExponent d) i) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = c * ∏ i, (z i * (-(z i)⁻¹) ^ d i) := by rw [hprod]
    _ = (∏ i, z i) * (c * ∏ i, (-(z i)⁻¹) ^ d i) := by
      rw [Finset.prod_mul_distrib]
      ring

/-- Evaluation of the signed reciprocal transform away from the coordinate
hyperplanes. -/
theorem eval_signedMultiaffineReciprocal
    {R sigma : Type*} [Field R] [Fintype sigma]
    {P : MvPolynomial sigma R} (hP : MvPolynomial.IsMultiaffine P)
    (z : sigma → R) (hz : ∀ i, z i ≠ 0) :
    MvPolynomial.eval z (signedMultiaffineReciprocal P) =
      (∏ i, z i) * MvPolynomial.eval (fun i => -(z i)⁻¹) P := by
  unfold signedMultiaffineReciprocal
  rw [MvPolynomial.sum_def, MvPolynomial.eval_sum]
  conv_rhs => rw [MvPolynomial.as_sum P, MvPolynomial.eval_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact eval_signedMultiaffineReciprocal_term d
    (fun i => MvPolynomial.degreeOf_le_iff.mp (hP i) d hd)
    (MvPolynomial.coeff d P) z hz

/-- Signed reciprocation factors over products in disjoint variable blocks. -/
theorem signedMultiaffineReciprocal_rename_mul_rename
    {sigma tau : Type*} [Fintype sigma] [Fintype tau]
    {F : MvPolynomial sigma ℂ} {G : MvPolynomial tau ℂ}
    (hF : MvPolynomial.IsMultiaffine F)
    (hG : MvPolynomial.IsMultiaffine G) :
    signedMultiaffineReciprocal
        (MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G) =
      MvPolynomial.rename Sum.inl (signedMultiaffineReciprocal F) *
        MvPolynomial.rename Sum.inr (signedMultiaffineReciprocal G) := by
  let s : Sum sigma tau → Set ℂ := fun _ => {z | z ≠ 0}
  apply MvPolynomial.funext_set s
  · intro i
    exact Set.infinite_of_injective_forall_mem UpperHalfPlane.coe_injective
      fun z => fun hzero => by
        have hz := z.coe_im_pos
        rw [hzero] at hz
        simp at hz
  · intro z hz
    have hz0 : ∀ i, z i ≠ 0 := fun i => hz i (Set.mem_univ i)
    have hleft0 : ∀ i, z (Sum.inl i) ≠ 0 := fun i => hz0 (Sum.inl i)
    have hright0 : ∀ i, z (Sum.inr i) ≠ 0 := fun i => hz0 (Sum.inr i)
    have hma : MvPolynomial.IsMultiaffine
        (MvPolynomial.rename Sum.inl F * MvPolynomial.rename Sum.inr G) := by
      apply (hF.rename Sum.inl_injective).mul_of_disjoint_vars
        (hG.rename Sum.inr_injective)
      rw [Finset.disjoint_left]
      intro v hvleft hvright
      obtain ⟨i, hi, hiv⟩ :=
        MvPolynomial.mem_vars_rename Sum.inl F hvleft
      obtain ⟨j, hj, hjv⟩ :=
        MvPolynomial.mem_vars_rename Sum.inr G hvright
      exact Sum.inl_ne_inr (hiv.trans hjv.symm)
    rw [eval_signedMultiaffineReciprocal hma z hz0]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_rename]
    rw [eval_signedMultiaffineReciprocal hF (z ∘ Sum.inl) hleft0,
      eval_signedMultiaffineReciprocal hG (z ∘ Sum.inr) hright0,
      Fintype.prod_sum_type]
    change
      ((∏ i : sigma, z (Sum.inl i)) * ∏ i : tau, z (Sum.inr i)) *
          (MvPolynomial.eval (fun i => -(z (Sum.inl i))⁻¹) F *
            MvPolynomial.eval (fun i => -(z (Sum.inr i))⁻¹) G) =
        (∏ i : sigma, z (Sum.inl i)) *
            MvPolynomial.eval (fun i => -(z (Sum.inl i))⁻¹) F *
          ((∏ i : tau, z (Sum.inr i)) *
            MvPolynomial.eval (fun i => -(z (Sum.inr i))⁻¹) G)
    ring

/-- Signed reciprocation commutes with constant multiplication on multiaffine
complex polynomials. -/
theorem signedMultiaffineReciprocal_C_mul
    {sigma : Type*} [Fintype sigma] {P : MvPolynomial sigma ℂ}
    (hP : MvPolynomial.IsMultiaffine P) (c : ℂ) :
    signedMultiaffineReciprocal (MvPolynomial.C c * P) =
      MvPolynomial.C c * signedMultiaffineReciprocal P := by
  let s : sigma → Set ℂ := fun _ => {z | z ≠ 0}
  apply MvPolynomial.funext_set s
  · intro i
    exact Set.infinite_of_injective_forall_mem UpperHalfPlane.coe_injective
      fun z => fun hzero => by
        have hz := z.coe_im_pos
        rw [hzero] at hz
        simp at hz
  · intro z hz
    have hz0 : ∀ i, z i ≠ 0 := fun i => hz i (Set.mem_univ i)
    rw [eval_signedMultiaffineReciprocal (hP.C_mul c) z hz0]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    rw [eval_signedMultiaffineReciprocal hP z hz0]
    ring

/-- Signed multiaffine reciprocation preserves upper-half-plane stability. -/
theorem MvUpperHalfPlaneStable.signedMultiaffineReciprocal
    {sigma : Type*} [Fintype sigma] {P : MvPolynomial sigma ℂ}
    (hstable : MvUpperHalfPlaneStable P)
    (hP : MvPolynomial.IsMultiaffine P) :
    MvUpperHalfPlaneStable (signedMultiaffineReciprocal P) := by
  intro z hz
  have hz0 : ∀ i, z i ≠ 0 := fun i hzero => by
    have := hz i
    rw [hzero] at this
    simp at this
  rw [eval_signedMultiaffineReciprocal hP z hz0]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i hi => hz0 i
  · apply hstable
    intro i
    change 0 < -((z i)⁻¹).im
    rw [Complex.inv_im]
    simpa only [neg_div, neg_neg] using
      div_pos (hz i) (Complex.normSq_pos.mpr (hz0 i))

end

end RealRooted
