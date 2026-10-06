import RealRooted.ClassicalHurwitzMatrix.Stability

/-!
# Hurwitz stability forces coefficient signs

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#hurwitzImpliesCoefficientPositivity

A real polynomial with positive leading coefficient and no zeros in the open
right half-plane has nonnegative coefficients.  If its zeros lie in the open
left half-plane, then every coefficient up to its degree is positive.

Over the reals such a polynomial is a positive constant times linear factors
`X - r` with `r ≤ 0` and quadratic factors `X² - 2 Re(z) X + |z|²` for
nonreal zeros `z`, and every such factor has nonnegative coefficients.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The real quadratic `X² - 2 Re(z) X + |z|²`, whose zeros are `z` and
`conj z`. -/
private def conjPairQuadratic (z : ℂ) : ℝ[X] :=
  X ^ 2 + C (-2 * z.re) * X + C (Complex.normSq z)

private theorem coeff_conjPairQuadratic (z : ℂ) (k : ℕ) :
    (conjPairQuadratic z).coeff k =
      if k = 0 then Complex.normSq z else if k = 1 then -2 * z.re
        else if k = 2 then 1 else 0 := by
  rcases k with _ | _ | _ | k <;>
    simp [conjPairQuadratic, coeff_X_pow, coeff_C, coeff_X]

private theorem natDegree_conjPairQuadratic (z : ℂ) :
    (conjPairQuadratic z).natDegree = 2 := by
  unfold conjPairQuadratic
  compute_degree!

private theorem monic_conjPairQuadratic (z : ℂ) :
    (conjPairQuadratic z).Monic := by
  unfold conjPairQuadratic
  monicity!

private theorem complexify_conjPairQuadratic (z : ℂ) :
    complexify (conjPairQuadratic z) = (X - C z) * (X - C (starRingEnd ℂ z)) := by
  have hsum : z + starRingEnd ℂ z = ((2 * z.re : ℝ) : ℂ) :=
    Complex.add_conj z
  have hprod : z * starRingEnd ℂ z = ((Complex.normSq z : ℝ) : ℂ) :=
    Complex.mul_conj z
  have hexp : (X - C z) * (X - C (starRingEnd ℂ z)) =
      X ^ 2 - C (z + starRingEnd ℂ z) * X + C (z * starRingEnd ℂ z) := by
    simp only [C_add, C_mul]
    ring
  rw [hexp, hsum, hprod]
  simp [conjPairQuadratic, complexify, sub_eq_add_neg]

/-- A nonreal zero `z` of a real polynomial `p` makes `X² - 2 Re(z) X + |z|²`
divide `p`. -/
private theorem conjPairQuadratic_dvd {p : ℝ[X]} {z : ℂ} (hz : z.im ≠ 0)
    (hroot : (complexify p).eval z = 0) :
    conjPairQuadratic z ∣ p := by
  rw [← map_dvd_map Complex.ofRealHom Complex.ofReal_injective
    (monic_conjPairQuadratic z)]
  change complexify (conjPairQuadratic z) ∣ complexify p
  rw [complexify_conjPairQuadratic]
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hroot
  rw [hr]
  refine mul_dvd_mul_left _ (dvd_iff_isRoot.mpr ?_)
  have hconj := complexify_conj_root hroot
  rw [hr, eval_mul, eval_sub, eval_X, eval_C] at hconj
  refine (mul_eq_zero.mp hconj).resolve_left (sub_ne_zero.mpr fun h ↦ hz ?_)
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- Induction over the real factorization of a polynomial with positive leading
coefficient whose complex zeros lie in `S`: positive constants, linear factors
`X - r` with `r ∈ S`, and quadratic factors for nonreal `z ∈ S`. -/
private theorem induction_on_realFactors {S : Set ℂ} {motive : ℝ[X] → Prop}
    (hC : ∀ c : ℝ, 0 < c → motive (C c))
    (hlin : ∀ (r : ℝ) (q : ℝ[X]), (r : ℂ) ∈ S → motive q → motive ((X - C r) * q))
    (hquad : ∀ (z : ℂ) (q : ℝ[X]), z ∈ S → z.im ≠ 0 → motive q →
      motive (conjPairQuadratic z * q)) :
    ∀ {p : ℝ[X]}, 0 < p.leadingCoeff →
      (∀ z, (complexify p).eval z = 0 → z ∈ S) → motive p := by
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  intro hlc hS
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hlc
  by_cases hdeg : n = 0
  · rw [eq_C_of_natDegree_eq_zero (hn.trans hdeg)]
    apply hC
    simpa [leadingCoeff, hn, hdeg] using hlc
  have step : ∀ Q q : ℝ[X], Q.Monic → Q.natDegree ≠ 0 → p = Q * q → motive q := by
    intro Q q hQ hQdeg hpQ
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hp0 (by simp [hpQ])
    refine ih q.natDegree ?_ rfl ?_ ?_
    · rw [← hn, hpQ, natDegree_mul hQ.ne_zero hq0]
      lia
    · rwa [hpQ, leadingCoeff_mul, hQ.leadingCoeff, one_mul] at hlc
    · intro w hw
      apply hS w
      simp [hpQ, complexify, eval_mul] at hw ⊢
      exact .inr hw
  have hdeg_pos : 0 < (complexify p).degree := by
    rw [complexify, degree_map_eq_of_injective Complex.ofRealHom.injective]
    exact natDegree_pos_iff_degree_pos.mp (by lia)
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg_pos
  by_cases him : z.im = 0
  · have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    have hroot : p.IsRoot z.re := by
      have h := hz
      rw [IsRoot.def, hzr] at h
      have h' : (((p.eval z.re : ℝ)) : ℂ) = 0 := by
        simpa [complexify] using
          (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := p) z.re).symm.trans h
      exact_mod_cast h'
    have hp := (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
    rw [hp]
    exact hlin z.re _ (hzr ▸ hS z hz)
      (step _ _ (monic_X_sub_C _) (by simp) hp)
  · obtain ⟨q, hq⟩ := conjPairQuadratic_dvd him hz
    rw [hq]
    exact hquad z q (hS z hz) him
      (step _ _ (monic_conjPairQuadratic z) (by simp [natDegree_conjPairQuadratic]) hq)

private theorem hasNonnegCoeffs_of_forall_coeff_pos {p : ℝ[X]}
    (h : ∀ k ≤ p.natDegree, 0 < p.coeff k) : HasNonnegCoeffs p := by
  intro k
  by_cases hk : k ≤ p.natDegree
  · exact (h k hk).le
  · rw [coeff_eq_zero_of_natDegree_lt (by lia)]

private theorem forall_coeff_pos_mul {a b : ℝ[X]}
    (ha : ∀ k ≤ a.natDegree, 0 < a.coeff k) (hb : ∀ k ≤ b.natDegree, 0 < b.coeff k) :
    ∀ k ≤ (a * b).natDegree, 0 < (a * b).coeff k := by
  have ha0 : a ≠ 0 := fun h ↦ by simpa [h] using ha 0 (Nat.zero_le _)
  have hb0 : b ≠ 0 := fun h ↦ by simpa [h] using hb 0 (Nat.zero_le _)
  intro k hk
  rw [natDegree_mul ha0 hb0] at hk
  rw [coeff_mul]
  apply Finset.sum_pos'
  · intro x _
    exact mul_nonneg (hasNonnegCoeffs_of_forall_coeff_pos ha x.1)
      (hasNonnegCoeffs_of_forall_coeff_pos hb x.2)
  · refine ⟨(min k a.natDegree, k - min k a.natDegree), ?_, ?_⟩
    · rw [Finset.mem_antidiagonal]
      lia
    · exact mul_pos (ha _ (min_le_right _ _)) (hb _ (by lia))

/-- A real polynomial with positive leading coefficient and no zeros in the
open right half-plane has nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_isRightHalfPlaneStable {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (h : IsRightHalfPlaneStable (complexify p)) :
    HasNonnegCoeffs p := by
  refine induction_on_realFactors (S := {z | z.re ≤ 0}) (fun c hc ↦ hasNonnegCoeffs_C hc.le)
    (fun r q hr hq ↦ ?_) (fun z q hz _ hq ↦ ?_) hp
    (fun z hz ↦ not_lt.mp fun hre ↦ h z hre hz)
  · have hr : r ≤ 0 := by simpa using hr
    refine HasNonnegCoeffs.mul (fun k ↦ ?_) hq
    rcases k with _ | _ | k <;> simp [coeff_X, coeff_C, hr]
  · have hz : z.re ≤ 0 := hz
    refine HasNonnegCoeffs.mul (fun k ↦ ?_) hq
    rw [coeff_conjPairQuadratic]
    split_ifs
    · exact Complex.normSq_nonneg z
    · linarith
    · norm_num
    · rfl

/-- For a real polynomial with positive leading coefficient, the coefficient
condition in `IsHurwitzStable` is automatic: weak Hurwitz stability is just the
absence of zeros in the open right half-plane. -/
theorem isHurwitzStable_iff_isRightHalfPlaneStable {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    IsHurwitzStable p ↔ IsRightHalfPlaneStable (complexify p) :=
  ⟨IsHurwitzStable.rightHalfPlaneStable,
    fun h ↦ ⟨hasNonnegCoeffs_of_isRightHalfPlaneStable hp h, h⟩⟩

/-- A strictly Hurwitz-stable real polynomial with positive leading coefficient
has every coefficient up to its degree positive. -/
theorem IsStrictlyHurwitzStable.coeff_pos {p : ℝ[X]} (h : IsStrictlyHurwitzStable p)
    (hp : HasPosLeadingCoeff p) {k : ℕ} (hk : k ≤ p.natDegree) :
    0 < p.coeff k := by
  refine induction_on_realFactors (S := {z | z.re < 0})
    (motive := fun p ↦ ∀ k ≤ p.natDegree, 0 < p.coeff k)
    (fun c hc k hk ↦ ?_) (fun r q hr hq ↦ ?_) (fun z q hz him hq ↦ ?_) hp
    (fun z hz ↦ h z hz) k hk
  · simp only [natDegree_C, Nat.le_zero] at hk
    simpa [hk] using hc
  · have hr : r < 0 := by simpa using hr
    refine forall_coeff_pos_mul (fun k hk ↦ ?_) hq
    rw [natDegree_X_sub_C] at hk
    rcases k with _ | _ | k
    · simpa using hr
    · simp
    · lia
  · have hz : z.re < 0 := hz
    refine forall_coeff_pos_mul (fun k hk ↦ ?_) hq
    rw [natDegree_conjPairQuadratic] at hk
    rw [coeff_conjPairQuadratic]
    have hnorm : 0 < Complex.normSq z :=
      Complex.normSq_pos.mpr fun h0 ↦ him (by simp [h0])
    split_ifs
    · exact hnorm
    · linarith
    · norm_num
    · lia

end RealRooted
