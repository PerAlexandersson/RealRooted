import RealRooted.ClassicalHurwitzMatrix.Stability.OddEvenConverse
import RealRooted.GarloffWagner.Hadamard
import RealRooted.Hadamard.GarloffWagner

/-!
# Hadamard products of Hurwitz-stable polynomials

Garloff--Wagner, *Hadamard products of stable polynomials are stable*, J. Math. Anal. Appl.
202 (1996), Theorem 1: the coefficientwise product of two Hurwitz-stable real polynomials is
Hurwitz stable (here in the convention `IsHurwitzStable` of nonnegative coefficients and no
root in the open right half-plane, and provided the product is nonzero).

Writing `a = q(X²) + X p(X²)`, Hurwitz stability of `a` means that `p` and `q` strictly
interlace (`isHurwitzStable_oddEvenPolynomial_iff`), or that one of them vanishes and the
other is a PF polynomial.  The Hadamard product acts on the two parts separately
(`hadamardProduct_oddEvenPolynomial`), and both cases are preserved: interlacing by
Garloff--Wagner, Theorem 4(b) (`StrictInterl.interl_hadamardProduct`), and PF polynomials by
the Schur--Malo theorem (`IsPFPolynomial.hadamardProduct`).
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- `q(X²)` is Hurwitz stable exactly when `q` is a nonzero PF polynomial. -/
theorem isHurwitzStable_oddEvenPolynomial_zero_left_iff {q : ℝ[X]} :
    IsHurwitzStable (oddEvenPolynomial 0 q) ↔ q ≠ 0 ∧ IsPFPolynomial q := by
  constructor
  · intro h
    have hq : q ≠ 0 := by
      rintro rfl
      exact (h.rightHalfPlaneStable 1 (by simp)) (by simp)
    have hstab := h.isUpperHalfPlaneStable_hermiteBiehlerPolynomial
    simp only [hermiteBiehlerPolynomial, complexify, Polynomial.map_zero, mul_zero,
      add_zero] at hstab
    exact ⟨hq, IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_right_of_oddEvenPolynomial h.hasNonnegCoeffs)
      (IsUpperHalfPlaneStable.splits_complexify hstab)⟩
  · rintro ⟨hq, hpf⟩
    refine ⟨hasNonnegCoeffs_oddEvenPolynomial (fun _ ↦ by simp) hpf.hasNonnegCoeffs,
      hermiteBiehlerStableToHurwitzOddEven (fun _ ↦ by simp) hpf.hasNonnegCoeffs ?_⟩
    have hs : q.Splits := hpf.eq_zero_or_splits.resolve_left hq
    simpa [hermiteBiehlerPolynomial, complexify] using
      Polynomial.Splits.isUpperHalfPlaneStable_complexify hs hq

/-- `X p(X²)` is Hurwitz stable exactly when `p` is a nonzero PF polynomial. -/
theorem isHurwitzStable_oddEvenPolynomial_zero_right_iff {p : ℝ[X]} :
    IsHurwitzStable (oddEvenPolynomial p 0) ↔ p ≠ 0 ∧ IsPFPolynomial p := by
  have hI (f : ℂ[X]) :
      IsUpperHalfPlaneStable (C Complex.I * f) ↔ IsUpperHalfPlaneStable f :=
    forall₂_congr fun z _ ↦ by simp [Complex.I_ne_zero]
  constructor
  · intro h
    have hp : p ≠ 0 := by
      rintro rfl
      exact (h.rightHalfPlaneStable 1 (by simp)) (by simp)
    have hstab := h.isUpperHalfPlaneStable_hermiteBiehlerPolynomial
    simp only [hermiteBiehlerPolynomial, complexify, Polynomial.map_zero, zero_add] at hstab
    exact ⟨hp, IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_left_of_oddEvenPolynomial h.hasNonnegCoeffs)
      (IsUpperHalfPlaneStable.splits_complexify ((hI _).mp hstab))⟩
  · rintro ⟨hp, hpf⟩
    refine ⟨hasNonnegCoeffs_oddEvenPolynomial hpf.hasNonnegCoeffs (fun _ ↦ by simp),
      hermiteBiehlerStableToHurwitzOddEven hpf.hasNonnegCoeffs (fun _ ↦ by simp) ?_⟩
    have hs : p.Splits := hpf.eq_zero_or_splits.resolve_left hp
    simpa [hermiteBiehlerPolynomial, complexify, hI] using
      Polynomial.Splits.isUpperHalfPlaneStable_complexify hs hp

/-- Both parts of a Hurwitz-stable `q(X²) + X p(X²)` are PF polynomials. -/
theorem IsHurwitzStable.isPFPolynomial_oddEvenPolynomial {p q : ℝ[X]}
    (h : IsHurwitzStable (oddEvenPolynomial p q)) : IsPFPolynomial p ∧ IsPFPolynomial q := by
  by_cases hp : p = 0
  · subst hp
    exact ⟨IsPFPolynomial.zero, (isHurwitzStable_oddEvenPolynomial_zero_left_iff.mp h).2⟩
  by_cases hq : q = 0
  · subst hq
    exact ⟨(isHurwitzStable_oddEvenPolynomial_zero_right_iff.mp h).2, IsPFPolynomial.zero⟩
  obtain ⟨hpnn, hqnn, hpq⟩ := (isHurwitzStable_oddEvenPolynomial_iff hp hq).mp h
  exact ⟨IsPFPolynomial.of_realRooted_nonneg hpnn hpq.1.2,
    IsPFPolynomial.of_realRooted_nonneg hqnn hpq.2.1.2⟩

/-- **Garloff--Wagner, Theorem 1.**  The coefficientwise (Hadamard) product of two
Hurwitz-stable real polynomials is Hurwitz stable, unless it vanishes. -/
theorem IsHurwitzStable.hadamardProduct {a b : ℝ[X]}
    (ha : IsHurwitzStable a) (hb : IsHurwitzStable b) (hab : hadamardProduct a b ≠ 0) :
    IsHurwitzStable (hadamardProduct a b) := by
  obtain ⟨p, q, rfl⟩ := exists_oddEvenPolynomial a
  obtain ⟨p', q', rfl⟩ := exists_oddEvenPolynomial b
  rw [hadamardProduct_oddEvenPolynomial] at hab ⊢
  obtain ⟨hp, hq⟩ := ha.isPFPolynomial_oddEvenPolynomial
  obtain ⟨hp', hq'⟩ := hb.isPFPolynomial_oddEvenPolynomial
  by_cases hP : RealRooted.hadamardProduct p p' = 0
  · rw [hP] at hab ⊢
    exact isHurwitzStable_oddEvenPolynomial_zero_left_iff.mpr
      ⟨by simpa using hab, hq.hadamardProduct hq'⟩
  by_cases hQ : RealRooted.hadamardProduct q q' = 0
  · rw [hQ] at hab ⊢
    exact isHurwitzStable_oddEvenPolynomial_zero_right_iff.mpr
      ⟨by simpa using hab, hp.hadamardProduct hp'⟩
  -- all four parts are nonzero, so both inputs are strictly interlacing pairs
  have hp0 : p ≠ 0 := by rintro rfl; simp at hP
  have hp0' : p' ≠ 0 := by rintro rfl; simp at hP
  have hq0 : q ≠ 0 := by rintro rfl; simp at hQ
  have hq0' : q' ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨hpnn, hqnn, hpq⟩ := (isHurwitzStable_oddEvenPolynomial_iff hp0 hq0).mp ha
  obtain ⟨hpnn', hqnn', hpq'⟩ := (isHurwitzStable_oddEvenPolynomial_iff hp0' hq0').mp hb
  have hint := StrictInterl.interl_hadamardProduct hpnn hqnn hpnn' hqnn' hpq hpq'
  exact (isHurwitzStable_oddEvenPolynomial_iff hP hQ).mpr
    ⟨hpnn.hadamardProduct hpnn', hqnn.hadamardProduct hqnn',
      (hint.resolve_left hP).resolve_left hQ⟩

end RealRooted
