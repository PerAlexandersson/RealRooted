import RealRooted.Hadamard.Hurwitz

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard consequences

Conditional odd/even reductions, PF and proper-position closure, reciprocal
shift transport, and coefficientwise Polya-frequency consequences.
-/

/-- **Garloff--Wagner, Theorem 4(b), reduced to legacy odd/even inputs**
(TODO T9).

The two-pair interlacing form of the Garloff--Wagner Hadamard theorem follows,
with a fully checked conditional reduction, from the following inputs (the
latter three are pre-existing interfaces from `RealRooted.VeroneseSection`):

* `hadamardPreservesHurwitzStableStatement` — Garloff--Wagner Theorem 1
  (Hadamard products of Hurwitz-stable polynomials are Hurwitz stable when the
  coefficientwise product is nonzero);
* `NonnegPrecToHurwitzOddEvenStatement` — the forward Hermite--Biehler bridge
  from proper position `Prec f g` of nonnegative-coefficient polynomials to
  Hurwitz stability of `oddEvenPolynomial f g = g(x²) + x·f(x²)`;
* `LegacyHurwitzOddEvenToFullyInterlacingPairStatement` — the legacy row-oriented
  Hurwitz-to-Lace bridge, now known false as a general theorem; and
* `FullyInterlacingPairToPrec0Statement` — the converse lace-to-interlacing
  bridge back to zero-aware proper position.

The bridge between the two-pair and single-polynomial worlds is the proven
algebraic identity `hadamardProduct_oddEvenPolynomial`:
`oddEvenPolynomial f g ⊙ oddEvenPolynomial p q
   = oddEvenPolynomial (f ⊙ p) (g ⊙ q)`,
whose even part is `g ⊙ q` and whose odd part is `f ⊙ p`.

Thus all of the interlacing bookkeeping of Theorem 4(b) is discharged here once
these conditional inputs are supplied.
Note that the odd/even polynomial of an interlacing pair is Hurwitz stable, not
real-rooted (e.g. `f = 1`, `g = X + 1` gives `X² + X + 1`), which is why the
reduction goes through `IsHurwitzStable` (Theorem 1) rather than the
single-polynomial real-rootedness fact
`garloffWagnerHadamardNonnegRealRootedStatement`. -/
theorem garloffWagnerHadamardNonnegPrec_of_oddEven
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hPrecToHurwitz : NonnegPrecToHurwitzOddEvenStatement)
    (hHurwitzToFull : LegacyHurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    ∀ {f g p q : ℝ[X]},
      HasNonnegCoeffs f → HasNonnegCoeffs g → HasNonnegCoeffs p → HasNonnegCoeffs q →
      Prec f g → Prec p q → Prec0 (hadamardProduct f p) (hadamardProduct g q) := by
  intro f g p q hf hg hp hq hfg hpq
  by_cases hfp0 : hadamardProduct f p = 0
  · simpa [hfp0] using prec0_zero_left (hadamardProduct g q)
  by_cases hgq0 : hadamardProduct g q = 0
  · simpa [hgq0] using prec0_zero_right (hadamardProduct f p)
  have hOE1 : IsHurwitzStable (oddEvenPolynomial f g) := hPrecToHurwitz hf hg hfg
  have hOE2 : IsHurwitzStable (oddEvenPolynomial p q) := hPrecToHurwitz hp hq hpq
  have hOEprod0 :
      hadamardProduct (oddEvenPolynomial f g) (oddEvenPolynomial p q) ≠ 0 := by
    rw [hadamardProduct_oddEvenPolynomial]
    exact oddEvenPolynomial_ne_zero_iff.mpr (Or.inl hfp0)
  exact hFullToPrec0 (hHurwitzToFull (by
    simpa [hadamardProduct_oddEvenPolynomial] using hThm1 hOE1 hOE2 hOEprod0))

/-- PF-polynomial wrapper around the checked nonnegative
Garloff--Wagner two-pair theorem. -/
def garloffWagnerHadamardPFPrecStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec f g →
    Prec p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec_of_nonnegPrec :
    garloffWagnerHadamardPFPrecStatement :=
  fun hf hg hp hq hfg hpq =>
    garloffWagnerHadamardNonnegPrec hf.hasNonnegCoeffs hg.hasNonnegCoeffs
      hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg hpq

/-- Zero-aware PF-polynomial wrapper around the checked Garloff--Wagner
two-pair theorem. -/
def garloffWagnerHadamardPFPrec0Statement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec0 f g →
    Prec0 p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec0_of_prec
    (hGW : garloffWagnerHadamardPFPrecStatement) :
    garloffWagnerHadamardPFPrec0Statement := by
  intro f g p q hf hg hp hq hfg hpq
  rcases hfg with rfl | rfl | hfg'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  rcases hpq with rfl | rfl | hpq'
  · simpa using prec0_zero_left (hadamardProduct g q)
  · simpa using prec0_zero_right (hadamardProduct f p)
  exact hGW hf hg hp hq hfg' hpq'

theorem garloffWagnerHadamardPFPrec0_of_nonnegPrec :
    garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFPrec0_of_prec
    garloffWagnerHadamardPFPrec_of_nonnegPrec

/-- PF-polynomial closure under Hadamard product, stated directly from the
zero-aware Garloff--Wagner PF wrapper. -/
theorem hadamardProduct_preserves_pf_of_garloffWagner
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  IsPFPolynomial.of_prec0_self
    (hp.hasNonnegCoeffs.hadamardProduct hq.hasNonnegCoeffs)
    (hGW hp hp hq hq hp.prec0_self hq.prec0_self)

theorem hadamardProduct_preserves_pf_of_nonnegPrec :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    garloffWagnerHadamardPFPrec0_of_nonnegPrec

theorem hadamardProduct_preserves_pf_of_matrixHadamardBridges
    (_hToFull : LegacyNonnegPrecToFullyInterlacingPairStatement)
    (_hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (_hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_nonnegPrec

theorem hadamardProduct_preserves_pf_of_hurwitzSchur
    (_hToFull : LegacyNonnegPrecToFullyInterlacingPairStatement)
    (_hFullToPrec0 : FullyInterlacingPairToPrec0Statement) :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_nonnegPrec

/-- The nonnegative two-pair Garloff--Wagner theorem gives PF closure under
Hadamard products through the zero-aware PF wrapper. -/
theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec :
    schurPolyaWagnerHadamardPFStatement :=
  hadamardProduct_preserves_pf_of_nonnegPrec

/-- The checked PF Hadamard theorem gives the one-polynomial
real-rootedness statement directly. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  intro p q hpnn hqnn hprr hqrr
  have hp : IsPFPolynomial p := IsPFPolynomial.of_realRooted_nonneg hpnn hprr.2
  have hq : IsPFPolynomial q := IsPFPolynomial.of_realRooted_nonneg hqnn hqrr.2
  have hpf : IsPFPolynomial (hadamardProduct p q) :=
    hadamardProduct_preserves_pf_of_nonnegPrec hp hq
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

/-- Fixed-right Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_prec0_right
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Prec0 f g) :
    Prec0 (hadamardProduct f p) (hadamardProduct g p) :=
  hGW hf hg hp hp hfg hp.prec0_self

/-- Fixed-left Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_prec0_left
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm] using
    hadamardProduct_preserves_prec0_right hGW hp hq hf hpq

theorem reciprocalShift_hadamardProduct (D : ℕ) (p q : ℝ[X]) :
    reciprocalShift D (hadamardProduct p q) =
      hadamardProduct (reciprocalShift D p) (reciprocalShift D q) := by
  ext n
  simp

/-- Hadamard closure for the reciprocal-interlacing cone. -/
def hadamardReciprocalConeClosureStatement : Prop :=
  ∀ {D : ℕ} {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec p (reciprocalShift D p) →
    Prec q (reciprocalShift D q) →
    Prec0 (hadamardProduct p q)
      (reciprocalShift D (hadamardProduct p q))

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
zero-aware PF two-pair Garloff--Wagner wrapper. -/
theorem hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (hGW : garloffWagnerHadamardPFPrec0Statement) :
    hadamardReciprocalConeClosureStatement := by
  intro D p q hp hq hprec_p hprec_q
  have hp_shift : IsPFPolynomial (reciprocalShift D p) :=
    IsPFPolynomial.of_realRooted_nonneg hp.hasNonnegCoeffs.reciprocalShift hprec_p.2.1.2
  have hq_shift : IsPFPolynomial (reciprocalShift D q) :=
    IsPFPolynomial.of_realRooted_nonneg hq.hasNonnegCoeffs.reciprocalShift hprec_q.2.1.2
  simpa [reciprocalShift_hadamardProduct] using
    hGW hp hp_shift hq hq_shift hprec_p.toPrec0 hprec_q.toPrec0

theorem hadamardReciprocalConeClosure_of_garloffWagner_prec
    (hGW : garloffWagnerHadamardPFPrecStatement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_prec0
    (garloffWagnerHadamardPFPrec0_of_prec hGW)

/-- Polynomial-coefficient form of Polya-frequency closure under termwise
products. This is finite-sequence closure packaged through coefficient
polynomials. -/
def polyaFrequencyHadamardCoeffStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPolyaFreqSeq p.coeff →
    IsPolyaFreqSeq q.coeff →
    IsPolyaFreqSeq (fun n => (hadamardProduct p q).coeff n)

theorem polyaFrequencyHadamardCoeff_of_schurPolyaWagner
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hSPW : schurPolyaWagnerHadamardPFStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  fun hp hq =>
    (hSPW (IsPFPolynomial.of_sequence hASW hp)
      (IsPFPolynomial.of_sequence hASW hq)).to_sequence

end RealRooted
