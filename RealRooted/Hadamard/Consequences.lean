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
* `NonnegStrictInterlToHurwitzOddEvenStatement` — the forward Hermite--Biehler bridge
  from proper position `StrictInterl f g` of nonnegative-coefficient polynomials to
  Hurwitz stability of `oddEvenPolynomial f g = g(x²) + x·f(x²)`;
* `LegacyHurwitzOddEvenToFullyInterlacingPairStatement` — the legacy row-oriented
  Hurwitz-to-Lace bridge, now known false as a general theorem; and
* `FullyInterlacingPairToInterlStatement` — the converse lace-to-interlacing
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
theorem garloffWagnerHadamardNonnegInterl_of_oddEven
    (hThm1 : hadamardPreservesHurwitzStableStatement)
    (hPrecToHurwitz : NonnegStrictInterlToHurwitzOddEvenStatement)
    (hHurwitzToFull : LegacyHurwitzOddEvenToFullyInterlacingPairStatement)
    (hFullToPrec0 : FullyInterlacingPairToInterlStatement) :
    ∀ {f g p q : ℝ[X]},
      HasNonnegCoeffs f → HasNonnegCoeffs g → HasNonnegCoeffs p → HasNonnegCoeffs q →
      StrictInterl f g → StrictInterl p q →
        Interl (hadamardProduct f p) (hadamardProduct g q) := by
  intro f g p q hf hg hp hq hfg hpq
  by_cases hfp0 : hadamardProduct f p = 0
  · simpa [hfp0] using interl_zero_left (hadamardProduct g q)
  by_cases hgq0 : hadamardProduct g q = 0
  · simpa [hgq0] using interl_zero_right (hadamardProduct f p)
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
def garloffWagnerHadamardPFStrictInterlStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    StrictInterl f g →
    StrictInterl p q →
    Interl (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFStrictInterl_of_nonnegStrictInterl :
    garloffWagnerHadamardPFStrictInterlStatement :=
  fun hf hg hp hq hfg hpq =>
    garloffWagnerHadamardNonnegInterl hf.hasNonnegCoeffs hg.hasNonnegCoeffs
      hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg hpq

/-- Zero-aware PF-polynomial wrapper around the checked Garloff--Wagner
two-pair theorem. -/
def garloffWagnerHadamardPFInterlStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Interl f g →
    Interl p q →
    Interl (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFInterl_of_strictInterl
    (hGW : garloffWagnerHadamardPFStrictInterlStatement) :
    garloffWagnerHadamardPFInterlStatement := by
  intro f g p q hf hg hp hq hfg hpq
  rcases hfg with rfl | rfl | hfg'
  · simpa using interl_zero_left (hadamardProduct g q)
  · simpa using interl_zero_right (hadamardProduct f p)
  rcases hpq with rfl | rfl | hpq'
  · simpa using interl_zero_left (hadamardProduct g q)
  · simpa using interl_zero_right (hadamardProduct f p)
  exact hGW hf hg hp hq hfg' hpq'

theorem garloffWagnerHadamardPFInterl_of_nonnegStrictInterl :
    garloffWagnerHadamardPFInterlStatement :=
  garloffWagnerHadamardPFInterl_of_strictInterl
    garloffWagnerHadamardPFStrictInterl_of_nonnegStrictInterl

/-- PF-polynomial closure under Hadamard product, stated directly from the
zero-aware Garloff--Wagner PF wrapper. -/
theorem hadamardProduct_preserves_pf_of_garloffWagner
    (hGW : garloffWagnerHadamardPFInterlStatement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  IsPFPolynomial.of_interl_self
    (hp.hasNonnegCoeffs.hadamardProduct hq.hasNonnegCoeffs)
    (hGW hp hp hq hq hp.interl_self hq.interl_self)

theorem hadamardProduct_preserves_pf_of_nonnegStrictInterl :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_garloffWagner
    garloffWagnerHadamardPFInterl_of_nonnegStrictInterl

theorem hadamardProduct_preserves_pf_of_matrixHadamardBridges
    (_hToFull : LegacyNonnegStrictInterlToFullyInterlacingPairStatement)
    (_hMatHad : hadamardPreservesHurwitzMatrixTNStatement)
    (_hFullToPrec0 : FullyInterlacingPairToInterlStatement) :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_nonnegStrictInterl

theorem hadamardProduct_preserves_pf_of_hurwitzSchur
    (_hToFull : LegacyNonnegStrictInterlToFullyInterlacingPairStatement)
    (_hFullToPrec0 : FullyInterlacingPairToInterlStatement) :
    {p q : ℝ[X]} → IsPFPolynomial p → IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q) :=
  hadamardProduct_preserves_pf_of_nonnegStrictInterl

/-- The nonnegative two-pair Garloff--Wagner theorem gives PF closure under
Hadamard products through the zero-aware PF wrapper. -/
theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegStrictInterl :
    schurPolyaWagnerHadamardPFStatement :=
  hadamardProduct_preserves_pf_of_nonnegStrictInterl

/-- The checked PF Hadamard theorem gives the one-polynomial
real-rootedness statement directly. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegStrictInterl :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  intro p q hpnn hqnn hprr hqrr
  have hp : IsPFPolynomial p := IsPFPolynomial.of_realRooted_nonneg hpnn hprr.2
  have hq : IsPFPolynomial q := IsPFPolynomial.of_realRooted_nonneg hqnn hqrr.2
  have hpf : IsPFPolynomial (hadamardProduct p q) :=
    hadamardProduct_preserves_pf_of_nonnegStrictInterl hp hq
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

/-- Fixed-right Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_interl_right
    (hGW : garloffWagnerHadamardPFInterlStatement)
    {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Interl f g) :
    Interl (hadamardProduct f p) (hadamardProduct g p) :=
  hGW hf hg hp hp hfg hp.interl_self

/-- Fixed-left Hadamard multiplication preserves zero-aware proper position
inside the PF cone. -/
theorem hadamardProduct_preserves_interl_left
    (hGW : garloffWagnerHadamardPFInterlStatement)
    {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    Interl (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm] using
    hadamardProduct_preserves_interl_right hGW hp hq hf hpq

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
    StrictInterl p (reciprocalShift D p) →
    StrictInterl q (reciprocalShift D q) →
    Interl (hadamardProduct p q)
      (reciprocalShift D (hadamardProduct p q))

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
zero-aware PF two-pair Garloff--Wagner wrapper. -/
theorem hadamardReciprocalConeClosure_of_garloffWagner_interl
    (hGW : garloffWagnerHadamardPFInterlStatement) :
    hadamardReciprocalConeClosureStatement := by
  intro D p q hp hq hprec_p hprec_q
  have hp_shift : IsPFPolynomial (reciprocalShift D p) :=
    IsPFPolynomial.of_realRooted_nonneg hp.hasNonnegCoeffs.reciprocalShift hprec_p.2.1.2
  have hq_shift : IsPFPolynomial (reciprocalShift D q) :=
    IsPFPolynomial.of_realRooted_nonneg hq.hasNonnegCoeffs.reciprocalShift hprec_q.2.1.2
  simpa [reciprocalShift_hadamardProduct] using
    hGW hp hp_shift hq hq_shift hprec_p.toInterl hprec_q.toInterl

theorem hadamardReciprocalConeClosure_of_garloffWagner_strictInterl
    (hGW : garloffWagnerHadamardPFStrictInterlStatement) :
    hadamardReciprocalConeClosureStatement :=
  hadamardReciprocalConeClosure_of_garloffWagner_interl
    (garloffWagnerHadamardPFInterl_of_strictInterl hGW)

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

@[deprecated garloffWagnerHadamardNonnegInterl_of_oddEven
  (since := "2026-09-18")]
alias garloffWagnerHadamardNonnegPrec_of_oddEven :=
  garloffWagnerHadamardNonnegInterl_of_oddEven

@[deprecated garloffWagnerHadamardPFStrictInterlStatement
  (since := "2026-09-18")]
abbrev garloffWagnerHadamardPFPrecStatement :=
  garloffWagnerHadamardPFStrictInterlStatement

@[deprecated garloffWagnerHadamardPFStrictInterl_of_nonnegStrictInterl
  (since := "2026-09-18")]
alias garloffWagnerHadamardPFPrec_of_nonnegPrec :=
  garloffWagnerHadamardPFStrictInterl_of_nonnegStrictInterl

@[deprecated garloffWagnerHadamardPFInterlStatement (since := "2026-09-18")]
abbrev garloffWagnerHadamardPFPrec0Statement :=
  garloffWagnerHadamardPFInterlStatement

@[deprecated garloffWagnerHadamardPFInterl_of_strictInterl
  (since := "2026-09-18")]
alias garloffWagnerHadamardPFPrec0_of_prec :=
  garloffWagnerHadamardPFInterl_of_strictInterl

@[deprecated garloffWagnerHadamardPFInterl_of_nonnegStrictInterl
  (since := "2026-09-18")]
alias garloffWagnerHadamardPFPrec0_of_nonnegPrec :=
  garloffWagnerHadamardPFInterl_of_nonnegStrictInterl

@[deprecated hadamardProduct_preserves_pf_of_nonnegStrictInterl
  (since := "2026-09-18")]
alias hadamardProduct_preserves_pf_of_nonnegPrec :=
  hadamardProduct_preserves_pf_of_nonnegStrictInterl

@[deprecated schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegStrictInterl
  (since := "2026-09-18")]
alias schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegPrec :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_nonnegStrictInterl

@[deprecated garloffWagnerHadamardNonnegRealRooted_of_nonnegStrictInterl
  (since := "2026-09-18")]
alias garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec :=
  garloffWagnerHadamardNonnegRealRooted_of_nonnegStrictInterl

@[deprecated hadamardProduct_preserves_interl_right (since := "2026-09-18")]
alias hadamardProduct_preserves_prec0_right :=
  hadamardProduct_preserves_interl_right

@[deprecated hadamardProduct_preserves_interl_left (since := "2026-09-18")]
alias hadamardProduct_preserves_prec0_left :=
  hadamardProduct_preserves_interl_left

@[deprecated hadamardReciprocalConeClosure_of_garloffWagner_interl
  (since := "2026-09-18")]
alias hadamardReciprocalConeClosure_of_garloffWagner_prec0 :=
  hadamardReciprocalConeClosure_of_garloffWagner_interl

@[deprecated hadamardReciprocalConeClosure_of_garloffWagner_strictInterl
  (since := "2026-09-18")]
alias hadamardReciprocalConeClosure_of_garloffWagner_prec :=
  hadamardReciprocalConeClosure_of_garloffWagner_strictInterl

end RealRooted
