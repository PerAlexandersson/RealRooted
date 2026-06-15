import RealRooted.PFPolynomial

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard products of real-rooted polynomials

This file defines the coefficientwise Hadamard product of two real
polynomials and records theorem interfaces for the classical preservation
results used by downstream combinatorial applications.

The main external reference is J. Garloff and D. G. Wagner, *Hadamard Products
of Stable Polynomials Are Stable*, J. Math. Anal. Appl. 202 (1996), 797--809.
Theorem 1 is the Hurwitz-stability form. Theorem 4 is the real-rooted
nonpositive-root form, including preservation of the interlacing/proper-position
relation.
-/

/-- Coefficientwise Hadamard product of two real polynomials. -/
def hadamardProduct (p q : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => monomial n (a * q.coeff n)

@[simp] theorem coeff_hadamardProduct (p q : ℝ[X]) (n : ℕ) :
    (hadamardProduct p q).coeff n = p.coeff n * q.coeff n := by
  classical
  rw [hadamardProduct, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _hb hbn
    simp [hbn]
  · intro hn
    rw [(Polynomial.notMem_support_iff).mp hn]
    simp

theorem hadamardProduct_comm (p q : ℝ[X]) :
    hadamardProduct p q = hadamardProduct q p := by
  ext n
  simp [mul_comm]

theorem hadamardProduct_assoc (p q r : ℝ[X]) :
    hadamardProduct (hadamardProduct p q) r =
      hadamardProduct p (hadamardProduct q r) := by
  ext n
  simp [mul_assoc]

@[simp] theorem hadamardProduct_zero_left (p : ℝ[X]) :
    hadamardProduct 0 p = 0 := by
  ext n
  simp

@[simp] theorem hadamardProduct_zero_right (p : ℝ[X]) :
    hadamardProduct p 0 = 0 := by
  ext n
  simp

theorem hadamardProduct_add_left (p q r : ℝ[X]) :
    hadamardProduct (p + q) r =
      hadamardProduct p r + hadamardProduct q r := by
  ext n
  simp
  grind

theorem hadamardProduct_add_right (p q r : ℝ[X]) :
    hadamardProduct p (q + r) =
      hadamardProduct p q + hadamardProduct p r := by
  ext n
  simp
  grind

theorem hadamardProduct_C_mul_left (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct (C a * p) q =
      C a * hadamardProduct p q := by
  ext n
  simp [mul_assoc]

theorem hadamardProduct_C_mul_right (a : ℝ) (p q : ℝ[X]) :
    hadamardProduct p (C a * q) =
      C a * hadamardProduct p q := by
  ext n
  simp
  grind

/-- Nonnegative coefficients are preserved by coefficientwise Hadamard
products. -/
theorem HasNonnegCoeffs.hadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  intro n
  simpa using mul_nonneg (hp n) (hq n)

theorem hasNonnegCoeffs_hadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) :=
  hp.hadamardProduct hq

/-- Nonnegative-coefficient Schur--Polya/Garloff--Wagner real-rootedness
interface for coefficientwise Hadamard products.

Garloff--Wagner, Theorem 4(a), proves this in the standard-polynomial setting
with only nonpositive zeros. The hypotheses below are the corresponding
nonnegative-coefficient wrapper: real-rooted nonzero polynomials with
nonnegative coefficients automatically have only nonpositive roots. The conclusion is
zero-aware because the Hadamard product can vanish when supports are disjoint.
-/
def garloffWagnerHadamardNonnegRealRootedStatement : Prop :=
  ∀ {p q : ℝ[X]},
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    (p ≠ 0 ∧ p.Splits) →
    (q ≠ 0 ∧ q.Splits) →
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0

theorem IsPFPolynomial.hadamardProduct
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement)
    {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  by_cases hq0 : q = 0
  · subst q
    simpa using IsPFPolynomial.zero
  rcases hGW hp.hasNonnegCoeffs hq.hasNonnegCoeffs
      (hp.ne_zero_and_splits hp0)
      (hq.ne_zero_and_splits hq0) with ⟨hrr, hnn, hroots⟩
  exact ⟨hnn, hrr, hroots⟩

/-- Polynomial PF form of the Schur--Polya--Wagner Hadamard theorem. -/
def schurPolyaWagnerHadamardPFStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    IsPFPolynomial (hadamardProduct p q)

theorem schurPolyaWagnerHadamardPF_of_garloffWagner_nonneg
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement) :
    schurPolyaWagnerHadamardPFStatement := by
  intro p q hp hq
  exact hp.hadamardProduct hGW hq

/-- Nonnegative-coefficient Garloff--Wagner interlacing interface for
coefficientwise Hadamard products.

This is the `Prec`/`Prec0` wrapper around Garloff--Wagner, Theorem 4(b):
if two nonnegative-coefficient real-rooted pairs are in the same
proper-position relation, then the pair of Hadamard products is again in
proper position.  The conclusion is zero-aware for the same support reason as
`garloffWagnerHadamardNonnegRealRootedStatement`.

TODO T9: formalize this statement in RealRooted, following Garloff--Wagner,
Theorem 4(b).  It is the remaining standard input used by the SuperEulerian
proof through its `StandardFacts` bundle.
-/
def garloffWagnerHadamardNonnegPrecStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    HasNonnegCoeffs p →
    HasNonnegCoeffs q →
    Prec f g →
    Prec p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

/-- PF-polynomial wrapper around the strict Garloff--Wagner two-pair theorem. -/
def garloffWagnerHadamardPFPrecStatement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec f g →
    Prec p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardPFPrecStatement := by
  intro f g p q hf hg hp hq hfg hpq
  exact hGW hf.hasNonnegCoeffs hg.hasNonnegCoeffs
    hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg hpq

/-- Zero-aware PF-polynomial wrapper around the Garloff--Wagner two-pair
theorem. This is the form most convenient for recursive arguments where a
support specialization may produce the zero polynomial. -/
def garloffWagnerHadamardPFPrec0Statement : Prop :=
  ∀ {f g p q : ℝ[X]},
    IsPFPolynomial f →
    IsPFPolynomial g →
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec0 f g →
    Prec0 p q →
    Prec0 (hadamardProduct f p) (hadamardProduct g q)

theorem garloffWagnerHadamardPFPrec0_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardPFPrec0Statement := by
  intro f g p q hf hg hp hq hfg hpq
  by_cases hf0 : f = 0
  · subst f
    simpa using prec0_zero_left (hadamardProduct g q)
  by_cases hg0 : g = 0
  · subst g
    simpa using prec0_zero_right (hadamardProduct f p)
  by_cases hp0 : p = 0
  · subst p
    simpa using prec0_zero_left (hadamardProduct g q)
  by_cases hq0 : q = 0
  · subst q
    simpa using prec0_zero_right (hadamardProduct f p)
  exact hGW hf.hasNonnegCoeffs hg.hasNonnegCoeffs
    hp.hasNonnegCoeffs hq.hasNonnegCoeffs
    (hfg.toPrec_of_ne hf0 hg0) (hpq.toPrec_of_ne hp0 hq0)

/-- The two-pair Garloff--Wagner theorem implies the one-polynomial
real-rootedness/PF Hadamard theorem by applying it to self-pairs. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegPrec
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    garloffWagnerHadamardNonnegRealRootedStatement := by
  intro p q hpnn hqnn hprr hqrr
  have hself : Prec0 (hadamardProduct p q) (hadamardProduct p q) :=
    hGW hpnn hpnn hqnn hqnn (prec_refl hprr.1 hprr.2) (prec_refl hqrr.1 hqrr.2)
  have hpf : IsPFPolynomial (hadamardProduct p q) :=
    IsPFPolynomial.of_prec0_self (hpnn.hadamardProduct hqnn) hself
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

theorem schurPolyaWagnerHadamardPF_of_garloffWagner_prec0
    (hGW : garloffWagnerHadamardPFPrec0Statement) :
    schurPolyaWagnerHadamardPFStatement := by
  intro p q hp hq
  have hself :
      Prec0 (hadamardProduct p q) (hadamardProduct p q) :=
    hGW hp hp hq hq hp.prec0_self hq.prec0_self
  exact IsPFPolynomial.of_prec0_self
    (hp.hasNonnegCoeffs.hadamardProduct hq.hasNonnegCoeffs) hself

/-- PF-polynomial closure under Hadamard product, stated directly from the
zero-aware Garloff--Wagner PF wrapper. -/
theorem hadamardProduct_preserves_pf_of_garloffWagner
    (hGW : garloffWagnerHadamardPFPrec0Statement)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  schurPolyaWagnerHadamardPF_of_garloffWagner_prec0 hGW hp hq

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
    Prec0 (hadamardProduct f p) (hadamardProduct f q) :=
  hGW hf hf hp hq hf.prec0_self hpq

theorem reciprocalShift_hadamardProduct (D : ℕ) (p q : ℝ[X]) :
    reciprocalShift D (hadamardProduct p q) =
      hadamardProduct (reciprocalShift D p) (reciprocalShift D q) := by
  ext n
  simp

/-- Hadamard closure for the reciprocal-interlacing cone, obtained from the
two-pair Garloff--Wagner theorem. -/
def hadamardReciprocalConeClosureStatement : Prop :=
  ∀ {D : ℕ} {p q : ℝ[X]},
    IsPFPolynomial p →
    IsPFPolynomial q →
    Prec p (reciprocalShift D p) →
    Prec q (reciprocalShift D q) →
    Prec0 (hadamardProduct p q)
      (reciprocalShift D (hadamardProduct p q))

theorem hadamardReciprocalConeClosure_of_garloffWagner
    (hGW : garloffWagnerHadamardNonnegPrecStatement) :
    hadamardReciprocalConeClosureStatement := by
  intro D p q hp hq hprec_p hprec_q
  have h := hGW hp.hasNonnegCoeffs hp.hasNonnegCoeffs.reciprocalShift
    hq.hasNonnegCoeffs hq.hasNonnegCoeffs.reciprocalShift hprec_p hprec_q
  simpa [reciprocalShift_hadamardProduct] using h

/-- Polynomial-coefficient form of Polya-frequency closure under termwise
products. This is finite-sequence closure packaged through coefficient
polynomials. -/
def polyaFrequencyHadamardCoeffStatement : Prop :=
  ∀ {p q : ℝ[X]},
    IsPolyaFreqSeq (fun n => p.coeff n) →
    IsPolyaFreqSeq (fun n => q.coeff n) →
    IsPolyaFreqSeq (fun n => (hadamardProduct p q).coeff n)

theorem polyaFrequencyHadamardCoeff_of_schurPolyaWagner
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hSPW : schurPolyaWagnerHadamardPFStatement) :
    polyaFrequencyHadamardCoeffStatement := by
  intro p q hp hq
  exact (hSPW (IsPFPolynomial.of_sequence hASW hp)
    (IsPFPolynomial.of_sequence hASW hq)).to_sequence

theorem polyaFrequencyHadamardCoeff_of_garloffWagner_nonneg
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    (hGW : garloffWagnerHadamardNonnegRealRootedStatement) :
    polyaFrequencyHadamardCoeffStatement :=
  polyaFrequencyHadamardCoeff_of_schurPolyaWagner hASW
    (schurPolyaWagnerHadamardPF_of_garloffWagner_nonneg hGW)

end RealRooted
