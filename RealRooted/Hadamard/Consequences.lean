import RealRooted.Hadamard.Hurwitz

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard consequences

PF and interlacing closure under Hadamard products, reciprocal shift
transport, and coefficientwise Pólya-frequency consequences.
-/

/-- Garloff--Wagner, Theorem 4(b), for PF polynomials: Hadamard products
preserve strict interlacing of PF pairs, in zero-aware form. -/
theorem garloffWagnerHadamardPFStrictInterl_of_nonnegStrictInterl {f g p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hfg : StrictInterl f g) (hpq : StrictInterl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) :=
  garloffWagnerHadamardNonnegInterl hf.hasNonnegCoeffs hg.hasNonnegCoeffs
    hp.hasNonnegCoeffs hq.hasNonnegCoeffs hfg hpq

/-- Garloff--Wagner, Theorem 4(b), for PF polynomials and zero-aware
interlacing inputs. -/
theorem garloffWagnerHadamardPFInterl_of_nonnegStrictInterl {f g p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hfg : Interl f g) (hpq : Interl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) := by
  rcases hfg with rfl | rfl | hfg'
  · simpa using interl_zero_left (hadamardProduct g q)
  · simpa using interl_zero_right (hadamardProduct f p)
  rcases hpq with rfl | rfl | hpq'
  · simpa using interl_zero_left (hadamardProduct g q)
  · simpa using interl_zero_right (hadamardProduct f p)
  exact garloffWagnerHadamardPFStrictInterl_of_nonnegStrictInterl hf hg hp hq hfg' hpq'

/-- PF polynomials are closed under coefficientwise Hadamard products. -/
theorem hadamardProduct_preserves_pf_of_nonnegStrictInterl {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  hp.hadamardProduct hq

/-- Nonnegative-coefficient Schur--Pólya/Garloff--Wagner real-rootedness for
coefficientwise Hadamard products (Garloff--Wagner, Theorem 4(a)).

Real-rooted nonzero polynomials with nonnegative coefficients have only
nonpositive roots.  The conclusion is zero-aware because the Hadamard product
can vanish when supports are disjoint. -/
theorem garloffWagnerHadamardNonnegRealRooted_of_nonnegStrictInterl {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hprr : p ≠ 0 ∧ p.Splits) (hqrr : q ≠ 0 ∧ q.Splits) :
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0 := by
  have hp : IsPFPolynomial p := IsPFPolynomial.of_realRooted_nonneg hpnn hprr.2
  have hq : IsPFPolynomial q := IsPFPolynomial.of_realRooted_nonneg hqnn hqrr.2
  have hpf : IsPFPolynomial (hadamardProduct p q) := hp.hadamardProduct hq
  exact ⟨hpf.eq_zero_or_splits, hpf.hasNonnegCoeffs, hpf.roots_nonpos⟩

/-- Fixed-right Hadamard multiplication preserves zero-aware interlacing
inside the PF cone. -/
theorem hadamardProduct_preserves_interl_right {f g p : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hp : IsPFPolynomial p)
    (hfg : Interl f g) :
    Interl (hadamardProduct f p) (hadamardProduct g p) :=
  garloffWagnerHadamardPFInterl_of_nonnegStrictInterl hf hg hp hp hfg hp.interl_self

/-- Fixed-left Hadamard multiplication preserves zero-aware interlacing
inside the PF cone. -/
theorem hadamardProduct_preserves_interl_left {f p q : ℝ[X]}
    (hf : IsPFPolynomial f) (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    Interl (hadamardProduct f p) (hadamardProduct f q) := by
  simpa [hadamardProduct_comm] using
    hadamardProduct_preserves_interl_right hp hq hf hpq

theorem reciprocalShift_hadamardProduct (D : ℕ) (p q : ℝ[X]) :
    reciprocalShift D (hadamardProduct p q) =
      hadamardProduct (reciprocalShift D p) (reciprocalShift D q) := by
  ext n
  simp

/-- Hadamard closure for the reciprocal-interlacing cone. -/
theorem hadamardReciprocalConeClosure {D : ℕ} {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hstrictInterl_p : StrictInterl p (reciprocalShift D p))
    (hstrictInterl_q : StrictInterl q (reciprocalShift D q)) :
    Interl (hadamardProduct p q) (reciprocalShift D (hadamardProduct p q)) := by
  have hp_shift : IsPFPolynomial (reciprocalShift D p) :=
    IsPFPolynomial.of_realRooted_nonneg hp.hasNonnegCoeffs.reciprocalShift hstrictInterl_p.2.1.2
  have hq_shift : IsPFPolynomial (reciprocalShift D q) :=
    IsPFPolynomial.of_realRooted_nonneg hq.hasNonnegCoeffs.reciprocalShift hstrictInterl_q.2.1.2
  simpa [reciprocalShift_hadamardProduct] using
    garloffWagnerHadamardPFInterl_of_nonnegStrictInterl hp hp_shift hq hq_shift
      hstrictInterl_p.toInterl hstrictInterl_q.toInterl

/-- Finite Pólya-frequency sequences are closed under coefficientwise
products.  Finite support is encoded by the coefficient sequences of the
polynomials `p` and `q`. -/
theorem polyaFrequencyHadamardCoeff {p q : ℝ[X]}
    (hp : IsPolyaFreqSeq p.coeff) (hq : IsPolyaFreqSeq q.coeff) :
    IsPolyaFreqSeq (fun n => (hadamardProduct p q).coeff n) :=
  ((IsPFPolynomial.of_sequence aissenSchoenbergWhitneyForwardOrZero hp).hadamardProduct
    (IsPFPolynomial.of_sequence aissenSchoenbergWhitneyForwardOrZero hq)).to_sequence

/-- **Maló's theorem (finite-support Toeplitz form).**  The entrywise product
of two totally nonnegative lower-triangular Toeplitz matrices is totally
nonnegative when their diagonal sequences have finite support.

Here finite support is represented canonically by polynomial coefficient
sequences.  The analogous statement for arbitrary totally nonnegative
matrices, or for arbitrary infinite-support Toeplitz sequences, is false. -/
theorem maloToeplitzHadamard_isTotallyNonneg {p q : ℝ[X]}
    (hp : (toeplitz p.coeff).IsTotallyNonneg)
    (hq : (toeplitz q.coeff).IsTotallyNonneg) :
    (Matrix.of fun i j =>
      toeplitz p.coeff i j * toeplitz q.coeff i j).IsTotallyNonneg := by
  have hcoeff : p.coeff * q.coeff =
      fun n => (hadamardProduct p q).coeff n := by
    funext n
    simp only [Pi.mul_apply, coeff_hadamardProduct]
  rw [← toeplitz_pointwise_mul]
  rw [hcoeff]
  exact polyaFrequencyHadamardCoeff hp hq

end RealRooted
