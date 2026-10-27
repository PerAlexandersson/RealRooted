module

public import RealRooted.Hadamard
public import RealRooted.Tactic.Finish

/-!
# Hadamard and Schur--Szegő family lemmas and automation

Pointwise lifts of the checked finite Schur--Szegő and Hadamard PF backends,
together with context-driven Hadamard interlacing automation.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- A finite Schur--Szegő composition of a bounded-degree PF factor and a
bounded-degree split input splits when the composition is nonzero. -/
theorem schurSzegoComp_splits_of_nonzero {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition hf hfdeg hpdeg hsplits) hout

/-- A nonzero finite Schur--Szegő composition splits when its PF factor has
degree at most two and its split input has degree at most the level. -/
theorem schurSzegoComp_splits_of_pf_factor_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_natDegree_le_two
      hf hfdeg hpdeg hsplits)
    hout

/-- A nonzero finite Schur--Szegő composition splits when its PF factor and
split input both have degree at most two. -/
theorem schurSzegoComp_splits_of_factors_natDegree_le_two
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ 2)
    (hsplits : p.Splits)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_factors_natDegree_le_two
      hf hfdeg hpdeg hsplits)
    hout

/-- A nonzero finite Schur--Szegő composition splits when the factor has
degree at most three and the composition has nonnegative cubic discriminant. -/
theorem schurSzegoComp_splits_of_pf_factor_natDegree_le_three_cubicDiscr
    {n : ℕ} {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr (schurSzegoComp n f p))
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_natDegree_le_three_cubicDiscr_nonneg hfdeg hdisc)
    hout

/-- At a level of at least three, a nonzero finite Schur--Szegő composition
with factor degree at most three splits when its cubic-discriminant numerator
is nonnegative. -/
theorem schurSzegoComp_splits_of_pf_factor_natDegree_le_three_cubicNum
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3)
    (hnum : 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits :=
  Or.resolve_left
    (finiteSchurSzegoComposition_of_pf_factor_natDegree_le_three_cubicDiscrNumerator_nonneg
      hn hfdeg hnum)
    hout

/-- Pointwise finite Schur--Szegő compositions of bounded-degree PF factors
and bounded-degree split inputs are zero or split. -/
theorem schurSzegoComp_sequence_zero_or_splits {N : Nat → ℕ}
    {F P : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ N i)
    (hPdeg : ∀ i : Nat, (P i).natDegree ≤ N i)
    (hPsplits : ∀ i : Nat, (P i).Splits) :
    ∀ i : Nat,
      schurSzegoComp (N i) (F i) (P i) = 0 ∨
        (schurSzegoComp (N i) (F i) (P i)).Splits := fun i =>
  finiteSchurSzegoComposition
    (hF i) (hFdeg i) (hPdeg i) (hPsplits i)

/-- Pointwise finite Schur--Szegő compositions of bounded-degree PF factors
and bounded-degree split inputs split when the compositions are nonzero. -/
theorem schurSzegoComp_sequence_splits {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ i : Nat, IsPFPolynomial (F i))
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ N i)
    (hPdeg : ∀ i : Nat, (P i).natDegree ≤ N i)
    (hPsplits : ∀ i : Nat, (P i).Splits)
    (hout : ∀ i : Nat, schurSzegoComp (N i) (F i) (P i) ≠ 0) :
    ∀ i : Nat, (schurSzegoComp (N i) (F i) (P i)).Splits := fun i =>
  Or.resolve_left
    (schurSzegoComp_sequence_zero_or_splits hF hFdeg hPdeg hPsplits i)
    (hout i)

/-- Pointwise Hadamard products of PF-polynomial families are PF. -/
theorem hadamardProduct_sequence_pf {P Q : Nat → ℝ[X]}
    (hP : ∀ i : Nat, IsPFPolynomial (P i))
    (hQ : ∀ i : Nat, IsPFPolynomial (Q i)) :
    ∀ i : Nat, IsPFPolynomial (hadamardProduct (P i) (Q i)) := fun i =>
  IsPFPolynomial.hadamardProduct (hP i) (hQ i)

/-- A nonzero scalar multiple of each rowwise Hadamard product of PF
polynomials is nonzero and real-rooted. -/
theorem isRealRooted_of_hadamardProduct_scalar_sequence
    {P L R : Nat → ℝ[X]} {c : Nat → ℝ}
    (hleft : ∀ n : Nat, IsPFPolynomial (L n))
    (hright : ∀ n : Nat, IsPFPolynomial (R n))
    (hproduct_ne : ∀ n : Nat, hadamardProduct (L n) (R n) ≠ 0)
    (hc : ∀ n : Nat, c n ≠ 0)
    (hrow : ∀ n : Nat, P n = C (c n) * hadamardProduct (L n) (R n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hproduct_pf :
      ∀ n : Nat, IsPFPolynomial (hadamardProduct (L n) (R n)) :=
    hadamardProduct_sequence_pf hleft hright
  intro n
  have hproduct := (hproduct_pf n).ne_zero_and_splits (hproduct_ne n)
  simpa [hrow n] using isRealRooted_C_mul hproduct.1 hproduct.2 (hc n)

/-- Pointwise Hadamard products of nonnegative, nonzero split polynomial
families are zero or split, have nonnegative coefficients, and have only
nonpositive roots. -/
theorem hadamardProduct_sequence_nonneg_realrooted {P Q : Nat → ℝ[X]}
    (hPnonneg : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQnonneg : ∀ i : Nat, HasNonnegCoeffs (Q i))
    (hP : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hQ : ∀ i : Nat, Q i ≠ 0 ∧ (Q i).Splits) :
    ∀ i : Nat,
      (hadamardProduct (P i) (Q i) = 0 ∨
          (hadamardProduct (P i) (Q i)).Splits) ∧
        HasNonnegCoeffs (hadamardProduct (P i) (Q i)) ∧
        ∀ r ∈ (hadamardProduct (P i) (Q i)).roots, r ≤ 0 := fun i =>
  garloffWagnerHadamardNonnegRealRooted_of_nonnegStrictInterl
    (hPnonneg i) (hQnonneg i) (hP i) (hQ i)

/-- Pointwise Hadamard products preserve coefficientwise nonnegativity. -/
theorem hadamardProduct_sequence_nonneg_coeffs {P Q : Nat → ℝ[X]}
    (hPnonneg : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQnonneg : ∀ i : Nat, HasNonnegCoeffs (Q i)) :
    ∀ i : Nat, HasNonnegCoeffs (hadamardProduct (P i) (Q i)) := fun i =>
  HasNonnegCoeffs.hadamardProduct (hPnonneg i) (hQnonneg i)

/-- Pointwise Hadamard products preserve the indicated interlacing of two
pairs with nonnegative coefficients. -/
theorem hadamardProduct_sequence_interl {F G P Q : Nat → ℝ[X]}
    (hF : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hG : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hP : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hQ : ∀ i : Nat, HasNonnegCoeffs (Q i))
    (hFG : ∀ i : Nat, StrictInterl (F i) (G i))
    (hPQ : ∀ i : Nat, StrictInterl (P i) (Q i)) :
    ∀ i : Nat,
      Interl (hadamardProduct (F i) (P i)) (hadamardProduct (G i) (Q i)) :=
  fun i =>
    StrictInterl.interl_hadamardProduct
      (hF i) (hG i) (hP i) (hQ i) (hFG i) (hPQ i)
/-- Closes a Hadamard-product interlacing goal for PF polynomials from
certificates found in the local context. It tries fixed-right-factor,
fixed-left-factor, and general PF forms in turn. -/
syntax (name := rr_hadamard_pf_interl_named)
  "rr_hadamard_pf_interl" : tactic

macro_rules
  | `(tactic| rr_hadamard_pf_interl) =>
      `(tactic|
        first
          | exact RealRooted.Interl.hadamardProduct_right
              rr_lookup_term rr_lookup_term rr_lookup_term rr_lookup_term
          | exact RealRooted.Interl.hadamardProduct_left
              rr_lookup_term rr_lookup_term rr_lookup_term rr_lookup_term
          | exact RealRooted.garloffWagnerHadamardPFInterl_of_nonnegStrictInterl
              rr_lookup_term rr_lookup_term rr_lookup_term rr_lookup_term
              rr_lookup_term rr_lookup_term)

end Tactic
end RealRooted

