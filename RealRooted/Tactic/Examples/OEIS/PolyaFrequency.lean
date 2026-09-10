import RealRooted.Tactic.Hadamard
import RealRooted.Tactic.MultiplierSequence
import RealRooted.Tactic.PFPolynomial

/-!
# OEIS Polya-frequency regression examples

Regression examples for PF-polynomial, Hadamard, and multiplier frontends.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted
namespace Tactic

/-- PF-polynomial product row-family exit exposed through the OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n)) :
    ∀ n : Nat, IsPFPolynomial (P n * Q n) := by
  rr_pf_sequence_mul using
    left_pf := hP,
    right_pf := hQ

/-- PF-polynomial real-rootedness row-family exit exposed through the OEIS
facade. -/
example {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits := by
  rr_pf_sequence_zero_or_splits using pf := hP

/-- Hadamard PF exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) := by
  rr_hadamard_pf using
    left_pf := hp,
    right_pf := hq

/-- Hadamard nonnegative real-rootedness exit exposed through the OEIS
facade. -/
example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hp : p ≠ 0 ∧ p.Splits) (hq : q ≠ 0 ∧ q.Splits) :
    (hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits) ∧
      HasNonnegCoeffs (hadamardProduct p q) ∧
      ∀ r ∈ (hadamardProduct p q).roots, r ≤ 0 := by
  rr_hadamard_nonneg_realrooted using
    left_nonneg := hpnn,
    right_nonneg := hqnn,
    left_realrooted := hp,
    right_realrooted := hq

/-- Hadamard nonnegative-coefficient exit exposed through the OEIS facade. -/
example {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) := by
  rr_hadamard_nonneg_coeffs using
    left_nonneg := hpnn,
    right_nonneg := hqnn

/-- Hadamard PF row-family exit exposed through the OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hQ : ∀ n : Nat, IsPFPolynomial (Q n)) :
    ∀ n : Nat, IsPFPolynomial (hadamardProduct (P n) (Q n)) := by
  rr_hadamard_sequence_pf using
    left_pf := hP,
    right_pf := hQ

/-- Hadamard nonnegative real-rootedness row-family exit exposed through the
OEIS facade. -/
example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQnn : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hP : ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits)
    (hQ : ∀ n : Nat, Q n ≠ 0 ∧ (Q n).Splits) :
    ∀ n : Nat,
      (hadamardProduct (P n) (Q n) = 0 ∨
          (hadamardProduct (P n) (Q n)).Splits) ∧
        HasNonnegCoeffs (hadamardProduct (P n) (Q n)) ∧
        ∀ r ∈ (hadamardProduct (P n) (Q n)).roots, r ≤ 0 := by
  rr_hadamard_sequence_nonneg_realrooted using
    left_nonneg := hPnn,
    right_nonneg := hQnn,
    left_realrooted := hP,
    right_realrooted := hQ

/-- Hadamard nonnegative-coefficient row-family exit exposed through the OEIS
facade. -/
example {P Q : Nat → ℝ[X]}
    (hPnn : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQnn : ∀ n : Nat, HasNonnegCoeffs (Q n)) :
    ∀ n : Nat, HasNonnegCoeffs (hadamardProduct (P n) (Q n)) := by
  rr_hadamard_sequence_nonneg_coeffs using
    left_nonneg := hPnn,
    right_nonneg := hQnn

/-- Hadamard proper-position row-family exit exposed through the OEIS facade. -/
example {F G P Q : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasNonnegCoeffs (F n))
    (hG : ∀ n : Nat, HasNonnegCoeffs (G n))
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hFG : ∀ n : Nat, Prec (F n) (G n))
    (hPQ : ∀ n : Nat, Prec (P n) (Q n)) :
    ∀ n : Nat,
      Prec0 (hadamardProduct (F n) (P n)) (hadamardProduct (G n) (Q n)) := by
  rr_hadamard_sequence_prec0 using
    first_left_nonneg := hF,
    first_right_nonneg := hG,
    second_left_nonneg := hP,
    second_right_nonneg := hQ,
    first_prec := hFG,
    second_prec := hPQ

/-- Schur--Szego row-family exit exposed through the OEIS facade. -/
example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ n : Nat, IsPFPolynomial (F n))
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hPdeg : ∀ n : Nat, (P n).natDegree ≤ N n)
    (hPsplits : ∀ n : Nat, (P n).Splits) :
    ∀ n : Nat,
      schurSzegoComp (N n) (F n) (P n) = 0 ∨
        (schurSzegoComp (N n) (F n) (P n)).Splits := by
  rr_schur_szego_sequence using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits

/-- Schur--Szego row-family nonzero endpoint exposed through the OEIS facade. -/
example {N : Nat → ℕ} {F P : Nat → ℝ[X]}
    (hF : ∀ n : Nat, IsPFPolynomial (F n))
    (hFdeg : ∀ n : Nat, (F n).natDegree ≤ N n)
    (hPdeg : ∀ n : Nat, (P n).natDegree ≤ N n)
    (hPsplits : ∀ n : Nat, (P n).Splits)
    (hout : ∀ n : Nat, schurSzegoComp (N n) (F n) (P n) ≠ 0) :
    ∀ n : Nat, (schurSzegoComp (N n) (F n) (P n)).Splits := by
  rr_schur_szego_sequence_splits using
    pf_factor := hF,
    pf_degree := hFdeg,
    input_degree := hPdeg,
    input_splits := hPsplits,
    nonzero := hout

/-- Schur--Szego low-degree PF-factor exit exposed through the OEIS facade. -/
example {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 2)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_two using
    pf_factor := hf,
    pf_degree_le_two := hfdeg,
    input_degree := hpdeg,
    input_splits := hsplits

/-- Schur--Szego cubic numerator route exposed through the OEIS facade. -/
example {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ 3)
    (hfn : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hsplits : p.Splits)
    (hnum : 3 ≤ n → 0 ≤ schurSzegoCompCubicDiscrNumerator n f p)
    (hout : schurSzegoComp n f p ≠ 0) :
    (schurSzegoComp n f p).Splits := by
  rr_schur_szego_pf_factor_degree_le_three_num_left_degree_splits using
    pf_factor := hf,
    pf_degree_le_three := hfdeg,
    pf_degree := hfn,
    input_degree := hpdeg,
    input_splits := hsplits,
    cubic_numerator := hnum,
    nonzero := hout

/-- Jensen nonnegative-coefficient row-family exit exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k) :
    ∀ n : Nat, HasNonnegCoeffs (jensenPolynomial (N n) (Gamma n)) := by
  rr_jensen_sequence_nonneg using
    level := N,
    sequence_nonneg := hGamma

/-- Jensen PF row-family exit from finite multipliers exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k)
    (hmult : ∀ n : Nat, IsFiniteMultiplierSequence (N n) (Gamma n)) :
    ∀ n : Nat, IsPFPolynomial (jensenPolynomial (N n) (Gamma n)) := by
  rr_jensen_sequence_pf_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult

/-- Finite PF-multiplier row-family conversion exposed through the OEIS
facade. -/
example {N : Nat → ℕ} {Gamma : Nat → ℕ → ℝ}
    (hGamma : ∀ n k, 0 ≤ Gamma n k)
    (hmult : ∀ n : Nat, IsFiniteMultiplierSequence (N n) (Gamma n)) :
    ∀ n : Nat, IsFinitePFMultiplierSequence (N n) (Gamma n) := by
  rr_finite_pf_multiplier_sequence_of_finite_multiplier using
    level := N,
    sequence_nonneg := hGamma,
    multiplier := hmult


end Tactic
end RealRooted
