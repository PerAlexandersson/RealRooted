import RealRooted.GarloffWagner
import RealRooted.Hadamard.Product
import RealRooted.HermiteBiehler.OddEven
import RealRooted.PFPolynomial

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Garloff--Wagner Hadamard theorems

Nonnegative coefficient closure, odd/even algebra, and the checked direct
interlacing theorems of Garloff--Wagner.
-/

/-- Nonnegative coefficients are preserved by coefficientwise Hadamard
products. -/
theorem HasNonnegCoeffs.hadamardProduct {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (hadamardProduct p q) :=
  (hadamardProduct_eq_diagonalOperator p q).symm ▸ hp.diagonalOperator hq

/-- **Odd/even Hadamard identity.**  The coefficientwise Hadamard product
commutes with the odd/even construction `oddEvenPolynomial p q = q(x²) + x·p(x²)`:
the even coefficients multiply the `q`-parts and the odd coefficients multiply
the `p`-parts. This is the algebraic bridge that reduces the two-pair
Garloff--Wagner interlacing theorem to the single-polynomial Hurwitz-stability
fact through the Hermite--Biehler odd/even correspondence. -/
theorem hadamardProduct_oddEvenPolynomial (p q p' q' : ℝ[X]) :
    hadamardProduct (oddEvenPolynomial p q) (oddEvenPolynomial p' q') =
      oddEvenPolynomial (hadamardProduct p p') (hadamardProduct q q') := by
  ext n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k by ring]
    simp
  · subst hk
    simp

/-- PF polynomials are closed under coefficientwise Hadamard products
(Schur--Pólya--Wagner; Garloff--Wagner, Theorem 4(a)). -/
theorem IsPFPolynomial.hadamardProduct {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (hadamardProduct p q) :=
  gwHadamardProductPF hp hq

/- Nonnegative-coefficient Garloff--Wagner interlacing interface for
coefficientwise Hadamard products.

This is the `StrictInterl`/`Interl` wrapper around Garloff--Wagner, Theorem 4(b):
if two nonnegative-coefficient real-rooted pairs are in the same
interlacing relation, then the pair of Hadamard products is again in
interlacing.  The conclusion is zero-aware because the Hadamard product can
vanish when supports are disjoint.

Orientation audit: in this repository `StrictInterl f g` is the convention `f ≪ g`.
In the differ-by-one case, `g` has the rightmost root; in the same-degree case,
each root of `f` is weakly to the left of the corresponding root of `g`.  Thus
for linear factors we have `StrictInterl (X + C b) (X + C a) ↔ a ≤ b`, because their
roots are `-b` and `-a`.  Consequently the Garloff--Wagner hypotheses written
as `g $ f` and `q $ p` are represented here as `StrictInterl f g` and `StrictInterl p q`, and
the conclusion is `Interl (f ⊙ p) (g ⊙ q)`.

The proof is `gwHadamardProductNonnegInterl` in `RealRooted.GarloffWagner`.
-/
/-- Hadamard product preserves interlacing in the nonnegative setting
(Garloff--Wagner, Theorem 4(b)). -/
theorem garloffWagnerHadamardNonnegInterl {f g p q : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hfg : StrictInterl f g) (hpq : StrictInterl p q) :
    Interl (hadamardProduct f p) (hadamardProduct g q) :=
  gwHadamardProductNonnegInterl hf hg hp hq hfg hpq

end RealRooted
