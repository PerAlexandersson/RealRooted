import RealRooted.JacobiDeformation
import RealRooted.Applications.OEIS.A132885
import RealRooted.SpectralProduct

/-!
# Jacobi deformation challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "jacobi-deformation"
authors = ["Micchelli", "Willoughby", "Alexandersson"]
years = [1979, 2026]

[[definitions]]
name = "RealRooted.JacobiDeformation.polynomial"
module = "RealRooted.JacobiDeformation.Basic"
label = "The Jacobi deformation J_{m,δ}"

[[definitions]]
name = "RealRooted.Applications.OEIS.A132885.polynomial"
module = "RealRooted.Applications.OEIS.A132885"
label = "Row polynomials of OEIS A132885"

[[definitions]]
name = "RealRooted.increasingEigenvalues"
module = "RealRooted.SpectralProduct"
label = "Eigenvalues of a symmetric matrix in increasing order"

[[theorems]]
name = "RealRooted.Challenges.JacobiDeformation.polynomial_splits_and_roots_neg"
label = "For every δ ≥ 0 all roots are real and negative"
headline = true

[[theorems]]
name = "RealRooted.Challenges.JacobiDeformation.interlaces_derivative_polynomial_zero"
label = "For 0 < δ < 1 the roots are simple and strictly interlace J′_{m,0}"
headline = true

[[theorems]]
name = "RealRooted.Challenges.JacobiDeformation.isPFPolynomial_polynomial"
label = "For every δ ≥ 0 the deformation is a PF polynomial"

[[theorems]]
name = "RealRooted.Applications.OEIS.A132885.splits_simple_roots_neg"
module = "RealRooted.Applications.OEIS.A132885"
label = "Rows of A132885 have simple negative roots"
headline = true

[[theorems]]
name = "RealRooted.Applications.OEIS.A132885.isPFPolynomial_polynomial"
module = "RealRooted.Applications.OEIS.A132885"
label = "Rows of A132885 are PF polynomials"

[[theorems]]
name = "RealRooted.Challenges.JacobiDeformation.aeval_prod_sub_increasingEigenvalues_nonneg"
label = "Micchelli–Willoughby: initial spectral products are entrywise nonnegative"
-->

<!-- realrooted-catalog-content -->
# The Jacobi deformation

For $m \in \mathbb{N}$ and real $\delta, c, d, U, V$, the Jacobi deformation is
the monic polynomial of degree $m$
$$
J_{m,\delta}^{c,d}(x; U, V) = \sum_{i + j \le m}
  \frac{m!}{(m - i - j)!\, i!\, j!}
  \frac{(m + c + d - 1 + \delta)_{i + j}}{(c)_i\, (d)_j}\,
  U^i V^j x^{m - i - j},
$$
where $(a)_n = a(a + 1) \cdots (a + n - 1)$ is the rising factorial.

**Theorem.** Let $c, d, U, V > 0$.

- For every $\delta \ge 0$, all roots of $J_{m,\delta}^{c,d}$ are real and
  strictly negative. Hence $J_{m,\delta}^{c,d}$ is a PF polynomial.
- If $m \ge 1$ and $0 < \delta < 1$, the roots of $J_{m,\delta}^{c,d}$ are
  simple and interlace the roots of the derivative of $J_{m,0}^{c,d}$:
  $(J_{m,0}^{c,d})' \ll J_{m,\delta}^{c,d}$, and the two polynomials have no
  common root.

The rows of the triangle OEIS A132885,
$$
A_n(x) = \sum_{k \le n/2} \binom{n - k}{k}\, T_{n - 2k}\, x^k,
$$
where $T_j$ is the central trinomial coefficient, are half-integer
specializations:
$A_{2m} = J_{m,1/2}^{1,1/2}(x; 1, 1/4)$ and
$A_{2m+1} = (m + 1)\, J_{m,1/2}^{1,3/2}(x; 1, 1/4)$. So for $n \ge 2$ the row
$A_n$ has simple, strictly negative roots, and every row is a PF polynomial.
The rows $A_0 = A_1 = 1$ are constant.

## Proof idea

The argument is finite and algebraic. With $s = c + d$, let $p_j$ be the
monic shifted Jacobi polynomials, orthogonal for the moment functional
$\ell(t^k) = (c)_k / (s)_k$, and let $\lambda_j = j(j + s - 1)$ be the
eigenvalues of the Jacobi operator.

1. A finite Appell kernel $K_\delta(r, z)$ is diagonal in the Jacobi basis,
   with positive weights that have a positive Newton expansion in the
   $\lambda_j$. Evaluated at $rz = -U/\xi$ and $(1 - r)(1 - z) = -V/\xi$, it
   recovers $J_{m,\delta}(\xi)$ up to the positive factor $(-\xi)^m$.
2. At the roots of a quasi-Jacobi polynomial $p_q - \tau p_{q-1}$, exact
   quadrature symmetrizes the collocation matrix of the Jacobi operator, and
   all its entries are strictly positive.
3. The **Micchelli–Willoughby theorem** makes the initial spectral products of
   that matrix entrywise nonnegative: if $A$ is a real symmetric matrix with
   nonnegative entries and, in the simple-spectrum case formalized here,
   eigenvalues $\mu_1 < \dots < \mu_N$, then
   $(A - \mu_1) \cdots (A - \mu_k)$ is entrywise nonnegative for every $k < N$.
   This gives strict signs of the kernel at pairs of quasi-Jacobi roots.
4. At $\delta = 0$ only the top weight survives, and $J_{m,0}$ is an explicit
   product over the roots of $p_m$, whose derivative has $m - 1$ simple roots.
   At each critical point $\xi$ of $J_{m,0}$, one shows
   $J_{m,\delta}(\xi)\, J_{m,0}''(\xi) < 0$ for $0 < \delta < 1$.
5. The unit shift $b J_{m,\delta+1} = (b + m) J_{m,\delta} - x J_{m,\delta}'$
   with $b = m + s - 1 + \delta$ transports negative real-rootedness from
   $[0, 1)$ to every $\delta \ge 0$.

## References

The theorem and its proof are original to this library (P. Alexandersson,
2026); there is no preprint yet.

C. A. Micchelli and R. A. Willoughby, “On functions which preserve the class
of Stieltjes matrices,” *Linear Algebra and its Applications* 23 (1979),
141–156.
The triangle is [OEIS A132885](https://oeis.org/A132885); the central trinomial
coefficients are [OEIS A002426](https://oeis.org/A002426). The Jacobi
polynomials used in the proof are on the
[Jacobi polynomials page](/RealRooted/families/jacobi-polynomials/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.JacobiDeformation`, `RealRooted.Applications.OEIS.A132885`, and
`RealRooted.SpectralProduct`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace JacobiDeformation

/-- For every `δ ≥ 0`, the Jacobi deformation splits and all its roots are
strictly negative. -/
theorem polynomial_splits_and_roots_neg (m : ℕ) {δ c d U V : ℝ} (hδ : 0 ≤ δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    (RealRooted.JacobiDeformation.polynomial m δ c d U V).Splits ∧
      ∀ r ∈ (RealRooted.JacobiDeformation.polynomial m δ c d U V).roots, r < 0 :=
  RealRooted.JacobiDeformation.polynomial_all_rank_nonneg_parameter m hδ hc hd hU hV

/-- For `m ≠ 0` and `0 < δ < 1`, the derivative of `J_{m,0}` interlaces
`J_{m,δ}`, the deformation has simple roots, and the two polynomials have no
common root. -/
theorem interlaces_derivative_polynomial_zero {m : ℕ} (hm : m ≠ 0) {δ c d U V : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Interlaces (RealRooted.JacobiDeformation.polynomial m 0 c d U V).derivative
        (RealRooted.JacobiDeformation.polynomial m δ c d U V) ∧
      HasSimpleRoots (RealRooted.JacobiDeformation.polynomial m δ c d U V) ∧
      ∀ r, (RealRooted.JacobiDeformation.polynomial m 0 c d U V).derivative.IsRoot r →
        ¬(RealRooted.JacobiDeformation.polynomial m δ c d U V).IsRoot r :=
  have h := RealRooted.JacobiDeformation.polynomial_strict_package
    (Nat.one_le_iff_ne_zero.mpr hm) hc hd hU hV hδ hδ1
  ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- For every `δ ≥ 0`, the Jacobi deformation is a PF polynomial. -/
theorem isPFPolynomial_polynomial (m : ℕ) {δ c d U V : ℝ} (hδ : 0 ≤ δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    IsPFPolynomial (RealRooted.JacobiDeformation.polynomial m δ c d U V) := by
  cases m with
  | zero =>
      rw [RealRooted.JacobiDeformation.polynomial_zero]
      exact IsPFPolynomial.one
  | succ m =>
      exact IsPFPolynomial.of_realRooted_nonneg
        (RealRooted.JacobiDeformation.hasNonnegCoeffs_polynomial_of_pos (by lia) hδ hc hd hU hV)
        (polynomial_splits_and_roots_neg (m + 1) hδ hc hd hU hV).1

/-- **Micchelli–Willoughby.** Let `A` be a real symmetric matrix with
nonnegative entries and simple spectrum `μ_0 < μ_1 < ⋯`. Then every initial
spectral product `(A - μ_0) ⋯ (A - μ_{k-1})` is entrywise nonnegative. -/
theorem aeval_prod_sub_increasingEigenvalues_nonneg {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j) (hsimple : StrictAnti (sortedEigenvalues A hA))
    (k : Fin (N + 1)) (i j : Fin (N + 1)) :
    0 ≤ aeval A (∏ l : Fin k,
      (X - C (increasingEigenvalues A hA ⟨l, l.isLt.trans k.isLt⟩))) i j := by
  have h := spectralProduct_entrywise_nonneg A hA hentry hsimple k i j
  rw [spectralInitialRoots, List.map_ofFn] at h
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  simpa [Function.comp_def, Algebra.algebraMap_eq_smul_one] using h

end JacobiDeformation
end Challenges
end RealRooted
