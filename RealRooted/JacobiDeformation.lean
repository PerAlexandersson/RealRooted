import RealRooted.JacobiDeformation.Parity
import RealRooted.JacobiDeformation.Strict

/-!
# The Jacobi deformation

For `c, d, U, V > 0`, `m : ℕ`, and `δ ≥ 0`, the Jacobi deformation is the
monic degree-`m` polynomial

`J_{m,δ}^{c,d}(X, U, V) = ∑_{i + j ≤ m} m! / ((m - i - j)! i! j!) ·
  (m + c + d - 1 + δ)_{i + j} / ((c)_i (d)_j) · U ^ i V ^ j X ^ (m - i - j)`

(`RealRooted.JacobiDeformation.polynomial m δ c d U V`).  This module is the
public entry point for its root theory:

* for `0 < δ < 1`, `J_{m,δ}` has `m` simple, strictly negative roots, is a
  PF polynomial, and is strictly interlaced by the derivative of `J_{m,0}`
  (`polynomial_strict_package`, `polynomial_strict_splits_simple_roots_neg`,
  `roots_card_polynomial_strict`, `isPFPolynomial_polynomial_strict`);
* for every `δ ≥ 0`, `J_{m,δ}` splits with strictly negative roots
  (`polynomial_all_rank_nonneg_parameter`);
* at `δ = 1 / 2`, `c = U = 1`, `V = 1 / 4` and `d ∈ {1 / 2, 3 / 2}`, the
  coefficients are central-trinomial expressions
  (`coeff_polynomial_even_centralTrinomial`,
  `coeff_polynomial_odd_centralTrinomial`), which give the rows of OEIS
  A132885 in `RealRooted.Applications.OEIS.A132885`.

## Structure of the proof

The argument is algebraic and finite; no integral representation or
limiting argument is used.  With `s = c + d`, let `p_j` be the monic shifted
Jacobi polynomials, `h_j` their squared norms for the moment functional
`ℓ(t ^ k) = (c)_k / (s)_k`, and `λ_j = j (j + s - 1)` the eigenvalues of the
positive Jacobi operator.

1. `Pochhammer`, `Basic`, `Boundary`: rising and falling factorials with the
   Chu--Vandermonde and Pfaff--Saalschütz identities; the finite algebra of
   the deformation; ranks zero and one.
2. `Kernel`, `NewtonIdentity`: the kernel weights
   `w_j(δ) = m! / (m - j)! · (m + s - 1 + δ)_j (δ)_{m-j} / (s)_{m+j}` and
   their positive Newton expansion `w_j / w_0 = ∑_k a_k(δ) Λ_k(λ_j)`.
3. `Moment`, `Appell`, `BoundaryProjection`, `KernelExpansion`: the finite
   Appell kernel `K_δ(r, z)` is diagonal in the Jacobi eigenbasis,
   `K_δ(r, z) = ∑_j w_j(δ) p_j(r) p_j(z) / h_j`, and evaluating it at the
   coordinates `r z = -U / ξ`, `(1 - r)(1 - z) = -V / ξ` of a value `ξ`
   recovers `J_{m,δ}(ξ)` up to the positive factor `(-ξ) ^ m`.
4. `Quadrature`, `JacobiOperator`, `Collocation`, `CollocationPositivity`:
   at the roots of a quasi-Jacobi polynomial `p_q - τ p_{q-1}`, exact
   quadrature symmetrizes the collocation matrix of the Jacobi operator, and
   a two-point rank-one compression argument makes every entry strictly
   positive, including at a root outside `(0, 1)`.
5. `KernelSign`, `SpectralKernel`, `QuasiNodes`, `CriticalKernelSign`: the
   Micchelli--Willoughby spectral-product lemma (`RealRooted.SpectralProduct`)
   makes the Newton factors of that matrix entrywise nonnegative, which gives
   strict signs of the weighted kernel at pairs of quasi-Jacobi roots.
6. `RootGeometry`, `ImageProduct`, `BaseProduct`: at `δ = 0` only the top
   weight survives and `J_{m,0} = ∏_i (X + U / r_i + V / (1 - r_i))` over the
   roots of `p_m`; its derivative has `m - 1` simple roots below
   `-(√U + √V) ^ 2`.
7. `CriticalCases`, `Strict`: at every critical point `ξ` of `J_{m,0}`,
   `J_{m,δ}(ξ) J_{m,0}''(ξ) < 0`, which gives the strict interlacing theorem
   for `0 < δ < 1`.
8. `Shift`: the unit shift `b J_{m,δ+1} = (b + m) J_{m,δ} - X J_{m,δ}'` with
   `b = m + s - 1 + δ` transports negative real-rootedness to every `δ ≥ 0`.
9. `Parity`: the central-trinomial specializations.
-/
