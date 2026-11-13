module

import RealRooted.Mesh.Derivative
import RealRooted.Mesh.DiscreteHermitePoulain
import RealRooted.Mesh.DiscreteMultiplier
import RealRooted.Mesh.DiscreteMultiplierSequence
import RealRooted.Mesh.DiscreteMultiplierSequenceLaguerrePolya
import RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur
import RealRooted.Mesh.Limit
import RealRooted.Mesh.FallingFactorial
import RealRooted.Mesh.FiniteDifferenceHyperbolicity
import RealRooted.Mesh.HermitePoulain

/-!
# Mesh and finite differences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "mesh-finite-difference"
formalized = "2026-10-27"
references = []
tags = []
authors = ["Brändén", "Krasikov", "Shapiro"]
years = [2016]

[[definitions]]
name = "Polynomial.MeshGE"
module = "RealRooted.Mesh.Basic"
label = "Mesh at least α"

[[definitions]]
name = "RealRooted.meshDifference"
module = "RealRooted.Mesh.FiniteDifference"
label = "The finite difference p(x) − λ p(x − α)"

[[definitions]]
name = "RealRooted.finiteDifferenceOp"
module = "RealRooted.Mesh.HermitePoulain"
label = "The finite-difference operator with symbol Q"

[[theorems]]
name = "Polynomial.MeshGE.sub_C_mul_derivative"
module = "RealRooted.Mesh.Derivative"
label = "Riesz: subtracting c p′ does not decrease the mesh"

[[theorems]]
name = "RealRooted.meshDifference_meshGE"
module = "RealRooted.Mesh.FiniteDifference"
label = "Positive finite differences preserve mesh bounds at least their step"

[[theorems]]
name = "RealRooted.forall_finiteDifferenceOp_meshGE_iff"
module = "RealRooted.Mesh.DiscreteHermitePoulain"
label = "Discrete Hermite–Poulain theorem"
headline = true

[[theorems]]
name = "RealRooted.meshGE_one_add_X_mul_meshDifference"
module = "RealRooted.Mesh.DiscreteMultiplier"
label = "The operator a p + b x (p(x) − p(x − 1)) preserves mesh at least one"

[[definitions]]
name = "RealRooted.IsDiscreteMultiplierSequence"
module = "RealRooted.Mesh.DiscreteMultiplierSequence"
label = "Discrete multiplier sequence"

[[theorems]]
name = "RealRooted.isDiscreteMultiplierSequence_eval"
module = "RealRooted.Mesh.DiscreteMultiplierSequence"
label = "φ(0), φ(1), … is a discrete multiplier sequence for φ with nonpositive zeros"

[[theorems]]
name = "RealRooted.IsDiscreteMultiplierSequence.le_succ"
module = "RealRooted.Mesh.DiscreteMultiplierSequence"
label = "Discrete multiplier sequences increase where they are positive"

[[theorems]]
name = "RealRooted.fallingFactorialMap_meshGE_one"
module = "RealRooted.Mesh.FallingFactorial"
label = "Brenti: x^i ↦ [x]_i sends nonnegative zeros to mesh at least one"

[[theorems]]
name = "RealRooted.neg_one_pow_mul_descPochhammerBasis_repr_nonneg"
module = "RealRooted.Mesh.FallingFactorial"
label = "Falling-factorial coefficients alternate in sign"

[[theorems]]
name = "RealRooted.IsDiscreteMultiplierSequence.nonneg_or_nonpos"
module = "RealRooted.Mesh.DiscreteMultiplierSequence"
label = "Nonzero entries of a discrete multiplier sequence share a sign"

[[theorems]]
name = "RealRooted.isDiscreteMultiplierSequence_iff_adjacent_of_two_nonzero"
module = "RealRooted.Mesh.DiscreteMultiplierSequence"
label = "Trivial discrete multiplier sequences"

[[theorems]]
name = "RealRooted.IsDiscreteMultiplierSequence.isMultiplierSequence"
module = "RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur"
label = "Discrete multiplier sequences are multiplier sequences"

[[theorems]]
name = "RealRooted.not_isDiscreteMultiplierSequence_geometric"
module = "RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur"
label = "ρ^i with 0 < ρ < 1 is not a discrete multiplier sequence"

[[theorems]]
name = "RealRooted.isDiscreteMultiplierSequence_of_isLaguerrePolyaTypeI"
module = "RealRooted.Mesh.DiscreteMultiplierSequenceLaguerrePolya"
label = "φ(0), φ(1), … is a discrete multiplier sequence for φ in the Laguerre–Pólya class"
[[theorems]]
name = "RealRooted.PreservesRealRootedOrZero.polyFiniteDifferenceOp_iff"
module = "RealRooted.Mesh.FiniteDifferenceHyperbolicity"
label = "p ↦ ∑ q_j(x) p(x − j) preserves real-rootedness iff at most one q_j is nonzero"

[[theorems]]
name = "RealRooted.finiteDifferenceOp_meshGE"
module = "RealRooted.Mesh.HermitePoulain"
label = "Symbols with nonnegative real zeros preserve Mesh ≥ β for every β ≥ α"

[[theorems]]
name = "RealRooted.HasOnlyNonnegRoots.of_tendsto_coeff"
module = "RealRooted.Mesh.Limit"
label = "Only nonnegative roots is closed under coefficientwise limits of bounded degree"
-->

<!-- realrooted-catalog-content -->
# Mesh and finite differences

Operators built from derivatives and finite differences preserve a lower bound on the distance
between consecutive roots of a real-rooted polynomial. This mesh condition is the finite
difference analogue of real-rootedness, and it leads to a discrete Hermite–Poulain theorem and
discrete multiplier sequences.

## Results

We write $p\in\mathrm{Mesh}_{\ge\alpha}$ if $p$ is real-rooted and consecutive roots, listed
increasingly with multiplicity, differ by at least $\alpha\ge0$. Theorem numbers refer to
Brändén, Krasikov and Shapiro.

**Theorem 1 (Riesz).** If $p\in\mathrm{Mesh}_{\ge\alpha}$ and $c\in\mathbb R$, then
$p-c\,p'\in\mathrm{Mesh}_{\ge\alpha}$.

**Theorem 2.** Let $\alpha,\lambda>0$ and $\beta\ge\alpha$. If $p\in\mathrm{Mesh}_{\ge\beta}$,
then $p(x)-\lambda\,p(x-\alpha)\in\mathrm{Mesh}_{\ge\beta}$.

**Theorem 3 (discrete Hermite–Poulain).** Let $\alpha>0$ and let $Q(t)=\sum_k a_kt^k$ be a real
polynomial. The operator
$$p(x)\longmapsto\sum_ka_k\,p(x-k\alpha)$$
maps $\mathrm{Mesh}_{\ge\alpha}$ into $\mathrm{Mesh}_{\ge\alpha}$ if and only if $Q$ is zero or
has only real nonnegative zeros. For such $Q$ it maps $\mathrm{Mesh}_{\ge\beta}$ into itself for
every $\beta\ge\alpha$.

**Theorem 5.** If $a,b\ge0$, $p\in\mathrm{Mesh}_{\ge1}$ and $p$ has only nonnegative zeros, then
$$a\,p(x)+b\,x\,\bigl(p(x)-p(x-1)\bigr)$$
lies in $\mathrm{Mesh}_{\ge1}$ and has only nonnegative zeros.

**Lemma 8.** Let $q_0,\dots,q_k$ be real polynomials. The operator
$$p(x)\longmapsto\sum_jq_j(x)\,p(x-j)$$
maps real-rooted polynomials to real-rooted polynomials or zero if and only if at most one $q_j$
is nonzero, and that $q_j$ is real-rooted.

A sequence $(a_i)$ is a *discrete multiplier sequence* if the linear operator with
$[x]_i\mapsto a_i[x]_i$ on the falling factorials $[x]_i=x(x-1)\cdots(x-i+1)$ maps every
$p\in\mathrm{Mesh}_{\ge1}$ with only nonnegative zeros to such a polynomial.

**Corollary 2.** If $\varphi\ne0$ is real-rooted with only nonpositive zeros, then
$(\varphi(i))_{i\ge0}$ is a discrete multiplier sequence. The same holds for $(\operatorname{Re}
\varphi(i))_{i\ge0}$ when $\varphi$ is a locally uniform limit of real-rooted polynomials with
nonnegative coefficients.

**Lemma 10 (Brenti).** The linear map $x^i\mapsto[x]_i$ sends every real-rooted polynomial with
only nonnegative zeros into $\mathrm{Mesh}_{\ge1}$, with only nonnegative zeros.

**Lemma 11 and Corollary 3.** If $p=\sum_{i\le n}a_i[x]_i$ lies in $\mathrm{Mesh}_{\ge1}$, has
only nonnegative zeros and positive leading coefficient, then $(-1)^{n-i}a_i\ge0$ for
$i\le n$. Consequently the entries of a discrete multiplier sequence are all nonnegative or all
nonpositive.

**Proposition 6.** Every discrete multiplier sequence is a multiplier sequence in the classical
sense. The converse fails: $(\rho^i)$ with $0<\rho<1$ is not a discrete multiplier sequence
(Remark 2).

**Proposition 7.** A sequence with at most two nonzero entries is a discrete multiplier sequence
if and only if its nonzero entries sit at adjacent indices $m,m+1$ and $a_ma_{m+1}\ge0$.

**Proposition 12.** If $(a_i)$ is a discrete multiplier sequence and $a_{m+2}>0$, then
$a_m\le a_{m+1}$.

## Proof

For Lemma 8 we apply the operator to $x^m$: two nonzero extreme shifts produce nonreal
[limits of zeros](rr:limits-of-zeros) by the Beraha–Kahane–Weiss theorem. Corollary 2 uses that
$\mathrm{Mesh}_{\ge\alpha}$ is closed under coefficientwise limits of bounded degree.

## References

- P. Brändén, I. Krasikov and B. Shapiro, *Elements of Pólya–Schur theory in the finite
  difference setting*, Proc. Amer. Math. Soc. 144 (2016): Theorems 1, 2, 3 and 5, Lemmas 8, 10
  and 11, Corollaries 2 and 3, Propositions 6, 7 and 12, and Remark 2. Theorem 1 is due to
  Riesz.
<!-- /realrooted-catalog-content -->

The definitions and theorems live in `RealRooted.Mesh.Basic`, `RealRooted.Mesh.Derivative`,
`RealRooted.Mesh.FiniteDifference`, `RealRooted.Mesh.HermitePoulain` (sufficiency in
Theorem 3), `RealRooted.Mesh.DiscreteHermitePoulain` (necessity and the equivalence),
`RealRooted.Mesh.DiscreteMultiplier` (Theorem 5), `RealRooted.Mesh.FallingFactorial` (Lemmas 10
and 11), `RealRooted.Mesh.DiscreteMultiplierSequence` (Corollaries 2 and 3, Propositions 7 and 12),
`RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur` (Proposition 6),
`RealRooted.Mesh.DiscreteMultiplierSequenceLaguerrePolya` (Corollary 2 in general), and
`RealRooted.Mesh.Limit`.
-/
