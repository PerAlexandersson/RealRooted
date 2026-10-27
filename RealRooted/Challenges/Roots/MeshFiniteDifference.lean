module

import RealRooted.Mesh.Derivative
import RealRooted.Mesh.DiscreteHermitePoulain
import RealRooted.Mesh.DiscreteMultiplier
import RealRooted.Mesh.DiscreteMultiplierSequence
import RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur
import RealRooted.Mesh.FallingFactorial

/-!
# Mesh and finite differences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "mesh-finite-difference"
formalized = "2026-10-27"
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
-->

<!-- realrooted-catalog-content -->
# Mesh and finite differences

For a real-rooted polynomial $p$, the *mesh* of $p$ is the smallest distance between
consecutive roots, counted with multiplicity. We write $p \in \mathrm{Mesh}_{\geq \alpha}$
(`Polynomial.MeshGE p α`) if $p$ is real-rooted and consecutive roots, listed increasingly
with multiplicity, differ by at least $\alpha \geq 0$. The results below are from
Brändén, Krasikov, and Shapiro, *Elements of Pólya–Schur theory in the finite difference
setting*, Proc. Amer. Math. Soc. 144 (2016).

**Theorem 1 (Riesz).** If $p \in \mathrm{Mesh}_{\geq \alpha}$ and $c \in \mathbb{R}$, then
$p - c\,p' \in \mathrm{Mesh}_{\geq \alpha}$.

**Theorem 2.** Let $\alpha, \lambda > 0$ and $\beta \geq \alpha$. If
$p \in \mathrm{Mesh}_{\geq \beta}$, then the finite difference
$p(x) - \lambda\, p(x - \alpha)$ lies in $\mathrm{Mesh}_{\geq \beta}$.

**Theorem 3 (discrete Hermite–Poulain).** Let $\alpha > 0$ and let
$Q(t) = \sum_{k} a_k t^k$ be a real polynomial. The operator
$$p(x) \longmapsto \sum_k a_k\, p(x - k\alpha)$$
maps $\mathrm{Mesh}_{\geq \alpha}$ into $\mathrm{Mesh}_{\geq \alpha}$ if and only if
$Q$ is zero or has only real nonnegative zeros. Sufficiency holds for every mesh bound
$\beta \geq \alpha$, and it is deduced from Theorem 2. The necessity proof was found by
Aristotle (Harmonic).

**Theorem 5.** If $a, b \geq 0$, $p \in \mathrm{Mesh}_{\geq 1}$, and $p$ has only
nonnegative zeros, then
$$a\,p(x) + b\,x\,\bigl(p(x) - p(x - 1)\bigr)$$
lies in $\mathrm{Mesh}_{\geq 1}$ and has only nonnegative zeros.

A sequence $(a_i)$ is a *discrete multiplier sequence* if the linear operator with
$[x]_i \mapsto a_i [x]_i$ on the falling factorials $[x]_i = x(x-1)\cdots(x-i+1)$ maps every
polynomial in $\mathrm{Mesh}_{\geq 1}$ with only nonnegative zeros to such a polynomial.

**Corollary 2 (polynomial case).** If $\varphi \neq 0$ is real-rooted with only nonpositive
zeros, then $(\varphi(i))_{i \geq 0}$ is a discrete multiplier sequence. The operator is
$\varphi(x\Delta)$, a composition of the operators of Theorem 5.

**Lemma 10 (Brenti).** The linear map $x^i \mapsto [x]_i$ sends every real-rooted polynomial
with only nonnegative zeros into $\mathrm{Mesh}_{\geq 1}$, with only nonnegative zeros.

**Lemma 11 and Corollary 3.** If $p = \sum_{i \leq n} a_i [x]_i$ lies in $\mathrm{Mesh}_{\geq 1}$,
has only nonnegative zeros and $a_n > 0$, then $(-1)^{n-i} a_i \geq 0$ for all $i$. Consequently
the nonzero entries of a discrete multiplier sequence all have the same sign.

**Proposition 7.** A sequence with at most two nonzero entries is a discrete multiplier sequence
if and only if its nonzero entries sit at adjacent indices $m, m+1$ and $a_m a_{m+1} \geq 0$.

**Proposition 6.** Every discrete multiplier sequence is a multiplier sequence in the classical
sense. The converse fails: $(\rho^i)$ with $0 < \rho < 1$ is not a discrete multiplier sequence
(Remark 2).

**Proposition 12.** If $(a_i)$ is a discrete multiplier sequence and $a_{m+2} > 0$, then
$a_m \leq a_{m+1}$.

## References

Brändén, Krasikov, and Shapiro, *Elements of Pólya–Schur theory in the finite difference
setting*, Proc. Amer. Math. Soc. 144 (2016), Theorems 1, 2, 3, and 5, Lemmas 10 and 11,
Corollaries 2 and 3, Propositions 6, 7 and 12, and Remark 2. Theorem 1 is due to Riesz.
<!-- /realrooted-catalog-content -->

The definitions and theorems live in `RealRooted.Mesh.Basic`, `RealRooted.Mesh.Derivative`,
`RealRooted.Mesh.FiniteDifference`, `RealRooted.Mesh.HermitePoulain` (sufficiency in
Theorem 3), `RealRooted.Mesh.DiscreteHermitePoulain` (necessity and the equivalence),
`RealRooted.Mesh.DiscreteMultiplier` (Theorem 5), `RealRooted.Mesh.FallingFactorial` (Lemmas 10
and 11), `RealRooted.Mesh.DiscreteMultiplierSequence` (Corollaries 2 and 3, Propositions 7 and 12),
and `RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur` (Proposition 6).
-/
