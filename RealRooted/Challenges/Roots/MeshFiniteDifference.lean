module

import RealRooted.Mesh.Basic
import RealRooted.Mesh.Derivative
import RealRooted.Mesh.DiscreteHermitePoulain
import RealRooted.Mesh.DiscreteMultiplier
import RealRooted.Mesh.DiscreteMultiplierSequence
import RealRooted.Mesh.DiscreteMultiplierSequenceLaguerrePolya
import RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur
import RealRooted.Mesh.FallingFactorial
import RealRooted.Mesh.FiniteDifference
import RealRooted.Mesh.FiniteDifferenceHyperbolicity
import RealRooted.Mesh.HermitePoulain

/-!
# Mesh and the discrete Hermite–Poulain theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
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
label = "Discrete Hermite–Poulain: Σ aₖ p(x − kα) preserves mesh ≥ α iff Q has only real zeros ≥ 0"
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
name = "RealRooted.fallingFactorialMap_meshGE_one"
module = "RealRooted.Mesh.FallingFactorial"
label = "Brenti: x^i ↦ [x]_i sends nonnegative zeros to mesh at least one"

[[theorems]]
name = "RealRooted.IsDiscreteMultiplierSequence.isMultiplierSequence"
module = "RealRooted.Mesh.DiscreteMultiplierSequencePolyaSchur"
label = "Discrete multiplier sequences are multiplier sequences"

[[theorems]]
name = "RealRooted.isDiscreteMultiplierSequence_of_isLaguerrePolyaTypeI"
module = "RealRooted.Mesh.DiscreteMultiplierSequenceLaguerrePolya"
label = "φ(0), φ(1), … is a discrete multiplier sequence for φ in the Laguerre–Pólya class"

[[theorems]]
name = "RealRooted.PreservesRealRootedOrZero.polyFiniteDifferenceOp_iff"
module = "RealRooted.Mesh.FiniteDifferenceHyperbolicity"
label = "p ↦ ∑ q_j(x) p(x − j) preserves real-rootedness iff at most one q_j is nonzero"


-->

<!-- realrooted-catalog-content -->
# Mesh and the discrete Hermite–Poulain theorem

The mesh of a real-rooted polynomial is the minimal distance between consecutive roots. A lower
bound on the mesh is the finite-difference analogue of real-rootedness. Brändén, Krasikov and
Shapiro prove a discrete Hermite–Poulain theorem for it and develop discrete multiplier
sequences.

## Results

We write $p\in\mathrm{Mesh}_{\ge\alpha}$ if $p$ is real-rooted and consecutive roots, listed
with multiplicity, differ by at least $\alpha\ge0$. Theorem numbers refer to Brändén, Krasikov
and Shapiro.

**Theorem (Riesz; Theorems 1 and 2).** If $p\in\mathrm{Mesh}_{\ge\beta}$, then
$p-c\,p'\in\mathrm{Mesh}_{\ge\beta}$ for real $c$, and
$p(x)-\lambda\,p(x-\alpha)\in\mathrm{Mesh}_{\ge\beta}$ for $\lambda>0$ and $0<\alpha\le\beta$.

**Theorem (discrete Hermite–Poulain; Theorem 3).** Let $\alpha>0$ and let $Q(t)=\sum_ka_kt^k$
be real. The operator $p(x)\mapsto\sum_ka_k\,p(x-k\alpha)$ maps $\mathrm{Mesh}_{\ge\alpha}$
into itself if and only if $Q$ is zero or has only real nonnegative zeros.

**Theorem 5.** If $a,b\ge0$ and $p\in\mathrm{Mesh}_{\ge1}$ has only nonnegative zeros, then so
has $a\,p(x)+b\,x\,\bigl(p(x)-p(x-1)\bigr)$.

**Lemma 8.** For real polynomials $q_0,\dots,q_k$, the operator $p\mapsto\sum_jq_j(x)\,p(x-j)$
preserves real-rootedness if and only if at most one $q_j$ is nonzero and that one is
real-rooted.

A sequence $(a_i)$ is a *discrete multiplier sequence* if the linear map $[x]_i\mapsto
a_i[x]_i$ on falling factorials $[x]_i=x(x-1)\cdots(x-i+1)$ preserves the polynomials in
$\mathrm{Mesh}_{\ge1}$ with only nonnegative zeros.

**Corollary 2.** If $\varphi$ is in the Laguerre–Pólya class with nonnegative coefficients, in
particular if $\varphi\ne0$ is real-rooted with only nonpositive zeros, then
$(\varphi(i))_{i\ge0}$ is a discrete multiplier sequence.

**Lemma 10 (Brenti).** The map $x^i\mapsto[x]_i$ sends real-rooted polynomials with only
nonnegative zeros into $\mathrm{Mesh}_{\ge1}$, with only nonnegative zeros.

**Proposition 6.** Every discrete multiplier sequence is a
[multiplier sequence](rr:multiplier-sequences). The converse fails: $(\rho^i)$ with $0<\rho<1$
is not a discrete multiplier sequence.

## Use

The mesh results transfer the Pólya–Schur theory of [multiplier sequences](rr:multiplier-sequences)
and the [Hermite–Poulain theorem](rr:hermite-poulain) from derivatives to finite differences,
which is the natural setting for polynomials in the falling-factorial basis.

## Proof

For Lemma 8 we apply the operator to $x^m$: two nonzero extreme shifts produce nonreal
[limits of zeros](rr:limits-of-zeros). Corollary 2 uses that $\mathrm{Mesh}_{\ge\alpha}$ is
closed under coefficientwise limits of bounded degree.

## References

P. Brändén, I. Krasikov and B. Shapiro, "Elements of Pólya–Schur theory in the finite
difference setting," *Proc. Amer. Math. Soc.* 144 (2016): Theorems 1, 2, 3 and 5, Lemmas 8 and
10, Corollary 2 and Proposition 6. Theorem 1 is due to Riesz.
<!-- /realrooted-catalog-content -->
-/
