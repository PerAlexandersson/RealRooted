module

import RealRooted.EulerOperator.OrbitPerturbationCayley
import RealRooted.EulerOperator.OrbitPerturbationFamily

/-!
# Monomial perturbations of the centered Euler orbit

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "centered-euler-orbit-perturbation"
formalized = "2026-11-10"
tags = ["realrooted-original"]
references = [
  "MaWang2008",
]

[[definitions]]
name = "RealRooted.centeredEulerOrbit"
module = "RealRooted.EulerOperator.OrbitPerturbation"
label = "Centered Euler orbit"

[[definitions]]
name = "RealRooted.orbitPerturbationRow"
module = "RealRooted.EulerOperator.OrbitPerturbationFamily"
label = "Perturbed orbit rows in the variable u"

[[theorems]]
name = "Polynomial.sq_mul_one_sub_sq_le_of_abs_eval_critical"
module = "RealRooted.Mathlib.Analysis.Polynomial.InverseBernstein"
label = "Inverse Bernstein inequality"

[[theorems]]
name = "RealRooted.centeredEulerOrbit_critical_values"
module = "RealRooted.EulerOperator.OrbitPerturbation"
label = "Critical values of the centered Euler orbit are at least one"

[[theorems]]
name = "RealRooted.centeredEulerOrbit_add_monomial"
module = "RealRooted.EulerOperator.OrbitPerturbationInterlacing"
label = "Monomial perturbations of the orbit interlace strictly"

[[theorems]]
name = "RealRooted.strictInterl_of_orbitPerturbation_recurrence"
module = "RealRooted.EulerOperator.OrbitPerturbationFamily"
label = "A three-term θ-recurrence family has interlacing rows"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_C_mul_add_C_mul_one_add_X_pow_of_recurrence"
module = "RealRooted.EulerOperator.OrbitPerturbationCayley"
label = "Eulerian form: perturbed Eulerian-type rows interlace strictly"

[[theorems]]
name = "RealRooted.strictInterl_C_mul_generalizedEulerian_add"
module = "RealRooted.EulerOperator.OrbitPerturbationCayley"
label = "Perturbed generalized Eulerian polynomials interlace strictly"

[[theorems]]
name = "RealRooted.strictInterl_cayleyTransform_succ_of_roots_mem_Icc"
module = "RealRooted.PolynomialValueEulerNumerator.Interlacing"
label = "The Cayley transform preserves degree-raising interlacing on [-1, 0]"
-->

<!-- realrooted-catalog-content -->
# Monomial perturbations of the centered Euler orbit

Let $s\ge1$ and $\kappa\ge s+4$.  Let $Q_0=1$, $Q_1=1+2u$,
$Q_2=1+\kappa u+\kappa u^2$ and, for $n\ge3$, with $\theta=u\,\frac{d}{du}$,

$$
(n-2)Q_n=\bigl((2n-3)(2u+1)+(n-2)s(u+1)\theta\bigr)Q_{n-1}
  -(n-1)(2u+1)\bigl((2u+1)+s(u+1)\theta\bigr)Q_{n-2}.
$$

Then every $Q_n$ has simple roots in $(-1,0)$, and $Q_n$ strictly
interlaces $Q_{n+1}$.  The theorem accepts any sequence with these seeds and
this recurrence.

**Proof idea.**  With $x=2u+1$, $\alpha=s/2$ and $r=(\kappa-4)/(2s)\ge1/2$,
we have $Q_n=r\,p_n(x)+(1-r)x^n$, where $p_0=1$ and
$p_{n+1}=x\,p_n+\alpha(x^2-1)p_n'$.  The polynomials $p_n$ have simple roots
in $(-1,1)$ with $p_n(\pm1)=(\pm1)^n$.  For $n\ge5$ every critical value
satisfies $|p_n(c)|\ge1$.  This holds for $p_5$ by explicit evaluation, and it
propagates from $p_n$ to $p_{n+1}$ through an inverse Bernstein inequality
$(1-x^2)p_n'(x)^2\ge n^2(1-p_n(x)^2)$ on $[-1,1]$.  We prove that inequality
by comparing $p_n(\cos t)$ with a harmonic $a\cos(n(t-\varphi))$, following
Erdélyi, Hardin and Saff
([arXiv:1307.4056](https://arxiv.org/abs/1307.4056)).  Degrees at most four
are checked directly.  So $h_n=p_n+bx^n$ with $-1<b\le1$ changes sign like
$p_n$ at the critical points of $p_n$.  The identity
$h_{n+1}=x\,h_n+\alpha(x^2-1)p_n'$ then gives $h_n\ll h_{n+1}$ by the
root-sign criterion of Ma and Wang [@MaWang2008, Thm. 2].

**Provenance.** The proof is new, developed for RealRooted (issue #2513),
and is of independent research interest.

**Eulerian form.**  The Cayley transform
$T_nf=(1-x)^nf\bigl(x/(1-x)\bigr)$ maps $Q_n$ to $c\,E_n+(1-c)(1+x)^n$,
where $c=r$, $E_0=1$ and
$E_{n+1}=\bigl(1+(1+sn)x\bigr)E_n+s\,x(1-x)E_n'$.  These are the
generalized Eulerian polynomials; for $s=1$ the $E_n$ are the Eulerian
polynomials.  So for $s\ge1$ and $c\ge1/2$ the rows
$A_n=c\,E_n+(1-c)(1+x)^n$ are real-rooted and $A_n$ strictly interlaces
$A_{n+1}$, because the Cayley transform preserves interlacing of polynomials
with roots in $[-1,0]$.

**Applications.**  The parameters $s=1$ with $c=1/2$, $2$, $3$, $7$ and
$s=2$ with $c=1/2$ give the OEIS triangles A141689, A141690, A141696, A141697
and A147565.

## References

The inverse Bernstein inequality follows T. Erdélyi, D. P. Hardin and
E. B. Saff, *Inverse Bernstein inequalities and min-max-min problems on the
unit circle*, Mathematika 61, 581–590.  See [@MaWang2008] for the
root-sign criterion.  The theorem was developed for
[RealRooted issue #2513](https://github.com/PerAlexandersson/RealRooted/issues/2513).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.EulerOperator.OrbitPerturbation`,
`RealRooted.EulerOperator.OrbitPerturbationInterlacing`,
`RealRooted.EulerOperator.OrbitPerturbationFamily` and
`RealRooted.EulerOperator.OrbitPerturbationCayley`.
-/
