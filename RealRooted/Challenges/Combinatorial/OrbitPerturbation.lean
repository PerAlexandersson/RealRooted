module

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

**Applications.**  After the Eulerian Möbius substitution, the parameters
$(s,\kappa)=(1,5)$, $(1,8)$, $(1,10)$, $(1,18)$ and $(2,6)$ give the OEIS
triangles A141689, A141690, A141696, A141697 and A147565.

## References

The inverse Bernstein inequality follows T. Erdélyi, D. P. Hardin and
E. B. Saff, *Inverse Bernstein inequalities and min-max-min problems on the
unit circle*, Mathematika 61, 581–590.  See [@MaWang2008] for the
root-sign criterion.  The theorem was developed for
[RealRooted issue #2513](https://github.com/PerAlexandersson/RealRooted/issues/2513).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.EulerOperator.OrbitPerturbation`,
`RealRooted.EulerOperator.OrbitPerturbationInterlacing` and
`RealRooted.EulerOperator.OrbitPerturbationFamily`.
-/
