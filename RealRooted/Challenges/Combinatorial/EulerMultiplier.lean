module

import RealRooted.EulerOperator.EulerMultiplier

/-!
# Euler multipliers of Eulerian Sturm sequences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "euler-multipliers"
formalized = "2026-11-10"
tags = ["realrooted-original"]
references = [
  "LiuWang2007",
  "MaWang2008",
]

[[definitions]]
name = "RealRooted.scaledEulerInsertionStep"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Scaled Euler insertion operator"

[[definitions]]
name = "RealRooted.eulerMultiplierSource"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Canonical scaled Euler insertion sequence"

[[theorems]]
name = "RealRooted.scaledEulerInsertion_simpleNegRooted"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Scaled Euler insertion rows have simple negative roots"

[[theorems]]
name = "RealRooted.eulerMultiplier_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Positive Euler multipliers form a strictly interlacing sequence"

[[theorems]]
name = "RealRooted.eulerMultiplier_lagTwo"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "Euler multipliers satisfy an explicit lag-two recurrence"

[[theorems]]
name = "RealRooted.eq_C_mul_eulerShift_of_eulerMultiplier_lagTwo"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "The two seeds and lag-two recurrence characterize the multiplier sequence"

[[theorems]]
name = "RealRooted.eulerMultiplier_lagTwo_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerOperator.EulerMultiplier"
label = "The lag-two recurrence has simple negative roots and strict interlacing"
headline = true
-->

<!-- realrooted-catalog-content -->
# Euler multipliers of Eulerian Sturm sequences

Let $\sigma>0$, let $\gamma_n>0$, and suppose
$\gamma_n(n-1)<\beta_n$ for $n\ge1$.  Starting with $F_0=1$, set

$$
F_n=\bigl(\sigma\gamma_n+\beta_nx+
  \gamma_n(1-x)\theta\bigr)F_{n-1},
\qquad \theta=x\frac{d}{dx},
$$

and $H_n=(\theta+\sigma)F_n$.  The main entry point accepts any sequence
$G_n$ satisfying the two Euler-multiplier seeds and the explicit lag-two
recurrence.  If its common scale is positive, it proves directly that every
$G_n$ has degree $n$ and only simple negative roots, and that
$G_n\ll G_{n+1}$.  The canonical source sequence above and the identity
$G_n=c(\theta+\sigma)F_n$ establish this result without source hypotheses
in the theorem interface.

**Provenance.** The proof is new, developed for RealRooted (issue #2512),
and is of independent research interest.  The critical root-sign criteria
used in the formalization are classical results of Liu--Wang and Ma--Wang
[@LiuWang2007, Thm. 2.1; @MaWang2008, Thm. 2].

For the ordinary Eulerian polynomials $A_n$, taking
$\sigma=\gamma_n=1$ and $\beta_n=n$ gives
$(\theta+1)A_n$.  After the corresponding index shifts and Möbius changes,
this supplies the Eulerian-polynomial applications A065826 and A348576.

## References

See [@LiuWang2007] and [@MaWang2008] for the classical interlacing
criteria.  The Euler-multiplier theorem and its applications were developed
for [RealRooted issue #2512](https://github.com/PerAlexandersson/RealRooted/issues/2512).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proof lives in
`RealRooted.EulerOperator.EulerMultiplier`.
-/
