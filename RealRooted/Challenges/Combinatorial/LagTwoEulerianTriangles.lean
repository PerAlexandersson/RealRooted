module

public import RealRooted.EulerianTriangles.LagTwoTriangle

/-!
# Positive lag-two Eulerian triangles

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "lag-two-eulerian-triangles"
formalized = "2026-11-09"
tags = ["realrooted-original"]
years = [2026]

[[definitions]]
name = "RealRooted.lagTwoEulerTriangle"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "Positive lag-two Eulerian coefficient triangle"

[[definitions]]
name = "RealRooted.lagTwoEulerRow"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "Row polynomial of a positive lag-two Eulerian triangle"

[[theorems]]
name = "RealRooted.lagTwoEuler_recurrence_certificate"
module = "RealRooted.EulerianTriangles.LagTwoRecurrence"
label = "General positive lag-two Euler recurrence theorem"

[[theorems]]
name = "RealRooted.lagTwoEulerRow_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "Lag-two Eulerian rows have simple negative roots and strictly interlace"
headline = true

[[theorems]]
name = "RealRooted.a157147To151Row_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "A157147--A157151 rows have simple negative roots and strictly interlace"

[[theorems]]
name = "RealRooted.a157637Row_simpleNegRooted_and_strictInterl"
module = "RealRooted.EulerianTriangles.LagTwoTriangle"
label = "A157637 rows have simple negative roots and strictly interlace"
-->

<!-- realrooted-catalog-content -->
# Positive lag-two Eulerian triangles

**Provenance.** This proof is new, was developed for RealRooted (issue
#2506), and is of independent research interest.  It gives a simultaneous
strict-interlacing induction for a general Euler operator recurrence with a
nonnegative lag-two correction.

For positive `a_n`, `b_n \ge a_n`, and nonnegative `c_n`, the checked theorem
proves that every degree-`n` row has `n` simple strictly negative roots.  It
also proves both consecutive strict interlacing and the auxiliary comparison

$$
(\theta+1)(n-\theta)F_{n-1}\prec F_n.
$$

The specialization `a_n=1`, `b_n=m`, `c_n=m\lambda_n` covers every
`m \ge 1`, `\lambda_n\ge0`.  In particular this includes constant
`\lambda=1`, the shape represented by A157147--A157151, and
`\lambda_n=n/2`, represented by A157637.  The coefficient triangle and its
theta-form row recurrence are both checked.

The negative-sign family is deliberately excluded.  For `m=1` (A157152) it
already fails at `n=8`: the reciprocal row satisfies `P_8(-1)=-96`.  The
negative-sign cases `m\ge2` remain open.
<!-- /realrooted-catalog-content -->
-/

public section

