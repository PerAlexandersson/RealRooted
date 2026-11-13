module

public import RealRooted.AllCombo
public import RealRooted.HermiteBiehler.StablePencil
public import RealRooted.ObreschkoffConverse.DegreeGap
public import RealRooted.ObreschkoffConverse.Forward
public import RealRooted.OperatorPreservesInterlacing

/-!
# Obreschkoff’s theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "obreschkoff"
formalized = "2026-07-10"
tags = []
references = [
  "Dedieu1992",
  "Obreschkoff1963",
]
authors = ["Obreschkoff", "Dedieu"]
years = [1963, 1992]

[[definitions]]
name = "RealRooted.AllComboRealRooted"
module = "RealRooted.AllCombo"
label = "Every real combination is real-rooted or zero"

[[theorems]]
name = "RealRooted.allComboRealRooted_of_strictInterl"
module = "RealRooted.ObreschkoffConverse.Forward"
label = "Interlacing gives a real-rooted pencil"

[[theorems]]
name = "RealRooted.interl_or_reverse_of_allComboRealRooted"
module = "RealRooted.OperatorPreservesInterlacing"
label = "A real-rooted pencil gives interlacing"

[[theorems]]
name = "RealRooted.allComboRealRooted_iff_interl_or_reverse"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Obreschkoff’s theorem as an equivalence"
headline = true
symcat = "obreschkoffDedieu"

[[theorems]]
name = "RealRooted.natDegree_close_of_allComboRealRooted"
module = "RealRooted.ObreschkoffConverse.DegreeGap"
label = "A real-rooted pencil of nonzero polynomials has degrees differing by at most one"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_bivariatePencil_iff_strictInterl"
module = "RealRooted.HermiteBiehler.StablePencil"
label = "Interlacing as stability of the bivariate pencil f(z) + w g(z)"
-->

<!-- realrooted-catalog-content -->
# Obreschkoff’s theorem

Two real-rooted polynomials interlace in one of the two orientations if and only if every real
linear combination of them is real-rooted.

## Results

A polynomial is *real-rooted* if it splits over $\mathbb R$; the zero polynomial counts as
real-rooted in this statement.

**Theorem (Obreschkoff).** [@Obreschkoff1963; @Dedieu1992] Let $f$ and $g$ be real polynomials.

- If $f\ll g$, then $\alpha f+\beta g$ is real-rooted or zero for all real $\alpha,\beta$.
- Conversely, if $\alpha f+\beta g$ is real-rooted for all real $\alpha,\beta$, then $f\ll g$ or
  $g\ll f$, where either polynomial may be zero.

Hence for real-rooted $f$ and $g$, every real linear combination is real-rooted if and only if
$f\ll g$ or $g\ll f$.

**Proposition (degrees).** If $f,g\ne0$ and every real combination of $f$ and $g$ is
real-rooted, then $|\deg f-\deg g|\le1$.

**Theorem (stable pencil).** Let $f\ne0$ and $g\ne0$ have nonnegative coefficients, with $f$
nonconstant. Then $f(z)+w\,g(z)$ has no zero with $z$ and $w$ both in the open upper half-plane
if and only if $g\ll f$, that is, $f$ has the largest root.

## Proof

One direction of the stable-pencil theorem specializes to $w=i$ and uses the Hermite–Biehler
theorem.

## References

[@Obreschkoff1963; @Dedieu1992]; see also the
[contextual statement on symmetricfunctions.com](sf:obreschkoffDedieu).
<!-- /realrooted-catalog-content -->

Human statement:
sf:obreschkoffDedieu

Original references include N. Obreschkoff, *Verteilung und Berechnung der
Nullstellen reeller Polynome* (1963), and J.-P. Dedieu, "Obreschkoff's theorem
revisited: what convex sets are contained in the set of hyperbolic polynomials?",
J. Pure Appl. Algebra 81 (1992), 269--278.

This module exposes the checked forward and converse Obreschkoff directions
and their combination as an equivalence. The continuity and common-root
analysis remains in `RealRooted.ObreschkoffConverse`.
-/
