module

import RealRooted.Favard
public import RealRooted.Favard.Orthogonality
public import RealRooted.Favard.Recurrence
public import RealRooted.Basic.ProperPosition

/-!
# Favard recurrences: real roots, interlacing and orthogonality

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "favard"
formalized = "2026-09-07"
tags = []
references = [
  "Favard1935",
]
authors = ["Favard"]
years = [1935]

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence"
module = "RealRooted.Favard.Recurrence"
label = "Favard three-term recurrence"

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence.functional"
module = "RealRooted.Favard.Orthogonality"
label = "The normalized moment functional"

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing"
module = "RealRooted.Favard.Orthogonality"
label = "The pairing ⟨p, q⟩ = L(pq)"

[[theorems]]
name = "RealRooted.Challenges.Favard.SatisfiesFavardRecurrence.strictInterl_succ"
label = "For positive β, consecutive Favard polynomials interlace"
symcat = "favardInterlacing"

[[theorems]]
name = "RealRooted.Challenges.Favard.SatisfiesFavardRecurrence.ne_zero_and_splits"
label = "For positive β, Favard polynomials are nonzero and real-rooted"

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing_iIsOrtho"
module = "RealRooted.Favard.Orthogonality"
label = "The Favard polynomials are orthogonal for the pairing ⟨p, q⟩ = L(pq)"
headline = true

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing_posDef"
module = "RealRooted.Favard.Orthogonality"
label = "For positive β, the pairing is positive definite"

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.linearMap_eq_smul_functional"
module = "RealRooted.Favard.Orthogonality"
label = "The orthogonalizing functional is unique up to scaling"
-->

<!-- realrooted-catalog-content -->
# Favard recurrences: real roots, interlacing and orthogonality

A monic three-term recurrence with positive subdiagonal coefficients produces real-rooted
polynomials with consecutive interlacing, and orthogonal polynomials for a normalized linear
functional.

## Results

We write $f\ll g$ if $f$ interlaces $g$; common roots are allowed unless stated. Let
$P_0=1$, $P_1=x-\alpha_0$ and
$$
P_{n+2}=(x-\alpha_{n+1})P_{n+1}-\beta_{n+1}P_n .
$$

**Theorem (interlacing).** [@Favard1935] Let $\alpha_n,\beta_n$ be real and $\beta_{n+1}>0$ for
all $n$. Then every $P_n$ is nonzero and real-rooted, and $P_n\ll P_{n+1}$.

**Theorem (orthogonality).** Let $R$ be an integral domain. The monic polynomials $P_n$ form a
basis of $R[x]$. Let $L$ be the linear functional that extracts the coefficient of $P_0$ in this
basis, and let $\langle p,q\rangle=L(pq)$.

- The family is orthogonal, and $\langle P_n,P_n\rangle=\beta_1\cdots\beta_n$.
- If a linear functional $L'$ satisfies $L'(P_n)=0$ for all $n\ne0$, then $L'=L'(1)\cdot L$.
  In particular, $L$ is unique up to scaling.
- Let $R$ be an ordered ring and $\beta_{n+1}>0$ for all $n$. Then the pairing is positive
  definite: $\langle p,p\rangle>0$ for all $p\ne0$.

## References

See [@Favard1935] and the
[interlacing overview on symmetricfunctions.com](sf:favardInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
sf:favardInterlacing

Original publication: J. Favard, "Sur les polynomes de Tchebicheff",
C. R. Acad. Sci. Paris 200 (1935), 2052--2053.

This module exposes the checked root-theoretic Favard recurrence theorem. The
ring-generic normalized functional and orthogonality theory live in
`RealRooted.Favard.Orthogonality`; concrete integral realizations remain in
analytic classical-family child modules.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace Favard

/-- Favard recurrence coefficients force consecutive interlacing. -/
theorem SatisfiesFavardRecurrence.strictInterl_succ {P : ℕ → ℝ[X]} {α β : ℕ → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β) (hβ : ∀ n, 0 < β (n + 1)) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) :=
  RealRooted.favardInterlacing hrec hβ n

/-- Favard recurrence coefficients force real-rootedness of every polynomial
in the sequence. -/
theorem SatisfiesFavardRecurrence.ne_zero_and_splits {P : ℕ → ℝ[X]} {α β : ℕ → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β) (hβ : ∀ n, 0 < β (n + 1)) (n : ℕ) :
    P n ≠ 0 ∧ (P n).Splits :=
  RealRooted.isRealRooted_of_favard hrec hβ n

end Favard
end Challenges
end RealRooted
