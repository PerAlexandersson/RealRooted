module

public import RealRooted.Hermite.Poulain
public import RealRooted.Hermite.PoulainInterlacing
public import RealRooted.Hermite.PoulainSymbolInterlacing

/-!
# Hermite–Poulain theorem

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hermite-poulain"
formalized = "2026-07-18"
references = []
tags = []
authors = ["Hermite", "Poulain"]

[[definitions]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator"
module = "RealRooted.Hermite.Poulain"
label = "The operator f(D)"

[[theorems]]
name = "RealRooted.HermitePoulain.applyAsDifferentialOperator_eq_zero_or_splits"
module = "RealRooted.Hermite.Poulain"
label = "Hermite–Poulain theorem"
headline = true
symcat = "hermitePoulainTheorem"

[[theorems]]
name = "RealRooted.HermitePoulain.interl_or_interl_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainInterlacing"
label = "Hermite–Poulain operators preserve interlacing"

[[theorems]]
name = "RealRooted.HermitePoulain.eq_zero_pair_or_stablePencil_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainSymbolInterlacing"
label = "Interlacing symbols reverse proper position"

[[theorems]]
name = "RealRooted.HermitePoulain.exists_listAlternates_applyAsDifferentialOperator"
module = "RealRooted.Hermite.PoulainSymbolInterlacing"
label = "Degree and root order for positive-coefficient symbols"
-->

<!-- realrooted-catalog-content -->
# Hermite–Poulain theorem

A constant-coefficient differential operator $f(D)$ with real-rooted symbol $f$ maps real-rooted
polynomials to zero or real-rooted polynomials, and preserves interlacing.

## Results

We write $g\ll h$ if $g$ interlaces $h$; repeated and common roots are allowed unless stated.
For $f(x)=\sum_ka_kx^k$ let $f(D)=\sum_ka_kD^k$ with $D=d/dx$.

**Theorem (Hermite–Poulain).** If $f$ and $p$ are nonzero and real-rooted, then $f(D)\,p$ is
zero or real-rooted.

**Corollary (interlacing).** Let $f$ be nonzero and real-rooted and let $g\ll h$. Then
$f(D)g\ll f(D)h$ or $f(D)h\ll f(D)g$, where we regard $0$ as interlacing every polynomial.

**Theorem (interlacing symbols).** Let $T$ be real-rooted, and suppose the pencil
$Q(x)+yP(x)$ is real stable. Then either both images vanish or
$Q(D)T-yP(D)T$ is real stable, equivalently $P(D)T+yQ(D)T$ is real stable.
Thus the signed proper-position orientation reverses. No coefficient-sign
condition on $P$, $Q$, or $T$ is needed.

If $P\ll Q$ have positive coefficients and $T\ne0$, both images have degree
$d=\deg T$. Their roots, listed increasingly with multiplicities, satisfy
$\widetilde q_1\le\widetilde p_1\le\cdots\le\widetilde q_d\le\widetilde p_d$,
where $\widetilde q_i$ are the roots of $Q(D)T$. Positive leading and constant
coefficients of the symbols already suffice for this conclusion.

## References

The theorem goes back to Hermite and Poulain; see the
[Hermite–Poulain theorem on symmetricfunctions.com](sf:hermitePoulainTheorem)
for further references, and the
[interlacing consequence](sf:hermitePoulainInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
sf:hermitePoulainTheorem

Original references include C. Hermite, G. Polya--I. Schur, N. Obreschkoff,
and B. Ya. Levin's account of entire functions.

The proof is in `RealRooted.Hermite.Poulain`; the interlacing consequences are in
`RealRooted.Hermite.PoulainInterlacing` and `RealRooted.Hermite.PoulainSymbolInterlacing`.
-/

public section

namespace RealRooted.Challenges.HermitePoulain

export RealRooted.HermitePoulain (applyAsDifferentialOperator)

end RealRooted.Challenges.HermitePoulain

@[deprecated (since := "2026-11-12")]
alias RealRooted.Challenges.HermitePoulain.differential_operator_preserves_real_rooted :=
  RealRooted.HermitePoulain.applyAsDifferentialOperator_eq_zero_or_splits
