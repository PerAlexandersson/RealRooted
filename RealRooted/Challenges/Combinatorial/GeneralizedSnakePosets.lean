module

import RealRooted.GeneralizedSnakePosets.FiniteBoard
import RealRooted.GeneralizedSnakePosets.Narayana.Modified
import RealRooted.GeneralizedSnakePosets.Narayana.PFFacts
import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence
import RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing
import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.SnakeConstant
import RealRooted.GeneralizedSnakePosets.SnakeRecurrence
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence

/-!
# h*-polynomials of generalized snake posets

<!-- realrooted-catalog
version = 1
kind = "conjecture"
conjecture = "Lee–Vindas-Meléndez–Wang (2024), Conjecture 5.1(1)"
section = "families"
slug = "generalized-snake-posets"
formalized = "2026-10-05"
references = [
  "BraunJal2026x",
  "AlexanderssonJal2024x",
]
authors = ["Lee", "Vindas-Meléndez", "Wang", "Braun", "Jal", "Alexandersson"]
years = [2024, 2026]

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.generalizedSnakeBoard"
module = "RealRooted.GeneralizedSnakePosets.SnakeBoard"
label = "Board of a generalized snake poset"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.rookPolynomial"
module = "RealRooted.GeneralizedSnakePosets.FiniteBoard"
label = "Non-nesting rook polynomial of a board"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Modified"
label = "Modified Narayana polynomials Pₙ"

[[definitions]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.rookSum"
module = "RealRooted.GeneralizedSnakePosets.TruncatedStaircase.Auxiliary"
label = "Auxiliary polynomials Gₙ"

[[theorems]]
objects = ["Modified Narayana polynomials"]
property = "pf"
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial_isPFPolynomial"
module = "RealRooted.GeneralizedSnakePosets.Narayana.PFFacts"
label = "Modified Narayana polynomials are Pólya-frequency"

[[theorems]]
objects = ["Modified Narayana polynomials"]
property = "interlacing"
name = "RealRooted.GeneralizedSnakePosets.modifiedNarayanaPolynomial_strictInterl_succ"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Modified"
label = "Consecutive modified Narayana polynomials interlace"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.affineModifiedNarayanaInterlacing_modified"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Turan"
label = "Affine combinations of consecutive modified Narayana polynomials interlace"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.FiniteSkewBoard.rookPolynomial_full_eq_modifiedNarayana"
module = "RealRooted.GeneralizedSnakePosets.Narayana.Recurrence"
label = "Full truncated staircases have rook polynomial Pₙ"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.rookSum_recurrence"
module = "RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence"
label = "The auxiliary polynomials Gₙ in terms of Pₙ"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.rookSum_strictInterl_modifiedNarayana"
module = "RealRooted.GeneralizedSnakePosets.Narayana.ShiftedDifferenceInterlacing"
label = "The auxiliary polynomial Gₙ interlaces Pₙ"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.generalizedSnakeRookModel_snakePolynomial_of_isConstant"
module = "RealRooted.GeneralizedSnakePosets.SnakeConstant"
label = "Constant words give modified Narayana polynomials"

[[theorems]]
name = "RealRooted.GeneralizedSnakePosets.rookPolynomial_recurrence"
module = "RealRooted.GeneralizedSnakePosets.SnakeRecurrence"
label = "Recurrence for the snake polynomials"

[[theorems]]
objects = ["Rook polynomials of generalized snake posets"]
property = "interlacing"
name = "RealRooted.GeneralizedSnakePosets.rookPolynomial_splits_and_interlaces"
module = "RealRooted.GeneralizedSnakePosets.SnakeRecurrence"
label = "Braun–Jal: h*-polynomials of generalized snake posets are real-rooted and interlace"
headline = true
-->

<!-- realrooted-catalog-content -->
# h*-polynomials of generalized snake posets

Lee, Vindas-Meléndez and Wang conjectured that the order polytope of a generalized snake poset
has a real-rooted $h^*$-polynomial. Braun and Jal proved this, and that deleting the last letter
of the defining word gives an interlacing polynomial.

## Results

A *generalized snake poset* $P(w)$ is a width-two poset built from a word $w$ in the letters $L$
and $R$. Under the Alexandersson–Jal correspondence between naturally labeled width-two posets
and skew shapes [@AlexanderssonJal2024x], the $h^*$-polynomial of the order polytope of $P(w)$
is the non-nesting rook polynomial
$$
M_w(x)=\sum_P x^{|P|}
$$
of a board determined by $w$. Here $P$ runs over the sets of cells with no two in a row and with
columns strictly decreasing as rows increase.

**Theorem (Braun–Jal).** [@BraunJal2026x, Thm. 4.1] If $w$ is nonempty, then $M_w$ is nonzero
and real-rooted, and $M_{w'}\ll M_w$, where $w'$ is $w$ with its last letter deleted.

This proves Conjecture 5.1(1) of E. Lee, A. R. Vindas-Meléndez and Z. Wang, "Generalized snake
posets, order polytopes, and lattice-point enumeration," arXiv:2411.18695 (2024).

## Proof

Let $N_n(x)=\sum_k\frac1n\binom nk\binom n{k-1}x^k$ be the Narayana polynomials and
$P_n=x^{-1}N_{n+1}$. Then $P_n$ is the rook polynomial of the full truncated staircase board of
size $n$, and $M_w=P_{|w|+1}$ for a constant word $w$. In general, let $k$ be the last position
(counting from $0$) where $w$ differs from its final letter, and $s=|w|-k-1$. Then
$$
M_w=M_{w[:k+1]}\,P_s+x\,M_{w[:k]}\,G_s,
$$
where $w[:j]$ is the prefix of length $j$ and $x\,G_{n-1}=P_n-(1+x)P_{n-1}$. The theorem follows
by induction along this recurrence from three facts: each $P_n$ is a Pólya frequency polynomial
with $P_n\ll P_{n+1}$; $G_n\ll P_n$, and $G_n-G_{n-1}$ has nonnegative coefficients; and
$(\lambda x+\nu)P_{m-1}+P_m\ll(\lambda x+\nu)P_m+P_{m+1}$ for $m\ge2$, $\lambda\ge0$ and
$\nu\ge-1$.

## References

[@BraunJal2026x, Thm. 4.1]; [@AlexanderssonJal2024x]; E. Lee, A. R. Vindas-Meléndez and
Z. Wang, arXiv:2411.18695 (2024), Conj. 5.1. See also
[rook matroid polynomials](sf:rookMatroidPolynomials) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
