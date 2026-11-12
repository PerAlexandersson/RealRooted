module

import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
import RealRooted.BorceaBranden.Applications.PoissonStarFinal
import RealRooted.BorceaBranden.Applications.PoissonStarTransport

/-!
# Fixed-factor preservers of the univariate Poisson star product

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "univariate-poisson-star-c"
formalized = "2026-10-12"
tags = []
references = [
  "Branden2006",
]
authors = ["Brändén"]
years = [2006]

[[theorems]]
name = "RealRooted.Poisson.starC_comm"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "The univariate Poisson product is symmetric"

[[theorems]]
name = "RealRooted.Poisson.starC_affine_right"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Formula for affine right inputs"

[[theorems]]
name = "RealRooted.Poisson.starC_nonneg"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Nonnegative inputs give nonnegative coefficients"

[[theorems]]
name = "RealRooted.Poisson.preservesAffineRealRooted_linear_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Affine test for a single linear factor"

[[theorems]]
name = "RealRooted.Poisson.starC_root_obstruction_not_splits"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "A root of the wrong sign obstructs real-rootedness"

[[theorems]]
name = "RealRooted.Poisson.poissonSignedSymbol_stable"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Signed-symbol stability from the root-sign condition"

[[theorems]]
name = "RealRooted.Poisson.preservesPF_of_neg_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "PF preservers at a negative parameter"

[[theorems]]
name = "RealRooted.Poisson.preservesRealRootedOrZero_zero_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Real-rootedness preservers at parameter zero"

[[theorems]]
name = "RealRooted.Poisson.preservesPF_zero_iff"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "PF preservers at parameter zero"

[[theorems]]
name = "RealRooted.Poisson.preservesPF_iff"
module = "RealRooted.BorceaBranden.Applications.PoissonStarGeneral"
label = "Complete PF-preserver classification for every parameter"
headline = true

[[theorems]]
name = "RealRooted.Poisson.preservesRealRootedOrZero_iff_isUpperHalfPlaneStablePencil_euler"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Real-rootedness preservation is equivalent to Euler-pencil stability"

[[theorems]]
name = "RealRooted.Poisson.preservesAffineRealRooted_iff_isUpperHalfPlaneStablePencil_euler"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Affine preservation is equivalent to Euler-pencil stability"

[[theorems]]
name = "RealRooted.Poisson.isUpperHalfPlaneStablePencil_euler_iff_isAdmissible"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Euler-pencil stability is equivalent to root-sign admissibility"

[[theorems]]
name = "RealRooted.Poisson.isUpperHalfPlaneStablePencil_euler_iff_poissonSignedSymbol_stable"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFinal"
label = "Euler-pencil stability is equivalent to signed-symbol stability"

[[theorems]]
name = "RealRooted.Poisson.poisson_affine_recurrence_strict"
module = "RealRooted.BorceaBranden.Applications.PoissonStarTransport"
label = "Five-way classification for positive affine Poisson recurrences"

[[theorems]]
name = "RealRooted.Poisson.fallingFactorialTransform_starC"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "The falling-factorial transform is multiplicative for the Poisson product"

[[theorems]]
name = "RealRooted.Poisson.starC_assoc"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "Associativity of the univariate Poisson product"
-->

<!-- realrooted-catalog-content -->
# Fixed-factor preservers of the univariate Poisson star product

Multiplication by a fixed polynomial $f$ in the Poisson star product $\star_c$ preserves PF
polynomials exactly when $f$ is PF for $c\ge0$ and exactly when $f$ is a nonnegative constant
for $c<0$.

## Results

For $c\in\mathbb R$ let
$$
f\star_c g=\sum_{j\ge0}\frac{c^j}{j!}\,x^jf^{(j)}g^{(j)}.
$$
A polynomial is *PF* if it has nonnegative coefficients and is zero or has only real,
nonpositive roots. The product is symmetric, associative, bilinear, has unit $1$, and equals
the ordinary product at $c=0$.

**Theorem (basic properties).** For an affine right input,
$f\star_c(a+bx)=af+bx\,(f+cf')$. If $c\ge0$ and $f,g$ have nonnegative coefficients, so does
$f\star_cg$. Let $\Phi_c$ be the falling-factorial transform with step $c$. Then
$\Phi_c(f\star_cg)=\Phi_c(f)\,\Phi_c(g)$, and associativity of $\star_c$ follows.

**Theorem (linear factors).** The polynomial $f\star_c(a+bx)$ splits for all real $a,b$ if and
only if $f=x-r$ satisfies $cr\le0$. If $cr>0$, then $(x-r)\star_c(x-r-c)=(x-r)^2+cr$ does not
split.

**Theorem (fixed PF factors).** Let $\mathrm{Pres}_c(f)$ mean that $f\star_cg$ is PF for every
PF polynomial $g$. For every real $c$,
$$
\mathrm{Pres}_c(f)\iff\begin{cases}f\text{ is PF}&\text{if }c\ge0,\\
f=a\text{ for a constant }a\ge0&\text{if }c<0.\end{cases}
$$
For $c=0$ this shows that $f\star_0g=fg$ preserves PF polynomials exactly when $f$ is PF, and
that it maps real-rooted $g$ to zero or to a real-rooted polynomial exactly when the nonzero
factor $f$ splits.

**Theorem (equivalent conditions).** Let $f\ne0$. The following are equivalent:

1. $f\star_cg$ is zero or real-rooted for every real-rooted $g$;
2. $f\star_c(a+bx)$ splits for all real $a,b$;
3. $f$ splits and $cr\le0$ for every root $r$ of $f$;
4. the Euler pencil $x\,(f+cf')+yf$ is stable in the upper half-plane;
5. the signed Weyl symbol $f\bigl(z(1-cw)\bigr)$ is stable.

**Theorem (affine recurrences).** Let $c>0$, let $a_n,b_n>0$ for all $n$, and let $P_0=1$ and
$$
P_{n+1}=(a_n+b_nx)\,P_n+c\,b_n\,x\,P_n'.
$$
Then $P_n$ is PF with simple, strictly negative roots, $P_n\ll P_{n+1}$ in the library's
`StrictInterl` sense, and $P_n$ and $P_{n+1}$ have no common root.

## References

See [@Branden2006].
<!-- /realrooted-catalog-content -->
-/
