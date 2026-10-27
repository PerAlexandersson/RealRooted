module

import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
import RealRooted.BorceaBranden.Applications.PoissonStarFinal
import RealRooted.BorceaBranden.Applications.PoissonStarTransport

/-!
# The univariate Poisson star product

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "univariate-poisson-star-c"
formalized = "2026-10-12"
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
headline = true

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
headline = true

[[theorems]]
name = "RealRooted.Poisson.fallingFactorialTransform_starC"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "The falling-factorial transform is multiplicative for the Poisson product"
headline = true

[[theorems]]
name = "RealRooted.Poisson.starC_assoc"
module = "RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial"
label = "Associativity of the univariate Poisson product"
headline = true
-->

<!-- realrooted-catalog-content -->
# The univariate Poisson star product

We define the symmetric product $f\star_c g$ by the finite derivative sum
$\sum_j c^jX^j f^{(j)}g^{(j)}/j!$.  It is additive in each input, compatible
with real scalar multiplication, has $1$ as a unit, and specializes at $c=0$
to ordinary multiplication.  For an affine right input $a+bX$, we prove
$f\star_c(a+bX)=af+bX(f+cf')$.  If $c\geq0$ and both inputs have nonnegative
coefficients, then so does $f\star_c g$.

For a linear fixed factor $X-r$, the affine-input test is exact:
$X-r$ maps every affine input to a split polynomial if and only if $cr\leq0$.
When $cr>0$, we prove that
$(X-r)\star_c(X-r-c)=(X-r)^2+cr$ is not split.  More generally, if a nonzero
split $f$ has $cr\leq0$ at every root $r$ of $f$, then its signed Weyl symbol
$f(z(1-cw))$ is stable.

We also prove the parameter-boundary PF results.  Multiplication by a
nonnegative constant preserves finite PF polynomials for every $c$.  For
$c<0$, a fixed left factor preserves every finite PF polynomial exactly when
it is a nonnegative constant.  At $c=0$, fixed left multiplication preserves
real-rootedness or zero exactly when its nonzero factor splits, and it
preserves finite PF polynomials exactly when that factor is PF.

For every real parameter, `preservesPF_iff` gives the complete fixed-factor
classification: PF factors when $c \geq 0$, and exactly the nonnegative
constants when $c < 0$. For a nonzero fixed factor, we identify five equivalent
conditions: preservation of all split inputs, preservation of
affine inputs, root-sign admissibility, stability of the Euler pencil, and
stability of the signed Poisson symbol. We also prove five conclusions for
every positive affine-recurrence row: Pólya frequency, simple roots, strictly
negative roots, strict interlacing with the next row, and no common roots. The
step-$c$ falling-factorial transform conjugates the Poisson product to ordinary
multiplication, proving both multiplicativity and associativity of $\star_c$.

## References

See [@Branden2006].
<!-- /realrooted-catalog-content -->
-/
