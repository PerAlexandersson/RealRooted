import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar

/-!
# The univariate Poisson star product

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "univariate-poisson-star-c"
formalized = "2026-10-11"
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
name = "RealRooted.Poisson.starC_root_obstruction_not_splits"
module = "RealRooted.BorceaBranden.Applications.UnivariatePoissonStar"
label = "Forbidden root signs give a nonsplit quadratic"

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

We do not formalize the proposed general-factor equivalences for
real-rootedness preservation, positive-parameter PF sufficiency, directed
proper-position transport, or the falling-factorial-transform consumer.

## References

P. Brändén, “On linear transformations preserving the Pólya Frequency
property,” *Transactions of the American Mathematical Society* 358 (2006),
no. 8, 3697–3716, [arXiv:math/0403364](https://arxiv.org/abs/math/0403364).
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.UnivariatePoissonStar

end RealRooted.Challenges.UnivariatePoissonStar
