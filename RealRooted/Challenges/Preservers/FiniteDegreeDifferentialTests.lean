module

import RealRooted.EvenDerivative.Basic
import RealRooted.EvenDerivative.Examples
import RealRooted.EvenDerivative.Interlacing
import RealRooted.EvenDerivative.Preserver
import RealRooted.EvenDerivative.Stability
import RealRooted.EvenDerivative.Symbol
import RealRooted.FiniteFreeAdditive.FiniteDegreeTests
import RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone

/-!
# Finite-degree tests for differential operators

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-degree-differential-tests"
formalized = "2026-11-01"
authors = []
references = [
  "BorceaBranden2009I",
]
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "The degree-N test h(D) X^N"

[[definitions]]
name = "RealRooted.PreservesOrderedPFUpTo"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "Two symbols give ordered PF images through degree N"

[[definitions]]
name = "RealRooted.HasKreinCompanionExpansion"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "A nonnegative combination of h and quotients h/(x − u)"

[[definitions]]
name = "RealRooted.evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Basic"
label = "The operator Δ_c f = ∑ cₖ xᵏ f^{(2k)}"

[[definitions]]
name = "RealRooted.evenDerivativeTest"
module = "RealRooted.EvenDerivative.Basic"
label = "The test polynomial p_N(z) = ∑ (-1)ᵏ cₖ (N)_{2k} z^{N-2k}"

[[definitions]]
name = "RealRooted.evenDerivativeSymbol"
module = "RealRooted.EvenDerivative.Symbol"
label = "The signed symbol ∑ (-1)ᵏ cₖ w^{2k}, so that p_N is the symbol applied to xᴺ"

[[theorems]]
name = "RealRooted.PreservesPFUpTo.iff_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "h(D) preserves PF polynomials of degree at most N exactly when h(D) X^N is PF"
headline = true

[[theorems]]
name = "RealRooted.finiteFreeAdditiveConvolution_finiteDifferentialTest"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "The finite free additive convolution with the test is the differential operator"

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.iff_differentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "Ordered PF images through degree N are detected by the two degree-N tests"

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.iff_jensenDifferentialTests"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "The same criterion through the reversed (Jensen) tests"

[[theorems]]
name = "RealRooted.PreservesOrderedPFUpTo.binomialDifferentialSymbol"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "Binomial symbols with Jensen tests (sX + 1)^r, (sX + 1)^(r-1): ordered PF images"

[[theorems]]
name = "RealRooted.FiniteDegreeOrdered.binomialDifferentialRecurrence_pf_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeOrderedTests"
label = "A binomial differential recurrence row is PF and preceded by the leading image"

[[theorems]]
name = "RealRooted.differentialRecurrence_pf_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeTests"
label = "An ordered PF pair of images gives a PF row X h(D)p + a k(D)p preceded by h(D)p"

[[theorems]]
name = "RealRooted.multishiftDifferentialRecurrence_pf_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "Multishift recurrence rows are PF and preceded by the full-symbol image"

[[theorems]]
name = "RealRooted.multishiftDifferentialRecurrence_induction"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "Induction along a multishift recurrence from a PF seed"

[[theorems]]
name = "RealRooted.isPFPolynomial_and_interl_iff_hasKreinCompanionExpansion"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions"
label = "For PF h ≠ 0: k is PF with k ≪ h iff k is a nonnegative sum of h and h/(x − u)"

[[theorems]]
name = "RealRooted.forall_differential_images_iff_isPFPolynomial_and_interl"
module = "RealRooted.FiniteFreeAdditive.FiniteDegreeCompanionCone"
label = "All-degree ordered PF preservation by (h, k) is equivalent to k being PF and k ≪ h"

[[theorems]]
name = "RealRooted.evenDerivative_preservesPF_tfae"
module = "RealRooted.EvenDerivative.Preserver"
label = "Δ_c preserves PF through degree N iff Δ_c(xᴺ) is real-rooted iff p_N is real-rooted"

[[theorems]]
name = "RealRooted.isPFPolynomial_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Preserver"
label = "If p_N is real-rooted, Δ_c maps PF polynomials of degree at most N to PF polynomials"

[[theorems]]
name = "RealRooted.splits_evenDerivativeOperator_prod"
module = "RealRooted.EvenDerivative.Stability"
label = "If p_n is real-rooted, Δ_c ∏ (x + rᵢ) is real-rooted for rᵢ ≥ 0"

[[theorems]]
name = "RealRooted.mvRealStable_evenDerivativePolarization"
module = "RealRooted.EvenDerivative.Stability"
label = "The polarization of p_n is real stable (Grace–Walsh–Szegő)"

[[theorems]]
name = "RealRooted.evenDerivativeOperator_X_pow_comp"
module = "RealRooted.EvenDerivative.Basic"
label = "Composition with −z²: Δ_c(xᴺ)(−z²) = (−1)ᴺ zᴺ p_N(z)"

[[theorems]]
name = "RealRooted.splits_evenDerivativeTest_of_le"
module = "RealRooted.EvenDerivative.Preserver"
label = "If p_N is real-rooted, then p_n is real-rooted for all n ≤ N"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator_X_pow_succ"
module = "RealRooted.EvenDerivative.Interlacing"
label = "Consecutive monomial images Δ_c(xᵐ) and Δ_c(xᵐ⁺¹) interlace"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Interlacing"
label = "Δ_c preserves interlacing of nonnegative-coefficient pairs through degree N"

[[theorems]]
name = "RealRooted.interl_evenDerivativeOperator"
module = "RealRooted.EvenDerivative.Interlacing"
label = "Δ_c preserves zero-aware interlacing of PF pairs through degree N"

[[theorems]]
name = "RealRooted.splits_evenDerivativeOperator_X_add_C_mul"
module = "RealRooted.EvenDerivative.Interlacing"
label = "Δ_c((x + a) h) is real-rooted for PF h and every real a"

[[theorems]]
name = "RealRooted.splits_evenDerivativeTest_of_splits_symbol"
module = "RealRooted.EvenDerivative.Symbol"
label = "Finitely supported c with a real-rooted signed symbol: p_N is real-rooted for every N"

[[theorems]]
name = "RealRooted.evenDerivativeOperator_capTwo_X_pow_four"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …): Δ_c(x⁴) = x²(x² + 12x + 24)"

[[theorems]]
name = "RealRooted.evenDerivativeOperator_capTwo_X_pow_five"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …): Δ_c(x⁵) = x³(x² + 20x + 120)"

[[theorems]]
name = "RealRooted.IsPFPolynomial.evenDerivativeCapTwo_of_natDegree_le_four"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …) the operator preserves PF polynomials through degree four"

[[theorems]]
name = "RealRooted.not_splits_evenDerivativeOperator_capTwo_X_pow_five"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 1, 1, 0, …) Δ_c(x⁵) is not real-rooted: preservation fails in degree five"

[[theorems]]
name = "RealRooted.isPFPolynomial_evenDerivativeOperator_square"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 2, 1, 0, …), f + 2x f'' + x² f^(4) preserves PF polynomials in every degree"

[[theorems]]
name = "RealRooted.strictInterl_evenDerivativeOperator_square_X_add_one_pow"
module = "RealRooted.EvenDerivative.Examples"
label = "For c = (1, 2, 1, 0, …) the images of (x + 1)³ and (x + 1)⁴ interlace"
-->

<!-- realrooted-catalog-content -->
# Finite-degree tests for differential operators

A constant-coefficient operator $h(D)$ preserves Pólya frequency polynomials of degree at most
$N$ if and only if the single polynomial $h(D)\,x^N$ is Pólya frequency. The same kind of test
holds for pairs of operators with interlacing images and for the even-derivative operators
$f\mapsto\sum_kc_kx^kf^{(2k)}$.

## Results

A polynomial is *PF* (Pólya frequency) if it is zero or has nonnegative coefficients and only
real nonpositive roots. Interlacing statements here use the
[zero-aware convention](rr:about). For a real polynomial $h=\sum_jh_jx^j$ and $D=d/dx$ let
$h(D)=\sum_jh_jD^j$. The *degree-$N$ test* of $h$ and its reversal, the *Jensen test*, are
$$
T_N(h)=h(D)\,x^N=\sum_{j\le N}\frac{N!}{(N-j)!}\,h_j\,x^{N-j},\qquad
J_N(h)=\sum_{j\le N}\frac{N!}{(N-j)!}\,h_j\,x^{j}.
$$
For $\deg p\le N$, the [finite free additive convolution](rr:finite-free-convolutions) of the
test with $p$ is $T_N(h)\boxplus_Np=h(D)p$.

**Theorem (scalar test).** $h(D)$ maps every PF polynomial of degree at most $N$ to a PF
polynomial if and only if $T_N(h)$ is PF.

**Theorem (ordered tests).** For real polynomials $h,k$ the following are equivalent.

1. For every PF polynomial $p$ of degree at most $N$, the polynomials $h(D)p$ and $k(D)p$ are
   PF and $h(D)p\ll k(D)p$.
2. $T_N(h)$ and $T_N(k)$ are PF and $T_N(h)\ll T_N(k)$.
3. $J_N(h)$ and $J_N(k)$ are PF and $J_N(k)\ll J_N(h)$.

If $h\ne0$ is PF, then (1) holds for every $N$ if and only if $k$ is PF and $k\ll h$, and this
happens exactly when $k$ is a nonnegative combination of $h$ and of the quotients $h/(x-u)$
with $h(u)=0$.

**Theorem (even derivatives).** Let $c_0=1$ and $c_k\ge0$, and put
$$
\Delta_cf=\sum_{k\ge0}c_k\,x^kf^{(2k)},\qquad
p_N(z)=\sum_{k\le N/2}(-1)^kc_k\,(N)_{2k}\,z^{N-2k},
$$
where $(N)_j=N(N-1)\cdots(N-j+1)$. The following are equivalent: $\Delta_c$ maps every PF
polynomial of degree at most $N$ to a PF polynomial; $\Delta_c(x^N)$ is real-rooted; $p_N$ is
real-rooted. If $c_k=0$ for $k>M$ and the signed symbol $\sum_{k\le M}(-1)^kc_kw^{2k}$ is
real-rooted, then this holds for every $N$.

For $c=(1,1,1,0,\dots)$ we get $\Delta_c(x^4)=x^2(x^2+12x+24)$ and
$\Delta_c(x^5)=x^3(x^2+20x+120)$, so $\Delta_c$ preserves PF polynomials up to degree four but
not five. For $c=(1,2,1,0,\dots)$ it preserves them in every degree.

The declarations below also cover binomial symbols, with $J_N(h)=(sx+1)^r$ and
$J_N(k)=(sx+1)^{r-1}$; the recurrence rows $x\,h(D)p+a\,k(D)p$ with $a\ge0$, which are PF and
interlaced by $h(D)p$, and their multishift versions; and, when $p_N$ is real-rooted,
preservation of interlacing by $\Delta_c$ through degree $N$.

## Proof

Substituting $x=-z^2$ gives $\Delta_c(x^N)(-z^2)=(-1)^Nz^Np_N(z)$, which relates the last two
conditions of the even-derivative theorem. The step from $p_N$ to all PF inputs uses the real
stability of the symmetric polarization of $p_N$ and the Grace–Walsh–Szegő theorem
[@BorceaBranden2009I, Theorem 2.3 and Proposition 2.4].

## References

- [@BorceaBranden2009I]
<!-- /realrooted-catalog-content -->
-/
