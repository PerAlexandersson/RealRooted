module

import RealRooted.FiniteFreeAdditive.HalfIntegerPreservation
import RealRooted.FiniteFreeAdditive.OrderedRoots
public import RealRooted.FiniteFreeAdditive.Preservation
public import RealRooted.FiniteFreeAdditive.RootWindow
import RealRooted.FiniteFreeAdditive.Stability
public import RealRooted.FiniteFreeMultiplicative
public import RealRooted.FiniteFreeRootCount
public import RealRooted.Hadamard.Grace
import RealRooted.NarayanaTransformation.Rectangular.Preservation
public import RealRooted.WagnerX.NonnegativeRoots
public import RealRooted.FiniteFreeAdditive.HalfIntegerConvolution
public import RealRooted.NarayanaTransformation.RootGeometry

/-!
# Real-rootedness and root locations under finite free convolutions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "finite-free-convolutions"
formalized = "2026-09-11"
tags = []
references = [
  "MarcusSpielmanSrivastava2022",
  "GribinskiMarcus2022",
  "LeakeRyder2018",
]
authors = ["Marcus", "Spielman", "Srivastava", "Gribinski", "Leake", "Ryder"]
years = [2018, 2022]

[[definitions]]
name = "RealRooted.finiteFreeAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive"
label = "Finite free additive convolution"

[[definitions]]
name = "RealRooted.rectangularAdditiveConvolution"
module = "RealRooted.RectangularConvolution"
label = "Rectangular additive convolution"

[[definitions]]
name = "RealRooted.generalizedRectangularAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive.HalfIntegerConvolution"
label = "Rectangular additive convolution with a real parameter"

[[definitions]]
name = "RealRooted.finiteFreeMultiplicativeConvolution"
module = "RealRooted.FiniteFreeMultiplicative"
label = "Finite free multiplicative convolution"

[[definitions]]
name = "RealRooted.signedReciprocal"
module = "RealRooted.FiniteFreeMultiplicative"
label = "Signed reciprocal x^d p(-1/x)"

[[definitions]]
name = "RealRooted.HasOnlyNonnegRoots"
module = "RealRooted.NarayanaTransformation.RootGeometry"
label = "Zero, or real-rooted with nonnegative roots"

[[definitions]]
name = "RealRooted.rectangularPolarization"
module = "RealRooted.RectangularPolarization"
label = "Two-block polarization of y^m p(xy)"

[[definitions]]
name = "RealRooted.reciprocalRectangularPolarization"
module = "RealRooted.RectangularPolarizationComplement"
label = "Signed reciprocal of the rectangular polarization"

[[theorems]]
name = "RealRooted.splits_finiteFreeAdditiveConvolution"
module = "RealRooted.FiniteFreeAdditive.Preservation"
label = "Marcus–Spielman–Srivastava: ⊞_d preserves real-rootedness"
headline = true

[[theorems]]
name = "RealRooted.IsRealRootedIn.finiteFreeAdditiveConvolution_Icc"
module = "RealRooted.FiniteFreeAdditive.RootWindow"
label = "Walsh–Leake–Ryder: ⊞_d sends roots in [A, B] and [a, b] into [A + a, B + b]"

[[theorems]]
name = "RealRooted.orderedRoot_finiteFreeAdditiveConvolution_bounds"
module = "RealRooted.FiniteFreeAdditive.OrderedRoots"
label = "Weyl bounds: the ith root of p ⊞_d q lies between α_i + a and α_i + b"

[[theorems]]
name = "RealRooted.finiteFreeAdditiveConvolution_comp_X_add_C"
module = "RealRooted.FiniteFreeAdditive.RootWindow"
label = "Translating the arguments of ⊞_d by s and t translates the output by s + t"

[[theorems]]
name = "RealRooted.finiteFreeAdditiveConvolution_eq_lowerDegree"
module = "RealRooted.FiniteFreeAdditive.Stability"
label = "For deg f ≤ m: f ⊞_D g = f ⊞_m (m!/D!) g^(D−m)"

[[theorems]]
name = "RealRooted.algebraicSymbol_finiteFreeAdditiveConvolutionDegreeBox"
module = "RealRooted.FiniteFreeAdditive.Stability"
label = "The coordinate convolution symbol is g(x_q + y_q) times spectator factors"

[[theorems]]
name = "RealRooted.finiteFreeAdditiveConvolutionAt_realStableOrZero"
module = "RealRooted.FiniteFreeAdditive.Stability"
label = "Finite free additive convolution preserves multivariate real stability"

[[theorems]]
name = "RealRooted.interl_finiteFreeAdditiveConvolution_right"
module = "RealRooted.FiniteFreeAdditive.Stability"
label = "Convolution by a fixed monic split factor preserves directed interlacing"

[[theorems]]
name = """RealRooted.Challenges.FiniteFreeConvolutions.\
hasOnlyNonnegRoots_rectangularAdditiveConvolution"""
label = "Gribinski–Marcus: the rectangular convolution preserves nonnegative roots"

[[theorems]]
name = "RealRooted.Challenges.FiniteFreeConvolutions.splits_and_roots_nonneg_rectangular_neg_half"
label = "The parameter −1/2 preserves nonnegative roots"

[[theorems]]
name = "RealRooted.Challenges.FiniteFreeConvolutions.splits_and_roots_nonneg_rectangular_pos_half"
label = "The parameter 1/2 preserves nonnegative roots"

[[theorems]]
name = "RealRooted.splits_finiteFreeMultiplicativeConvolution"
module = "RealRooted.FiniteFreeRootCount"
label = "Marcus–Spielman–Srivastava: ⊠_d preserves real-rootedness"

[[theorems]]
name = "RealRooted.signedReciprocal_schurSzegoComp"
module = "RealRooted.FiniteFreeMultiplicative"
label = "The signed reciprocal turns Schur–Szegő composition into ⊠_d"

[[theorems]]
name = "RealRooted.coeff_rectangularAdditiveConvolution_of_le"
module = "RealRooted.RectangularConvolution"
label = "Coefficients of the rectangular additive convolution"

[[theorems]]
name = "RealRooted.natDegree_rectangularAdditiveConvolution_le"
module = "RealRooted.RectangularConvolution"
label = "The rectangular additive convolution has degree at most n"

[[theorems]]
name = "RealRooted.isMultiaffine_rectangularPolarization"
module = "RealRooted.RectangularPolarization"
label = "The rectangular polarization is multiaffine in both blocks"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_rectangularPolarization"
module = "RealRooted.RectangularPolarization"
label = "Rectangular polarization preserves upper-half-plane stability"

[[theorems]]
name = """RealRooted.\
mvUpperHalfPlaneStable_reciprocalRectangularPolarization"""
module = "RealRooted.RectangularPolarizationComplement"
label = "The signed reciprocal polarization is also stable"

[[theorems]]
name = "RealRooted.rectangularDifferential_diagonal_identity"
module = "RealRooted.RectangularConvolutionIdentity"
label = "The differential pairing of the two polarizations is the rectangular convolution"
-->

<!-- realrooted-catalog-content -->
# Real-rootedness and root locations under finite free convolutions

The finite free additive and multiplicative convolutions preserve real-rootedness, the additive
one moves roots by at most the root range of the second factor, and the rectangular additive
convolution preserves nonnegative roots.

## Results

We write $f\ll g$ if $f=0$, $g=0$ or $f$ interlaces $g$; common roots are allowed. Write
$p(x)=\sum_{i=0}^{d}a_ix^{d-i}$ and $q(x)=\sum_{j=0}^{d}b_jx^{d-j}$ in a degree box of size $d$.
The *finite free additive convolution* is
$$
(p\boxplus_dq)(x)=\sum_{k=0}^{d}x^{d-k}\sum_{i+j=k}
  \frac{(d-i)!\,(d-j)!}{d!\,(d-k)!}\,a_ib_j .
$$
The *rectangular additive convolution* $p\boxplus_{m,n}q$ in a degree box of size $n$ multiplies
each term by the further factor $\frac{(n+m-i)!\,(n+m-j)!}{(n+m)!\,(n+m-k)!}$. More generally,
for real $\alpha$ the weight of $a_ib_j$ in the box of size $n$ is
$$
\frac{(n)^{\underline{k}}}{(n)^{\underline{i}}\,(n)^{\underline{j}}}\cdot
\frac{(n+\alpha)^{\underline{k}}}{(n+\alpha)^{\underline{i}}\,(n+\alpha)^{\underline{j}}},
\qquad k=i+j,
$$
with falling factorials $(x)^{\underline{k}}$; $\alpha=m$ is the rectangular case. The
*finite free multiplicative convolution* is
$$
(p\boxtimes_dq)(x)=\sum_{k=0}^{d}(-1)^k\binom dk^{-1}a_kb_k\,x^{d-k},
$$
that is, $(-1)^d(p*_dq)(-x)$ for the Schur--Szegő composition
$p*_dq=\sum_k\binom dk^{-1}p_kq_kx^k$ of the coefficients $p_k,q_k$ of $x^k$.

**Theorem (real-rootedness).**

- If $p,q$ are real-rooted of degree at most $d$, then $p\boxplus_dq$ is real-rooted
  [@MarcusSpielmanSrivastava2022].
- If $p,q$ are real-rooted of degree at most $d$ and $q$ has only nonnegative roots, then
  $p\boxtimes_dq$ is real-rooted [@MarcusSpielmanSrivastava2022].
- The signed reciprocal $\hat p=x^dp(-1/x)$ satisfies
  $\widehat{p*_dq}=\hat p\boxtimes_d\hat q$.

**Theorem (root location).** Let $p,q$ have degree exactly $d$ and be real-rooted.

- If the roots of $p$ lie in $[A,B]$ and the roots of $q$ lie in $[a,b]$, then the roots of
  $p\boxplus_dq$ lie in $[A+a,B+b]$ (Walsh's theorem in the finite free setting; see
  [@LeakeRyder2018, Prop. 1.1]).
- If $\alpha_i$ and $\rho_i$ are the $i$th smallest roots of $p$ and of $p\boxplus_dq$, and the
  roots of $q$ lie in $[a,b]$, then $\alpha_i+a\le\rho_i\le\alpha_i+b$.
- $p(x+s)\boxplus_dq(x+t)=(p\boxplus_dq)(x+s+t)$ for all real $s,t$ and $\deg p,\deg q\le d$.

**Theorem (stability and interlacing).** Let $g\ne0$ be real-rooted with $\deg g\le D$.

- If $\deg f\le m\le D$, then $f\boxplus_Dg=f\boxplus_m\tfrac{m!}{D!}g^{(D-m)}$.
- Convolution by $g$ in a single variable $x_q$, namely
  $p\mapsto\sum_{i\le D}\frac{(D-i)!}{D!}\,[x^{D-i}]g\;\partial_q^{\,i}p$, maps multivariate
  real stable polynomials of degree at most $D$ in $x_q$ to real stable polynomials or zero.
  In the degree box $\kappa$ with $\kappa_q=D$, its algebraic symbol is
  $g(x_q+y_q)\prod_{i\ne q}(x_i+y_i)^{\kappa_i}$.
- If $g$ is monic of degree $D$, $\deg f,\deg h\le D$, both have positive leading coefficient and
  $h\ll f$ with both nonzero, then $h\boxplus_Dg\ll f\boxplus_Dg$.

**Theorem (rectangular convolution).** The polynomial $f\boxplus_{m,n}g$ has degree at most $n$.
If $f,g$ have degree exactly $n$, positive leading coefficients and only nonnegative roots, then
$f\boxplus_{m,n}g$ is zero or real-rooted with only nonnegative roots [@GribinskiMarcus2022].
The same holds for the parameters $\alpha=\pm\tfrac12$, for real-rooted $f,g$ of degree at most
$n$ with only nonnegative roots.

**Theorem (rectangular polarization).** For a complex polynomial $p$ of degree $n$ let
$$
P(x,y)=\sum_{k=0}^{n}\frac{p_k}{\binom nk\binom{m+n}{m+k}}\,
  e_k(x_1,\dots,x_n)\,e_{m+k}(y_1,\dots,y_{m+n}).
$$
Then $P$ is multiaffine and specializes to $y^mp(xy)$ when all $x_i=x$ and all $y_j=y$. If the
bivariate polynomial $p(xy)$ is upper-half-plane stable, then $P$ is upper-half-plane stable,
and so is its signed reciprocal $\tilde P$, defined by
$\tilde P(z)=(-1)^m\prod_iz_i\,P(-1/z)$. For real $f,g$, let $P_f$ be the polarization of $f$
and $\tilde P_g$ the reciprocal polarization of $g$. Applying $\tilde P_g(-\partial)$ to $P_f$
and then setting all $x_i=x$ and all $y_j=y$ gives $y^m\,(f\boxplus_{m,n}g)(xy)$.

## Proof

The additive theorem follows from the Lieb--Sokal lemma: the convolution is a differential
operator in $q$ applied to $p$. The parameters $\pm\tfrac12$ reduce to $\boxplus_{2n}$ and
$\boxplus_{2n+1}$ through the lifts $p(x^2)$ and $x\,p(x^2)$. The rectangular case uses the
polarization above [@GribinskiMarcus2022].

## References

[@MarcusSpielmanSrivastava2022; @GribinskiMarcus2022; @LeakeRyder2018]. The
[Narayana page](/RealRooted/families/narayana/) treats the Narayana transformation.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.FiniteFreeAdditive`, `RealRooted.FiniteFreeAdditive.RootWindow`,
`RealRooted.FiniteFreeAdditive.OrderedRoots`,
`RealRooted.FiniteFreeAdditive.Stability`,
`RealRooted.RectangularConvolution`,
`RealRooted.NarayanaTransformation.Rectangular` and
`RealRooted.FiniteFreeMultiplicative`.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace FiniteFreeConvolutions

/-- **Gribinski–Marcus.** The rectangular additive convolution of two
polynomials of degree `n` with positive leading coefficients and only
nonnegative roots has only nonnegative roots. -/
theorem hasOnlyNonnegRoots_rectangularAdditiveConvolution {m n : ℕ} {f g : ℝ[X]}
    (hfdeg : f.natDegree = n) (hgdeg : g.natDegree = n)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf : HasOnlyNonnegRoots f) (hg : HasOnlyNonnegRoots g) :
    HasOnlyNonnegRoots (rectangularAdditiveConvolution m n f g) :=
  rectangularAdditiveConvolutionPreservesNonnegRoots hfdeg hgdeg hf_pos hg_pos hf hg

/-- The generalized rectangular convolution with parameter `-1 / 2` preserves
real-rootedness with nonnegative roots in degree at most `n`. -/
theorem splits_and_roots_nonneg_rectangular_neg_half (n : ℕ) (p q : ℝ[X])
    (hp : p.Splits) (hq : q.Splits)
    (hproots : ∀ r ∈ p.roots, 0 ≤ r) (hqroots : ∀ r ∈ q.roots, 0 ≤ r)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n) :
    (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q).Splits ∧
      ∀ r ∈ (generalizedRectangularAdditiveConvolution (-(1 / 2 : ℝ)) n p q).roots,
        0 ≤ r :=
  splits_and_forall_roots_nonneg_generalizedRectangularAdditiveConvolution_neg_half n p q
    hp hq hproots hqroots hpdeg hqdeg

/-- The generalized rectangular convolution with parameter `1 / 2` preserves
real-rootedness with nonnegative roots in degree at most `n`. -/
theorem splits_and_roots_nonneg_rectangular_pos_half (n : ℕ) (p q : ℝ[X])
    (hp : p.Splits) (hq : q.Splits)
    (hproots : ∀ r ∈ p.roots, 0 ≤ r) (hqroots : ∀ r ∈ q.roots, 0 ≤ r)
    (hpdeg : p.natDegree ≤ n) (hqdeg : q.natDegree ≤ n) :
    (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q).Splits ∧
      ∀ r ∈ (generalizedRectangularAdditiveConvolution (1 / 2 : ℝ) n p q).roots,
        0 ≤ r :=
  splits_and_forall_roots_nonneg_generalizedRectangularAdditiveConvolution_pos_half n p q
    hp hq hproots hqroots hpdeg hqdeg

end FiniteFreeConvolutions
end Challenges
end RealRooted
