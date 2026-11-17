module

import RealRooted.CombinatorialExamples.DerangementStatistic
import RealRooted.SymmetricDecomposition.Definitions
import RealRooted.SymmetricDecomposition.DerangementTransform
import RealRooted.SymmetricDecomposition.EulerFPolynomial
import RealRooted.SymmetricDecomposition.FPolynomial
import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
import RealRooted.SymmetricDecomposition.FPolynomialSequence
import RealRooted.SymmetricDecomposition.Theorem26

/-!
# Symmetric decompositions and the f-transform (Brändén–Solus)

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "branden-solus"
formalized = "2026-10-02"
references = [
  "BrandenSolus2019",
]
authors = ["Brändén", "Solus"]
years = [2019]

[[definitions]]
name = "RealRooted.IsIdDecomposition"
module = "RealRooted.SymmetricDecomposition.Definitions"
label = "Symmetric I_d-decomposition"

[[definitions]]
name = "RealRooted.fPolynomial"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-transform f_d(h) = Σ h_k x^k (x + 1)^(d − k)"

[[definitions]]
name = "RealRooted.DerangementTransform.transform"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "Derangement transform x^j ↦ d_j"

[[theorems]]
name = "RealRooted.BrandenSolus.strictInterl_iff_of_isIdDecomposition"
module = "RealRooted.SymmetricDecomposition.Theorem26"
label = "Brändén–Solus: five interlacing conditions on p = a + xb are equivalent"
headline = true

[[theorems]]
name = "RealRooted.DerangementTransform.transform_magicExpansion_isPF"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "The derangement image of a nonnegative magic-basis combination is zero or real-rooted"

[[theorems]]
name = "RealRooted.DerangementTransform.transform_magicExpansion_strictInterl"
module = "RealRooted.SymmetricDecomposition.DerangementTransform"
label = "For d ≥ 2 and a positive coordinate, the image lies between A_d and d_d"

[[theorems]]
objects = ["Derangement polynomials"]
name = "RealRooted.DerangementStatistic.derangementExcGenPoly_isRealRooted"
module = "RealRooted.CombinatorialExamples.DerangementStatistic"
label = "The excedance polynomial of derangements is real-rooted for n ≥ 2"

[[theorems]]
name = "RealRooted.splits_fPolynomial_iff"
module = "RealRooted.SymmetricDecomposition.EulerFPolynomial"
label = "For deg p ≤ d, the f-transform f_d(p) is real-rooted exactly when p is"

[[theorems]]
name = "RealRooted.fPolynomial_derivative"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "The derivative rule (x + 1)² f_d(p)′ = d(x + 1) f_d(p) + f_d(p′)"

[[theorems]]
name = "RealRooted.eq_fPolynomial_of_derivRec"
module = "RealRooted.SymmetricDecomposition.FPolynomialRecurrence"
label = "The f-transform turns a derivative recurrence into a derivative recurrence"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_natDegree_of_roots_lt_one"
module = "RealRooted.SymmetricDecomposition.FPolynomial"
label = "The f-transform preserves interlacing of polynomials with roots below one"

[[theorems]]
name = "RealRooted.StrictInterl.fPolynomial_sequence"
module = "RealRooted.SymmetricDecomposition.FPolynomialSequence"
label = "Half-growth sequences transfer consecutive interlacing"
-->

<!-- realrooted-catalog-content -->
# Symmetric decompositions and the f-transform (Brändén–Solus)

Every polynomial of degree at most $d$ splits uniquely into two palindromic pieces. P. Brändén
and L. Solus showed that interlacing of these pieces is equivalent to interlacing of $p$ with
its reversal and to several other conditions, and they applied this to $h^*$-polynomials and to
the derangement transform.

## Results

Put $I_d(p)=x^dp(1/x)$. An *$I_d$-decomposition* of $p$ is a pair $(a,b)$ with $p=a+xb$,
$\deg a\le d$, $\deg b\le d-1$, $I_d(a)=a$ and $I_{d-1}(b)=b$. For $\deg h\le d$ the
*f-transform* is
$$
f_d(h)=\sum_{k=0}^dh_k\,x^k(x+1)^{d-k},
$$
the substitution $x\mapsto x/(x+1)$ homogenized to degree $d$. Let $R_d(p)(x)=(-1)^dp(-1-x)$.

**Theorem (Brändén–Solus).** [@BrandenSolus2019, Thm. 2.6] Let $\deg p\le d$, and let $(a,b)$
be an $I_d$-decomposition of $p$ with $a,b\ne0$ and nonnegative coefficients. Then the following
are equivalent:
$$
b\ll a,\qquad a\ll p,\qquad b\ll p,\qquad I_d(p)\ll p,\qquad R_d(f_d(p))\ll f_d(p).
$$

**Theorem (derangement transform).** [@BrandenSolus2019, Cor. 3.7] Let $d_n$ be the
derangement polynomial, counting derangements of $n$ letters by excedances, and $D$ the linear
map $x^j\mapsto d_j$. If $c_0,\dots,c_d\ge0$, then $D\bigl(\sum_kc_kx^k(1+x)^{d-k}\bigr)$ is zero
or real-rooted with nonpositive roots. If $d\ge2$ and some $c_k>0$, it lies between
$D\bigl((1+x)^d\bigr)$ and $d_d$ in the interlacing order. In particular $d_n$ is real-rooted for
$n\ge2$.

**Theorem (f-transform).** Let $\deg p\le d$.

- $f_d(p)$ is real-rooted if and only if $p$ is real-rooted.
- $(x+1)^2f_d(p)'=d\,(x+1)f_d(p)+f_d(p')$. Hence if $Q_{n+1}=a_nQ_n'+b_nQ_n$ with
  $\deg a_n\le2$, $\deg b_n\le1$ and $\deg Q_n\le n$, the rows $f_n(Q_n)$ satisfy an explicit
  recurrence of the same kind.
- If $f\ll g$ and all their roots are below $1$, then $f_{\deg f}(f)\ll f_{\deg g}(g)$.
- If $Q_j$ are nonzero real-rooted with nonnegative coefficients,
  $\deg Q_j=\lfloor(j+1)/2\rfloor$ and $Q_j\ll Q_{j+1}$, then
  $f_n(Q_n)\ll f_{n+1}(Q_{n+1})$ for $n\ge1$.

## Use

The equivalences reduce interlacing of $p$ with its reversal to the simpler pair $b\ll a$. The
f-transform carries the peak polynomials, which have the half-growth degree pattern, to the
alternating-runs polynomials, so their real-rootedness and interlacing pass over. See also the
[symmetric-decomposition overview on symmetricfunctions.com](sf:symmetricIDecomposition).

## Proof

The derangement transform is the Chow derangement transform of the Pascal matrix, so the
theorem is a case of the [Brändén–Vecchi theorem](rr:chow-polynomials). The f-transform maps a
root $r\ne1$ of $p$ to $r/(1-r)$, which gives the root and interlacing statements; the derivative
rule is a direct computation.

## References

[@BrandenSolus2019].
<!-- /realrooted-catalog-content -->
-/
