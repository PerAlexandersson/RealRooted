module

public import RealRooted.AffineFamily
public import RealRooted.Basic.ProperPosition
public import RealRooted.Derivative.Interlacing
public import RealRooted.HlavacekSolus.Shelling
public import RealRooted.Interlacing.ConeBounds
public import RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks
public import RealRooted.ObreschkoffConverse.Derivative
public import RealRooted.ReciprocalShift.ProperPosition
public import RealRooted.Wagner.LeftSum
public import RealRooted.WagnerRightSum
public import RealRooted.WagnerX.NonnegativeRoots
public import RealRooted.WeightedSum

/-!
# Interlacing

<!-- realrooted-catalog
version = 1
kind = "method"
section = "concepts"
slug = "interlacing"
formalized = "2026-07-10"
references = [
  "Fisk2006x",
  "Wagner1992",
  "Jensen1913",
  "Branden2015",
  "BrandenLeite2024x",
  "HlavacekSolus2022",
]
authors = ["Rolle", "Jensen", "Wagner", "Fisk", "Brändén", "Saud Leite", "Hlavacek", "Solus"]
years = [1691, 1913, 1992, 2006, 2015, 2022, 2024]

[[definitions]]
name = "RealRooted.StrictInterl"
module = "RealRooted.Basic.ProperPosition"
label = "Interlacing f ≪ g of nonzero real-rooted polynomials"

[[theorems]]
name = "RealRooted.derivative_interlaces_of_natDegree_ne_zero"
module = "RealRooted.Derivative.Interlacing"
label = "Rolle: the derivative of a nonconstant real-rooted f satisfies f′ ≪ f"

[[theorems]]
name = "RealRooted.StrictInterl.derivative"
module = "RealRooted.ObreschkoffConverse.Derivative"
label = "If f ≪ g and f is nonconstant, then f′ ≪ g′"

[[theorems]]
name = "Polynomial.exists_mem_jensenDisk_of_isRoot_derivative"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks"
label = "Jensen: non-real zeros of p′ lie in the Jensen disks of p"

[[theorems]]
name = "RealRooted.StrictInterl.add_of_right_of_posLeadingCoeff"
module = "RealRooted.WagnerRightSum"
label = "Wagner: if f ≪ h and g ≪ h, then f + g ≪ h"
headline = true
symcat = "wagnerLemma"

[[theorems]]
name = "RealRooted.StrictInterl.add_of_left"
module = "RealRooted.Wagner.LeftSum"
label = "Wagner: if h ≪ f and h ≪ g, then h ≪ f + g"

[[theorems]]
name = "RealRooted.StrictInterl.weightedSum_right_of_nonneg"
module = "RealRooted.WeightedSum"
label = "A nonnegative combination of polynomials interlacing h interlaces h"

[[theorems]]
name = "RealRooted.strictInterl_iff_mul_X_of_roots_nonpos"
module = "RealRooted.WagnerX.NonnegativeRoots"
label = "With nonpositive roots, f ≪ g if and only if g ≪ x f"

[[theorems]]
name = "RealRooted.interl_weightedSum_cone"
module = "RealRooted.Interlacing.ConeBounds"
label = "Cone lemma: a nonnegative combination F of f₀ ≪ ⋯ ≪ fₙ satisfies f₀ ≪ F ≪ fₙ"

[[theorems]]
name = "RealRooted.strictInterl_of_forall_affine_mul_add_splits"
module = "RealRooted.AffineFamily"
label = "Brändén: if (sx + t) f + g is real-rooted for all s, t > 0, then f ≪ g"

[[theorems]]
name = "RealRooted.reciprocalShift_reverses_strictInterl"
module = "RealRooted.ReciprocalShift.ProperPosition"
label = "The reciprocal shift x^D p(1/x) reverses interlacing of PF polynomials"

[[theorems]]
name = "RealRooted.HlavacekSolus.isRealRooted_hPolynomial_of_perm_isInterlacingSeqNonneg"
module = "RealRooted.HlavacekSolus.Shelling"
label = "Hlavacek–Solus: interlacing relative h-polynomials give a real-rooted h-polynomial"
symcat = "shellingInterlacingCriterion"
-->

<!-- realrooted-catalog-content -->
# Interlacing

Two real-rooted polynomials interlace if their roots alternate. Interlacing is the standard
route to real-rootedness: it survives differentiation, sums with a common partner (Wagner's
lemma) and nonnegative combinations of an interlacing sequence (the cone lemma). The convention
below is used throughout the catalog; a page that departs from it says so.

## Results

Let $f$ and $g$ be nonzero real-rooted polynomials with roots $s_1\le\dotsb\le s_k$ and
$r_1\le\dotsb\le r_m$, listed with multiplicity. We say that $f$ *interlaces* $g$, and write
$f\ll g$, if either

- $m=k+1$ and $r_1\le s_1\le r_2\le s_2\le\dotsb\le s_k\le r_{k+1}$, or
- $m=k$ and $s_1\le r_1\le s_2\le r_2\le\dotsb\le s_k\le r_k$.

Thus $g$ has the largest root, $\deg g$ is $\deg f$ or $\deg f+1$, and common and repeated
roots are allowed. Some statements also allow $f=0$ or $g=0$; the zero polynomial then
interlaces every polynomial and is interlaced by every polynomial. A sequence
$f_0,f_1,\dotsc$ is *interlacing* if $f_i\ll f_j$ for all $i<j$, and a *Sturm sequence* if
$f_{i+1}\ll f_i$ and $\deg f_{i+1}=\deg f_i-1$ for every $i$. A polynomial is *PF* if it has
nonnegative coefficients and only real nonpositive roots.

**Theorem (Rolle; derivatives).** If $f$ is real-rooted of degree $d\ge1$, then $f'$ is
real-rooted of degree $d-1$ and $f'\ll f$. If $f\ll g$ and $f$ is nonconstant, then
$f'\ll g'$.

**Theorem (Jensen).** [@Jensen1913] Let $p$ be a nonconstant real polynomial. Every non-real
zero of $p'$ lies in a *Jensen disk* of $p$: the closed disk whose diameter is the segment from
a non-real zero $z$ of $p$ to $\bar z$.

**Theorem (Wagner's lemma).** [@Wagner1992] Let $f$ and $g$ have positive leading
coefficients.

1. If $f\ll h$ and $g\ll h$, then $f+g\ll h$. More generally, if $f_1,\dotsc,f_k\ll h$ have
   positive leading coefficients and $a_1,\dotsc,a_k\ge0$ are not all zero, then
   $\sum_ia_if_i\ll h$.
2. If $h\ll f$ and $h\ll g$, then $h\ll f+g$.

If all real roots of $f$ and $g$ are nonpositive, then $f\ll g$ if and only if $g\ll xf$.

**Theorem (cone lemma; Brändén and Saud Leite).** [@BrandenLeite2024x, Lemma 3.1] Let
$f_0,\dotsc,f_n$ be an interlacing sequence of nonzero real-rooted polynomials with nonnegative
coefficients, and let $\lambda_0,\dotsc,\lambda_n\ge0$. Then $F=\sum_i\lambda_if_i$ satisfies
$f_0\ll F\ll f_n$, where $F$ may be zero. In particular, if $f\ll g$ have nonnegative
coefficients and $a,b\ge0$, then $f\ll af+bg\ll g$.

**Theorem (affine combinations; Brändén).** Let $f,g\ne0$ have nonnegative coefficients. If
$(sx+t)f+g$ is real-rooted for all $s,t>0$, then $f\ll g$.

**Theorem (reciprocal shift).** For $D\ge\deg p$ let $p_D(x)=x^Dp(1/x)$. If $p\ll q$ are PF
polynomials of degree at most $D$, then $q_D\ll p_D$.

**Corollary (shellings; Hlavacek–Solus).** [@HlavacekSolus2022, Thm. 3.1] Let a shellable
simplicial complex be subdivided. If the h-polynomials of the relative pieces of the shelling,
in some order, form an interlacing sequence with nonnegative coefficients, and the h-polynomial
of the subdivision is nonzero, then this h-polynomial is real-rooted.

## Use

By the [Hermite–Kakeya–Obreschkoff theorem](rr:hermite-kakeya-obreschkoff), $f\ll g$ or
$g\ll f$ holds exactly when every real linear combination of $f$ and $g$ is real-rooted.
Interlacing sequences come from [three-term recurrences](rr:orthogonal-polynomials), from
[principal submatrices](rr:cauchy-interlacing) and from the
[Liu–Wang and Ma–Wang criteria](rr:ma-wang-liu-wang). Interlacing is preserved by
[differential operators with real-rooted symbol](rr:hermite-poulain), it can be tested with
[Wronskians and Bézout matrices](rr:bezoutian), and families with a
[common interleaver](rr:common-interleavers) have real-rooted sums.

## Proof

Rolle's theorem puts a zero of $f'$ strictly between consecutive distinct zeros of $f$, and a
zero of $f$ of multiplicity $m$ is a zero of $f'$ of multiplicity $m-1$; counting gives
$f'\ll f$. If $f\ll g$, every real combination of $f$ and $g$ is real-rooted, hence so is its
derivative, and the converse half of the Hermite–Kakeya–Obreschkoff theorem gives $f'\ll g'$.
Wagner's lemma is a sign argument: $f$ and $g$ have the same sign pattern at the roots of $h$,
so $f+g$ does too. For the reciprocal shift, inversion reverses the order of negative roots.

## References

[@Fisk2006x]; [@Wagner1992]; [@Jensen1913]; [@Branden2015, Lemma 7.8.4];
[@BrandenLeite2024x, Lemma 3.1]; [@HlavacekSolus2022, Thm. 3.1]. See also
[interlacing](sf:interlacesPolynomial), [Wagner's lemma](sf:wagnerLemma) and the
[shelling criterion](sf:shellingInterlacingCriterion) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
