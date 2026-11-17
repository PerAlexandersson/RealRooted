module

public import RealRooted.AllCombo
public import RealRooted.BorceaBranden.MultivariateHKO
public import RealRooted.BorceaBranden.RealHKOConverse
public import RealRooted.HermiteBiehler.StablePencil
public import RealRooted.ObreschkoffConverse.DegreeGap
public import RealRooted.ObreschkoffConverse.Forward
public import RealRooted.OperatorPreservesInterlacing

/-!
# Hermite–Kakeya–Obreschkoff theorem

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "hermite-kakeya-obreschkoff"
formalized = "2026-07-10"
references = [
  "Obreschkoff1963",
  "Dedieu1992",
  "BorceaBranden2009I",
  "BorceaBranden2010",
]
authors = ["Hermite", "Kakeya", "Obreschkoff", "Dedieu", "Borcea", "Brändén"]
years = [1963, 1992, 2009, 2010]

[[definitions]]
name = "RealRooted.AllComboRealRooted"
module = "RealRooted.AllCombo"
label = "Every real combination of f and g is real-rooted or zero"

[[definitions]]
name = "RealRooted.MvProperPosition"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Proper position F ≪ G: G + iF is stable"

[[theorems]]
name = "RealRooted.allComboRealRooted_iff_interl_or_reverse"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Every real combination of f and g is real-rooted iff f ≪ g or g ≪ f"
headline = true
symcat = "obreschkoffDedieu"

[[theorems]]
name = "RealRooted.allComboRealRooted_of_strictInterl"
module = "RealRooted.ObreschkoffConverse.Forward"
label = "If f ≪ g, every real combination of f and g is real-rooted or zero"

[[theorems]]
name = "RealRooted.interl_or_reverse_of_allComboRealRooted"
module = "RealRooted.OperatorPreservesInterlacing"
label = "If every real combination is real-rooted or zero, then f ≪ g or g ≪ f"

[[theorems]]
name = "RealRooted.natDegree_close_of_allComboRealRooted"
module = "RealRooted.ObreschkoffConverse.DegreeGap"
label = "A real-rooted pencil of nonzero polynomials has degrees differing by at most one"

[[theorems]]
name = "RealRooted.mvUpperHalfPlaneStable_bivariatePencil_iff_strictInterl"
module = "RealRooted.HermiteBiehler.StablePencil"
label = "With nonnegative coefficients, f(z) + w g(z) is stable iff g ≪ f"

[[theorems]]
name = "RealRooted.MvProperPosition.allComboMvRealStableOrZero"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Borcea–Brändén: proper position makes every real combination real stable or zero"

[[theorems]]
name = "RealRooted.AllComboMvRealStableOrZero.eq_zero_or_properPosition"
module = "RealRooted.BorceaBranden.RealHKOConverse"
label = "Borcea–Brändén: a real stable real span gives proper position in one order"

[[theorems]]
name = "RealRooted.mvProperPosition_iff_mvStablePencil"
module = "RealRooted.BorceaBranden.MultivariateHKO"
label = "Proper position F ≪ G iff the pencil G + wF is real stable"
-->

<!-- realrooted-catalog-content -->
# Hermite–Kakeya–Obreschkoff theorem

Two real polynomials interlace, in one of the two orders, exactly when every real linear
combination of them is real-rooted. Borcea and Brändén extended the theorem to several
variables, where interlacing becomes proper position and real-rootedness becomes real
stability.

## Results

In this statement the zero polynomial counts as real-rooted, and $f\ll g$ allows $f=0$ or
$g=0$.

**Theorem (Hermite–Kakeya–Obreschkoff).** [@Obreschkoff1963; @Dedieu1992] Let $f$ and $g$ be
real polynomials. If $f\ll g$, then $\alpha f+\beta g$ is real-rooted for all real
$\alpha,\beta$. Conversely, if $\alpha f+\beta g$ is real-rooted for all real $\alpha,\beta$,
then $f\ll g$ or $g\ll f$, and if moreover $f,g\ne0$, then $|\deg f-\deg g|\le1$.

**Theorem (stable pencil).** Let $f,g\ne0$ have nonnegative coefficients, with $f$ nonconstant.
Then $f(z)+w\,g(z)$ has no zero with $z$ and $w$ both in the open upper half-plane if and only
if $g\ll f$.

A polynomial $P\in\mathbb C[z_i:i\in\sigma]$ is *stable* if $P(z)\ne0$ whenever every $z_i$ lies
in the open upper half-plane, and *real stable* if moreover its coefficients are real. Real
polynomials $F$ and $G$ are in *proper position*, $F\ll G$, if $G+iF$ is stable.

**Theorem (Borcea–Brändén).** [@BorceaBranden2009I, Lemma 1.8 and Thm. 1.9] Let
$F,G\in\mathbb R[z_i:i\in\sigma]$.

1. If $\sigma$ is finite and $F\ll G$, then $\alpha F+\beta G$ is zero or real stable for all
   real $\alpha,\beta$.
2. If $\alpha F+\beta G$ is zero or real stable for all real $\alpha,\beta$, then $F=G=0$,
   $F\ll G$ or $G\ll F$.
3. $F\ll G$ if and only if $G+wF$, in the variables $z_i$ and a new variable $w$, is real
   stable.

Through the [Hermite–Biehler theorem](rr:hermite-biehler-hurwitz), proper position is the
multivariate counterpart of interlacing.

## Use

The theorem turns interlacing into a statement about a pencil, so it is the usual way to show
that a linear operator preserves interlacing: if it preserves real-rootedness, it maps the
pencil of $f$ and $g$ to the pencil of their images. Its multivariate form is the basis of the
[Borcea–Brändén classification](rr:borcea-branden-classification) of stability preservers.

## Proof

One direction of the stable pencil theorem specializes to $w=i$ and uses the Hermite–Biehler
theorem. For the multivariate converse, if neither $G=0$ nor $F=cG$, the quotient $F/G$ takes no
real value on the product of upper half-planes, because $F-cG$ is real stable. This set is
connected, so $\operatorname{Im}(F/G)$ has constant sign, and the sign decides between
$F\ll G$ and $G\ll F$.

## References

[@Obreschkoff1963]; [@Dedieu1992]; [@BorceaBranden2009I, Lemma 1.8 and Thm. 1.9];
[@BorceaBranden2010]. See also the
[Obreschkoff–Dedieu theorem](sf:obreschkoffDedieu) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
