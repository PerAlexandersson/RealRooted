module

import RealRooted.AffineDerivative
public import RealRooted.AffineFamily
public import RealRooted.FolkloreLemma
public import RealRooted.HlavacekSolus.Shelling
import RealRooted.HlavacekSolus.PolytopalShelling
import RealRooted.HlavacekSolus.HalfOpenCube
import RealRooted.HlavacekSolus.CubicalShelling
public import RealRooted.Interlacing.ConeBounds
public import RealRooted.ShiftLemma
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition

/-!
# Closure of interlacing under cones, affine combinations and shifts

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "interlacing-closure"
formalized = "2026-10-06"
tags = []
references = [
  "Fisk2006x",
  "Branden2015",
  "BrandenLeite2024x",
]
authors = ["Fisk", "Brändén", "Saud Leite", "Hlavacek", "Solus"]
years = [2006, 2015, 2021, 2024]

[[theorems]]
name = "RealRooted.strictInterl_of_forall_affine_mul_add_splits"
module = "RealRooted.AffineFamily"
label = "Brändén: real-rooted affine combinations force interlacing"

[[theorems]]
name = "RealRooted.interl_weightedSum_cone"
module = "RealRooted.Interlacing.ConeBounds"
label = "A nonnegative combination of an interlacing sequence lies between its ends"
headline = true

[[theorems]]
name = "RealRooted.Challenges.InterlacingClosure.strictInterl_affine_derivative"
label = "c f + (1 − x) f′ ≪ f for c > deg f"

[[theorems]]
name = "RealRooted.strictInterl_add_X_sub_one_mul"
module = "RealRooted.ShiftLemma"
label = "Shift lemma: h ≪ f and h(0) ≤ f(0) give f ≪ f + (x − 1) h"

[[theorems]]
name = "RealRooted.strictInterl_sub_X_mul_pair_of_posLeadingCoeff"
module = "RealRooted.FolkloreLemma"
label = "Subtracting x g: g ≪ f − x g ≪ f"

[[theorems]]
name = "RealRooted.HlavacekSolus.isRealRooted_hPolynomial_of_perm_isInterlacingSeqNonneg"
module = "RealRooted.HlavacekSolus.Shelling"
label = "Hlavacek–Solus: interlacing shelling pieces give a real-rooted h-polynomial"

[[definitions]]
name = "RealRooted.HlavacekSolus.cubeColoredEulerian"
module = "RealRooted.HlavacekSolus.HalfOpenCube"
label = "The refined type-B Eulerian polynomial A_{d,l}^(2) as an Euler numerator"

[[definitions]]
name = "RealRooted.HlavacekSolus.cubeRelativeHRow"
module = "RealRooted.HlavacekSolus.HalfOpenCube"
label = "The 2d + 1 relative h-polynomials of the half-open d-cubes"

[[theorems]]
name = "RealRooted.HlavacekSolus.polytopalHPolynomial_eq_sum_relativePieces"
module = "RealRooted.HlavacekSolus.PolytopalShelling"
label = "The h-polynomial of a polytopal shelling is the sum of the relative h-polynomials"

[[theorems]]
name = "RealRooted.HlavacekSolus.isRealRooted_polytopalHPolynomial_of_perm_interlacingNonneg"
module = "RealRooted.HlavacekSolus.PolytopalShelling"
label = "Polytopal shellings with interlacing relative pieces have real-rooted h-polynomial"

[[theorems]]
name = "RealRooted.HlavacekSolus.cubeColoredEulerian_strictInterl_succ"
module = "RealRooted.HlavacekSolus.HalfOpenCube"
label = "A_{d,l}^(2) interlaces A_{d,l+1}^(2) for l < d"

[[theorems]]
name = "RealRooted.HlavacekSolus.cubeRelativeHRow_isInterlacingSeqNonneg"
module = "RealRooted.HlavacekSolus.CubicalShelling"
label = "Relative h-polynomials of half-open d-cubes form a nonnegative interlacing sequence"

[[theorems]]
name = "RealRooted.isRealRooted_sum_of_mem_isInterlacingSeqNonneg"
module = "RealRooted.HlavacekSolus.CubicalShelling"
label = "A nonzero sum of members of a nonnegative interlacing sequence is real-rooted"

-->

<!-- realrooted-catalog-content -->
# Closure of interlacing under cones, affine combinations and shifts

Interlacing is preserved by nonnegative combinations of an interlacing sequence and by several
affine and shift operations, and it gives real-rooted h-polynomials of shellings.

## Results

We write $f\ll g$ if $f$ and $g$ are nonzero and real-rooted, $g$ has the rightmost root, and the
roots alternate, with $\deg g=\deg f$ or $\deg g=\deg f+1$. Roots are compared weakly. In the
cone lemma, either side may also be zero.

**Theorem (affine combinations, Brändén).** Let $f,g$ be nonzero with nonnegative coefficients.
If $(sx+t)f+g$ is real-rooted for all $s,t>0$, then $f\ll g$.

**Theorem (cone lemma, Brändén and Saud Leite).** [@BrandenLeite2024x, Lemma 3.1] Let
$f_0,\dots,f_n$ be real-rooted with nonnegative coefficients, and suppose that $f_i\ll f_j$ for
all $i<j\le n$. Then for all $\lambda_0,\dots,\lambda_n\ge0$ the combination
$F=\sum_i\lambda_if_i$ satisfies $f_0\ll F\ll f_n$, where either side may be zero.

**Theorem (affine derivative).** Let $f$ be real-rooted of degree $d\ge1$ with positive leading
coefficient and only nonpositive roots. If $c>d$, then $cf+(1-x)f'\ll f$.

**Theorem (shift lemma).** Let $h\ll f$, where both have positive leading coefficients and only
nonpositive roots, and suppose that $h(0)\le f(0)$. Then $f\ll f+(x-1)h$.

**Theorem (subtracting $xg$).** Let $f,g$ be monic with $\deg f=\deg g+1$ and only nonpositive
roots, and let $g\ll f$. If $f-xg$ has positive leading coefficient, then
$g\ll f-xg\ll f$. The positivity hypothesis is not automatic, since the leading terms of $f$
and $xg$ cancel.

**Theorem (shellings, Hlavacek and Solus).** We use finite abstract simplicial complexes, a
subdivision given by a carrier map with facet coverage, and a shelling of the base complex.
Suppose that, in some order, the h-polynomials of the relative pieces form an interlacing
sequence of real-rooted polynomials with nonnegative coefficients, and that the h-polynomial of
the subdivision is nonzero. Then the h-polynomial of the subdivision is real-rooted.

**Proposition (polytopal shellings).** Let a shelling of a graded face set be given by ordered,
pairwise disjoint relative pieces that cover all faces. The h-polynomial is the sum of the
h-polynomials of the relative pieces. If these, in some order, form a nonnegative interlacing
sequence and the sum is nonzero, then the h-polynomial is real-rooted.

**Theorem (half-open cubes).** For $0\le l\le 2d$, let $h_{d,l}=A^{(2)}_{d,l}$ if $l\le d$ and
$h_{d,l}=x\cdot I_dA^{(2)}_{d,2d-l}$ if $d<l$, where $I_d$ is reflection in degree $d$ and
$A^{(2)}_{d,l}$ is the refined type-B Eulerian polynomial, defined as the Euler numerator of
$t\mapsto(2t)^l(2t+1)^{d-l}$. These are the relative h-polynomials of half-open $d$-cubes.
Then $A^{(2)}_{d,l}\ll A^{(2)}_{d,l+1}$ for $l<d$, and $h_{d,0},\dots,h_{d,2d}$ is a nonnegative
interlacing sequence. Every sum, with repetitions, of members of a nonnegative interlacing
sequence is real-rooted when it is nonzero. Consequently, if the h-polynomial of a polytopal
shelling is nonzero and every relative h-polynomial is some $h_{d,l}$, then it is real-rooted.

## Proof

The affine derivative, shift and subtraction statements are sign arguments at the roots of $f$:
at such a root $r\le0$, the new polynomial takes the value $(1-r)f'(r)$, $(r-1)h(r)$ or
$-r\,g(r)$ respectively, so it alternates in sign and the intermediate value theorem places its
roots. The cone lemma follows by applying one-sided cone lemmas for finite sums to the two
endpoint relations.

## References

See [@Fisk2006x], [@Branden2015, Lemma 7.8.4], and
[@BrandenLeite2024x, Lemma 3.1]. See also the
[interlacing sequences on symmetricfunctions.com](sf:interlacingSequenceDefinition).
For the shelling criterion, see M. Hlavacek and L. Solus, “Subdivisions of
shellable complexes,” *J. Combin. Theory Ser. A* (2021), Theorem 3.1,
[arXiv:2003.07328](https://arxiv.org/abs/2003.07328).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.AffineFamily`,
`RealRooted.Interlacing.ConeBounds`, `RealRooted.AffineDerivative`,
`RealRooted.ShiftLemma` and `RealRooted.FolkloreLemma`.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace InterlacingClosure

/-- **Affine derivative.** If `f` is real-rooted of degree `d ≠ 0` with
positive leading coefficient and nonpositive roots, and `c > d`, then
`c f + (1 - X) f'` interlaces `f`. -/
theorem strictInterl_affine_derivative {f : ℝ[X]} (hf : f.Splits) (hdeg : f.natDegree ≠ 0)
    (hf_pos : HasPosLeadingCoeff f) (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    StrictInterl (C c * f + (1 - X) * f.derivative) f :=
  strictInterl_affine_derivative' hf (Nat.one_le_iff_ne_zero.mpr hdeg) hf_pos hroots_nonpos hc

end InterlacingClosure
end Challenges
end RealRooted
