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
# Interlacing closure challenge entry point

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
label = "c f + (1 − x) f′ interlaces f"

[[theorems]]
name = "RealRooted.strictInterl_add_X_sub_one_mul"
module = "RealRooted.ShiftLemma"
label = "Shift lemma: f is interlaced by f + (x − 1) h"

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
label = "A sum of members of a nonnegative interlacing sequence, with repetitions, is real-rooted"

-->

<!-- realrooted-catalog-content -->
# Closure properties of interlacing

Here $f \ll g$ means that $f$ and $g$ are nonzero and real-rooted, $g$ has the
rightmost root, and the roots alternate, with $\deg g = \deg f$ or
$\deg g = \deg f + 1$. Roots are compared weakly. In the cone lemma, either
side is also allowed to be zero.

**Affine combinations (Brändén).** Let $f, g$ be nonzero with nonnegative
coefficients. If $(sx + t) f + g$ is real-rooted for all $s, t > 0$, then
$f \ll g$.

**Cone lemma (Brändén, Saud Leite).** [@BrandenLeite2024x, Lemma 3.1] Let
$f_0, \dots, f_n$ be real-rooted with
nonnegative coefficients, and suppose $f_i \ll f_j$ for all $i < j \le n$.
Then for all $\lambda_0, \dots, \lambda_n \ge 0$ the combination
$F = \sum_i \lambda_i f_i$ satisfies $f_0 \ll F \ll f_n$, where either side
may be zero.

**Affine derivative.** Let $f$ be real-rooted of degree $d \ge 1$ with
positive leading coefficient and only nonpositive roots. If $c > d$, then
$c f + (1 - x) f' \ll f$.

**Shift lemma.** Let $h \ll f$, where both have positive leading coefficients
and only nonpositive roots, and suppose $h(0) \le f(0)$. Then
$f \ll f + (x - 1) h$.

**Subtracting $x g$.** Let $f, g$ be monic with $\deg f = \deg g + 1$, only
nonpositive roots, and $g \ll f$. If $f - x g$ has positive leading
coefficient, then $g \ll f - x g \ll f$. The positivity hypothesis is not
automatic, since the leading terms of $f$ and $x g$ cancel.

**Shellings (Hlavacek–Solus).** Let a finite simplicial subdivision of a
shellable complex be given, together with a shelling of the base complex.
Suppose that, in some order, the h-polynomials of the relative pieces form an
interlacing sequence of real-rooted polynomials with nonnegative coefficients,
and that the h-polynomial of the subdivision is nonzero. Then the latter
h-polynomial is real-rooted. Only the finite combinatorial content of the
subdivision axioms is formalized.

**Cubical shellings.** In the abstract polytopal setting, a shelling is an ordered list of
pairwise disjoint relative face sets covering all faces of the subdivision, and the
h-polynomial of the subdivision is the sum of the relative h-polynomials of the pieces.
If the pieces, in some order, form a nonnegative interlacing sequence, the sum is
real-rooted. In a stable shelling of a cubical complex every relative piece is a
half-open cube $[-1,1]^d_l$ with $0\le l\le 2d$, whose h-polynomial is the refined
type-B Eulerian polynomial $A_{d,l}^{(2)}$ for $l\le d$ and
$x\cdot I_dA^{(2)}_{d,2d-l}$ (a reflection) for $d<l$, with $A_{d,l}^{(2)}$ the Euler
numerator of $t\mapsto(2t)^l(2t+1)^{d-l}$. All these polynomials are real-rooted with
nonnegative coefficients, $A_{d,l}^{(2)}$ interlaces $A_{d,l+1}^{(2)}$ for $l<d$, and the
whole row of $2d+1$ relative h-polynomials is a nonnegative interlacing sequence.
Hence a shelling all of whose relative pieces are half-open cubes has a real-rooted
h-polynomial; the identification of the pieces with half-open cubes (their Lemma 3.2) is
the hypothesis that the geometric argument supplies.

## Proof idea

The last three statements are sign arguments at the roots of $f$: at such a
root $r \le 0$, the new polynomial takes the value $(1 - r) f'(r)$, $(r - 1) h(r)$
or $-r\, g(r)$, so it alternates in sign and the intermediate value theorem
places its roots. The cone lemma combines the common-interleaver theory with
the two endpoint relations. For the affine criterion, the hypothesis first
forces $\deg g \in \{\deg f, \deg f + 1\}$ and the real-rootedness of $x f$.
For $\deg f \ge 2$ it then gives $g \ll x f$, and nonnegative coefficients
turn this into $f \ll g$ by Wagner's lemma.

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
