import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.EulerianCone
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Preserver

open Polynomial Set

/-!
# The weighted deco Eulerian transform

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "deco-eulerian-transform"
authors = ["Alexandersson"]
years = [2026]

[[definitions]]
name = "RealRooted.Applications.OEIS.weightedDecoEulerian"
module = "RealRooted.Applications.OEIS.A144438.Weighted"
label = "Weighted deco Eulerian polynomials"

[[definitions]]
name = "RealRooted.Applications.OEIS.weightedDecoTransform"
module = "RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Basic"
label = "Weighted deco Eulerian transform"

[[theorems]]
name = "RealRooted.Challenges.DecoEulerian.weightedDecoTransform_splits_hasSimpleRoots_roots_neg"
label = "The weighted deco transform preserves interval-rooted polynomials"
headline = true

[[theorems]]
name = "RealRooted.EulerianTransform.transform_X_mul_eq_X_mul_weightedDecoTransform"
module = "RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.EulerianCone"
label = "At weight zero the deco transform is the Eulerian transformation, shifted"

[[theorems]]
name = "RealRooted.Applications.OEIS.weightedDecoTransform_zero_isPF_of_magicExpansion"
module = "RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.EulerianCone"
label = "At weight zero the deco transform is real-rooted on the whole magic cone"
-->

<!-- realrooted-catalog-content -->
# The weighted deco Eulerian transform

For a real parameter $w$, define $P_{-1}^{(w)}(x)=0$,
$P_0^{(w)}(x)=1$, and

$$
P_{n+1}^{(w)}(x)
=x(1-x)(P_n^{(w)})'(x)
 +(1+(n+1)x)P_n^{(w)}(x)
 +wxP_{n-1}^{(w)}(x).
$$

Let $\mathcal T_w\colon\mathbb R[u]\to\mathbb R[x]$ be the linear map
determined by $\mathcal T_w(u^n)=P_n^{(w)}(x)$.

**Theorem.** Let $0\leq w\leq1$. If a nonconstant real polynomial $f$
splits over $\mathbb R$ and all its zeros belong to $[-1,0]$, then
$\mathcal T_w(f)$ splits over $\mathbb R$, has no repeated zero, and all its
zeros are strictly negative.

At $w=0$, the recurrence is the ordinary Eulerian recurrence
`generalizedEulerian 1` (`weightedDecoEulerian_zero_weight`), whose members are
classically the Eulerian polynomials $A_{n+1}(x)$. At $w=1$, it is the
recurrence-defined family `decoEulerian` (`weightedDecoEulerian_one_weight`),
whose initial values and recurrence match the coefficient triangle
[OEIS A144438](https://oeis.org/A144438). The descent and deco-polyomino
interpretations are cited, not formalized.

At $w=0$ the transform is real-rooted on the larger cone of nonnegative combinations of
$u^k(1+u)^{d-k}$: since $\mathcal A(uf)=x\,\mathcal T_0(f)$ for the Eulerian transformation
$\mathcal A\colon 1\mapsto 1,\ u^n\mapsto xA_n(x)$, this follows from Athanasiadis's cone
theorem. Whether the cone version holds for $0<w\leq 1$ is open.

## Proof idea

For inputs $(u+a)^n$, a symmetric arrowhead matrix controls the new zeros and
the companion residues. The induction uses the scaled energy $wE_n\leq1$;
the case $w=0$ follows directly from the companion Schur complement. For
inputs $\prod_j(u+a_j)$ with $a_j\in[0,1]$, a first-contact argument on the
parameter cube forces a vanishing companion residue onto the diagonal
$a_1=\dotsb=a_n$, contradicting the diagonal estimate. Factoring an arbitrary
input over $\mathbb R$ completes the proof.

## References

P. Alexandersson, *An Eulerian deformation from deco polyominoes*, manuscript
(2026).

E. Barcucci, A. Del Lungo, and R. Pinzani, [“Deco polyominoes, permutations
and random generation,”](https://doi.org/10.1016/0304-3975(95)00199-9)
*Theoretical Computer Science* 159 (1996), 29–42.
<!-- /realrooted-catalog-content -->

This module exposes the checked interval-preservation theorem. The energy,
first-contact, and factor-induction arguments live in
`RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted`.
-/

namespace RealRooted
namespace Challenges
namespace DecoEulerian

/-- The weighted deco Eulerian transform sends every nonconstant polynomial
with all zeros in `[-1, 0]` to a polynomial with simple negative zeros. -/
theorem weightedDecoTransform_splits_hasSimpleRoots_roots_neg
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {f : ℝ[X]}
    (hfDegree : f.natDegree ≠ 0) (hfSplits : f.Splits)
    (hfRoots : ∀ r, f.IsRoot r → r ∈ Icc (-1 : ℝ) 0) :
    (Applications.OEIS.weightedDecoTransform w f).Splits ∧
      HasSimpleRoots (Applications.OEIS.weightedDecoTransform w f) ∧
        ∀ r, (Applications.OEIS.weightedDecoTransform w f).IsRoot r → r < 0 :=
  Applications.OEIS.weightedDecoTransform_splits_hasSimpleRoots_and_roots_neg
    hw0 hw1 (Nat.one_le_iff_ne_zero.mpr hfDegree) hfSplits hfRoots

end DecoEulerian
end Challenges
end RealRooted
