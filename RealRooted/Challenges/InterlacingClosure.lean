import RealRooted.AffineDerivative
import RealRooted.AffineFamily
import RealRooted.FolkloreLemma
import RealRooted.HlavacekSolus.Shelling
import RealRooted.Interlacing.ConeBounds
import RealRooted.ShiftLemma

/-!
# Interlacing closure challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "interlacing-closure"
authors = ["Fisk", "Brändén", "Saud Leite", "Hlavacek", "Solus"]
years = [2006, 2015, 2021, 2024]

[[theorems]]
name = "RealRooted.Challenges.InterlacingClosure.strictInterl_of_forall_affine_mul_add_splits"
label = "Brändén: real-rooted affine combinations force interlacing"
headline = true

[[theorems]]
name = "RealRooted.interl_weightedSum_cone"
module = "RealRooted.Interlacing.ConeBounds"
label = "A nonnegative combination of an interlacing sequence lies between its ends"
headline = true

[[theorems]]
name = "RealRooted.Challenges.InterlacingClosure.strictInterl_affine_derivative"
label = "c f + (1 − x) f′ interlaces f"

[[theorems]]
name = "RealRooted.Challenges.InterlacingClosure.strictInterl_add_X_sub_one_mul"
label = "Shift lemma: f is interlaced by f + (x − 1) h"

[[theorems]]
name = "RealRooted.strictInterl_sub_X_mul_pair_of_posLeadingCoeff"
module = "RealRooted.FolkloreLemma"
label = "Subtracting x g: g ≪ f − x g ≪ f"

[[theorems]]
name = "RealRooted.HlavacekSolus.isRealRooted_hPolynomial_of_perm_isInterlacingSeqNonneg"
module = "RealRooted.HlavacekSolus.Shelling"
label = "Hlavacek–Solus: interlacing shelling pieces give a real-rooted h-polynomial"
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

**Cone lemma (Brändén, Saud Leite).** Let $f_0, \dots, f_n$ be real-rooted with
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

S. Fisk, *Polynomials, roots, and interlacing*, arXiv:math/0612833 (2006);
P. Brändén, “Unimodality, log-concavity, real-rootedness and beyond,”
*Handbook of Enumerative Combinatorics*, CRC Press, 2015, Lemma 7.8.4;
P. Brändén and L. Saud Maia Leite, “Totally nonnegative matrices, chain
enumeration and zeros of polynomials,” *Advances in Mathematics* 487 (2026),
110760, arXiv:2412.06595, Lemma 3.1.
See also the
[interlacing sequences on symmetricfunctions.com][seq].

[seq]: https://www.symmetricfunctions.com/realRootedInterlacing.htm#interlacingSequenceDefinition
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.AffineFamily`,
`RealRooted.Interlacing.ConeBounds`, `RealRooted.AffineDerivative`,
`RealRooted.ShiftLemma` and `RealRooted.FolkloreLemma`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace InterlacingClosure

/-- **Brändén, Lemma 7.8.4.** If `f, g` are nonzero with nonnegative
coefficients and `(s X + t) f + g` is real-rooted for all `s, t > 0`, then
`f ≪ g`. -/
theorem strictInterl_of_forall_affine_mul_add_splits {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (haff : ∀ s t : ℝ, 0 < s → 0 < t → ((C s * X + C t) * f + g).Splits) :
    StrictInterl f g := by
  refine strictInterl_of_affine_family_nonneg hf0 hg0 hf hg fun {s t} hs ht ↦ ⟨?_, haff s t hs ht⟩
  intro h0
  have hcoeff := congrArg (coeff · g.natDegree) h0
  simp only [coeff_add, coeff_zero] at hcoeff
  have hprod := (hasNonnegCoeffs_affine_linear hs.le ht.le).mul hf g.natDegree
  have hlead : 0 < g.coeff g.natDegree := hg.pos_leadingCoeff hg0
  linarith

/-- **Affine derivative.** If `f` is real-rooted of degree `d ≠ 0` with
positive leading coefficient and nonpositive roots, and `c > d`, then
`c f + (1 - X) f'` interlaces `f`. -/
theorem strictInterl_affine_derivative {f : ℝ[X]} (hf : f.Splits) (hdeg : f.natDegree ≠ 0)
    (hf_pos : HasPosLeadingCoeff f) (hroots_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    {c : ℝ} (hc : (f.natDegree : ℝ) < c) :
    StrictInterl (C c * f + (1 - X) * f.derivative) f :=
  strictInterl_affine_derivative' hf (Nat.one_le_iff_ne_zero.mpr hdeg) hf_pos hroots_nonpos hc

/-- **Shift lemma.** If `h ≪ f`, both have positive leading coefficients and
nonpositive roots, and `h(0) ≤ f(0)`, then `f ≪ f + (X - 1) h`. -/
theorem strictInterl_add_X_sub_one_mul {f h : ℝ[X]} (hhf : StrictInterl h f)
    (hf_pos : HasPosLeadingCoeff f) (hh_pos : HasPosLeadingCoeff h)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) (hh_nonpos : ∀ r ∈ h.roots, r ≤ 0)
    (heval : h.eval 0 ≤ f.eval 0) :
    StrictInterl f (f + (X - 1) * h) := by
  simpa using strictInterl_shift hhf.2.1.1 hhf.2.1.2 hhf.1.1 hhf.1.2 hf_nonpos hh_nonpos
    hf_pos hh_pos hhf heval

end InterlacingClosure
end Challenges
end RealRooted
