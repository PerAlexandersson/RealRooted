module

public import RealRooted.LiuWang.CombinedFlux
public import RealRooted.LiuWang.SequenceCore
public import RealRooted.LiuWang.FiniteFamily
public import RealRooted.MaWang.CriticalSign
import RealRooted.LiuWangRecursion
import RealRooted.MaWang.DerivativeStep
public import RealRooted.MaWang.DerivativeSequence
import RealRooted.MaWang.StrictStep
public import RealRooted.SimpleRoots
public import RealRooted.Basic.Coefficients

/-!
# The Liu–Wang and Ma–Wang interlacing criteria

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "ma-wang-liu-wang"
formalized = "2026-10-06"
tags = []
references = [
  "LiuWang2007",
  "MaWang2008",
]
authors = ["Liu", "Wang", "Ma"]
years = [2007, 2008]

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_mul_add_sum_mul_of_combined_flux_of_pos"
module = "RealRooted.LiuWang.CombinedFlux"
label = "General form: f ≪ af + Σ bᵢgᵢ from the combined flux at the zeros of f"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_of_interlaces_eval_mul_nonpos"
module = "RealRooted.MaWang.Weak.DerivativeSign"
label = "f ≪ F when g interlaces f without common zeros and F g ≤ 0 at the zeros of f"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_mul_add_mul_of_eval_nonpos"
module = "RealRooted.LiuWang.General"
label = "Liu–Wang criterion: f ≪ af + bg when b ≤ 0 at the zeros of f"

[[theorems]]
name = "RealRooted.strictInterl_of_eval_mul_derivative_nonpos"
module = "RealRooted.MaWang.Weak.DerivativeSign"
label = "f ≪ F when F f' ≤ 0 at the simple zeros of f"

[[theorems]]
name = "RealRooted.Challenges.MaWangLiuWang.strictInterl_mul_add_mul_derivative_of_eval_nonpos"
label = "Ma–Wang criterion: f ≪ uf + vf' when v ≤ 0 at the zeros of f"
symcat = "maWangDerivativeCriterion"

[[theorems]]
name = "RealRooted.StrictInterl.eval_mul_eval_derivative_nonneg"
module = "RealRooted.MaWang.Weak.DerivativeSign"
label = "An interlacer g ≪ f has the sign of f' at the zeros of f"

[[theorems]]
name = "RealRooted.Challenges.MaWangLiuWang.strictInterl_and_hasSimpleRoots_of_eval_neg"
label = "Strict Ma–Wang step: simple zeros propagate when v < 0"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_mul_add_sum_mul_of_eval_nonpos"
module = "RealRooted.LiuWang.FiniteFamily"
label = "Liu–Wang criterion for finite sums of interlacers, repeated roots allowed"

[[theorems]]
name = "RealRooted.strictInterl_of_eval_mul_derivative_neg"
module = "RealRooted.MaWang.CriticalSign"
label = "Strict interlacing from strict critical signs"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_succ_of_recurrence_of_eval_nonpos"
module = "RealRooted.LiuWang.SequenceCore"
label = "Liu–Wang criterion for three-term recurrences"

[[theorems]]
name = "RealRooted.MaWang.strictInterl_derivative_nonpos_sequence"
module = "RealRooted.MaWang.DerivativeSequence"
label = "Ma–Wang criterion for derivative recurrences"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_derivative_lag_of_eval_nonpos"
module = "RealRooted.LiuWang.FiniteFamily"
label = "Liu–Wang step with an additional derivative term"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_sequence_of_derivative_lag"
module = "RealRooted.LiuWangRecursion"
label = "Liu–Wang criterion for derivative–lag recurrences"
-->

<!-- realrooted-catalog-content -->
# The Liu–Wang and Ma–Wang interlacing criteria

If an interlacer of $f$ is added to $af$ with a coefficient that is nonpositive at the roots of
$f$, the sum is again interlaced by $f$; the same holds for $uf+vf'$ with $v\le0$ at the roots.

## Results

For nonzero real-rooted polynomials $f$ and $F$ we write $f\ll F$ if $f$ interlaces $F$ (see
the [interlacing page](/RealRooted/concepts/interlacing/)): the roots interlace weakly,
$F$ has the largest root, and $\deg F-\deg f\in\{0,1\}$. Shared and repeated roots are allowed.
The statement $f\ll F$ includes that $F$ is real-rooted. Throughout, "positive" for a
polynomial refers to its leading coefficient.

**Theorem (Liu–Wang).** [@LiuWang2007, Thm. 2.1] Let $f,g,a,b\in\mathbb R[x]$ and $F=af+bg$.
Suppose that $g\ll f$, that $g$ and $F$ are positive, and that
$\deg f\le\deg F\le\deg f+1$. If $b(r)\le0$ at every real root $r$ of $f$, then $f\ll F$.
Both shapes $\deg g=\deg f$ and $\deg g+1=\deg f$ are allowed, $f$ and $g$ may have common and
repeated roots, and the leading coefficient of $f$ may have either sign.

**Theorem (Ma–Wang).** [@MaWang2008, Thm. 2] Let $f,u,v\in\mathbb R[x]$ and $F=uf+vf'$. Suppose
that $f$ is real-rooted, that $f$ and $F$ are positive, and that
$\deg f\le\deg F\le\deg f+1$. If $v(r)\le0$ at every root $r$ of $f$, then $f\ll F$. There is no
degree hypothesis on $f$.

**Theorem (Ma–Wang, strict form).** Suppose in addition that $\deg f\ne0$, that $f$ has simple
roots, that $\deg F=\deg f+1$, and that $v(r)<0$ at every root $r$ of $f$. Then $f\ll F$ and
$F$ has simple roots.

**Theorem (general form).** Let $f,a\in\mathbb R[x]$ and, for a finite index set $s$, let
$g_i,b_i\in\mathbb R[x]$. Put $F=af+\sum_{i\in s}b_ig_i$. Suppose that $f$ is real-rooted and
positive, that $g_i\ll f$ and $g_i$ is positive for each $i$, that $F$ is positive, and that
$\deg f\le\deg F\le\deg f+1$. If
$$
\Bigl(\sum_{i\in s}b_i(r)\,g_i(r)\Bigr)f'(r)\le0
$$
at every real root $r$ of $f$, and $b_i(r)\le0$ for every $i$ at every repeated root $r$ of
$f$, then $f\ll F$. The Liu–Wang theorem, the Ma–Wang theorem and the finite-sum form below are
special cases.

**Theorem (finite sums).** Let $f\ne0$ be real-rooted, with leading coefficient of either sign,
and let $F=af+\sum_{i\in s}b_ig_i$ with $g_i\ll f$ and $g_i$ positive, $F$ positive and
$\deg f\le\deg F\le\deg f+1$. If $b_i(r)\le0$ at every root $r$ of $f$ for each $i$, then
$f\ll F$. At repeated roots the termwise conditions cannot be replaced by the combined
condition $F(r)f'(r)\le0$, which is vacuous there.

**Theorem (weak signs).** Let $g\ll f$ with $\deg g+1=\deg f$, with no common roots, let $g$ and
$F$ be positive, and $\deg f\le\deg F\le\deg f+1$. If $F(r)g(r)\le0$ at every root $r$ of $f$,
then $f\ll F$.

**Theorem (derivative signs).** Let $f$ be real-rooted with simple roots and positive, let $F$
be positive with $\deg f\le\deg F\le\deg f+1$. If $F(r)f'(r)\le0$ at every root $r$ of $f$,
then $f\ll F$. Common roots of $f$ and $F$ are allowed. Conversely, if $g\ll f$ and both are
positive, then $g(r)f'(r)\ge0$ at every root $r$ of $f$.

**Theorem (strict critical signs).** If $f$ is nonconstant and real-rooted, $f$ and $F$ are
positive, $\deg f\le\deg F\le\deg f+1$, and $F(r)f'(r)<0$ at every root $r$ of $f$, then
$f\ll F$.

**Theorem (sequences).** Let $(P_n)_{n\ge0}$ be positive with $P_0\ll P_1$ and
$\deg P_{n+1}\le\deg P_{n+2}\le\deg P_{n+1}+1$ for all $n$. Then $P_n\ll P_{n+1}$ for all $n$
in each of the following cases; in particular every $P_n$ is real-rooted, and consecutive
polynomials may share roots.

- $P_{n+2}=A_nP_{n+1}+B_nP_n$ with $B_n(r)\le0$ at every root $r$ of $P_{n+1}$.
- $P_{n+2}=U_nP_{n+1}+V_nP_{n+1}'$ with $V_n(r)\le0$ at every root $r$ of $P_{n+1}$.
- $P_{n+2}=U_nP_{n+1}+V_nP_{n+1}'+W_nP_n$ with $V_n(r)\le0$ and $W_n(r)\le0$ at every root $r$
  of $P_{n+1}$.

**Theorem (derivative–lag step).** Let $f\ne0$ be real-rooted and positive, let $g\ll f$ be
positive, and put $F=uf+vf'+wg$. Suppose that $F$ is positive and
$\deg f\le\deg F\le\deg f+1$. If $v(r)\le0$ and $w(r)\le0$ at every root $r$ of $f$, then
$f\ll F$. Common roots of $f$ and $g$ are allowed.

## Use

The criteria give the interlacing of consecutive rows of polynomial families defined by
recurrences or by first-order differential operators.

## References

[@LiuWang2007, Thm. 2.1]; [@MaWang2008, Thm. 2]; see also the
[Ma–Wang and Liu–Wang criteria on symmetricfunctions.com](sf:maWangDerivativeCriterion). That
site states the Liu–Wang theorem for $F$ and $g$ with leading coefficients of the same sign, the
negative case following by replacing $F,g$ with $-F,-g$, and also gives a strict form of the
theorem, which is not included here.
<!-- /realrooted-catalog-content -->

The general form (combined flux) lives in `RealRooted.LiuWang.CombinedFlux`; the
Liu–Wang theorem (`RealRooted.LiuWang.General`) and the finite-sum form
(`RealRooted.LiuWang.FiniteFamily`) are its corollaries. The weak-sign and
derivative-sign criteria live in `RealRooted.MaWang.Weak.DerivativeSign`, and the
derivative steps in `RealRooted.MaWang.DerivativeStep` and
`RealRooted.MaWang.StrictStep`.
-/

public section

open Polynomial

namespace RealRooted
namespace Challenges
namespace MaWangLiuWang

/-- **Ma–Wang derivative criterion** (Ma–Wang 2008, Theorem 2).  Let `f` be real-rooted, and
let `F = u f + v f'` have degree `deg f` or `deg f + 1`, with `f` and `F` of positive leading
coefficient.  If `v` is nonpositive at every root of `f`, then `f ≪ F`. -/
theorem strictInterl_mul_add_mul_derivative_of_eval_nonpos {f u v : ℝ[X]} (hf : f.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hv : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    StrictInterl f (u * f + v * f.derivative) :=
  MaWang.strictInterl_derivative_of_nonpos_of_splits hf hdeg_lo hdeg_hi hF_pos hf_pos hv

/-- **Strict Ma–Wang step.**  If moreover `f` is nonconstant with simple roots, `F` has degree
`deg f + 1`, and `v` is negative at every root of `f`, then `F` also has simple roots. -/
theorem strictInterl_and_hasSimpleRoots_of_eval_neg {f F u v : ℝ[X]} (hf : f.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hF_pos : HasPosLeadingCoeff F) (hdegf : f.natDegree ≠ 0)
    (hdeg : F.natDegree = f.natDegree + 1) (hsimple : HasSimpleRoots f)
    (hrec : F = u * f + v * f.derivative) (hv : ∀ r, f.IsRoot r → v.eval r < 0) :
    StrictInterl f F ∧ HasSimpleRoots F :=
  strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ hf hf_pos hF_pos
    (Nat.one_le_iff_ne_zero.mpr hdegf) hdeg hsimple hrec hv

end MaWangLiuWang
end Challenges
end RealRooted
