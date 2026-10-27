module

public import RealRooted.LiuWang.CombinedFlux
public import RealRooted.LiuWang.SequenceCore
public import RealRooted.LiuWang.FiniteFamily
public import RealRooted.MaWang.CriticalSign
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
headline = true

[[theorems]]
name = "RealRooted.strictInterl_of_eval_mul_derivative_nonpos"
module = "RealRooted.MaWang.Weak.DerivativeSign"
label = "f ≪ F when F f' ≤ 0 at the simple zeros of f"
headline = true

[[theorems]]
name = "RealRooted.Challenges.MaWangLiuWang.strictInterl_mul_add_mul_derivative_of_eval_nonpos"
label = "Ma–Wang criterion: f ≪ uf + vf' when v ≤ 0 at the zeros of f"
headline = true

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
-->

<!-- realrooted-catalog-content -->
# The Liu–Wang and Ma–Wang interlacing criteria

For nonzero real-rooted polynomials $f$ and $F$ we write $f \ll F$
(`StrictInterl f F`) as on the [interlacing page](/RealRooted/concepts/interlacing/):
the zeros interlace weakly and $F$ has the largest zero, so that
$\deg F - \deg f \in \{0, 1\}$. Shared and repeated zeros are allowed. In
particular, $f \ll F$ includes the statement that $F$ is real-rooted.

**Theorem (general form).** Let $f, a \in \mathbb{R}[x]$ and, for a finite index set
$s$, let $g_i, b_i \in \mathbb{R}[x]$ ($i \in s$). Put
$F = a f + \sum_{i \in s} b_i g_i$. Suppose that $f$ is real-rooted with a positive
leading coefficient (repeated zeros are allowed), that $g_i \ll f$ and $g_i$ has a
positive leading coefficient for each $i$, that $F$ has a positive leading coefficient,
and that $\deg f \leq \deg F \leq \deg f + 1$. If the combined flux satisfies
$$\Bigl(\sum_{i \in s} b_i(r)\, g_i(r)\Bigr) f'(r) \leq 0$$
at every real zero $r$ of $f$, and $b_i(r) \leq 0$ for every $i$ at every repeated
zero $r$ of $f$, then $f \ll F$.

All criteria below are special cases, and in RealRooted they are proved as
corollaries of this theorem:
- one interlacer $g \ll f$ gives the Liu–Wang theorem;
- $g = f'$ gives the Ma–Wang theorem;
- a finite family with termwise signs gives the finite-sum form;
- at simple zeros the combined condition reduces to the derivative-sign criterion
  $F(r) f'(r) \leq 0$.

**Theorem (weak signs).** If $g$ interlaces $f$, the two have no common zeros, $g$ and
$F$ have positive leading coefficients, $\deg f \leq \deg F \leq \deg f + 1$, and
$F(r)\, g(r) \leq 0$ at every zero $r$ of $f$, then $f \ll F$. The derivative-sign
criterion below is the case $g = f'$.

**Theorem (Liu–Wang).** [@LiuWang2007, Thm. 2.1] Let
$f, g, a, b \in \mathbb{R}[x]$ and
$F = a f + b g$. Suppose that $g \ll f$, that $g$ and $F$ have positive leading
coefficients, and that $\deg f \leq \deg F \leq \deg f + 1$. If $b(r) \leq 0$
at every real zero $r$ of $f$, then $f \ll F$.

Both shapes $\deg g = \deg f$ and $\deg g + 1 = \deg f$ are allowed, $f$ and $g$
may have common and repeated zeros, and the leading coefficient of $f$ may have
either sign.

**Theorem (derivative signs).** Let $f$ be real-rooted with simple zeros and a
positive leading coefficient, and let $F$ have a positive leading coefficient
and $\deg f \leq \deg F \leq \deg f + 1$. If $F(r) f'(r) \leq 0$ at every zero
$r$ of $f$, then $f \ll F$. Common zeros of $f$ and $F$ are allowed.

Conversely, if $g \ll f$ and both have positive leading coefficients, then
$g(r) f'(r) \geq 0$ at every zero $r$ of $f$.

**Theorem (Ma–Wang).** [@MaWang2008, Thm. 2] Let $f, u, v \in \mathbb{R}[x]$ and
$F = u f + v f'$. Suppose that $f$ is real-rooted, that $f$ and $F$ have
positive leading coefficients, and that $\deg f \leq \deg F \leq \deg f + 1$.
If $v(r) \leq 0$ at every zero $r$ of $f$, then $f \ll F$.

There is no degree hypothesis on $f$. For the strict form, suppose in addition
that $\deg f \neq 0$, that $f$ has simple zeros, that $\deg F = \deg f + 1$, and
that $v(r) < 0$ at every zero $r$ of $f$. Then $f \ll F$ and $F$ has simple
zeros.

**Theorem (finite sums).** Let $f$ be real-rooted with a positive leading
coefficient (repeated zeros are allowed), and let $F = a f + \sum_{i \in s} b_i g_i$ for a
finite index set $s$. Suppose that $g_i \ll f$ and $g_i$ has a positive leading
coefficient for each $i \in s$, that $F$ has a positive leading coefficient, and
that $\deg f \leq \deg F \leq \deg f + 1$. If $b_i(r) \leq 0$ at every zero $r$
of $f$ for each $i \in s$, then $f \ll F$. At repeated zeros the termwise conditions
cannot be replaced by the combined condition $F(r) f'(r) \leq 0$, which is vacuous there.

**Theorem (strict critical signs).** If $f$ is nonconstant and split, $f$ and $F$ have
positive leading coefficients, $\deg f \leq \deg F \leq \deg f + 1$, and
$F(r) f'(r) < 0$ at every zero $r$ of $f$, then $f \ll F$.

**Sequence forms.** Let $(P_n)_{n \geq 0}$ have positive leading coefficients,
with $P_0 \ll P_1$ and $\deg P_{n+1} \leq \deg P_{n+2} \leq \deg P_{n+1} + 1$
for all $n$.

- If $P_{n+2} = A_n P_{n+1} + B_n P_n$ and $B_n(r) \leq 0$ at every zero $r$ of
  $P_{n+1}$, then $P_n \ll P_{n+1}$ for all $n$.
- If $P_{n+2} = U_n P_{n+1} + V_n P_{n+1}'$ and $V_n(r) \leq 0$ at every zero
  $r$ of $P_{n+1}$, then $P_n \ll P_{n+1}$ for all $n$.

In both cases every $P_n$ is real-rooted, and consecutive polynomials may share
zeros.

The site states the Liu–Wang theorem with $F$ and $g$ having leading
coefficients of the same sign; the negative case follows by replacing $F$ and
$g$ with $-F$ and $-g$. The site also gives a strict form of the Liu–Wang
theorem, with strict inequalities between the zeros. That strict form is not
stated here.

## References

See [@LiuWang2007, Thm. 2.1] and [@MaWang2008, Thm. 2]. See also the
[Ma–Wang and Liu–Wang criteria on symmetricfunctions.com](sf:maWangDerivativeCriterion).
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
