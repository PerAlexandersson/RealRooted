import RealRooted.LiuWang.SequenceCore
import RealRooted.MaWang.DerivativeStep
import RealRooted.MaWang.StrictStep

/-!
# The Liu–Wang and Ma–Wang interlacing criteria

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "ma-wang-liu-wang"
authors = ["Liu", "Wang", "Ma"]
years = [2007, 2008]

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
name = "RealRooted.Challenges.MaWangLiuWang.strictInterl_mul_add_sum_mul_of_eval_nonpos"
label = "Liu–Wang criterion for finite sums of interlacers"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_succ_of_recurrence_of_eval_nonpos"
module = "RealRooted.LiuWang.SequenceCore"
label = "Liu–Wang criterion for three-term recurrences"

[[theorems]]
name = "RealRooted.Challenges.MaWangLiuWang.strictInterl_succ_of_derivative_recurrence"
label = "Ma–Wang criterion for derivative recurrences"
-->

<!-- realrooted-catalog-content -->
# The Liu–Wang and Ma–Wang interlacing criteria

For nonzero real-rooted polynomials $f$ and $F$ we write $f \ll F$
(`StrictInterl f F`) as on the [interlacing page](/RealRooted/concepts/interlacing/):
the zeros interlace weakly and $F$ has the largest zero, so that
$\deg F - \deg f \in \{0, 1\}$. Shared and repeated zeros are allowed. In
particular, $f \ll F$ includes the statement that $F$ is real-rooted.

**Theorem (Liu–Wang).** Let $f, g, a, b \in \mathbb{R}[x]$ and
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

**Theorem (Ma–Wang).** Let $f, u, v \in \mathbb{R}[x]$ and
$F = u f + v f'$. Suppose that $f$ is real-rooted, that $f$ and $F$ have
positive leading coefficients, and that $\deg f \leq \deg F \leq \deg f + 1$.
If $v(r) \leq 0$ at every zero $r$ of $f$, then $f \ll F$.

There is no degree hypothesis on $f$. For the strict form, suppose in addition
that $\deg f \neq 0$, that $f$ has simple zeros, that $\deg F = \deg f + 1$, and
that $v(r) < 0$ at every zero $r$ of $f$. Then $f \ll F$ and $F$ has simple
zeros.

**Theorem (finite sums).** Let $f$ be real-rooted with simple zeros and a
positive leading coefficient, and let $F = a f + \sum_{i \in s} b_i g_i$ for a
finite index set $s$. Suppose that $g_i \ll f$ and $g_i$ has a positive leading
coefficient for each $i \in s$, that $F$ has a positive leading coefficient, and
that $\deg f \leq \deg F \leq \deg f + 1$. If $b_i(r) \leq 0$ at every zero $r$
of $f$ for each $i \in s$, then $f \ll F$.

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

## Proof idea

If $f$ has simple zeros and $g \ll f$, then $g$ and $f'$ are both interlacers
of $f$, so $g(r) f'(r) \geq 0$ at every zero $r$ of $f$. Hence
$F(r) f'(r) = b(r) g(r) f'(r) \leq 0$, and the derivative-sign theorem applies.
That theorem perturbs $F$ to $F - \delta f'$, whose signs at the zeros of $f$
are strict, proves real-rootedness in the limit $\delta \to 0$, and then reads
off the interlacing. A common zero $r$ of $f$ and $g$ is a zero of $F$; dividing
$f$, $g$ and $F$ by $x - r$ reduces the degree, and the general Liu–Wang
theorem follows by induction. The Ma–Wang theorem is the case $g = f'$, and the
sequence forms apply the one-step criteria inductively.

## References

L. L. Liu and Y. Wang, [“A unified approach to polynomial sequences with only
real zeros,”](https://doi.org/10.1016/j.aam.2006.02.003) *Advances in Applied
Mathematics* 38 (2007), 542–560, Theorem 2.1.
S.-M. Ma and Y. Wang, [“q-Eulerian polynomials and polynomials with only real
zeros,”](https://doi.org/10.37236/741) *Electronic Journal of Combinatorics*
15 (2008), #R17, Theorem 2.
See also the
[Ma–Wang and Liu–Wang criteria on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#maWangDerivativeCriterion).
<!-- /realrooted-catalog-content -->

The general Liu–Wang theorem lives in `RealRooted.LiuWang.General`, the
derivative-sign criterion in `RealRooted.MaWang.Weak.DerivativeSign`, and the
derivative steps in `RealRooted.MaWang.DerivativeStep` and
`RealRooted.MaWang.StrictStep`.
-/

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

/-- **Liu–Wang criterion for finite sums.**  Let `f` be real-rooted with simple roots and
positive leading coefficient, and let `F = a f + ∑ i ∈ s, b i * g i` have positive leading
coefficient and degree `deg f` or `deg f + 1`.  If every `g i` is an interlacer `g i ≪ f` with
positive leading coefficient and every `b i` is nonpositive at the roots of `f`, then
`f ≪ F`. -/
theorem strictInterl_mul_add_sum_mul_of_eval_nonpos {ι : Type*} {f a : ℝ[X]} {s : Finset ι}
    {b g : ι → ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hf : f.Splits)
    (hf_nodup : f.roots.Nodup) (hg : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hb : ∀ i ∈ s, ∀ r, f.IsRoot r → (b i).eval r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + ∑ i ∈ s, b i * g i))
    (hdeg_lo : f.natDegree ≤ (a * f + ∑ i ∈ s, b i * g i).natDegree)
    (hdeg_hi : (a * f + ∑ i ∈ s, b i * g i).natDegree ≤ f.natDegree + 1) :
    StrictInterl f (a * f + ∑ i ∈ s, b i * g i) := by
  refine strictInterl_of_eval_mul_derivative_nonpos hf_pos hf hf_nodup hF_pos hdeg_lo hdeg_hi
    fun r hr ↦ ?_
  rw [eval_add, eval_mul, hr.eq_zero, mul_zero, zero_add, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_nonpos fun i hi ↦ ?_
  rw [eval_mul, mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg (hb i hi r hr)
    ((hg i hi).eval_mul_eval_derivative_nonneg (hg_pos i hi) hf_pos hr)

/-- **Ma–Wang criterion for derivative recurrences.**  Let
`P (n + 2) = U n * P (n + 1) + V n * (P (n + 1))'`, where every `P n` has positive leading
coefficient and each step keeps or raises the degree by one.  If `P 0 ≪ P 1` and `V n` is
nonpositive at the roots of `P (n + 1)`, then `P n ≪ P (n + 1)` for all `n`. -/
theorem strictInterl_succ_of_derivative_recurrence {P U V : ℕ → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1)) (hpos : ∀ n, HasPosLeadingCoeff (P n))
    (hrec : ∀ n, P (n + 2) = U n * P (n + 1) + V n * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1)
    (hV : ∀ n r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0) :
    ∀ n, StrictInterl (P n) (P (n + 1)) := by
  refine strictInterl_sequence_of_base_and_step hbase fun n hprev ↦ ?_
  have hstep := strictInterl_mul_add_mul_derivative_of_eval_nonpos hprev.2.1.2 (hpos (n + 1))
    (hrec n ▸ hpos (n + 2)) (hrec n ▸ hdeg_lo n) (hrec n ▸ hdeg_hi n) (hV n)
  rwa [← hrec n] at hstep

end MaWangLiuWang
end Challenges
end RealRooted
