module

public import RealRooted.CombinatorialExamples.ColoredSetPartitions
public import RealRooted.CombinatorialExamples.Motzkin
public import RealRooted.CombinatorialExamples.PathPowerIndependence
public import RealRooted.CombinatorialExamples.Simsun
public import RealRooted.CombinatorialExamples.SingletonFreeSetPartitions
public import RealRooted.CombinatorialExamples.StirlingPermutations
public import RealRooted.CombinatorialExamples.SturmDerangementsExc
public import RealRooted.CombinatorialExamples.Touchard
public import RealRooted.LiuWang.CombinedFlux
public import RealRooted.LiuWang.Criterion
public import RealRooted.LiuWang.SequenceCore
public import RealRooted.LiuWangRecursion
public import RealRooted.MaWang.DerivativeSequence
public import RealRooted.MaWang.DerivativeStep
public import RealRooted.MaWang.StrictStep
public import RealRooted.ThreeTermRecurrence.PositiveAffineLag

/-!
# Liu–Wang and Ma–Wang interlacing criteria

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "ma-wang-liu-wang"
formalized = "2026-10-06"
references = [
  "LiuWang2007",
  "MaWang2008",
  "GesselStanley1978",
  "MantaciRakotondrajao2003",
  "Bona2009",
  "ChowShiu2011",
  "Wang2014",
  "BonaHezo2016",
]
authors = ["Liu", "Wang", "Ma"]
years = [2007, 2008]

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_mul_add_mul_of_eval_nonpos"
module = "RealRooted.LiuWang.Criterion"
label = "Liu–Wang: f ≪ af + bg when g ≪ f and b ≤ 0 at the roots of f"
headline = true

[[theorems]]
name = "RealRooted.MaWang.strictInterl_derivative_of_nonpos_of_splits"
module = "RealRooted.MaWang.DerivativeStep"
label = "Ma–Wang: f ≪ uf + vf′ when v ≤ 0 at the roots of f"
symcat = "maWangDerivativeCriterion"

[[theorems]]
name = "RealRooted.MaWang.strictInterl_and_hasSimpleRoots_of_eval_neg"
module = "RealRooted.MaWang.StrictStep"
label = "Ma–Wang, strict form: v < 0 at the roots keeps the roots simple"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_mul_add_sum_mul_of_combined_flux_of_pos"
module = "RealRooted.LiuWang.CombinedFlux"
label = "Common generalization for finite sums af + Σ bᵢgᵢ"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_succ_of_recurrence_of_eval_nonpos"
module = "RealRooted.LiuWang.SequenceCore"
label = "Rows of P(n+2) = A P(n+1) + B P(n) interlace when B ≤ 0 at the roots of P(n+1)"

[[theorems]]
name = "RealRooted.MaWang.strictInterl_derivative_nonpos_sequence"
module = "RealRooted.MaWang.DerivativeSequence"
label = "Rows of P(n+1) = U P(n) + V P(n)′ interlace when V ≤ 0 at the roots of P(n)"

[[theorems]]
name = "RealRooted.LiuWang.strictInterl_sequence_of_derivative_lag"
module = "RealRooted.LiuWangRecursion"
label = "Rows of P(n+2) = U P(n+1) + V P(n+1)′ + W P(n) interlace when V, W ≤ 0 there"

[[theorems]]
name = "RealRooted.PositiveAffineLag.interlacing_and_roots"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "Positive affine lags: rows interlace, with simple negative roots"

[[theorems]]
objects = ["Touchard polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_touchard_succ"
module = "RealRooted.CombinatorialExamples.Touchard"
label = "Consecutive Touchard polynomials interlace"
symcat = "touchardPolynomial"

[[theorems]]
objects = ["Stirling-permutation descent polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_stirlingPermutations_succ"
module = "RealRooted.CombinatorialExamples.StirlingPermutations"
label = "Consecutive Stirling-permutation descent polynomials interlace"

[[theorems]]
objects = ["Derangement polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_sturmDerangementsExc_succ"
module = "RealRooted.CombinatorialExamples.SturmDerangementsExc"
label = "Consecutive derangement polynomials interlace"
symcat = "derangementPolynomial"

[[theorems]]
objects = ["Simsun polynomials"]
property = "interlacing"
name = "RealRooted.strictInterl_simsun_succ"
module = "RealRooted.CombinatorialExamples.Simsun"
label = "Consecutive simsun polynomials interlace"

[[theorems]]
objects = ["Singleton-free set-partition polynomials"]
property = "interlacing"
name = "RealRooted.strictInterl_singletonFreeSetPartitions_succ"
module = "RealRooted.CombinatorialExamples.SingletonFreeSetPartitions"
label = "Consecutive singleton-free set-partition polynomials interlace"

[[theorems]]
objects = ["Colored set-partition polynomials"]
property = "interlacing"
name = "RealRooted.interlaces_coloredSetPartitions_succ"
module = "RealRooted.CombinatorialExamples.ColoredSetPartitions"
label = "Consecutive colored set-partition polynomials interlace"

[[theorems]]
objects = ["Motzkin polynomials"]
name = "RealRooted.isRealRooted_motzkin"
module = "RealRooted.CombinatorialExamples.Motzkin"
label = "Motzkin polynomials are real-rooted"

[[theorems]]
objects = ["Motzkin polynomials"]
property = "interlacing"
name = "RealRooted.strictInterl_motzkin_succ"
module = "RealRooted.CombinatorialExamples.Motzkin"
label = "Consecutive Motzkin polynomials interlace"

[[theorems]]
objects = ["Independence polynomials of path powers"]
name = "RealRooted.splits_sum_choose_sub_mul"
module = "RealRooted.CombinatorialExamples.PathPowerIndependence"
label = "Independence polynomials of path powers ∑ C(m − rk, k) xᵏ are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Liu–Wang and Ma–Wang interlacing criteria

If $g$ interlaces $f$, then $f$ interlaces $af+bg$ whenever $b$ is nonpositive at the roots of
$f$. Applied to consecutive rows of a recurrence, this criterion and its derivative form, due to
L. L. Liu and Y. Wang and to S.-M. Ma and Y. Wang, prove that the Touchard, Stirling-permutation,
derangement and many other combinatorial polynomials form interlacing sequences.

## Results

A polynomial is *positive* if its leading coefficient is positive. The conclusion $f\ll F$
includes that $F$ is real-rooted.

**Theorem (Liu–Wang).** [@LiuWang2007, Thm. 2.1] Let $f,g,a,b\in\mathbb R[x]$ and $F=af+bg$.
Suppose that $g\ll f$, that $g$ and $F$ are positive, and that
$\deg f\le\deg F\le\deg f+1$. If $b(r)\le0$ at every real root $r$ of $f$, then $f\ll F$.

**Theorem (Ma–Wang).** [@MaWang2008, Thm. 2] Let $f,u,v\in\mathbb R[x]$ and $F=uf+vf'$. Suppose
that $f$ is real-rooted, that $f$ and $F$ are positive, and that $\deg f\le\deg F\le\deg f+1$.
If $v(r)\le0$ at every root $r$ of $f$, then $f\ll F$. If moreover $f$ is nonconstant with
simple roots, $\deg F=\deg f+1$ and $v(r)<0$ at every root, then $F$ has simple roots.

Both are special cases of one statement for $F=af+\sum_ib_ig_i$ with finitely many positive
$g_i\ll f$.

**Theorem (recurrences).** Let $(P_n)_{n\ge0}$ be positive with $P_0\ll P_1$ and
$\deg P_{n+1}\le\deg P_{n+2}\le\deg P_{n+1}+1$ for all $n$. In each of the following cases
$P_n\ll P_{n+1}$ for all $n$, so every $P_n$ is real-rooted:

- $P_{n+2}=A_nP_{n+1}+B_nP_n$ with $B_n\le0$ at the roots of $P_{n+1}$;
- $P_{n+2}=U_nP_{n+1}+V_nP_{n+1}'$ with $V_n\le0$ at the roots of $P_{n+1}$;
- $P_{n+2}=U_nP_{n+1}+V_nP_{n+1}'+W_nP_n$ with $V_n,W_n\le0$ at the roots of $P_{n+1}$.

For example, if $0<P_0\le P_1$ are constants, $b_n,c_n\ge0$, $d_n>0$ and
$P_{n+2}=(1+b_n+c_n)P_{n+1}+(d_nx-b_n)P_n$, then $P_n$ has degree $\lfloor n/2\rfloor$ and simple
negative roots, and $P_n\ll P_{n+1}$.

**Corollary (families).** Consecutive rows interlace for each of the following recurrences:

- Touchard polynomials: $T_0=1$, $T_{n+1}=xT_n+xT_n'$;
- descent polynomials of Stirling permutations: $P_0=1$, $P_{n+1}=(2n+1)xP_n+x(1-x)P_n'$;
- derangement polynomials (excedances): $P_0=P_1=0$, $P_2=x$,
  $P_{n+3}=x\bigl((n+2)P_{n+1}+(n+2)P_{n+2}+(1-x)P_{n+2}'\bigr)$, from $n=2$;
- simsun polynomials: $P_0=1$, $P_{n+1}=(1+nx)P_n+x(1-2x)P_n'$;
- singleton-free set partitions: $D_0=1$, $D_1=0$, $D_{n+2}=x\bigl((n+1)D_n+D_{n+1}'\bigr)$,
  from $n=2$;
- colored set partitions, for natural numbers $c,m$: $T_0=1$, $T_{n+1}=(x+c)T_n+mxT_n'$;
- Motzkin polynomials $M_k=\sum_a\binom k{2a}\mathrm{Cat}_a\,x^a$, $k\ge1$, which satisfy
  $(k+2)M_k=(2k+1)M_{k-1}+(k-1)(4x-1)M_{k-2}$.

**Corollary (path powers).** For all natural numbers $r,m$ the polynomial
$\sum_k\binom{m-rk}{k}x^k$ is real-rooted. For $r\le m$ it is the independence polynomial of the
$r$th power of a path, a claw-free graph, so this also follows from the
[Chudnovsky–Seymour theorem](rr:chudnovsky-seymour).

## Use

These criteria are the standard route from a recurrence to interlacing. For a first-order
recurrence $P_{n+1}=uP_n+vP_n'$ with nonnegative coefficients, the roots of $P_n$ are
nonpositive, so it suffices that $v\le0$ on $(-\infty,0]$. Recurrences whose roots stay in a
window are treated on the [root-window page](rr:recurrence-root-windows).

## Proof

At a root $r$ of $f$ we have $F(r)=b(r)g(r)$, and $g(r)f'(r)\ge0$ because $g\ll f$. Hence
$F(r)f'(r)\le0$, so $F$ changes sign between consecutive roots of $f$, and the degree condition
places the last root of $F$ to the right of the roots of $f$. The Ma–Wang theorem is the same
argument with $g=f'$. For the families, the coefficients of $P_n'$ and of the earlier row are
nonpositive at the nonpositive roots of $P_n$.

## References

[@LiuWang2007, Thm. 2.1]; [@MaWang2008, Thm. 2]. The families are from
[@GesselStanley1978; @MantaciRakotondrajao2003; @Bona2009; @ChowShiu2011; @Wang2014;
@BonaHezo2016]. See also the [Ma–Wang criterion](sf:maWangDerivativeCriterion), the
[Touchard polynomials](sf:touchardPolynomial), the
[derangement polynomials](sf:derangementPolynomial) and the
[Motzkin-polynomial theorem](sf:motzkinPolynomialsRealRooted) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
