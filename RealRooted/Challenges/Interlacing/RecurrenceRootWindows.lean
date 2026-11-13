module

import RealRooted.DerivativeRecurrence.EndpointWindow
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.Interlacing.ConstantPrefixFixedDelay
import RealRooted.Interlacing.RemainderCertificate
import RealRooted.Interlacing.Reversal
import RealRooted.Interlacing.VariableDelay
import RealRooted.ProductSequence.BinomialDerivativeFamily
import RealRooted.ProductSequence.Core
import RealRooted.ProductSequence.EndpointPair
import RealRooted.ProductSequence.FactorFamilies
import RealRooted.ProductSequence.FixedDerivative
import RealRooted.ProductSequence.Interlacing
import RealRooted.ProductSequence.Lifts
import RealRooted.ProductSequence.ScalarFamilies
import RealRooted.ThreeTermRecurrence.Coefficients
import RealRooted.ThreeTermRecurrence.LagFeedback
import RealRooted.ThreeTermRecurrence.ParityProduct
import RealRooted.ThreeTermRecurrence.PositiveAffineLag

/-!
# Interlacing for linear recurrences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "recurrence-root-windows"
formalized = "2026-10-01"
tags = []
references = [
  "LiuWang2007",
  "MaWang2008",
  "Fisk2006x",
  "Wagner1992",
  "Branden2006",
]
authors = ["Liu", "Wang", "Ma", "Fisk", "Wagner", "Brändén"]
years = [1992, 2006, 2007, 2008]

[[definitions]]
name = "RealRooted.binomialDerivativeRow"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "The normalized fixed derivatives (r!)⁻¹ D^r (X^r (1 + X)^n)"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Rows of P_{n+1} = A_n P_n′ + B_n P_n interlace if their roots stay in a window"
headline = true

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_le"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with an upper root bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_of_degree"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Degree-bounded interlacing in a root window"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_div"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with a moving lower bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_le_mono_div"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with a moving upper bound"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_roots_mem_Icc_mono_of_or"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Two-sided moving windows, either condition on each side"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Three-term interlacing in a fixed root window"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_le_of_ratio"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Three-term interlacing from a ratio barrier"

[[theorems]]
name = "RealRooted.threeTerm_interlaces_of_roots_mem_Icc_of_barrier"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Three-term interlacing with a barrier"

[[theorems]]
name = "RealRooted.strictInterl_of_lagFeedback"
module = "RealRooted.ThreeTermRecurrence.LagFeedback"
label = "Pairwise interlacing for lag-feedback windows"

[[theorems]]
name = "RealRooted.splits_of_lagFeedback"
module = "RealRooted.ThreeTermRecurrence.LagFeedback"
label = "Splitting for lag-feedback recurrences"

[[theorems]]
name = "RealRooted.eq_parityProduct_of_thirdOrderRecurrence"
module = "RealRooted.ThreeTermRecurrence.ParityProduct"
label = "Parity products represented by an order-three recurrence"

[[theorems]]
name = "RealRooted.interlaces_of_parityProduct"
module = "RealRooted.ThreeTermRecurrence.ParityProduct"
label = "Interlacing of parity products"

[[theorems]]
name = "RealRooted.eq_reflect_of_secondOrderDerivativeRecurrence"
module = "RealRooted.Interlacing.Reversal"
label = "Reflection of a second-order derivative recurrence"

[[theorems]]
name = "RealRooted.eq_reflect_of_threeTerm"
module = "RealRooted.Interlacing.Reversal"
label = "Reflection of a three-term recurrence"

[[theorems]]
name = "RealRooted.interlaces_of_eq_reflect"
module = "RealRooted.Interlacing.Reversal"
label = "Interlacing transferred through reversal"

[[theorems]]
name = "RealRooted.splits_of_eq_reflect"
module = "RealRooted.Interlacing.Reversal"
label = "Splitting transferred through reversal"

[[theorems]]
name = "RealRooted.strictInterl_quadratic_of_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Interlacing from a quadratic division remainder"

[[theorems]]
name = "RealRooted.strictInterl_linear_of_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Interlacing from a linear division remainder"

[[theorems]]
name = "RealRooted.Interlaces.pow_mul_of_quadratic_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Power-factor rows from a quadratic remainder criterion"

[[theorems]]
name = "RealRooted.Interlaces.pow_mul_of_linear_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Power-factor rows from a linear remainder criterion"

[[theorems]]
name = "RealRooted.derivativeRecurrence_interlaces_of_endpoint_windows"
module = "RealRooted.DerivativeRecurrence.EndpointWindow"
label = "Interlacing when each next row has its roots in the next window"

[[theorems]]
name = "RealRooted.splits_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Variable-delay recurrences have real-rooted rows"

[[theorems]]
name = "RealRooted.strictInterl_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Row i interlaces row n whenever p(n) ≤ i ≤ n"

[[theorems]]
name = "RealRooted.hasNonnegCoeffs_of_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Variable-delay rows have nonnegative coefficients"

[[theorems]]
name = "RealRooted.strictInterl_of_scaled_variableDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "The same interlacing for the scaled recurrence a(n+1) F(n) + b(n+1) X F(p(n+1))"

[[theorems]]
name = "RealRooted.strictInterl_of_fixedDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Fixed delay L: rows A and B interlace when A ≤ B ≤ A + L"

[[theorems]]
name = "RealRooted.strictInterl_of_scaled_fixedDelay_recurrence"
module = "RealRooted.Interlacing.VariableDelay"
label = "Scaled fixed delay L: rows A and B interlace when A ≤ B ≤ A + L"

[[theorems]]
name = "RealRooted.strictInterl_of_constant_prefix_fixed_delay_recurrence"
module = "RealRooted.Interlacing.ConstantPrefixFixedDelay"
label = "Fixed-delay recurrences started from a constant prefix: interlacing of rows"

[[theorems]]
name = "RealRooted.roots_neg_of_constant_prefix_fixed_delay_recurrence"
module = "RealRooted.Interlacing.ConstantPrefixFixedDelay"
label = "Constant-prefix rows have only negative roots"

[[theorems]]
name = "RealRooted.natDegree_of_constant_prefix_fixed_delay_recurrence"
module = "RealRooted.Interlacing.ConstantPrefixFixedDelay"
label = "Constant-prefix rows have degree n / L"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_factor_sequence"
module = "RealRooted.ProductSequence.Core"
label = "Products of real-rooted factors are real-rooted"

[[theorems]]
name = "RealRooted.productSequence_interlaces"
module = "RealRooted.ProductSequence.Interlacing"
label = "Multiplying by linear factors gives consecutive interlacing"

[[theorems]]
name = "RealRooted.productSequence_natDegree"
module = "RealRooted.ProductSequence.Interlacing"
label = "Degree growth of a product sequence"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_affine_sequence"
module = "RealRooted.ProductSequence.FactorFamilies"
label = "Affine-factor product closure"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_X_add_C_pow_sequence"
module = "RealRooted.ProductSequence.FactorFamilies"
label = "Powered affine product closure"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_lift_sequence"
module = "RealRooted.ProductSequence.Lifts"
label = "Row-wise product lifts"

[[theorems]]
name = "RealRooted.isRealRooted_of_scalar_monomial_lift_sequence"
module = "RealRooted.ProductSequence.Lifts"
label = "Scalar-monomial lifts"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_scalar_linear_sequence"
module = "RealRooted.ProductSequence.ScalarFamilies"
label = "Alternating scalar-linear closure"

[[theorems]]
name = "RealRooted.isRealRooted_of_product_scalar_X_add_C_pow_sequence"
module = "RealRooted.ProductSequence.ScalarFamilies"
label = "Alternating powered-affine closure"

[[theorems]]
name = "RealRooted.strictInterl_endpoint_sum_then_X_pair_sequence"
module = "RealRooted.ProductSequence.EndpointPair"
label = "Endpoint-pair strict interlacing"

[[theorems]]
name = "RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_sequence"
module = "RealRooted.ProductSequence.EndpointPair"
label = "Endpoint-pair real-rootedness"

[[theorems]]
name = "RealRooted.isRealRooted_of_endpoint_sum_then_X_pair_lift_sequence"
module = "RealRooted.ProductSequence.EndpointPair"
label = "Endpoint-power pair lift"

[[theorems]]
name = "RealRooted.interlaces_self_mul_of_natDegree_eq_one"
module = "RealRooted.ProductSequence.Interlacing"
label = "Interlacing after one linear factor"

[[theorems]]
name = "RealRooted.isRealRooted_finset_prod_X_sub_C"
module = "RealRooted.ProductSequence.Core"
label = "Finite products of linear factors"

[[theorems]]
name = "RealRooted.finiteLinearProductSequence_realRooted"
module = "RealRooted.ProductSequence.Core"
label = "Finite linear product sequences"

[[theorems]]
name = "RealRooted.strictInterl_iterate_derivative_mul_X_sub_C_pow_succ"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "Fixed derivatives of q (X - a)^n and q (X - a)^(n+1) interlace"

[[theorems]]
name = "RealRooted.iterate_derivative_mul_X_sub_C_pow_standard"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "Fixed derivatives of q (X - a)^n are real-rooted with positive leading coefficient"

[[theorems]]
name = "RealRooted.roots_iterate_derivative_mul_X_sub_C_pow_mem_Icc"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "Fixed derivatives have roots in any interval containing a and the roots of q"

[[theorems]]
name = "RealRooted.sum_pow_mul_iterate_derivative_mul_X_sub_C_pow_eq_zero"
module = "RealRooted.ProductSequence.FixedDerivative"
label = "A pure-lag recurrence for fixed derivatives of q (X - a)^n"

[[theorems]]
name = "RealRooted.coeff_binomialDerivativeRow"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "Binomial derivative rows: the coefficients are C(n, k) C(k + r, r)"

[[theorems]]
name = "RealRooted.binomialDerivativeRow_add_two"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "Binomial derivative rows: a three-term recurrence in n"

[[theorems]]
name = "RealRooted.strictInterl_binomialDerivativeRow_succ"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "Consecutive binomial derivative rows interlace"

[[theorems]]
name = "RealRooted.roots_binomialDerivativeRow_mem_Icc"
module = "RealRooted.ProductSequence.BinomialDerivativeFamily"
label = "Binomial derivative rows have roots in [-1, 0]"

[[theorems]]
name = "RealRooted.hasNonnegCoeffs_and_sub_mul_of_threeTerm"
module = "RealRooted.ThreeTermRecurrence.Coefficients"
label = "Coefficient positivity of a three-term recurrence through weighted differences"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.PositiveAffineLag.coefficients_and_degree"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "Positive affine lags: nonnegative coefficients and successive differences"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.PositiveAffineLag.interlacing_and_roots"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "Positive affine lags: rows interlace, with simple negative roots"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.PositiveAffineLag.ratio_interlacing_and_roots"
module = "RealRooted.ThreeTermRecurrence.PositiveAffineLag"
label = "Positive affine lags: the same conclusions under weaker ratio hypotheses"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Interlacing for linear recurrences

Consecutive rows of a linear recurrence interlace when their roots stay in a window on which the
coefficient of the derivative, or of the older row, is nonpositive, and the signs outside the
window keep the next row's roots inside. Three-term, lag, delay and product recurrences are
variants of this principle.

## Results

In the window theorems, $P_n$ are real polynomials with $\deg P_n=D_0+n$ and positive leading
coefficient, and $A_n,B_n,a_n,b_n$ are real polynomials; a sign condition on a set holds at
every point of the set. When $D_0=0$ we also assume $P_0\ll P_1$.

**Theorem (root window).** Let $P_{n+1}=A_nP_n'+B_nP_n$ and $L\le U$. Suppose that all roots of
$P_0$ are real and lie in $[L,U]$, and that for every $n$

- $A_n\le0$ on $[L,U]$, and
- $A_n\ge0$ outside $[L,U]$, with $B_n>0$ on $(U,\infty)$ and $B_n<0$ on $(-\infty,L)$.

Then $P_n\ll P_{n+1}$ for all $n$. The same holds with no lower bound: all roots of $P_0$ are at
most $U$, $A_n\le0$ on $(-\infty,U]$, and $A_n\ge0$, $B_n>0$ on $(U,\infty)$.

**Theorem (three-term recurrences).** Let $P_{n+2}=a_nP_{n+1}+b_nP_n$ with $P_0\ll P_1$, all
roots of $P_0$ and $P_1$ in $[L,U]$, and for all $n$: $b_n\le0$ on $[L,U]$; $a_n>0$ and
$b_n\ge0$ on $(U,\infty)$; $a_n<0$ and $b_n\ge0$ on $(-\infty,L)$. Then $P_n\ll P_{n+1}$ for
all $n$.

**Theorem (delay recurrences).** Let $p:\mathbb N\to\mathbb N$ be weakly increasing on
$n\ge1$ with $p(n)<n$, let $w(n)\ge0$, $Q_0=1$ and
$$
Q_{n+1}=Q_n+w(n+1)\,x\,Q_{p(n+1)}.
$$
Then every $Q_n$ has nonnegative coefficients and is real-rooted, and $Q_i\ll Q_n$ whenever
$p(n)\le i\le n$. The same holds for $F_{n+1}=a(n+1)F_n+b(n+1)\,x\,F_{p(n+1)}$ with $F_0=1$,
$a(n)>0$ and $b(n)\ge0$.

The following variants also hold.

- *Moving windows*: windows $[L_n,U_n]$ with $L_n$ nonincreasing and $U_n$ nondecreasing, and
  the weaker outside condition $B_n(x)(x-U)+\min(A_n(x),0)(D_0+n)>0$ for $x>U$ (and its mirror
  image below $L$).
- *Endpoint windows*: for any sets $W_n$ with $A_n\le0$ on $W_n$, it suffices that each new
  row has its roots in $W_{n+1}$; this is a form of [@MaWang2008, Theorem 2].
- *Three-term variants* that allow $b_n<0$ beyond $U$, through a ratio bound on the leading
  coefficients or a barrier function.
- *Positive affine lags*: if $0<P_0\le P_1$ are constants, $b_n,c_n\ge0$, $d_n>0$ and
  $P_{n+2}=(1+b_n+c_n)P_{n+1}+(d_nx-b_n)P_n$, then $P_n$ has degree $\lfloor n/2\rfloor$,
  nonnegative coefficients and simple negative roots, and $P_n\ll P_{n+1}$ with no common root.
- *Fixed delays*: for $Q_{n+1}=Q_n+w(n+1)\,x\,Q_{\max(n+1-L,0)}$, and for
  $P_{n+L}=a_nP_{n+L-1}+b_nxP_n$ started from $L$ positive constants, $P_A\ll P_B$ whenever
  $A\le B\le A+L$. The lag recurrences $P_{n+p}=\alpha P_{n+p-1}+c_nxP_n$ are of this form.
- *Parity products*: if $s_m\ll s_{m+1}$ and $t_m\ll t_{m+1}$ both satisfy
  $x_{m+2}=\beta x_{m+1}-\mu^2x_m$, then the products $s_0t_0,\ s_1t_0,\ s_1t_1,\ s_2t_1,\dots$
  satisfy one third-order recurrence and consecutive ones interlace.
- *Products*: if $P_{n+1}=F_nP_n$ with real-rooted factors, then every $P_n$ is real-rooted, and
  $P_n\ll P_{n+1}$ when every $F_n$ is linear. For real-rooted $q$ with positive leading
  coefficient and $r\le\deg q$,
  $D^r\bigl(q(x-a)^n\bigr)\ll D^r\bigl(q(x-a)^{n+1}\bigr)$; for instance the rows
  $\frac1{r!}D^r\bigl(x^r(1+x)^n\bigr)=\sum_k\binom nk\binom{k+r}rx^k$ interlace, with roots in
  $[-1,0]$.
- *Reversal*: real-rootedness and interlacing pass to the reversals $x^{D_0+n}R_n(1/x)$, with
  explicit reversed recurrences.
- *Division remainders*: if $R=ax^2+bx+c$ with $a>0$ and $S=R\,(px+d)+\alpha x+\beta$ with
  $p>0$, $\alpha<0$ and $a\beta^2-b\alpha\beta+c\alpha^2<0$, then $R\ll S$.

## Proof

Each step is the [Liu–Wang or Ma–Wang criterion](rr:ma-wang-liu-wang): if the roots of $P_n$
lie in the window, then $A_n\le0$ at these roots gives $P_n\ll P_{n+1}$. Beyond the window
$P_n$ and $P_n'$ have constant signs, and the sign conditions on $A_n$ and $B_n$ make
$P_{n+1}$ nonzero there, so its roots stay in the window. The delay recurrences follow
the induction of [@Fisk2006x, Example 16.10] with the interlacing cone rules of
[@Wagner1992, Section 3], and for positive affine lags $P_{n+1}-P_n$ has nonnegative
coefficients, so the Liu–Wang criterion applies [@LiuWang2007].

## References

- [@LiuWang2007]
- [@MaWang2008, Theorem 2]
- [@Fisk2006x, Example 16.10]
- [@Wagner1992, Section 3]
- [@Branden2006]
<!-- /realrooted-catalog-content -->
-/
