import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.ThreeTermRecurrence.LagFeedback
import RealRooted.ThreeTermRecurrence.ParityProduct
import RealRooted.Interlacing.Reversal
import RealRooted.Interlacing.RemainderCertificate
import RealRooted.DerivativeRecurrence.EndpointWindow

/-!
# Recurrence root windows and interlacing

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "recurrence-root-windows"
formalized = "2026-10-01"
authors = ["Liu", "Wang", "Brändén"]
years = [2006, 2007]

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_roots_mem_Icc"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing from a fixed root window"

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_roots_le"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with an upper root bound"

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_roots_mem_Icc_of_degree"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Degree-bounded interlacing in a root window"

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_roots_mem_Icc_mono_div"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with a moving lower bound"

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_roots_le_mono_div"
module = "RealRooted.DerivativeRecurrence.RootWindow"
label = "Interlacing with a moving upper bound"

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_roots_mem_Icc_mono_of_or"
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
name = "RealRooted.eq_parityProduct_of_rec3"
module = "RealRooted.ThreeTermRecurrence.ParityProduct"
label = "Parity products represented by an order-three recurrence"

[[theorems]]
name = "RealRooted.interlaces_of_parityProduct"
module = "RealRooted.ThreeTermRecurrence.ParityProduct"
label = "Interlacing of parity products"

[[theorems]]
name = "RealRooted.eq_reflect_of_derivRec₂"
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
label = "Power-factor rows from a quadratic remainder certificate"

[[theorems]]
name = "RealRooted.Interlaces.pow_mul_of_linear_remainder"
module = "RealRooted.Interlacing.RemainderCertificate"
label = "Power-factor rows from a linear remainder certificate"

[[theorems]]
name = "RealRooted.derivRec_interlaces_of_endpoint_windows"
module = "RealRooted.DerivativeRecurrence.EndpointWindow"
label = "Root windows from endpoint signs only"
-->

<!-- realrooted-catalog-content -->
# Recurrence root windows and interlacing

We study polynomial sequences whose recurrences provide a one-step route to
`Interlaces (P n) (P (n + 1))`. For a first-order derivative recurrence
`P (n + 1) = A n * (P n)' + B n * P n`, we keep the roots in a prescribed
window. On the window containing the roots, the condition `A n ≤ 0` gives the
interlacing step. Sign conditions outside the window move the roots of the next
row into the next window: above an upper bound we use `A n ≥ 0` and `B n > 0`,
and below a lower bound we use `A n ≥ 0` and `B n < 0`. The degree-bounded
variants replace these outside signs with the corresponding logarithmic
derivative inequalities.

We also allow the window to move with `n`. The lower-bound results use a
nonincreasing bound, including the quotient form `p n / q n`; the upper-bound
results use a nondecreasing bound, including the quotient form that covers the
root pattern of A110608. The hypotheses are multiplied through by positive
denominators, so the applications need no quotient inequalities. The most general
form lets both ends move, and at each point beyond either end it accepts either
the sign conditions or the degree-bounded inequality.

For a three-term recurrence
`P (n + 2) = a n * P (n + 1) + b n * P n`, we apply the same window induction
with the sign of `b` on the window and the signs of `a` and `b` outside it. A
ratio barrier handles the case where `b` can have the wrong sign: positivity
of a function `ρ` and the inequality
`a n (x) * ρ x + b n (x) > 0` propagate positivity beyond the upper root
bound, together with the required ratio between consecutive rows.

The lag-feedback results treat
`P (n + p) = α P (n + p - 1) + c n X P n`, with `α > 0` and `c n > 0`.
They keep each window pairwise interlacing and then obtain splitting. For
parity products, we combine two solutions of a three-term recurrence in the
alternating rows `s m * t m` and `s (m + 1) * t m`. A Casoratian compatibility
condition identifies these products with a sequence satisfying an order-three
recurrence, after which interlacing follows from the two input sequences.

For order-three recurrences whose characteristic polynomial is \((\lambda - q)^3\), the rows have
the form \(q^{n-e} R_n\) with \(R_n\) of degree at most two. Dividing \(q R_{n+1}\) by \(R_n\)
leaves a remainder \(\alpha X + \beta\). When \(R_n = aX^2 + bX + c\) with \(a > 0\), the
quotient has positive leading coefficient, \(\alpha < 0\), and
\(a\beta^2 - b\alpha\beta + c\alpha^2 < 0\), the root of the remainder lies between the roots of
\(R_n\), and consecutive rows interlace.

Finally, reversal transfers these arguments through
`X ^ (D₀ + n) * P n (1 / X)`. The reflection link theorems cover both
second-order derivative and three-term recurrences, while the transfer
theorems carry interlacing and splitting back to the original rows. The row
tactics `rr_row_interlaces` and `rr_row_splits` use these routes.

## References

L. L. Liu and Y. Wang, “A unified approach to polynomial sequences with only
real zeros,” *Advances in Applied Mathematics* 38 (2007), 542–560.

P. Brändén, “On linear transformations preserving the Pólya frequency
property,” *Transactions of the American Mathematical Society* 358 (2006).
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.RecurrenceRootWindows

end RealRooted.Challenges.RecurrenceRootWindows
