import RealRooted.IteratedDerivativeShift
import RealRooted.Tactic.IteratedDerivativeShift
import RealRooted.Tactic.IteratedDerivativeShiftProduct

/-!
# Iterated derivative shifts

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "iterated-derivative-shift"
formalized = "2026-10-05"

[[theorems]]
name = "RealRooted.splits_tDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Positive shifts preserve splitness"

[[theorems]]
name = "RealRooted.splits_tDeriv_all"
module = "RealRooted.IteratedDerivativeShift"
label = "All real shifts preserve splitness"
headline = true

[[theorems]]
name = "RealRooted.strictInterl_tDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Positive shifts give strict interlacing"
headline = true

[[theorems]]
name = "RealRooted.derivative_strictInterl_tDeriv_of_nonpos"
module = "RealRooted.IteratedDerivativeShift"
label = "Nonpositive shifts from the derivative"

[[theorems]]
name = "RealRooted.derivative_strictInterl_tDeriv_of_nonpos_of_common_factor"
module = "RealRooted.IteratedDerivativeShift"
label = "Common-factor derivative interlacing"

[[theorems]]
name = "RealRooted.hasSimpleRoots_iterateTDeriv_of_natDegree"
module = "RealRooted.IteratedDerivativeShift"
label = "Simple roots after degree-many shifts"

[[theorems]]
name = "RealRooted.hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le"
module = "RealRooted.IteratedDerivativeShift"
label = "Simple roots after enough negative shifts"

[[theorems]]
name = "RealRooted.exists_delta_and_real_root_near_iterateTDeriv"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots for monic regularizations"

[[theorems]]
name = "RealRooted.exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots after normalization"

[[theorems]]
name = "RealRooted.exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted_iterate_derivative"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots in a derivative tower"

[[theorems]]
name = "RealRooted.exists_delta_and_real_root_near_iterateTDeriv_of_lt_rootMultiplicity"
module = "RealRooted.IteratedDerivativeShift"
label = "Nearby roots from multiplicity"

[[theorems]]
name = "RealRooted.Tactic.iterateTDeriv_sequence_splits"
module = "RealRooted.Tactic.IteratedDerivativeShift"
label = "Sequence iterates preserve splitness"

[[theorems]]
name = "RealRooted.Tactic.iterateTDeriv_sequence_strictInterl_succ"
module = "RealRooted.Tactic.IteratedDerivativeShift"
label = "Sequence iterates strictly interlace"

[[theorems]]
name = "RealRooted.isRealRooted_iterateTDeriv"
module = "RealRooted.Tactic.IteratedDerivativeShiftProduct"
label = "An iterate remains real-rooted"

[[theorems]]
name = "RealRooted.isRealRooted_of_iteratedTDeriv_product_sequence"
module = "RealRooted.Tactic.IteratedDerivativeShiftProduct"
label = "Left-factor product recurrence"

[[theorems]]
name = "RealRooted.isRealRooted_of_iteratedTDeriv_product_right_sequence"
module = "RealRooted.Tactic.IteratedDerivativeShiftProduct"
label = "Right-factor product recurrence"
-->

<!-- realrooted-catalog-content -->
# Iterated derivative shifts

We study the derivative-shift operator $T_\varepsilon p = p - \varepsilon p'$
and its iterates. If $p$ is split, then a positive shift preserves splitness,
and the same is true for every real shift. For a positive shift and a nonzero
split polynomial, $p$ strictly interlaces $T_\varepsilon p$.

We also record the two interlacing directions used by derivative arguments. For
a split polynomial with positive leading coefficient and positive degree, a
nonpositive shift places $p'$ before $T_\varepsilon p$. A common-factor
version removes the leading-coefficient assumption on $p$ when $p$ and
$p'$ are represented using a shared factor and an interlacing quotient pair.

We obtain split polynomials for positive or arbitrary real shifts, and
successive positive iterates strictly interlace when the starting polynomial is
nonzero and split. If $f$ is nonzero and split with degree $n$, then
$T_\varepsilon^n f$ has simple roots for $\varepsilon > 0$. The analogous
negative-shift statement holds after at least $\deg p$ iterations.

We use the continuity results to make the regularization usable near a prescribed root.
For a monic split polynomial, each real root has a nearby root of
$T_\varepsilon^n p$ for sufficiently small positive $\varepsilon$. A
nonzero split polynomial is reduced to the monic case by scaling; the same
argument applies to roots in an iterated derivative, and hence to any root
whose multiplicity is larger than the derivative order.

Finally, the sequence adapters apply the preservation and strict-interlacing
results pointwise to varying shifts and iteration depths. The product results
show that a recurrence $P_{n+1}=F_n T_{\varepsilon_n}^{k_n}P_n$, with a
nonzero split base and nonzero split factors, keeps every row nonzero and
split; the factor may occur on either side of the iterate.

## References

That `p ↦ p - ε p'` preserves real-rootedness is a classical fact going back to Laguerre; for the
general theory of such preservers see G. Pólya and J. Schur, “Über zwei Arten von Faktorenfolgen in
der Theorie der algebraischen Gleichungen,” *J. Reine Angew. Math.* 144 (1914), 89–113. The
iterated regularization is used in the converse of Obreschkoff's theorem: N. Obreschkoff,
*Verteilung und Berechnung der Nullstellen reeller Polynome*, VEB Deutscher Verlag der
Wissenschaften, 1963.
<!-- /realrooted-catalog-content -->
-/

namespace RealRooted.Challenges.IteratedDerivativeShift

end RealRooted.Challenges.IteratedDerivativeShift
