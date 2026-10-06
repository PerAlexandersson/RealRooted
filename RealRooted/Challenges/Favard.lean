import RealRooted.Favard
import RealRooted.Favard.Orthogonality

/-!
# Favard challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "favard"
authors = ["Favard"]
years = [1935]

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence"
module = "RealRooted.Favard.Recurrence"
label = "Favard three-term recurrence"

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence.functional"
module = "RealRooted.Favard.Orthogonality"
label = "The normalized moment functional"

[[definitions]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing"
module = "RealRooted.Favard.Orthogonality"
label = "The pairing ⟨p, q⟩ = L(pq)"

[[theorems]]
name = "RealRooted.Challenges.Favard.SatisfiesFavardRecurrence.strictInterl_succ"
label = "Consecutive polynomials interlace"

[[theorems]]
name = "RealRooted.Challenges.Favard.SatisfiesFavardRecurrence.ne_zero_and_splits"
label = "Favard polynomials are real-rooted"

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing_iIsOrtho"
module = "RealRooted.Favard.Orthogonality"
label = "Favard’s theorem: the polynomials are orthogonal"
headline = true

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.pairing_posDef"
module = "RealRooted.Favard.Orthogonality"
label = "Positive coefficients make the pairing positive definite"

[[theorems]]
name = "RealRooted.SatisfiesFavardRecurrence.linearMap_eq_smul_functional"
module = "RealRooted.Favard.Orthogonality"
label = "The orthogonalizing functional is unique up to scaling"
-->

<!-- realrooted-catalog-content -->
# Favard recurrences

Let $P_0 = 1$, $P_1 = x - \alpha_0$ and
$$
P_{n+2} = (x - \alpha_{n+1}) P_{n+1} - \beta_{n+1} P_n .
$$
If every $\beta_{n+1}$ is positive, the real polynomials $P_n$ are nonzero and
real-rooted, and consecutive polynomials interlace.

**Favard’s theorem.** Over an integral domain $R$, the monic polynomials $P_n$
form a basis of $R[x]$. Let $L$ be the linear functional that extracts the
coefficient of $P_0$ in this basis, and let $\langle p, q \rangle = L(pq)$.

- The family is orthogonal: $\langle P_m, P_n \rangle = 0$ for $m \ne n$.
- A linear functional $L'$ with $L'(P_n) = 0$ for all $n \ne 0$ equals
  $L'(1) \cdot L$, so $L$ is unique up to scaling.
- Over an ordered ring, if every $\beta_{n+1}$ is positive, the pairing is
  positive definite: $\langle p, p \rangle > 0$ for all $p \ne 0$.

## References

J. Favard, “Sur les polynômes de Tchebicheff,” *Comptes rendus de l’Académie
des sciences* 200 (1935), 2052–2053.  See also the
[interlacing overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#favardInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#favardInterlacing

Original publication: J. Favard, "Sur les polynomes de Tchebicheff",
C. R. Acad. Sci. Paris 200 (1935), 2052--2053.

This module exposes the checked root-theoretic Favard recurrence theorem. The
ring-generic normalized functional and orthogonality theory live in
`RealRooted.Favard.Orthogonality`; concrete integral realizations remain in
analytic classical-family child modules.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Favard

/-- Favard recurrence coefficients force consecutive interlacing. -/
theorem SatisfiesFavardRecurrence.strictInterl_succ {P : ℕ → ℝ[X]} {α β : ℕ → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β) (hβ : ∀ n, 0 < β (n + 1)) (n : ℕ) :
    StrictInterl (P n) (P (n + 1)) :=
  RealRooted.favardInterlacing hrec hβ n

/-- Favard recurrence coefficients force real-rootedness of every polynomial
in the sequence. -/
theorem SatisfiesFavardRecurrence.ne_zero_and_splits {P : ℕ → ℝ[X]} {α β : ℕ → ℝ}
    (hrec : SatisfiesFavardRecurrence P α β) (hβ : ∀ n, 0 < β (n + 1)) (n : ℕ) :
    P n ≠ 0 ∧ (P n).Splits :=
  RealRooted.isRealRooted_of_favard hrec hβ n

end Favard
end Challenges
end RealRooted
