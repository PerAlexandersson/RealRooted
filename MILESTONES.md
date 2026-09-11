# Formalization milestones

A curated guide to major theorems, not a count of helper lemmas.

**Reading the status:** “Proved” means the stated theorem has a Lean witness;
its mathematical hypotheses still apply. “Conditional” means an explicit external
model identity or other unformalized input remains. An open target has no witness.
The scope notes are part of the claim, not fine print.

This generated source catalog is not a live CI badge. The `milestone-audit` CI
artifact records a transitive-axiom audit for one exact Git revision. Only a
successful full build followed by that audit validates that revision. The separate
Comparator workflow independently rechecks only its configured theorem list;
catalog membership does not imply independent-comparator coverage.

Source of truth: [milestones.json](milestones.json). Regenerate with
`python3 scripts/check_milestones.py --write`.

## Cauchy eigenvalue interlacing

Status: Proved theorem

Delete one row and the matching column from a real symmetric or complex Hermitian matrix. The smaller matrix's eigenvalues lie between those of the original.

Scope: All finite sizes, under the Hermitian hypothesis; the formal statement uses ordered eigenvalues.

- Lean theorem: [RealRooted.Challenges.CauchyInterlacing.principalSubmatrix_eigenvalues_interlace](RealRooted/Challenges/CauchyInterlacing.lean)

## Favard recurrences produce real roots

Status: Proved theorem

A monic three-term recurrence with positive Favard coefficients produces nonzero polynomials with only real roots.

Scope: The standard recurrence and positive coefficients are mathematical hypotheses. This entry covers roots, not existence of an orthogonality measure.

- Lean theorem: [RealRooted.Challenges.Favard.realRooted](RealRooted/Challenges/Favard.lean)
- Lean theorem: [RealRooted.Challenges.Favard.interlacing](RealRooted/Challenges/Favard.lean)

## Aissen–Schoenberg–Whitney: roots and total positivity

Status: Proved theorem

The finite-polynomial correspondence connects nonpositive real roots with nonnegativity of every minor of the coefficient Toeplitz matrix.

Scope: The reverse direction assumes nonnegative coefficients; both directions use the repository's real-rooted/zero conventions. This is a polynomial theorem, not the classification of arbitrary infinite generating functions.

- Lean theorem: [RealRooted.Challenges.AissenSchoenbergWhitney.forwardTheorem](RealRooted/Challenges/AissenSchoenbergWhitney.lean)
- Lean theorem: [RealRooted.Challenges.AissenSchoenbergWhitney.reverseTheorem](RealRooted/Challenges/AissenSchoenbergWhitney.lean)

## Obreschkoff: interlacing and real polynomial pencils

Status: Proved theorem

Interlacing guarantees that every real linear combination has only real roots or is zero. Conversely, this pencil property forces interlacing up to orientation.

Scope: The converse witness explicitly assumes nonzero split inputs and equal or consecutive degrees. The catalog does not omit these degree and orientation conventions.

- Lean theorem: [RealRooted.Challenges.Obreschkoff.allCombinationsRealRooted_of_interlaces](RealRooted/Challenges/Obreschkoff.lean)
- Lean theorem: [RealRooted.Challenges.Obreschkoff.interlaces_or_reverse_of_allCombinationsRealRooted](RealRooted/Challenges/Obreschkoff.lean)

## Claw-free graph independence polynomials

Status: Proved theorem

For every finite claw-free graph, the polynomial counting independent vertex sets by size has only real roots.

Scope: The graph must be claw-free: no induced vertex with three pairwise nonadjacent neighbors. The graph and its independence polynomial are formalized objects.

- Lean theorem: [RealRooted.Challenges.ChudnovskySeymour.clawFree_indepPoly_splits](RealRooted/Challenges/ChudnovskySeymour.lean)

## Ordinary homogenization preserves stability

Status: Proved theorem

Adding one variable to make all monomials have the same total degree preserves multivariate real stability when coefficients are nonnegative.

Scope: Stability means nonvanishing when every variable has positive imaginary part. The strict result assumes a nonzero stable input; a separate witness includes zero. Padding to a larger homogenizing degree is also covered.

- Lean theorem: [RealRooted.Challenges.Homogenization.ordinaryHomogenization_stable](RealRooted/Challenges/Homogenization.lean)
- Lean theorem: [RealRooted.Challenges.Homogenization.ordinaryHomogenization_stable_of_totalDegree_le](RealRooted/Challenges/Homogenization.lean)
- Lean theorem: [RealRooted.Challenges.Homogenization.ordinaryHomogenization_stableOrZero](RealRooted/Challenges/Homogenization.lean)
- [Tracking issue #550](https://github.com/PerAlexandersson/RealRooted/issues/550)

## Totally nonnegative matrix principal interlacing

Status: Proved theorem

For a finite real matrix whose every minor is nonnegative, the characteristic polynomial of its leading or trailing principal section interlaces that of the matrix.

Scope: Includes singular and reducible matrices. Interlacing is weak (coincident roots are allowed), and the sections remove the first or last index; this entry does not claim arbitrary principal deletion.

- Lean theorem: [RealRooted.Challenges.TotallyNonnegative.leadingPrincipal_charpoly_interlaces](RealRooted/Challenges/TotallyNonnegative.lean)
- Lean theorem: [RealRooted.Challenges.TotallyNonnegative.trailingPrincipal_charpoly_interlaces](RealRooted/Challenges/TotallyNonnegative.lean)
- [Tracking issue #552](https://github.com/PerAlexandersson/RealRooted/issues/552)

## Pólya–Schur milestone: PF multipliers give real-zero entire functions

Status: Proved theorem

A PF multiplier sequence has an exponential generating function in the Laguerre–Pólya class: a locally uniform limit of real-rooted real polynomials. Unless identically zero, its zeros are real.

Scope: The PF multiplier condition is stronger than coefficient nonnegativity alone. Zero sequences and initial zero coefficients are included. Alternating the coefficient signs reflects the function. This is a proved forward branch, not the full classification.

- Lean theorem: [RealRooted.Challenges.PolyaSchur.pfMultiplier_egf_isLaguerrePolya](RealRooted/Challenges/PolyaSchur.lean)
- Lean theorem: [RealRooted.Challenges.PolyaSchur.pfMultiplier_egf_real_zero](RealRooted/Challenges/PolyaSchur.lean)
- Lean theorem: [RealRooted.Challenges.PolyaSchur.pfMultiplier_alternating_egf_isLaguerrePolya](RealRooted/Challenges/PolyaSchur.lean)
- [Tracking issue #563](https://github.com/PerAlexandersson/RealRooted/issues/563)

## Braun–Jal generalized snake rook polynomials

Status: Conditional theorem — external inputs remain

The formalized recurrence and interlacing machinery yields the generalized-snake rook-polynomial theorem from explicit board-model inputs.

Scope: Conditional: the theorem still takes the auxiliary recurrence, board-difference nonnegativity, snake recurrence, degree identity and constant-board identification as inputs. A theorem with these hypotheses is not an unconditional proof of the complete combinatorial model.

- Lean theorem: [RealRooted.Challenges.BraunJal.generalizedSnakeRookModel_theorem41](RealRooted/Challenges/BraunJal.lean)

## Full analytic Pólya–Schur classification

Status: Open target — not proved

Complete the analytic classification of real-rootedness-preserving multiplier sequences, including the remaining converse and product-description bridges.

Scope: Open at this catalog checkpoint. The proved PF forward branch is listed separately above; a green build or a closed subtask does not settle this larger target.

- [Tracking issue #563](https://github.com/PerAlexandersson/RealRooted/issues/563)
