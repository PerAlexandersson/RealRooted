# Hadamard Classical Machinery Issues

This file is intentionally only an index.  The actionable plan now lives in
GitHub issues, so each piece can be assigned, discussed, and closed
independently.

## Umbrella

- [#34: Formalize Garloff-Wagner Hadamard proper-position statement](https://github.com/PerAlexandersson/RealRooted/issues/34)

Main Lean target:

```lean
RealRooted.garloffWagnerHadamardNonnegPrec
```

This is currently a theorem-shaped target name; until the classical theorem is
formalized, it may be represented by an intentional `sorry` stub.

## Subissues

- [#56: Audit Hadamard proper-position orientation](https://github.com/PerAlexandersson/RealRooted/issues/56)
- [#57: Build Hadamard coefficient API and Schur-Szego normalization](https://github.com/PerAlexandersson/RealRooted/issues/57)
- [#58: Formalize finite multiplier sequences and finite Polya-Schur](https://github.com/PerAlexandersson/RealRooted/issues/58)
- [#59: Formalize Schur-Szego composition for nonpositive roots](https://github.com/PerAlexandersson/RealRooted/issues/59)
- [#60: Formalize Grace apolarity needed for Hadamard machinery](https://github.com/PerAlexandersson/RealRooted/issues/60)
- [#61: Remove downstream StandardFacts dependency after Garloff-Wagner](https://github.com/PerAlexandersson/RealRooted/issues/61)

## Suggested Order

1. Do #56 before proving any classical theorem, so the `Prec` orientation is
   fixed against the literature.
2. Do #57 before #58 or #59; both proof routes need the coefficient and degree
   API.
3. Use #58 for the direct finite multiplier-sequence route to the
   real-rootedness Hadamard theorem.
4. Use #59 as the Schur-Szego route and possible bridge toward proper
   position.
5. Use #60 only if Grace apolarity or the stable-polynomial route is actually
   needed for #34.
6. Close #34 in `RealRooted/Hadamard.lean`, then do #61 in SuperEulerian.

## Verification

For Lean work in this package, run a focused build first:

```bash
lake build RealRooted.Hadamard
```

Before merging theorem work, coordinate and run the full project build:

```bash
lake build
```
