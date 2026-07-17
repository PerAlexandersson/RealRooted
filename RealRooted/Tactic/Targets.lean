/-!
# Tactic target families

This module records the intended examples and OEIS families for the tactic
work.  It is documentation in an importable Lean file, so it is visible to git
despite the repository-wide `*.md` ignore rule.

## First existing examples

The first successful tactic demos should reproduce proofs parallel to existing
examples, without rewriting those examples immediately.

- `touchard`: one-step derivative recurrence, Ma-Wang/Liu-Wang shape.
- `coloredSetPartitions`: parameterized one-step derivative recurrence.
- `stirlingPermutations`: Eulerian-style derivative recurrence.
- `typeBEulerian`: signed Eulerian-style derivative recurrence.
- `simsun`: derivative recurrence with root-sign side goals.
- `narayanaQuot`/`narayana`: Liu-Wang/Jacobi-like three-term recurrence.
- `motzkin`: recurrence with parity-sensitive interlacing side conditions.

## OEIS Family A/B targets

These should be the first OEIS-facing targets for `rr_ma_wang`.

- Family A, Eulerian one-step differential examples:
  `A008517`, `A120434`, `A144696`, `A144697`, `A144698`, `A144699`,
  `A156919`, `A257606`, `A257607`, `A296229`.
- Family B, half-line one-step differential examples:
  `A021009`, `A046089`, `A049352`, `A049353`, `A079621`, `A111578`,
  `A143496`, `A154537`, `A225466`, `A364071`.

## Executable OEIS recurrence test bed

`RealRooted.Tactic.Examples.OEISTestbed` contains the first executable
sequence-labelled regression tests from the Erik/sqrt2 recurrence survey.
The examples do not yet formalize the row definitions; they isolate the
certificate fragments that should be automatic once a sequence-specific file
provides the recurrence identity, degree facts, root interval, and base cases.

Current test-bed entries:

- Ma--Wang Family A:
  `A008517`, `A120434`, `A156919`;
- Ma--Wang Family B and OEIS-stated conjecture targets:
  `A321966`, `A322944`;
- Liu--Wang Family E:
  `A049403`, `A061896`, `A100862`, `A154227`, `A249248`;
- Narayana/Jacobi Family G:
  `A001263`, `A091044`, `A145596`, `A178343`;
- Favard/Chebyshev Family F:
  `A049310`, `A053117`, `A053120`, `A053122`, `A053124`, `A078812`,
  `A084930`, `A124038`.

These 22 entries are meant to stay small and executable.  Harder targets such
as `A390883` should be recorded here, but not forced into this scalar test bed
until a refinement, companion-vector recurrence, or production-matrix
certificate is explicit.

## OEIS Family C/D/H targets

These are useful after the Ma-Wang tactic handles explicit root intervals and
sign windows.

- Family C inner interval examples:
  `A019538`, `A112493`, `A131689`, `A134991`, `A145901`, `A186695`,
  `A199400`, `A253284`, `A259456`, `A284861`.
- Family D shifted first-derivative examples:
  `A008278`, `A021010`, `A060821`, `A066325`, `A076256`, `A089503`,
  `A106800`, `A159834`, `A341287`, `A395972`.
- Family H second-derivative or factored examples:
  `A008299`, `A105278`, `A111884`, `A123125`, `A132062`, `A143543`,
  `A216916`, `A216917`, `A216918`, `A216919`.

## OEIS Family E/G targets

These should drive `rr_liu_wang`.

- Family E, three-term Sturm examples:
  `A053123`, `A080246`, `A100862`, `A154227`, `A154228`, `A249248`,
  `A049403`, `A057094`, `A061896`, `A079510`.
- Family G, Narayana/Jacobi/quadratic-lag examples:
  `A001263`, `A008459`, `A060693`, `A091156`, `A108108`, `A126216`,
  `A126217`, `A131198`, `A174867`, `A243676`.

## OEIS Family F targets

These should drive `rr_favard`.

- Favard/Chebyshev-style examples:
  `A049310`, `A053117`, `A053120`, `A053122`, `A053124`, `A053125`,
  `A078812`, `A098593`, `A127672`, `A187360`.

## OEIS Family I/J targets

These should wait for refined-vector certificates or operator factorizations.

- Family I Ore/Weyl-factorization examples:
  `A036560`, `A099759`, `A141689`, `A141690`, `A141696`, `A141697`,
  `A157012`, `A219836`, `A290448`.
- Family J pure lag-3 or transfer examples:
  `A060923`, `A060924`, `A098172`, `A109954`, `A109970`, `A145677`,
  `A156578`, `A158821`, `A158909`, `A165620`, `A199221`, `A277627`.
- Family J denominator/Riordan examples:
  `A079508`, `A108558`, `A115179`, `A116647`, `A117434`, `A119308`,
  `A122765`, `A122766`, `A123160`, `A171608`, `A253283`.
- Family J derivative-transfer examples:
  `A092371`, `A101920`, `A155495`, `A162303`, `A168287`, `A168288`,
  `A168289`, `A168290`, `A176200`, `A176204`, `A257142`, `A259454`,
  `A319251`, `A370232`.
- Hard staged examples:
  `A390883` and the associated-Stirling rows `A059022`--`A059025`.

For Family J, the desired success criterion is not a tactic proof from the
raw scalar recurrence.  The success criterion is a tactic proof once a refined
vector recurrence, production matrix, or lower-order factorization has been
made explicit.
-/

namespace RealRooted
namespace Tactic

/- Documentation-only target ledger. -/

end Tactic
end RealRooted
