# RealRooted tactic plan

Date: 2026-07-01

This note is a plan for tactic support for recurrence-based
real-rootedness proofs in the `RealRooted` Lean project.  It is written for
an implementation agent.  The intent is not to create a broad mathematical
search tactic.  The intent is to automate the repetitive proof shell that
already appears in the combinatorial examples, while keeping the mathematical
certificate explicit and inspectable.

## Guiding principle

The tactic should be certificate-driven.

The user or a generated Lean file supplies:

- the recurrence;
- degree and leading-coefficient facts;
- nonnegative-coefficient or root-interval facts;
- the intended engine: Ma-Wang, Liu-Wang, Favard, Wagner, or Branden matrix;
- base cases and indexing conventions.

The tactic then applies existing formalized theorems and discharges routine
side goals by simplification, arithmetic, and polynomial normalization.

It should not try to infer an unknown proof route from an arbitrary
recurrence.  In particular, long-lag scalar recurrences from OEIS should not
be attacked directly unless a refined vector or lower-order theorem has
already been supplied.

## Existing proof engines

The tactic layer should first reuse these checked declarations.

- `RealRooted.MaWang`
  - `prec_ma_wang`
  - `prec_ma_wang_same`
  - `prec_ma_wang_succ`
  - `prec_of_interlaces_evalCoeff_nonpos`
  - weak/no-common Liu-Wang variants near the end of `MaWang.lean`
- `RealRooted.GeneralizedLiuWang`
  - `polynomialWeightedSum`
  - `prec_generalizedLiuWang_strict`
  - `prec_generalizedLiuWang_of_no_common`
  - `generalizedLiuWangCriterion`
- `RealRooted.Favard`
  - `SatisfiesFavardRecurrence`
  - `favardInterlacing`
  - `isRealRooted_of_favard`
  - `isGeneralizedSturmSeq_reverse_range_map_of_favard`
- `RealRooted.MatrixInterlacing`
  - `matPolyAction`
  - `matrix_preserves_interlacing_seq`
  - `matrix_preserves_interlacing_seq0_of_2x2`
  - `matrix_preserves_interlacing_seq0_of_2x2_weak`
- `RealRooted.StaircaseSum`, `RealRooted.RowThreshold`,
  `RealRooted.ProductFamily`, and the Wagner files for specialized transfer
  and sum closures.

The first tactic implementation should not add new mathematics to these
files.  If a theorem wrapper is missing, add it explicitly as a theorem first,
then teach the tactic to use it.

## Existing example pattern

The tactic should target the pattern used by files such as:

- `RealRooted/CombinatorialExamples/Touchard.lean`
- `RealRooted/CombinatorialExamples/ColoredSetPartitions.lean`
- `RealRooted/CombinatorialExamples/StirlingPermutations.lean`
- `RealRooted/CombinatorialExamples/TypeBEulerian.lean`
- `RealRooted/CombinatorialExamples/Simsun.lean`
- `RealRooted/CombinatorialExamples/Narayana.lean`
- `RealRooted/CombinatorialExamples/Motzkin.lean`

The repeated structure is:

1. define a polynomial family `P : Nat -> R[X]`;
2. prove the recurrence, often by `rfl` or a short rewrite;
3. prove coefficient, degree, nonzero, and leading-coefficient facts;
4. prove nonnegative coefficients or an explicit root bound;
5. prove the induction step `Prec (P n) (P (n+1))`;
6. derive `Interlaces`, `Splits`, and a prefix Sturm-sequence theorem.

The tactic should automate steps 5 and 6 first.  Steps 1-4 should remain
explicit certificate lemmas, because they are the valuable mathematical and
combinatorial content.

## Proposed file layout

Add a new tactic namespace under the Lean library:

```text
RealRooted/Tactic.lean
RealRooted/Tactic/Attr.lean
RealRooted/Tactic/SideGoals.lean
RealRooted/Tactic/MaWang.lean
RealRooted/Tactic/LiuWang.lean
RealRooted/Tactic/Favard.lean
RealRooted/Tactic/Matrix.lean
RealRooted/Tactic/OEIS.lean
```

Recommended staging:

1. start with `Attr.lean` and `SideGoals.lean`;
2. add `MaWang.lean`;
3. add `Favard.lean`;
4. add `LiuWang.lean`;
5. add `Matrix.lean`;
6. add `OEIS.lean` only after the first four parts are stable.

Do not import these tactics from `RealRooted.lean` at first unless the user
explicitly wants tactic code in the umbrella import.  It is enough that
focused builds such as

```bash
lake build RealRooted.Tactic.MaWang
```

work.

## Current implementation status

The first certificate-driven layer is implemented.

- `Attr.lean` defines tag attributes for recurrence, degree, sign, base-case,
  and matrix certificates, plus `#rr_certificates` / `rr_certificates` for
  inspecting visible tagged declarations.
- `Lookup.lean` defines `rr_lookup`, a conservative exact lookup tactic using
  local hypotheses first and unique tagged certificates second.  It also
  supports attribute-restricted forms such as `rr_lookup [rr_nonzero]`.
- `SideGoals.lean` defines `rr_side`, a conservative side-goal closer.
- `Finish.lean` defines small proof-tail dispatchers that consume `Prec`
  certificates.
- `MaWang.lean` defines dispatchers for `prec_ma_wang`,
  `prec_ma_wang_same`, and `prec_ma_wang_succ`.
- `Favard.lean` defines a dispatcher for the Favard interlacing and
  real-rootedness theorems.
- `LiuWang.lean` defines weak/no-common and strict generalized Liu-Wang
  dispatchers.
- `Matrix.lean` defines strict and weak matrix-transfer dispatchers.
- `Examples/` contains abstract smoke tests for these dispatchers.
  It also contains a small Touchard regression file under
  `Examples/Combinatorial.lean`.

## Attribute system

Use custom attributes for certificate lemmas.  This is preferable to
hard-coding sequence names.

Suggested attributes:

```lean
attribute [rr_recurrence] P_succ
attribute [rr_degree] natDegree_P
attribute [rr_nonzero] P_ne_zero
attribute [rr_pos_lc] P_posLeadingCoeff
attribute [rr_nonneg] P_nonnegCoeffs
attribute [rr_root_bound] roots_nonpos_P_of_isRealRooted
attribute [rr_base_prec] prec_P_one_two
attribute [rr_base_interlaces] interlaces_P_zero_one
```

For matrix proofs:

```lean
attribute [rr_matrix_rect] G_rect
attribute [rr_matrix_nonneg] G_nonneg
attribute [rr_matrix_2x2] G_has2x2
attribute [rr_matrix_threshold] G_threshold
```

Implementation note:
start with attributes that are ordinary `TagAttribute`s.  The first tactic can
search local hypotheses and tagged declarations by type.  It does not need a
rich persistent certificate database on day one.

Later, if lookup becomes ambiguous, introduce parametric syntax:

```lean
rr_ma_wang using
  splits := P_splits,
  degree_two := P_degree_two,
  degree_lower := P_degree_lower,
  degree_upper := P_degree_upper,
  target_pos_lc := next_posLeadingCoeff,
  source_pos_lc := P_posLeadingCoeff,
  root_sign := root_sign_certificate
```

The explicit form should always be available even if attribute search works.

## Tactic 1: `rr_side`

Purpose:
close routine side goals after an engine theorem has been applied.

Scope:
`rr_side` should be conservative.  It should be safe to run in examples and
should fail clearly if the mathematical certificate is missing.

Initial behavior:

1. unfold local recurrence coefficient definitions when explicitly tagged or
   passed;
2. simplify polynomial evaluation:
   `Polynomial.eval_add`, `Polynomial.eval_mul`, `Polynomial.eval_C`,
   `Polynomial.eval_X`, derivative coefficient simplifications;
3. rewrite with known recurrence and degree lemmas;
4. close simple arithmetic with `norm_num`, `positivity`, `lia`, and
   `nlinarith`;
5. normalize polynomial identities with `ring_nf` or `ring`;
6. use local hypotheses via `simp_all` and `grind` only at the end.

Non-goals:

- no broad `aesop` search initially;
- no unfolding all definitions in context;
- no attempt to prove real-rootedness directly;
- no attempt to discover a root interval.

Suggested implementation shape:

```lean
syntax "rr_side" : tactic
```

The implementation can first be a macro expanding to a robust sequence of
standard tactics:

```lean
first
  | positivity
  | norm_num
  | ring_nf
  | lia
  | nlinarith
  | simp_all [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
  | grind
```

As soon as this gets too blunt, replace it by an elaborator tactic that tries
these in a controlled order and produces a short failure message.

## Tactic 2: `rr_ma_wang`

Purpose:
prove one-step derivative recurrence induction steps of the form

```text
P_{n+1} = u_n * P_n + v_n * derivative(P_n).
```

Target goals:

```lean
Prec (P n) (P (n + 1))
Interlaces (P n) (P (n + 1))
P n != 0 /\ (P n).Splits
forall n, P n != 0 /\ (P n).Splits
IsSturmSeq (P_prefix n)
```

Recommended first version:
only support a goal that is already a `Prec` step, e.g.

```lean
theorem prec_P_succ : forall n, Prec (P n) (P (n + 1)) := by
  intro n
  rr_ma_wang
```

The tactic should:

1. split base cases if requested or if the family starts at small indices;
2. find the previous `Prec` hypothesis in the induction step;
3. derive `P n` real-rooted from the previous `Prec`;
4. derive `Interlaces (P n).derivative (P n)` by `derivative_interlaces`;
5. rewrite the recurrence target into `u * f + v * f.derivative`;
6. apply `prec_ma_wang` or `prec_of_interlaces_evalCoeff_nonpos`;
7. solve degree, leading-coefficient, and root-sign side goals by `rr_side`.

The root-sign side goal should not be guessed.  It should use a tagged root
bound lemma and a tagged sign lemma, for example:

```lean
lemma roots_nonpos_P_of_isRealRooted ...
lemma eval_v_nonpos_of_nonpos ...
```

or a direct local theorem:

```lean
lemma P_v_root_sign :
    forall n r, (P n).IsRoot r -> (v n).eval r <= 0
```

The tactic should support both.

Useful syntax:

```lean
rr_ma_wang

rr_ma_wang using
  recurrence := P_succ,
  degree := natDegree_P,
  pos_lc := P_posLeadingCoeff,
  root_sign := P_v_root_sign
```

Expected first test cases:

- `Touchard.lean`
- `ColoredSetPartitions.lean`
- `StirlingPermutations.lean`
- `TypeBEulerian.lean`
- `Simsun.lean`

The implementation should try to reproduce one existing theorem with a new
parallel theorem name first, not rewrite the existing examples immediately.

## Tactic 3: `rr_finish_sequence`

Purpose:
derive standard corollaries once the consecutive `Prec` theorem is proved.

Target goals:

```lean
Interlaces (P n) (P (n + 1))
P n != 0 /\ (P n).Splits
IsSturmSeq (P_prefix n)
IsGeneralizedSturmSeq (P_prefix n)
```

This tactic should be deliberately simple:

- for `Interlaces`, apply `hprec.toInterlaces` plus degree facts;
- for real-rootedness, use `(hprec n).2.1` or the base case;
- for prefix Sturm sequences, follow the recursive proof pattern in the
  combinatorial examples.

Suggested syntax:

```lean
rr_finish_sequence using prec_P_succ, degree := natDegree_P
```

The tactic should probably require the `Prec` theorem explicitly.  Attribute
lookup can be added later.

## Tactic 4: `rr_favard`

Purpose:
discharge orthogonal-polynomial style three-term recurrences that fit
`SatisfiesFavardRecurrence`.

Target pattern:

```text
P_0 = 1,
P_1 = X - C alpha_0,
P_{n+2} = (X - C alpha_{n+1}) * P_{n+1}
          - C beta_{n+1} * P_n,
beta_{n+1} > 0.
```

The tactic should:

1. construct or find a proof of `SatisfiesFavardRecurrence P alpha beta`;
2. prove positivity of `beta`;
3. apply `favardInterlacing` or `isRealRooted_of_favard`;
4. use `isGeneralizedSturmSeq_reverse_range_map_of_favard` for prefix results.

Suggested syntax:

```lean
rr_favard

rr_favard using
  recurrence := P_favard,
  beta_pos := beta_pos
```

Expected first test cases:

- Chebyshev-like examples already in `CombinatorialExamples`;
- OEIS Family F examples after a small Lean wrapper defines the parametric
  family.

## Tactic 5: `rr_liu_wang`

Purpose:
handle two-polynomial and finite-sum Liu-Wang recurrences where the new row is
a weighted sum of one or more interlacers of a base polynomial.

Target pattern:

```text
F = a * f + sum_i b_i * g_i,
g_i interlaces f,
b_i(root of f) <= 0.
```

This tactic is more fragile than `rr_ma_wang`, so it should be implemented
after `rr_ma_wang` and `rr_favard`.

The tactic should:

1. identify the distinguished interlacer `g`;
2. build the list `l : List (R[X] x R[X])` for the remaining terms;
3. apply `generalizedLiuWangCriterion` or the strict variant;
4. solve common interlacing and sign side goals from explicit certificates.

Suggested syntax:

```lean
rr_liu_wang using
  head := g,
  rest := [(b1, g1), (b2, g2)],
  degree := F_degree,
  signs := root_signs
```

Expected first test cases:

- Family E three-term recurrences with `t` in the lag term;
- selected Family G/Jacobi-like examples where the sign conditions are clean;
- `LiuWangBenchmark.lean` only after the tactic handles the basic shape.

## Tactic 6: `rr_matrix`

Purpose:
apply Branden matrix/interlacing-sequence preservers when a refined vector
recurrence is already written as a matrix action.

Target pattern:

```text
F_{n+1} = matPolyAction G_n F_n
```

with:

- rectangular matrix rows;
- entrywise nonnegative coefficients;
- `Has2x2InterlacingProperty` or `Has2x2InterlacingProperty0`;
- input vector `IsInterlacingSeqNonneg` or `IsInterlacingSeq0Nonneg`.

First version:
do not synthesize the matrix from a scalar recurrence.  Require the theorem
statement or local context to contain the matrix recurrence explicitly.

Suggested syntax:

```lean
rr_matrix

rr_matrix using
  action := F_succ_eq_matPolyAction,
  rect := G_rect,
  nonneg := G_nonneg,
  minors := G_2x2
```

Expected first test cases:

- simple staircase or row-threshold matrices;
- Veronese matrix snippets if a small local test can be isolated;
- later, OEIS Family J refined-vector proofs.

Family J warning:
this tactic should not try to prove a raw scalar lag-3 or lag-8 recurrence.
The input must already be a refined vector recurrence or production matrix.

## Tactic 7: `rr_oeis`

Purpose:
provide a thin user-facing wrapper for generated OEIS family files.

This should be the last tactic, not the first.  It can dispatch based on an
explicit engine tag:

```lean
rr_oeis ma_wang
rr_oeis favard
rr_oeis liu_wang
rr_oeis matrix
```

Generated OEIS files should remain explicit enough that a failed tactic leaves
a readable proof obligation.  For example:

```lean
namespace RealRooted.OEIS.A008517

def P : Nat -> R[X] := ...

@[rr_recurrence] lemma P_succ ...
@[rr_degree] lemma natDegree_P ...
@[rr_pos_lc] lemma P_posLeadingCoeff ...
@[rr_nonneg] lemma P_nonnegCoeffs ...
@[rr_root_bound] lemma roots_nonpos_P_of_isRealRooted ...

theorem prec_P_succ : forall n, Prec (P n) (P (n + 1)) := by
  rr_oeis ma_wang

theorem isRealRooted_P : forall n, P n != 0 /\ (P n).Splits := by
  rr_finish_sequence using prec_P_succ

end RealRooted.OEIS.A008517
```

The generated file should not hide the recurrence or certificate lemmas.
Those are the audit trail.

## Certificate records

Once basic tactics work, consider adding theorem-facing certificate
structures.  Do this only if attributes become hard to manage.

Possible structure for Ma-Wang:

```lean
structure MaWangCertificate (P : Nat -> R[X]) where
  u : Nat -> R[X]
  v : Nat -> R[X]
  recurrence :
    forall n, P (n + 1) = u n * P n + v n * (P n).derivative
  degree_lo :
    forall n, (P n).natDegree <=
      (u n * P n + v n * (P n).derivative).natDegree
  degree_hi :
    forall n, (u n * P n + v n * (P n).derivative).natDegree <=
      (P n).natDegree + 1
  pos_lc : forall n, HasPosLeadingCoeff (P n)
  root_sign :
    forall n r, (P n).IsRoot r ->
      (v n).eval r * ((P n).derivative.eval r)^2 < 0
```

This exact strict sign condition matches `prec_ma_wang`.  For the examples
that naturally use weak signs, either use `prec_of_interlaces_evalCoeff_nonpos`
or define a separate weak certificate structure.

Possible structure for Favard:

```lean
structure FavardCertificate (P : Nat -> R[X]) where
  alpha beta : Nat -> R
  recurrence : SatisfiesFavardRecurrence P alpha beta
  beta_pos : forall n, 0 < beta (n + 1)
```

Possible structure for matrix transfer:

```lean
structure MatrixCertificate (G : List (List R[X])) (n : Nat) where
  rect : forall row, row in G -> row.length = n
  nonneg : forall row, row in G -> forall p, p in row -> HasNonnegCoeffs p
  minors :
    forall i1 i2 : Fin G.length, forall j1 j2 : Fin n,
      i1 <= i2 -> j1 <= j2 ->
        Has2x2InterlacingProperty ...
```

Do not introduce these structures until a tactic has been tested on several
examples.  Attributes are more flexible during early development.

## Generated OEIS Lean files

Generated files should be split by theorem family, not by hundreds of IDs in
one file.

Suggested layout:

```text
RealRooted/OEIS/Common.lean
RealRooted/OEIS/MaWang.lean
RealRooted/OEIS/LiuWang.lean
RealRooted/OEIS/Favard.lean
RealRooted/OEIS/Matrix.lean
RealRooted/OEIS/Special/A390883.lean
```

Each generated family file should contain:

1. a short module docstring with OEIS IDs;
2. definitions of parametric families, not only singleton IDs;
3. recurrence lemmas;
4. certificate lemmas tagged for tactics;
5. theorem statements for `Prec`, `Interlaces`, `Splits`, and prefixes;
6. comments linking back to the OEIS workbench generator or recurrence
   evidence.

Avoid one-off files unless the sequence is mathematically important, such as
`A390883`, or unless it tests a new theorem family.

## Implementation phases

### Phase 0: no metaprogramming

Before writing an elaborator tactic, make a few theorem wrappers that shorten
example proofs.  For example:

```lean
theorem prec_one_step_derivative_of_root_sign ...
```

If theorem wrappers remove most boilerplate, the tactic can stay shallow.

### Phase 1: side-goal tactic

Implement `rr_side` as a macro or simple elaborator tactic.

Tests:

- local sign goals from `Touchard`;
- degree side goals from `ColoredSetPartitions`;
- simple polynomial identity goals from `StirlingPermutations`.

Build:

```bash
lake build RealRooted.Tactic.SideGoals
```

### Phase 2: Ma-Wang tactic

Implement `rr_ma_wang` for a theorem whose goal is already a `Prec` step.

Do not make it handle all final corollaries yet.

Tests:

- create a new small file under `RealRooted/Tactic/Examples/MaWang.lean`, or
  a temporary theorem in the tactic test file;
- prove a `Prec` theorem for Touchard-like recurrence;
- prove a colored-set-partition-like recurrence with parameters.

Build:

```bash
lake build RealRooted.Tactic.MaWang
```

### Phase 3: sequence finisher

Implement `rr_finish_sequence`.

Tests:

- derive `Interlaces`;
- derive `Splits`;
- derive `IsSturmSeq` for a recursive prefix list.

### Phase 4: Favard tactic

Implement `rr_favard`.

Tests:

- a minimal Chebyshev/Favard recurrence;
- one OEIS Family F representative after writing a small wrapper.

### Phase 5: generalized Liu-Wang tactic

Implement `rr_liu_wang`.

Tests:

- one clean Family E representative;
- one generalized finite-sum example if available.

### Phase 6: matrix tactic

Implement `rr_matrix`.

Tests:

- a small explicit `2 x 2` or `3 x 3` matrix whose entries are `0`, `1`, and
  `X`;
- a row-threshold matrix wrapper using `RowThreshold.lean`;
- eventually a refined vector proof for a Family J case.

### Phase 7: generated OEIS examples

Add generated Lean examples only after the tactic APIs are stable.

Start with:

- one Family A/B Ma-Wang example;
- one Family E Liu-Wang example;
- one Family F Favard example;
- no Family J scalar example until a refined vector is available.

## Testing and build discipline

Use focused builds after each file:

```bash
lake build RealRooted.Tactic.SideGoals
lake build RealRooted.Tactic.MaWang
lake build RealRooted.Tactic.Favard
```

Only after touching public theorem interfaces or imports, run:

```bash
lake build
```

The current repository uses a cached Lake build directory outside the
workspace.  Do not edit `.lake` output.

If the repo is dirty, do not rewrite unrelated files.  Keep tactic work in the
new `RealRooted/Tactic/` files unless a core theorem wrapper is truly needed.

## Failure behavior

A good tactic failure should say which certificate is missing.

Examples:

```text
rr_ma_wang: could not find recurrence lemma for P
rr_ma_wang: could not prove root-sign side goal; try supplying root_sign := ...
rr_favard: goal does not match a Favard conclusion and no target theorem was supplied
rr_matrix: matrix recurrence was not found; supply action := ...
```

Avoid silent fallback to broad search.  If `rr_side` cannot close a goal, it
should leave the exact Lean goal for the implementer.

## What not to automate

Do not automate:

- deriving a combinatorial recurrence from definitions;
- finding a root interval;
- selecting a refined vector for a long-lag scalar recurrence;
- proving Branden `2 x 2` matrix conditions from scratch;
- discovering common interlacing relations;
- rewriting OEIS data into Lean definitions.

Those are mathematical or data-generation tasks.  The tactic should consume
their certificates after they have been stated.

## Priority targets for OEIS families

Recommended order:

1. Families A/B: one-step derivative, roots on a half-line.
2. Family F: Favard/Chebyshev recurrences.
3. Family E: three-term Liu-Wang/Sturm recurrences.
4. Clean subfamilies of C/D/G where root intervals and signs are explicit.
5. Family H only after a reusable second-derivative or factorization theorem
   is available.
6. Family I only when the Ore/Weyl factorization has been converted to a
   first-order system theorem.
7. Family J only after a refined vector or production-matrix recurrence has
   been supplied.

The first coding milestone should be a tactic-proved theorem for one existing
example, not a generated OEIS file.

## Minimal successful demo

A good first merged demo would add:

```text
RealRooted/Tactic/Attr.lean
RealRooted/Tactic/SideGoals.lean
RealRooted/Tactic/MaWang.lean
RealRooted/Tactic/Examples/Touchard.lean
```

The demo theorem should be parallel to the existing Touchard theorem, e.g.

```lean
theorem prec_touchard_succ_by_tactic :
    forall n : Nat, Prec (touchard n) (touchard (n + 1)) := by
  -- explicit base cases if needed
  rr_ma_wang
```

It is fine if the first version still needs explicit arguments:

```lean
rr_ma_wang using
  recurrence := touchard_succ,
  degree := natDegree_touchard,
  pos_lc := touchard_posLeadingCoeff,
  nonneg := touchard_nonnegCoeffs,
  root_bound := roots_nonpos_touchard_of_isRealRooted
```

That explicit syntax is likely better for generated OEIS files anyway.

## 2026-07-29 OEIS/Sturm Refactor Checkpoint

The companion `real-rooted-oeis` repo now has enough tactic ledger data to
guide refactoring without adding another layer of ad hoc wrappers.  The useful
source files there are:

- `proof-targets/tactic-ledger.md`;
- `proof-targets/tactic-golf-audit.md`;
- `proof-targets/proof-testbed-tactic-alignment.md`;
- `proof-targets/open-tactic-work-packages.md`.

The Hoster--Stump tracker in the OEIS repo has already been migrated:
`sqrt-of-2/real-rooted-oeis#2` is closed, and the matching RealRooted issue
`#99` is closed with `RealRooted/Challenges/HosterStump.lean` present but not
imported by the root module.  It should not drive new tactic work.

The main repeated OEIS/Sturm lanes are:

- `halfline-sturm-t-lag`: 68 rows, already represented by public Liu--Wang
  tactic tokens and executable examples;
- `quadratic-lag-sturm`: 39 rows, already represented by public Liu--Wang
  tactic tokens and several exact testbed examples;
- Ma--Wang derivative lanes: larger, but separate from the current Liu--Wang
  degree/state problem.

The next reusable abstraction should be a small Liu--Wang/Sturm state package,
not another shape-specific sequence theorem.  It should carry exactly the data
that the OEIS ledgers repeat:

```text
LwSturmState P n:
  Prec (P n) (P (n+1))
  HasPosLeadingCoeff (P n)
  HasPosLeadingCoeff (P (n+1))
  HasNonnegCoeffs (P n) or an explicit root interval for P (n+1)
  natDegree data for P n and P (n+1)
  no-common-root certificate for the adjacent pair
```

Then add a branch layer that consumes the stored degree data and chooses the
same-degree or successor-degree Liu--Wang conclusion.  This is the right place
to handle plateau examples such as degree pattern `0,0,1,1,2,2,...`; the tactic
should not infer that pattern from coefficients.

After that state layer exists, the safe golf targets are:

- keep public tactic names such as `rr_lw_tR_lag_sequence_realrooted` as
  facades, but route them through the state package;
- compress repeated negative-square and denominator-normalized payloads into
  typed certificate constructors;
- prefer one generic positive `X * R` lag theorem over separate wrappers for
  current factor `X`, `C c * X`, and `1 + X`, unless the specialized theorem is
  materially clearer at generated call sites;
- avoid public tactic renames until downstream OEIS wrappers have aliases and
  coverage tests.

Focused verification for this pass should include:

```bash
lake build RealRooted.Tactic.LiuWang
lake build RealRooted.Tactic.Examples.LiuWang
lake build RealRooted.Tactic.OEIS
```

Run a full `lake build` only after changing public theorem signatures, imports,
or generated coverage.

## 2026-08-03 Recurrence-defined model identification

The merged `rr_model_sequence` frontend transfers real-rootedness once a
pointwise equality with a checked model is available. The remaining generic
plumbing is recurrence uniqueness, not another sequence-specific
real-rootedness theorem.

`RealRooted.Tactic.RecurrenceIdentification` supplies pointwise uniqueness and
direct model-transfer frontends for common fixed-lag shapes:

- `rr_identify_lag_one_sequence` and `rr_model_lag_one_sequence`;
- `rr_identify_lag_two_sequence` and `rr_model_lag_two_sequence`;
- `rr_identify_lag_three_sequence` and `rr_model_lag_three_sequence`.

The recurrence step is an arbitrary function of the index and preceding rows,
so the same API covers polynomial multiplication, affine Favard steps, and
derivative recurrences without naming any OEIS sequence. The companion OEIS
agreement audit currently has 4 local lag-one rows, 31 local lag-two rows, and
3 local lag-three rows. Each still needs a formal OEIS row definition plus
initial-value and recurrence proofs; finite cached-row checks do not discharge
those obligations.
