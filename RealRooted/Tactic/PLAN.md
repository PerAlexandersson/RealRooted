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

### 2026-07-30 Liu-Wang Global Nonpositive Projections Auto

Add the missing global-nonpositive auto projections for nonzero and
consecutive interlacing.  This is a catalog-agnostic tactic facade over
`LwNonposLagSequenceState.of_nonpos` and `LwNonposLagSequenceState.of_den`.
The caller still supplies the base `Prec` certificate, leading-coefficient
certificate, lag term, recurrence certificate, strict degree increment, and
no-common-root certificate.  The only automatic step is the existing
`rr_sign` discharge for the supplied global lag.

The first planning pass considered adding only interlacing, because the
existing `rr_lw_global_nonpos_sequence_realrooted_auto` and denominator variant
route through `rr_exact_realrooted_sequence_or_projection`.  The focused build
found that a direct nonzero projection through that finisher can hit the
heartbeat limit in `RealRooted/Tactic/Examples/LiuWang.lean`, so this slice
adds direct nonzero endpoints.  A candidate direct splitting endpoint was also
tested, but the abstract examples still hit heartbeat limits.  Splitting is
therefore left to the existing real-rooted endpoints for now.  The accepted
endpoints are still generic: they do not infer a proof route or depend on any
sequence catalogue, and they simply project fields from the already-built
Liu-Wang state.

Planned tactic syntax in `RealRooted/Tactic/LiuWang.lean`:

```lean
rr_lw_global_nonpos_sequence_nonzero_auto using
  base := hbase,
  pos_lc := hpos,
  lag := B,
  recurrence := hrec,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_global_nonpos_sequence_interlaces_auto using
  base := hbase,
  pos_lc := hpos,
  lag := B,
  recurrence := hrec,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_global_nonpos_sequence_den_nonzero_auto using
  base := hbase,
  pos_lc := hpos,
  lag := B,
  raw_recurrence := hraw,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_global_nonpos_sequence_den_interlaces_auto using
  base := hbase,
  pos_lc := hpos,
  lag := B,
  raw_recurrence := hraw,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_global_nonpos_sequence_den_interlaces_auto using
  base := hbase,
  pos_lc := hpos,
  lag := B,
  den_nonzero := hden,
  raw_recurrence := hraw,
  degree_succ := hdeg_succ,
  no_common_roots := hno
```

Planned macro bodies:

```lean
exact
  (RealRooted.LwNonposLagSequenceState.of_nonpos
    (B := B) hbase hpos (by
      intro n r hr
      rr_sign) hrec hdeg_succ hno).ne_zero_sequence

exact
  (RealRooted.LwNonposLagSequenceState.of_nonpos
    (B := B) hbase hpos (by
      intro n r hr
      rr_sign) hrec hdeg_succ hno).interlaces_sequence

exact
  (RealRooted.LwNonposLagSequenceState.of_den
    (B := B) hbase hpos (by
      intro n r hr
      rr_sign) hden hraw hdeg_succ hno).ne_zero_sequence

-- The denominator interlacing case is the same construction, followed by
-- `.interlaces_sequence`.
```

Keep `(B := B)` explicit so the lag used by `rr_sign` is pinned by the surface
syntax rather than inferred from the recurrence.  Put the macro cases in a
small dedicated `macro_rules` block near the global-nonpositive syntax, not in
the large Liu-Wang dispatcher, since previous projection slices hit macro
recursion limits there.

Examples should stay abstract and catalog-free in
`RealRooted/Tactic/Examples/LiuWang.lean`:

- direct nonzero endpoint for the non-denominator shell;
- one non-denominator interlacing endpoint using a constant negative-square
  lag;
- one non-denominator endpoint using an `n`-dependent scaled negative
  quadratic lag;
- direct nonzero endpoint for the denominator shell;
- one denominator endpoint without explicit `den_nonzero`, covering the
  default denominator macro rule;
- one denominator endpoint with an explicit `den_nonzero`, covering the base
  macro rule;

Claude-derived review notes kept: preserve the existing keyword order; pin the
lag with `(B := B)`; keep the `_den` optional-denominator self-dispatch
pattern; and close projection goals with plain `exact` rather than a
projection-tolerant finisher.  The local heartbeat failure is the reason this
slice intentionally adds nonzero endpoints despite the initial review
suggestion to avoid aliases; splitting endpoints were not kept because the
candidate macros remained heartbeat-heavy in the generic examples.

### 2026-07-30 AllCombo Endpoint Splits Projections

Status: completed.

Add a small catalog-agnostic AllCombo golf slice for endpoint splitting.
Currently `AllComboRealRooted f g` immediately proves `f.Splits` and
`g.Splits` by specializing the pencil at `(1, 0)` or `(0, 1)`, but the public
surface mostly exposes this through either explicit scalar syntax or
`isRealRooted_left/right`, which unnecessarily carries a nonzero certificate
when the goal is only splitting.

Planned core lemmas in `RealRooted/AllCombo.lean`, inside the first
`AllComboRealRooted` namespace block:

```lean
lemma left_splits {f g : ℝ[X]} (hall : AllComboRealRooted f g) : f.Splits
lemma right_splits {f g : ℝ[X]} (hall : AllComboRealRooted f g) : g.Splits
```

Then redefine the existing bundled endpoint lemmas as:

```lean
lemma isRealRooted_left
    (hall : AllComboRealRooted f g) (hf0 : f ≠ 0) :
    f ≠ 0 ∧ f.Splits :=
  ⟨hf0, hall.left_splits⟩

lemma isRealRooted_right
    (hall : AllComboRealRooted f g) (hg0 : g ≠ 0) :
    g ≠ 0 ∧ g.Splits :=
  ⟨hg0, hall.right_splits⟩
```

Planned sequence wrappers and tactics in `RealRooted/Tactic/AllCombo.lean`:

```lean
theorem allCombo_sequence_left_splits
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, (F i).Splits

theorem allCombo_sequence_right_splits
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i)) :
    ∀ i : Nat, (G i).Splits

rr_all_combo_left_splits using all_combo := hall
rr_all_combo_right_splits using all_combo := hall
rr_all_combo_sequence_left_splits using all_combo := hall
rr_all_combo_sequence_right_splits using all_combo := hall
```

Examples should be abstract smoke tests in
`RealRooted/Tactic/Examples/AllCombo.lean`.  A small call-site golf pass may
rewrite low-blast uses that currently discard the nonzero conjunct solely to
recover `.Splits`.  Avoid touching `CommonInterleaverTwo.lean` in this slice
because it is one of the known Erik conflict-plan files.  Do not tag the new
lemmas as `[simp]`; use explicit calls so they do not fire on metavariable
splitting goals.

Claude-derived review notes: keep the `simpa using hall 1 0` and
`simpa using hall 0 1` proofs centralized in the core lemmas, make tactic
macros expand to `exact`, use one-argument `using all_combo := ...` syntax,
and keep the slice free of sequence-specific/OEIS logic.

### 2026-07-30 AllCombo Closed-Form Exits

Status: completed.

Add tactic wrappers for the new closed-form exit lemmas in
`RealRooted/AllCombo.lean`.  This is a catalog-agnostic tactic slice:
generated files must still supply the all-combo hypothesis, the closed-form
identity, and any required nonzero certificate explicitly.

Planned backend wrappers in `RealRooted/Tactic/AllCombo.lean`:

```lean
theorem allCombo_sequence_splits_of_eq_combo
    {F G P : Nat -> ℝ[X]} {a b : Nat -> ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i) :
    ∀ i : Nat, (P i).Splits
```

```lean
theorem allCombo_sequence_ne_zero_and_splits_of_eq_combo
    {F G P : Nat -> ℝ[X]} {a b : Nat -> ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i)
    (hP0 : ∀ i : Nat, P i ≠ 0) :
    ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits
```

Planned tactic syntax:

```lean
rr_all_combo_splits_of_eq_combo using
  all_combo := hall,
  eq_combo := hp

rr_all_combo_ne_zero_and_splits_of_eq_combo using
  all_combo := hall,
  eq_combo := hp,
  nonzero := hp0

rr_all_combo_sequence_splits_of_eq_combo using
  all_combo := hall,
  eq_combo := hP

rr_all_combo_sequence_ne_zero_and_splits_of_eq_combo using
  all_combo := hall,
  eq_combo := hP,
  nonzero := hP0
```

The examples should be abstract smoke tests in
`RealRooted/Tactic/Examples/AllCombo.lean`, with no sequence names or
catalog-specific comments.

### 2026-07-30 AllCombo Linear Recombination Frontends

Status: completed.

Add tactic wrappers for the existing all-combination linear-recombination
closure.  This is still a purely certificate-driven frontend: the caller
supplies the all-combo hypothesis and both endpoint equality certificates.
The tactic does not solve coefficient identities or guess a change of basis.

Planned backend wrapper in `RealRooted/Tactic/AllCombo.lean`:

```lean
theorem allCombo_sequence_linear_recombination
    {F G P Q : Nat -> ℝ[X]} {a b c d : Nat -> ℝ}
    (hall : ∀ i : Nat, AllComboRealRooted (F i) (G i))
    (hP : ∀ i : Nat, P i = C (a i) * F i + C (b i) * G i)
    (hQ : ∀ i : Nat, Q i = C (c i) * F i + C (d i) * G i) :
    ∀ i : Nat, AllComboRealRooted (P i) (Q i)
```

Planned tactic syntax:

```lean
rr_all_combo_linear_recombination using
  all_combo := hall,
  left_eq_combo := hp,
  right_eq_combo := hq

rr_all_combo_sequence_linear_recombination using
  all_combo := hall,
  left_eq_combo := hP,
  right_eq_combo := hQ
```

The examples should be abstract smoke tests only.  A later generated proof body
may use these wrappers as the transport layer, but no generated-search tactic
is introduced here.

### 2026-07-30 Generated-Row Scalar Helper Cleanup

Status: completed.

The tactic layer should be catalog-agnostic.  The scalar-denominator helpers
already live under generic names in `RealRooted/Tactic/ScalarDen.lean`:

```lean
rr_scalar_active_den_all
rr_scalar_active_den_all_term
rr_scalar_coeff_at n
rr_scalar_coeff_all
rr_scalar_coeff_all_term
```

The generated-row defaults now route through these `rr_scalar_*` names.  Older
catalog-facing aliases remain as compatibility shims, but reusable tactic code
should not depend on catalog-named helper syntax.

The generic `RealRooted.Tactic` entry point no longer re-exports the historical
catalog facade.  Existing generated or catalog-facing files can still import
that compatibility facade directly, while ordinary tactic users get the
reusable backend modules without catalog-specific syntax.

Likewise, the generic `RealRooted.Tactic.Examples` umbrella does not import
historical catalog-facing example batches by default.  Those modules remain
explicitly buildable regression files, but direct imports are required so the
ordinary example aggregate stays catalog-neutral.

The documentation-only target ledger `RealRooted.Tactic.Targets` follows the
same rule.  It remains directly importable, but is not re-exported from
`RealRooted.Tactic`, since ordinary tactic users do not need sequence target
notes in the generic tactic API.

### 2026-07-30 Finish Named-Wrapper Fixture Cleanup

Status: implemented in `RealRooted/Tactic/Examples/Finish.lean`.

`RealRooted/Tactic/Examples/Finish.lean` should stay a generic tactic example
module.  Its named-wrapper regression tests should not import a concrete
catalog sequence.  Replace the sequence-backed fixture with local synthetic
families:

```lean
def namedFinishSmoke (n : Nat) : ℝ[X] := 1
def namedFinishSmokeRefined (n : Nat) : List ℝ[X] := []
```

and generated-style wrappers:

```lean
theorem namedFinishSmoke_generated_realRooted (n : Nat) :
    namedFinishSmoke n ≠ 0 ∧ (namedFinishSmoke n).Splits
theorem namedFinishSmoke_generated_ne_zero (n : Nat) :
    namedFinishSmoke n ≠ 0
theorem namedFinishSmoke_generated_splits (n : Nat) :
    (namedFinishSmoke n).Splits
theorem namedFinishSmoke_generated_interlaces (n : Nat) :
    IsInterlacingSeq0Nonneg (namedFinishSmokeRefined n)
```

The examples should continue to exercise `rr_nonzero`, `rr_splits`,
`rr_realrooted`, `rr_interlaces`, and `rr_finish`, but the file-level
OEIS/A-number scan should become empty.

Verification passed with focused builds for
`RealRooted.Tactic.Examples.Finish` and `RealRooted.Tactic.Examples`, followed
by full `lake build RealRooted`, using the external-cache Lake recipe.

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

### 2026-07-30 Liu-Wang State Projection Golf

Status: completed.

The strict-degree `LwNonposLagSequenceState` package already projects the
`Prec` chain, rowwise bundled real-rootedness, and consecutive interlacing.
Added explicit endpoint projections so users and generated proof bodies do not
need to call a real-rootedness tactic when the target is only nonzero or only
`Splits`:

```lean
theorem LwNonposLagSequenceState.ne_zero_sequence
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, P n ≠ 0

theorem LwNonposLagSequenceState.splits_sequence
    (h : LwNonposLagSequenceState P A B) :
    ∀ n : Nat, (P n).Splits
```

Add tactic facades:

```lean
rr_lw_nonpos_lag_state_nonzero using state := hstate
rr_lw_nonpos_lag_state_splits using state := hstate
```

Both are smoke-tested on the existing unit-`X` state example block in
`RealRooted/Tactic/Examples/LiuWang.lean`.  The tactic cases live in their own
small `macro_rules` block rather than the large Liu-Wang dispatcher block, to
avoid pushing that existing macro block over Lean's recursion limit.  This is
a generic projection/golf slice only: no new recurrence shape, no
sequence-specific tactic, no `rr_ore`, and no catalog references in reusable
Lean.

### 2026-07-30 Liu-Wang Strict Branch Sequence State

Status: completed.

The next plateau-safe abstraction should promote the existing active-range
same-degree/successor-degree example skeleton into a reusable state.  The
mathematics is already available through:

- `prec_lw_two_strict_branch_of_neg` for a single adjacent step;
- `prec_sequence_of_base_and_degree_branches` for the sequence induction.

Added a sequence state that keeps the branch evidence explicit:

```lean
structure LwStrictBranchSequenceState (P A B : Nat → ℝ[X]) where
  hbase : Prec (P 0) (P 1)
  hpos : ∀ n : Nat, HasPosLeadingCoeff (P n)
  hrec : ∀ n : Nat, P (n + 2) = A n * P (n + 1) + B n * P n
  hdegree : ∀ n : Nat,
    (P (n + 2)).natDegree = (P (n + 1)).natDegree ∨
      (P (n + 2)).natDegree = (P (n + 1)).natDegree + 1
  hinter : ∀ n : Nat,
    Prec (P n) (P (n + 1)) → Interlaces (P n) (P (n + 1))
  hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r
  hB_neg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (B n).eval r < 0
```

Added projections:

```lean
theorem LwStrictBranchSequenceState.prec_sequence ...
theorem LwStrictBranchSequenceState.isRealRooted ...
theorem LwStrictBranchSequenceState.ne_zero_sequence ...
theorem LwStrictBranchSequenceState.splits_sequence ...
theorem LwStrictBranchSequenceState.interlaces_sequence ...
```

Added tactic endpoints:

```lean
rr_lw_strict_branch_sequence_state using
  base := hbase,
  pos_lc := hpos,
  recurrence := hrec,
  degree_branch := hdegree,
  interlacer := hinter,
  no_common_roots := hno,
  head_neg := hB_neg

rr_lw_strict_branch_state using state := hstate
rr_lw_strict_branch_state_realrooted using state := hstate
rr_lw_strict_branch_state_nonzero using state := hstate
rr_lw_strict_branch_state_splits using state := hstate
rr_lw_strict_branch_state_interlaces using state := hstate
```

This state should not infer plateau patterns, root intervals, or coefficient
signs.  Generated and hand-written files must still supply those certificates.
The reusable tactic layer remains catalog-agnostic and sequence-agnostic.
The existing active-range plateau/successor skeleton example now packages the
data through the state tactic, and a compact smoke example checks the
real-rootedness, nonzero, splitting, and interlacing projection endpoints.

### 2026-07-30 Liu-Wang Strict Branch Direct Endpoints

Status: completed.

Added direct tactic endpoints that construct `LwStrictBranchSequenceState`
inline and immediately project the requested sequence property.  These are
pure golf facades over the explicit state fields; they must not infer degree
branches, root signs, root intervals, or sequence-specific facts.

Added tactics:

```lean
rr_lw_strict_branch_sequence using
  base := hbase,
  pos_lc := hpos,
  recurrence := hrec,
  degree_branch := hdegree,
  interlacer := hinter,
  no_common_roots := hno,
  head_neg := hB_neg

rr_lw_strict_branch_sequence_realrooted using ...
rr_lw_strict_branch_sequence_nonzero using ...
rr_lw_strict_branch_sequence_splits using ...
rr_lw_strict_branch_sequence_interlaces using ...
```

The implementation should keep these cases in a small dedicated `macro_rules`
block, not in the large Liu-Wang dispatcher, to avoid repeating the recursion
limit issue from the state projection slice.  Smoke examples should exercise
the direct endpoints on the same plateau/successor skeleton data already used
for the state package.
The plateau/successor skeleton example now closes the `Prec` chain directly,
while a separate smoke example checks the direct real-rootedness, nonzero,
splitting, and interlacing endpoints.

### 2026-07-30 Liu-Wang Nonpositive-Lag Direct Projections

Status: completed.

The nonpositive-lag strict-degree shell already has:

- direct `Prec` and bundled real-rootedness tactics,
  `rr_lw_nonpos_lag_sequence` and
  `rr_lw_nonpos_lag_sequence_realrooted`;
- state projections
  `rr_lw_nonpos_lag_state_nonzero`,
  `rr_lw_nonpos_lag_state_splits`, and
  `rr_lw_nonpos_lag_state_interlaces`.

Added direct projection endpoints that construct
`LwNonposLagSequenceState.of_nonpos` inline and project the requested property:

```lean
rr_lw_nonpos_lag_sequence_nonzero using
  base := hbase,
  pos_lc := hpos,
  lag_nonpos := hB,
  recurrence := hrec,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_nonpos_lag_sequence_splits using ...
rr_lw_nonpos_lag_sequence_interlaces using ...
```

This is a pure facade/golf slice.  It should not add any new recurrence
shape, infer signs or degrees, touch generated sequence files, or introduce
catalog-specific names.
The generic examples now include a compact smoke test for the direct nonzero,
splitting, and consecutive-interlacing projections.

### 2026-07-30 Liu-Wang Inductive Nonpositive-Lag Endpoints

Status: completed.

The inductive nonpositive-lag shell lets the lag sign supplier depend on the
current row's real-rootedness certificate.  The reusable constructor already
exists:

```lean
LwNonposLagSequenceState.of_inductive_nonpos
```

Added direct tactic endpoints that construct this state inline and project the
requested sequence property:

```lean
rr_lw_nonpos_lag_sequence_inductive_nonpos using
  base := hbase,
  pos_lc := hpos,
  lag_inductive_nonpos := hB,
  recurrence := hrec,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_nonpos_lag_sequence_inductive_nonpos_realrooted using ...
rr_lw_nonpos_lag_sequence_inductive_nonpos_nonzero using ...
rr_lw_nonpos_lag_sequence_inductive_nonpos_splits using ...
rr_lw_nonpos_lag_sequence_inductive_nonpos_interlaces using ...
```

This is another pure facade/golf slice.  The lag-sign supplier remains an
explicit certificate; the tactic must not infer row real-rootedness, signs,
degrees, or sequence-specific facts.
The generic examples now use the direct `Prec` endpoint for the inductive
lag-sign skeleton and include a compact smoke test for bundled
real-rootedness, nonzero, splitting, and consecutive interlacing.

### 2026-07-30 Liu-Wang Denominator Nonpositive-Lag Projections

Status: completed.

The denominator-normalized nonpositive-lag shell already has direct `Prec`
and bundled real-rootedness endpoints:

```lean
rr_lw_nonpos_lag_sequence_den using ...
rr_lw_nonpos_lag_sequence_den_realrooted using ...
```

Added direct projection endpoints that construct
`LwNonposLagSequenceState.of_den` inline and project the requested property:

```lean
rr_lw_nonpos_lag_sequence_den_nonzero using
  base := hbase,
  pos_lc := hpos,
  lag_nonpos := hB,
  den_nonzero := hden,
  raw_recurrence := hraw,
  degree_succ := hdeg_succ,
  no_common_roots := hno

rr_lw_nonpos_lag_sequence_den_splits using ...
rr_lw_nonpos_lag_sequence_den_interlaces using ...
```

This is a pure facade/golf slice over explicit denominator-normalized
certificates.  It should not infer denominators, signs, degrees, or sequence
facts, and it should stay independent of catalog files.
The cases live in a dedicated `macro_rules` block: placing them in the large
Liu-Wang dispatcher hit the existing macro recursion-depth limit.  The generic
examples include a compact smoke test for nonzero, splitting, and consecutive
interlacing.

### 2026-07-30 PosCombo Same-Degree Split Projections

Status: completed.

The positive-combination same-degree API already has bundled endpoint
real-rootedness projections:

```lean
PosComboRealRooted.isRealRooted_left_of_sameDegree
PosComboRealRooted.isRealRooted_right_of_sameDegree
```

Manual proof files still often peeled `.2` from these bundled facts when they
only needed `Splits`.  Added split-only endpoint projections parallel to the
existing succ-degree split API:

```lean
lemma PosComboRealRooted.left_splits_of_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) : f.Splits

lemma PosComboRealRooted.right_splits_of_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) : g.Splits
```

Added sequence wrappers in `RealRooted/Tactic/PosCombo.lean`:

```lean
posCombo_sequence_left_same_degree_splits
posCombo_sequence_right_same_degree_splits
```

Added tactic frontends, keeping keyword order parallel to the existing
same-degree real-rootedness frontends:

```lean
rr_pos_combo_left_same_degree_splits using
  pos_combo := hfg,
  left_pos_lc := hf_pos,
  right_pos_lc := hg_pos,
  same_degree := hdeg

rr_pos_combo_sequence_left_same_degree_splits using ...

rr_pos_combo_right_same_degree_splits using ...

rr_pos_combo_sequence_right_same_degree_splits using ...
```

Smoke examples stay abstract and catalog-free in
`RealRooted/Tactic/Examples/PosCombo.lean`.  The new core projections are used
for low-blast manual golf in `RealRooted/SameDegreeCubicRootCount.lean`, where
the old code repeatedly derived `f.Splits` and `g.Splits` from the `.2` field
of bundled same-degree real-rootedness.
