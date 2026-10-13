# Big descents on 132-avoiding permutations

This directory preserves a computer-assisted mathematical proof that every
big-descent polynomial for 132-avoiding permutations has simple negative
roots. The constant rows satisfy the statement vacuously. This is research
evidence for [issue #1623](https://github.com/PerAlexandersson/RealRooted/issues/1623),
not a Lean-checked result or part of the theorem catalog.

Start with [the complete proof](132-all-n-proof-2026-10-13.md) and
[the formalization plan](132-all-n-formalization-plan-agent-2026-10-13.md).
Other notes retain earlier intermediate results and their historical status
labels. The complete proof selects precisely which sections it uses.
In particular, we use the final elementary near-root appendix; Rouché,
entire-function endpoint limits, and canonical products are unnecessary.

The proof combines explicit estimates at both parameter ends, an independently
verified rational interval certificate for every n>=100, and exact Sturm
counts for n=0,...,99. The compact certificate has 4471 parameter intervals
and 84896 kernel rectangles. Three independent agents checked the analytic
estimates, certificate arithmetic, finite data provenance, and final counting.

## Replay the compact certificate

The Python checker uses only the standard library. From this directory:

```bash
gzip -dc 132-all-n-certificate-2026-10-13/rr132-compact-certificate-full.json.gz \
  > /tmp/b132-compact-replay-input.json
python 132-all-n-certificate-2026-10-13/rr132-certificate-independent-check.py \
  /tmp/b132-compact-replay-input.json /tmp/b132-compact-replay-receipt.json
```

The uncompressed certificate SHA256 must be
`5cbbebe20c8b5fb9883c09f6f6577428e93b8d17fe4a401847417552d17d53a0`.
The accepted receipt records complete coverage of [1/200,8] and threshold100.
The checker independently recomputes rational inequalities; it does not
trust the searcher's saved positivity values or import its arithmetic.
The search script is retained for provenance and is unnecessary for replay.

## Replay the finite rows

`verify_rows.py` checks saved data against every defining recurrence identity,
the exact finite input, degree/positivity, and the saved root counts:

```bash
python 132-all-n-certificate-2026-10-13/verify_rows.py
```

To recompute those root counts, build the supplied thin Rust driver against
the existing `polytool` library. It calls
`polytool::count_real_roots_prs_bigint_coeffs`, which counts **distinct** real
roots using an exact primitive integer Sturm sequence. It asserts that this
count equals the original polynomial degree for each of the 100 rows. Given
the compiled library path in `B132_POLYTOOL_RLIB`:

```bash
rustc --edition=2021 -O \
  132-all-n-certificate-2026-10-13/rr132-finite-root-count.rs \
  --extern "polytool=$B132_POLYTOOL_RLIB" \
  -L "dependency=$(dirname "$B132_POLYTOOL_RLIB")" \
  -o /tmp/b132-finite-root-count
/tmp/b132-finite-root-count \
  < 132-all-n-certificate-2026-10-13/rr132-finite-rows.txt \
  > /tmp/b132-finite-root-count.jsonl
```

Compare the output with the preserved JSONL. The source audit used Rust
workspace commit `4349e40c96d4832aae5320c6c08bcdcc99cbcd0f`; the owning
root-count source was clean. This driver generates no polynomial family.
Maintained Rust generator integration remains a separate issue obligation.

## Formalization boundary

The Python arithmetic and Rust output are external exact checks. They do
not replace a Lean soundness proof or kernel replay. The formalization
must establish the contour identity, quartic/phase geometry, both endpoint
estimates, and a sound compact checker before using the final root theorem.
Existing RealRooted sign-change and Sturm APIs can handle the final counting
and finite cases. No Lean files or Lake configuration were changed here.
