# Formalization architecture for the B132 integral proof

Owner: delegated read-only Lean-library/theory lane. Parent owns issue #1623,
the final mathematical audit, and the certificate publication. Claude retains
the sole Lean implementation and build lane. No source edits or builds were
performed for this plan.

Source audit: origin/main `cbc151407cdd33b3cd0b666650f278fa02d69779`.
The primary checkout remains older; implementation must use current main.

## Mathematical target and current boundary

The intended final theorem is that every B_n has only simple negative roots,
with the constant rows B_0=B_1=1 and B_2=2 included vacuously. The recurrence
family has degree floor(2(n-1)/3) for n>=1 and nonnegative coefficients.
We separate its theorem from the identification with the permutation model.

The current paper route partitions q=(s-1)^(1/3)>0 into:

- 0<q<=1/200: the audited near comparison T_n<A_n for every n>=1;
- 1/200<=q<=8: the exact compact certificate for every n>=100;
- s>=512: the audited far comparison for every n>=1.

The ranges overlap and cover every s>1. The independently checked finite
rows below 100 complete the intended all-index proof once all artifact
and proof audits are accepted. This note does not change their status.

At inspection, `/tmp/rr132-compact-certificate-full.json` has status complete,
4471 parameter boxes, no remaining boxes, 80-bit dyadic endpoints, and N=100.
Its SHA256 is
`5cbbebe20c8b5fb9883c09f6f6577428e93b8d17fe4a401847417552d17d53a0`.
The 10974058-byte artifact must be durably pinned by the parent. A successful
external exact checker is not yet a Lean proof of its soundness.

## Proposed module order

Use namespace `RealRooted.BigDescents132` and a topic directory under
`RealRooted/CombinatorialExamples/BigDescents132/`. The names below are
proposed declarations, not already checked APIs.

1. **Basic / GeneratingFunction.** Define the recurrence polynomial family
   over the rationals or integers and transport it to real polynomials.
   Prove initial rows, `bigDescentPoly_ne_zero`, coefficient nonnegativity,
   `bigDescentPoly_natDegree`, and `bigDescentPoly_eval_zero`. Establish
   the algebraic generating function and the selected square-root branch
   near its origin. Do not use a definition by nonintegral natural division.
   The canonical generator and model-identity debt already belong to #1623.

2. **Quartic / Phase.** Construct the two real roots a,b and the unique
   upper-half-plane root lambda of W_s, for s>1. Prove exact factorization,
   0<a<1<b<s, b<|lambda|, and the required endpoint/angle formulas.
   Establish the continuous explicit phase

       theta=arg lambda,
       phi=(arg(lambda-a)+arg(lambda-b)+theta)/2
             -arg(lambda-s)-3pi/4,
       Phi_n=n theta+phi.

   Prove `phase_strictMono` for n>=1, its endpoint limits, and existence
   of every finite grid point Phi_n=m*pi. The actual angle functions use
   upper-half-plane arguments; avoid introducing an arbitrary global
   branch of arg(kappa). The identity exp(i phi)=kappa/|kappa| must retain
   its sign, rather than follow just from squaring both sides.

3. **RadialIntegral.** Define the continuous factor H_s(u), its integral
   I_n, the positive real-cut integral T_n, and the real amplitude A_n.
   Prove the exact identity

       B_n(1-s)=T_n+(4/sqrt(pi))Re(kappa lambda^n I_n).

   This is the largest missing analytic dependency. Its proof needs
   coefficient extraction, continuation of the chosen square root on the
   complement of the cuts, the removable pole at s, both boundary jumps,
   and vanishing endpoint/corner contributions. Existing circle-integral
   APIs do not already prove this deformation around two slits and a
   broken radial cut. The factor 4/sqrt(pi), orientation, and positive
   sign of T_n are acceptance obligations.

4. **IntegralComparison / Near / Far.** Prove the beta-moment identities
   directly by interval integration by parts, then the general comparison

       Re H_s(u)>h0>0 for all u in [0,1]
       ==> T_n/A_n <= D0(2n+1)(b/|lambda|)^n.

   Prove the two endpoint bounds with the audited rational constants.
   Use the independently audited elementary appendix of
   `132-near-kernel-agent-2026-10-13.md` for near-root localization.
   Polynomial signs and the intermediate value theorem give
   -r+q<A<-r+3q/2 for the negative scaled root, where r=4^(1/3).
   Vieta then gives |Z-r*exp(i*pi/3)|<17q/10<2q for the upper
   scaled root. These are the same bounds used by all subsequent
   constants. Rouché's theorem is no longer a dependency.
   The far proof uses angles, real inequalities and interval-integral
   comparison. Neither proof needs entire-function limits, Stirling's
   formula, or canonical products.

5. **Certificate / Arithmetic, Soundness, Data.** Formalize a small exact
   rational/dyadic interval evaluator and its soundness, then replay the
   accepted compact certificate. The generator remains untrusted: fixed
   root brackets, interval covers and arithmetic witnesses are the input.
   Do not formalize the exploratory bisection/search algorithm. Details
   are below.

6. **SmallCases / RootSigns.** Certify B_0 through B_99 with exact
   polynomial identities and rational sign-separating points or Euclid
   chains. Combine endpoint and compact comparisons to prove every
   required phase-grid sign for n>=100. Apply the existing sign-change
   API, retain the resulting distinct root witnesses, and obtain
   simplicity and strict negativity.

The final declarations should be ordinary theorems:

    bigDescentPoly_splits (n : Nat)
    bigDescentPoly_hasSimpleRoots (n : Nat)
    bigDescentPoly_root_neg (n : Nat) (hr : IsRoot (bigDescentPoly n) r)

The permutation-enumerator theorem follows only after its generating
function or recurrence identity is checked. An explicit model-identity
boundary is acceptable; assuming the integral formula or comparison in
the final unconditional root theorem is not.

## Existing APIs that genuinely help

- `RealRooted.splits_of_strict_sign_changes_fin`, in
  `RootCounting/SignChanges.lean`, handles d+1 ordered sign-alternating
  points. It requires p!=0 and natDegree p=d.
- `RealRooted.splits_of_sign_changes_with_left_endpoint` handles the
  case with only d finite points and a positive leading coefficient.
  It supplies the missing leftmost point from the leading-term sign.
  These exactly match ell_n>0 and ell_n=0 after reversing the phase
  grid, since t=1-s is decreasing.
- `exists_roots_strictly_interlacing_of_consecutive_signs`, used inside
  that API, supplies distinct real-root witnesses. Together with
  `RealRooted.RootCounting.roots_nodup_of_card_roots` and
  `HasSimpleRoots.of_roots_nodup`, it upgrades the final degree count
  to simple roots. A short companion to the sign-change theorem may
  expose this existing proof rather than duplicate it in B132.
- `RealRooted.roots_nonpos_of_hasNonnegCoeffs` and
  `isRoot_nonpos_of_hasNonnegCoeffs`, in `Basic/Coefficients.lean`,
  exclude positive roots; the positive constant coefficient excludes zero.
- `RealRooted.splits_iff_distinctSturmVariations_sub_eq_natDegree`,
  in `RootCounting/Sturm.lean`, is an exact finite alternative. Its
  interval must contain every real root, and its right side uses the
  squarefree part's degree. A separate squarefreeness check is needed
  if the chosen certificate only establishes splitting.
- `rr_interlaces_explicit` proves exact Euclidean interlacing chains.
  The BigDescents321 small-case files demonstrate kernel-checked integer
  list identities and Bezout certificates. They are useful patterns,
  not certificates for B132. `rr_splits_explicit` alone is not a generic
  high-degree solver: its inspected interface handles small degree or
  complete rational factorization.
- `Complex.circleIntegral_logDeriv_eq_sum_zeros` and related theorems
  in `Mathlib/Analysis/Complex/ArgumentPrinciple.lean` provide circle
  zero counts with explicit factorization hypotheses. They do not
  directly provide the required branch-cut integral formula. Neither
  Hurwitz nor Rouché is needed for the audited endpoint estimates;
  near-root localization uses polynomial signs, IVT, and Vieta.

For quartic geometry, W_s''(x)=12((x-1)^2+s-1)>0 is an elementary
way to obtain at most two real roots, supplementing the sign changes
W_s(0)>0, W_s(1)<0, W_s(s)>0. It avoids requiring a generic theorem
that classifies quartics from the discriminant sign. All the additional
ordering and modulus inequalities must still be proved.

## What the compact checker must prove

The new reflected checker has a bounded mathematical scope:

1. Sound outward rounding for addition, subtraction, multiplication,
   division when zero is excluded, integer powers, and nonnegative
   square roots. An integer square-root witness can use its two defining
   squared inequalities. Complex rectangles then use pairs of intervals.
2. Exact coverage of [1/200,8], with ordered touching/overlapping
   rational endpoints. For every parameter box, check the signs that
   locate the two scaled real roots of

       P_q(z)=z^4+6qz^2+(4-4q^3)z-3q^2.

   Root uniqueness comes from Quartic. The external searcher's root
   iteration count is irrelevant to soundness.
3. Exact coverage of t in [0,1/q_lower], containing t=(1-u)/q
   for every u in [0,1] and every q in that parameter box.
4. Nonzero denominators and strict positivity of

       (Im(H^2))^2+4h0^2 Re(H^2)-4h0^4.

   Continuity and H(1)=1 then select Re H>h0; taking a complex
   square root numerically is unnecessary.
5. A rational upper bound r<1 for b/|lambda|, a positive bound D4
   for D0^4, and a finite rational power inequality at the certified
   maximizing integer

       max(100,ceil((3r-1)/(2(1-r)))).

   Prove the discrete-ratio monotonicity separately, so that a checked
   value at this integer covers every n>=100. Avoid rounded logarithms.

The BigDescents321 `Reflect.check_sound` supplies a precedent for
kernel reduction and polynomial identities, but is not an interval
arithmetic soundness theorem. Prove this new checker before accepting
generated data. Chunk the 4471-box artifact into coherent lemmas to
keep compilation bounded and diagnosable. A theorem from `decide +kernel`
plus a proved checker is suitable; an opaque assertion that an external
program returned true is not.

## Implementation priorities and acceptance

First formalize the recurrence/degree facts and the exact finite rows;
these provide immediate checked results and test the chosen polynomial
representation. Next prove the reusable comparison and certificate
soundness, then the quartic/phase and endpoint estimates. The contour
identity should receive an early feasibility review because it is the
largest analytic risk. Complete the final assembly only after every
dependency has an unconditional checked witness.

The final route no longer depends on #1646, #1679, the Motzkin boundary
multiplier, or the Laguerre--Polya endpoint functions. Those remain
independent useful theory; they should not delay this proof.

Acceptance requires exact coverage and all finite rows, strict signs
rather than nonnegative ones, constants and the n modulo 3 boundary,
the selected branches and contour orientation, certificate-checker
soundness, and the final exact-revision build and applicable axiom audits.
No new B132 target in this plan is reported as already Lean formalized.
