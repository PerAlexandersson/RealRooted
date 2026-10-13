# A rational certificate for the compact B132 parameter interval

Owner: delegated eventual-proof audit agent; parent owns the interval
prototype and integration. Status: exact sufficient conditions and a
certificate plan; no completed compact cover is asserted here.
Related issue: #1623. No Lean source or builds were changed.

The independently audited endpoint comparisons cover q<=1/200 and
s>=512, where q=(s-1)^(1/3). Thus it suffices to handle

    1/200<=q<=511^(1/3).

We can harmlessly enlarge the upper endpoint to q=8 when constructing
a rational cover. A certificate on this compact interval, together with
exact checks for a finite set of degrees, could complete the all-index
argument. Numerical samples are used only to choose subdivisions and
candidate lower bounds; the accepted artifact must consist of exact
inequalities valid on every full interval.

## Source-root enclosures

Use the scaled polynomial

    P_q(z)=z^4+6q z^2+(4-4q^3)z-3q^2.

It has exactly two real roots A<0<B, corresponding to
a=1+qA and b=1+qB. The other roots are Z and conj(Z), with

    Re Z=-(A+B)/2,
    (Im Z)^2=6q+3A^2/4+AB/2+3B^2/4.

Consequently the original upper root lambda=U+iV satisfies

    U=1-q(A+B)/2,
    V^2=q^2*(6q+3A^2/4+AB/2+3B^2/4),
    R^2=U^2+V^2.

For a rational parameter interval Q=[q_0,q_1], choose rational
brackets [A_0,A_1] and [B_0,B_1]. Certify, for every q in Q,

    P_q(A_0)>0, P_q(A_1)<0, A_0<A_1<0,
    P_q(B_0)<0, P_q(B_1)>0, 0<=B_0<B_1.

The known quartic root count and the intermediate value theorem then
identify the enclosed roots. For each fixed bracket endpoint, P_q is
a polynomial of degree at most three in q. Its signs can be certified
by Bernstein coefficients after the affine substitution from Q to
[0,1]. Floating-point root values do not enter the accepted certificate.

These enclosures supply a rational rectangle for (q,A,B). Its points
need not themselves satisfy the quartic relations; proving the required
inequalities on that larger rectangle is a sufficient condition.
Subdivision in q makes the independent root brackets tighter when
their extra width prevents a certificate.

## A polynomial test for the real part of H

Choose a rational h_0>0 on each q interval. Write

    H_s(u)^2=X(u)+iY(u).

The exact criterion

    E(u)=Y(u)^2+4h_0^2 X(u)-4h_0^4>0,   0<=u<=1,              (1)

implies Re H_s(u)>h_0 throughout the interval. Indeed, with
w=H_s(u)^2,

    E=(|w|+Re w-2h_0^2)(|w|-Re w+2h_0^2).

The second factor is strictly positive. Hence the principal square
root of w has real part greater than h_0. Also (1) rules out w on
the nonpositive real axis. Since H_s is continuous and H_s(1)=1,
its square root has that positive branch on the connected interval.

There is a polynomial form of (1). Put

    P(u)=(u lambda-a)(u lambda-b)(u lambda-conj(lambda)),
    N(u)=P(u)(lambda-s)^2,
    D(u)=P(1)(u lambda-s)^2.

Then H_s(u)^2=N(u)/D(u), and D is nonzero by the root geometry.
Let Z=N conj(D). Clearing the positive denominator gives

    E_*=(Im Z)^2+4h_0^2 Re Z |D|^2-4h_0^4 |D|^4>0.           (2)

This is a real polynomial in u,U,V,a,b,s. All powers of V are
even: Re Z and |D|^2 have even V powers, while Im Z has odd
powers and is squared. Substituting the displayed exact expression
for V^2 therefore produces a polynomial with rational coefficients
in q,A,B,u. Its degree in u is at most ten.

Equation (2) is suitable for tensor Bernstein coefficients on a
rational box. All coefficients positive prove the inequality on the
box. If a coefficient fails, subdivide; failure of this sufficient
test is not a counterexample to positivity. Direct rational interval
evaluation of H^2 and (1) is an alternative, and the parent lane is
prototyping that route. This agent does not duplicate that script.

## A moment certificate with no radicals

The real-cut monotonicity bound gives

    T_n/A_n <= D_0(2n+1)rho^n,
    rho=b/R,
    D_0=|b-lambda|sqrt(b-a)|lambda-s|
          /[2h_0 |c(1)|R^2 sqrt(b)].                          (3)

Although D_0 contains radicals, its fourth power is rational in
the source-root variables. Define

    D_a=(U-a)^2+V^2,
    D_b=(U-b)^2+V^2,
    D_s=(U-s)^2+V^2,
    r=U^2+V^2.

Then cancellation gives

    D_0^4=D_b*(b-a)^2*D_s^2
              /[64h_0^4 D_a V^2 r b^2].                    (4)

To verify it, use
|c(1)|^4=4V^2 D_a D_b/r^3 in the fourth power of (3).
Every denominator in (4) is positive. Thus the sufficient moment
condition is the entirely rational inequality

    D_0^4(2n+1)^4(b^2/r)^(2n)<1.                             (5)

Suppose a box certifies D_0^4<=d_*, b^2/r<=p_*<1, with rational
d_*,p_*. A finite list of rational power checks establishes (5)
for all n>=N. Specifically, choose M>=N with

    p_*(2M+3)^2<=(2M+1)^2.

Then (2n+1)p_*^(n/2) decreases for every n>=M. Check (5) with
the upper bounds d_*,p_* for n=N,...,M; the last check and this
monotonicity prove the entire tail. No rounded logarithm or square
root is used. This matters near the lower q endpoint, where the
maximum may occur substantially after the proposed N.

## Acceptance artifact

A completed certificate should retain, for each q interval:

- rational endpoints covering [1/200,8] with no gaps;
- rational A and B root brackets and exact sign certificates;
- the rational h_0 and every u subdivision used for (1) or (2);
- exact lower bounds for all cleared denominators;
- rational d_*,p_* and the finite moment-power checks through M;
- the common degree threshold N and exact B_n checks below N.

The degree threshold is proved only after every parameter box passes.
A numerically observed threshold or a sample grid does not supply a
certificate. Root brackets must be valid on the whole q interval,
not merely at its midpoint or endpoints.

## Rust capability audit

We read the shared Rust library guide, ran cargo metadata, inspected
the runtime registry, and searched the relevant source, tests, and
examples. The existing `polytool` crate provides exact univariate
Bernstein coordinates via `bernstein_basis_coordinates` in
`polytool/src/basis.rs`, exported through the `bernstein` CLI.
It accepts rational coefficients and supports degree elevation.
The existing tests in `polytool/tests/cli_bigint.rs` cover its exact
coefficient and JSON conventions. Applying that map successively
to coordinate axes gives tensor Bernstein coordinates; there is no
need to reimplement its univariate conversion.

We found no registered complex interval API or ready multivariate
root-box certificate API. The parent's bounded rational interval
prototype is therefore a justified exploratory exception. If it
becomes reusable, its stable core belongs in the narrowest owning
Rust crate after coordinating source ownership. No Rust source was
changed and no new polynomial family was generated here.

## Search-code audit and independent replay

We read `/tmp/rr132-compact-certify.py` without editing it. The
outward dyadic arithmetic is correct for addition, multiplication,
division, integer powers, and square roots. Its separate searches for
each bracket endpoint preserve the necessary exact polynomial sign.
The source-root identities and the scaled H^2 formula are correct.
Its t=(1-u)/q cover [0,1/q_left] contains every actual u in [0,1].

The discrete moment maximum also has an exact shortcut. For 0<r<1,
the sequence (2n+1)r^n changes from increasing to decreasing at

    n=ceil((3r-1)/(2(1-r))).

Thus over n>=N its maximum is attained at the greater of this
integer and N. An integer equality at the threshold gives two
equal adjacent maxima, so either is valid. The search script's
single peak check is sufficient and can replace the finite list
described above.

A separate verifier was written at
`/tmp/rr132-certificate-independent-check.py`. It imports none of
the search code. It recomputes root endpoint signs, each kernel
rectangle's positivity inequality, the rational moment bound, and
both u and q coverage. It uses exact Fraction arithmetic for all
intermediate operations; dyadic enclosures are introduced only for
input data, with their inclusion checked. Its receipt records the
SHA-256 hash of the exact input artifact and distinguishes complete
coverage from a checked partial prefix. Acceptance of a completed
compact certificate requires this replay to finish successfully.

## Completed independent replay

The full immutable artifact
`/tmp/rr132-compact-certificate-full.json` passed the independent
Fraction verifier on 2026-10-13. The checked result is

    forall q in [1/200,8], forall integer n>=100,
      A_n(1+q^3)>0 and T_n(1+q^3)/A_n(1+q^3)<1.

The certificate has 4,471 parameter intervals and 84,896 kernel
rectangles. The verifier recomputed all root endpoint signs, all
kernel positivity inequalities, every moment peak, and exact
coverage of the entire parameter interval. No assertion failed.
The source artifact's SHA-256 hash is

    5cbbebe20c8b5fb9883c09f6f6577428e93b8d17fe4a401847417552d17d53a0

The receipt is `/tmp/rr132-compact-full-independent-check.json`;
it records complete coverage, threshold 100, and runtime 86.609
seconds. The parent lane should preserve the artifact, verifier,
and receipt together in its durable checkpoint.

This completes the compact certificate obligation. Combining it
with the audited endpoint integral comparisons supplies every phase
grid sign for n>=100. The full B132 theorem additionally requires
the parent to integrate the exact finite-row verification and the
previously audited analytic representation and phase/count lemmas.
