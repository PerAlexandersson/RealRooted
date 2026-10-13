# Uniform oscillation and eventual real-rootedness for B132

Owner: academic Codex theory lane. Related issue: RealRooted #1623.
Status: proved on paper using the explicit contour integral below and the
previously proved endpoint limits and count matching. Not Lean verified.
The all-index goal remains OPEN: the proof gives an unspecified threshold.

## The result

There exists N such that, for every n>=N, the polynomial B_n has
d_n=floor(2(n-1)/3) distinct strictly negative roots. In particular, all
sufficiently large B_n are real-rooted with simple roots.

This is stronger than the previously proved proportion-one statement.
We do not infer the conclusion for every n from numerical checks below
an unrelated bound. An explicit sufficient threshold and exact checks
below it, or a separate all-index argument, are still required for the
original conjecture.

We retain the quartic roots a,b,lambda,conj(lambda), with
0<a<1<b<s, Im(lambda)>0, R=|lambda|>b, and

    W_s(w)=w^4-4w^3+6s w^2-4s^2 w+s^2,
    theta=arg(lambda), delta=2pi/3-theta,
    Phi_n=n theta+phi,
    M_n=2|kappa| R^n n^(-3/2).

The definitions and exact phase normalization are those in
`132-phase-count-matching-2026-10-13.md`. We prove the uniform estimate

    |B_n(1-s)/M_n(s)-cos(Phi_n(s))|
        <= C/(n theta(s))+C/(n delta(s)),                         (1)

with a constant C independent of n>=1 and s>1. Constants in this note
are positive and can change from line to line. Existence, rather than
an explicit numerical value, is asserted for each uniform constant.

## An exact radial integral

For 0<=u<=1, define

    c(u)=sqrt(u-a/lambda) sqrt(u-b/lambda)
                         sqrt(u-conj(lambda)/lambda),
    H(u)=c(u)/c(1) * (lambda-s)/(u lambda-s),
    I_n=integral_0^1 u^(n-1)(1-u)^(1/2) H(u) du.                  (2)

All three square roots are principal values. Their arguments avoid
the nonpositive real axis on this interval: the first two have positive
imaginary part; the third has nonzero imaginary part unless theta=pi/2,
when it is positive real. Thus H is continuous and H(1)=1.

Define the positive real integral

    T_n=1/(2pi(s-1)) integral_a^b
           x^(n-1) sqrt((x-a)(b-x)) |x-lambda|/(s-x) dx.           (3)

Then, for every integer n>=1 and s>1,

    B_n(1-s)=T_n+(4/sqrt(pi)) Re(kappa lambda^n I_n).              (4)

We give the contour derivation to fix its signs. In the reciprocal
generating variable w=1/z, the generating function is

    G(w)=V(1/w,1-s)
      =(w^2-2w+s-sqrt(W_s(w)))/(2(1-s)(w-s)),
    G(w)=sum_(n>=1) B_n(1-s) w^(-n) near infinity.

Take sqrt(W_s(w)) asymptotic to w^2 at infinity, with cuts [a,b]
and the broken line from conj(lambda) through 0 to lambda. These cuts
are disjoint. The second consists of the two radial segments. The
apparent pole at w=s is removable: on the positive axis above b,
sqrt(W_s(s))=s(s-1)=s^2-2s+s. There are no other finite poles.

For n>=1, B_n is the integral of w^(n-1)G(w)/(2pi i) around a
large positive contour. Deforming to the cuts is legitimate; small
endpoint circles vanish, as does the circle around the corner at zero,
where G is bounded on each side and w^(n-1) is integrable.

On the upper side of [a,b], sqrt(W_s(x))=i sqrt(-W_s(x)). The upper
side of the positively oriented contour runs from b to a, so its jump
contribution is exactly the positive expression (3).

On the upper radial segment w=u lambda, the side with larger argument
has value

    sqrt(W_s(u lambda))=+i lambda^2 (1-u)^(1/2)c(u),

and the other side has the negative value. This follows by continuing
from w=t lambda, t>1, where the factors of sqrt(W_s(w))/w^2 have
their principal branches. Its contour contribution is

    -lambda^(n+2)/(2pi(s-1)) integral_0^1
        u^(n-1)(1-u)^(1/2)c(u)/(u lambda-s) du
      =(2/sqrt(pi)) kappa lambda^n I_n.

The lower radial segment contributes its complex conjugate. This proves
(4), including the factor and the positive sign of T_n.

## Uniform bounds near s=1

Put q=(s-1)^(1/3). All bounds in this section hold for 0<q<=q0,
where q0 is a sufficiently small fixed positive constant. The simple
root expansions from the quartic note give

    lambda=1+c q+O(q^2),   c=4^(1/3)exp(i pi/3),
    a=1-4^(1/3)q+O(q^2),  b=1+3q^3/4+O(q^6).

Consequently,

    |lambda-mu| is comparable to q,  mu=a,b,conj(lambda),
    |lambda-s| is comparable to q,
    |kappa| is comparable to q^(-5/2),
    log(R/b)>=c0 q.                                             (5)

Here and below “comparable” means upper and lower bounds by fixed
positive constant multiples, uniformly in the indicated parameter range.
The leading terms are nonzero, so the expansions imply these bounds.

We claim that the normalized radial factor satisfies

    |H(u)-1|<=C(1-u)/q,              0<=u<=1.                    (6)

To prove it, set v=1-u. The numerator factors in c(u) have modulus
at most C(q+v), whereas |c(1)|>=c q^(3/2). Furthermore

    |u lambda-s|>=c(q+v).

For u>=1/2 the imaginary part is at least c q; if v is a sufficiently
large multiple of q, the triangle inequality in
u lambda-s=u(lambda-s)-s v gives the lower bound c v. For u<=1/2
the denominator is uniformly bounded away from zero. Together these
prove the displayed bound for every u. Therefore

    |H(u)|<=C sqrt(1+v/q).

When v<=epsilon q for a sufficiently small fixed epsilon, all three
numerator factors remain a distance at least c q from zero. Logarithmic
differentiation of (2) gives |H'(u)|<=C/q there. Using H(1)=1 proves
(6) on this small interval. When v>=epsilon q, the preceding global
bound and sqrt(1+v/q)+1<=C_epsilon v/q prove (6) on its complement.

Let beta_n=Beta(n,3/2). Integrating (6) gives

    |I_n-beta_n|<=C/q * Beta(n,5/2)
                 <=C beta_n/(nq).                              (7)

The exact beta ratio is Beta(n,5/2)/Beta(n,3/2)=3/(2n+3).
Also (2/sqrt(pi)) n^(3/2) beta_n=1+O(1/n), uniformly for n>=1.
Thus the normalized complex-pair contribution in (4) differs from
cos(Phi_n) by at most C/(nq). The O(1/n) term is absorbed by enlarging
C, since q<=q0.

For the positive real-cut contribution, x in [a,b] satisfies
|x-lambda|<=Cq and x-a<=Cq. Hence

    sqrt((x-a)(b-x)) |x-lambda| <= C q^(3/2) sqrt(b-x).

Since s-x>=b-x, integration of (3) gives

    0<T_n<=C q^(-1) b^n.

By (5), after division by M_n this yields

    T_n/M_n<=C(nq)^(3/2) exp(-c0 nq).                            (8)

The function y^(5/2)exp(-c0 y) is bounded on y>0, so (8) is at
most C/(nq). Combined with (7), this proves a uniform error C/(nq)
near s=1. Since theta is comparable to q there, this is the first
term required in (1). In particular, no isolated transfer estimate at
the real branch point b, or separation from its nearby removable pole,
is used.

## Uniform bounds near infinity

Put e=s^(-1/3). We take 0<e<=e0 for a fixed sufficiently small e0.
With r0=4^(1/3) and omega=exp(2pi i/3), the root expansions give

    lambda=s^(2/3)(r0 omega-r0^2 omega^2 e/2+O(e^2)),
    b=s^(2/3)(r0-r0^2 e/2+O(e^2)),
    a=1/4+O(1/s).

In particular,

    b and R are comparable to e^(-2), s=e^(-3),
    |kappa| is comparable to e^2,
    log(R/b)>=c1 e,       delta is comparable to e.               (9)

For the logarithmic gap the leading coefficient is 3r0/4>0.
The normalized real roots a/lambda and b/lambda tend to 0 and
omega^2, while conj(lambda)/lambda tends to omega. Thus c(1) stays
away from zero and c(u) remains uniformly bounded on [0,1]. Also
|u lambda-s|>=s-R>=s/2 for small e. It follows that H is uniformly
bounded. On [1/2,1], every numerator factor stays away from zero and
H' is uniformly bounded. Using H(1)=1 on that interval, and boundedness
on its complement, proves

    |H(u)-1|<=C(1-u),      |I_n-beta_n|<=C beta_n/n.               (10)

For (3), put x=b u and use x-a<=x, |x-lambda|<=Cb, and s-x>=s/2.
Extending the lower integration limit to zero yields

    T_n<=C b^(n+2)/s^2 * Beta(n+1/2,3/2)
         <=C e^2 b^n n^(-3/2).

Therefore

    T_n/M_n<=C exp(-c1 ne).                                    (11)

Equations (10)--(11) give an error at most C/n+C exp(-c1 ne).
Since exp(-c1 y)<=C/y for y>0 and delta is comparable to e, this
is bounded by C/(n delta), after adjusting the constant.

## The compact middle range and the global estimate

On the remaining compact interval 1+q0^3<=s<=e0^(-3), H is uniformly
bounded on [0,1] and H' is uniformly bounded on [1/2,1], by the same
nonvanishing argument. Thus (10) holds there. The real integral T_n
is at most C b^n; |kappa| stays away from zero, and b/R<=rho<1.
Its normalized size is at most C n^(3/2)rho^n<=C/n. This proves
a uniform error C/n on the middle range. Since theta and delta are
bounded above, it is absorbed by the right side of (1).

The three ranges cover s>1. Taking the maximum of their constants
proves (1), with all quantifiers stated at the beginning. This also
supplies a direct proof of the older compact-uniform oscillation result.

The only asymptotic estimate for special functions used in these bounds
is the fixed-parameter beta/gamma ratio, obtainable from
[Stirling's expansion](https://dlmf.nist.gov/5.11#i).
The endpoint root expansions and positive modulus gaps were proved
algebraically in the preceding notes. The elementary contour derivation
and the uniform estimates above are our deductions.

## Counting all sufficiently large rows

We now apply the proved conditional counting theorem in
`132-phase-count-matching-2026-10-13.md`. Choose a fixed integer K large
enough for its near-endpoint zero count and so that the right side of
(1) is less than one at all phase grid points with K<=m<=d_n-K.
Such a choice exists because phi is bounded and, at those grid points,

    n theta>=K pi-O(1),   n delta>=K pi-O(1),

uniformly in n and its residue class. Equation (1) now proves the
interior alternating signs, without a conjectural premise. The endpoint
limits supply K roots on each outer side for all sufficiently large n,
and the grid supplies d_n-2K roots between. There are d_n distinct
negative roots in total. Their number equals the degree, proving the
eventual real-rootedness theorem stated above.

## Remaining all-index work and formalization boundaries

We still need either an effective threshold with the full exceptional
range verified, an argument propagating this eventual result backwards,
or a direct proof of every phase-grid sign. The stronger all-index sign
conjecture (13) in the previous note remains open. In (4), positivity of
T_n alone does not determine the sign: at odd phase points it opposes
the desired sign. We have not proved pointwise positivity of Re H, nor
a sufficiently sharp all-n domination estimate. Numerical sector samples
are not a substitute for either assertion.

No new GitHub issue is needed for this continuation of #1623. Proposed
analytic declarations under the agreed B132 namespace include
`eval_eq_realCut_add_radialPair`, `radialFactor_sub_one_bound_near_one`,
`realCut_div_amplitude_bound`, `normalized_eval_sub_cos_bound`, and
`eventually_hasSimpleNegativeRoots`. Each must carry its actual uniform
quantifiers; the last is an eventual theorem, not `forall n`.
The analytic dependency on the already proved paper endpoint/count
lemmas must be made explicit until those lemmas are formalized.

Acceptance: the cuts, branch choices, removable pole and contour signs
in (4) must be checked; constants in (6)--(11) must be independent of n
and uniform in the indicated parameter range; all three degree residue
classes must be included in the count. No finite numerical audit or
statement scaffold counts as the analytic proof. Claude retains sole
Lean implementation/build ownership.

## Verification record

The contour signs and coefficient identity were sanity-checked by
50-digit quadrature for n=1,2,3,8 at s=1.001,1.1,2,6,1000 against
the existing exact B rows. Maximum relative residual was below 6e-47.
These 20 checks have no interval enclosures and are numerical only;
the proof of (4) is the contour argument above. The companion JSON
retains those values. The bounded Python probe was used because the
existing Rust tools have no complex contour-quadrature API; it introduces
no new polynomial family generator and is not root-test evidence.
