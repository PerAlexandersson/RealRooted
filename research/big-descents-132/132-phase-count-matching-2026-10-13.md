> Update 2026-10-13: the uniform oscillation estimate is now proved on paper, yielding eventual simple negative roots. The all-index conjecture remains open because the threshold is unspecified. See [the complete argument](https://github.com/PerAlexandersson/RealRooted/issues/1623#issuecomment-6139065292).

# Matching the endpoint counts to the quartic phase

Owner: academic Codex theory lane. Related issue: RealRooted #1623.
Status: the phase normalization, endpoint zero indexing, and conditional
counting theorem below are proved on paper. The uniform oscillation
estimate (12) remains OPEN. No Lean verification is claimed.

We continue the two preceding notes, `132-dominant-quartic-phase-2026-10-12.md`
and `132-endpoint-limits-2026-10-13.md`. They prove the dominant quartic
geometry, compact-uniform oscillation, and both locally uniform endpoint
limits. Here we determine the additive constants in the zero counts.
This removes a possible integer-offset obstruction to joining those results.

## A fixed argument for the oscillatory coefficient

Let s>1 and let a,b,lambda,conj(lambda) be the roots of

    W_s(z)=z^4-4z^3+6s z^2-4s^2 z+s^2,

with 0<a<1<b<s and Im(lambda)>0. Write theta=arg(lambda) in (0,2pi/3).
We retain the coefficient kappa of the dominant asymptotic from the
quartic note. A continuous, explicitly normalized argument of kappa is

    phi(s)=(arg(lambda-a)+arg(lambda-b)+theta)/2
                    -arg(lambda-s)-3pi/4.                         (1)

Every argument on the right is the principal argument of a point in
the upper half-plane. In particular, the formula has no unspecified
integer multiple of 2pi.

To verify it, use

    kappa=c lambda^2/(4sqrt(pi)(1-s)(lambda-s)),
    c=product_(mu!=lambda) sqrt(1-mu/lambda),

with the principal square roots established in the quartic note. The
arguments of the real-root factors are arg(lambda-a)-theta and
arg(lambda-b)-theta, and

    arg(1-conj(lambda)/lambda)=pi/2-theta.

Both real-root ratios have positive real part since |lambda|>b>a.
The negative factor 1-s then gives (1). We also have the useful exact
identity

    kappa^2=lambda W_s'(lambda)/(16pi(s-1)^2(lambda-s)^2).          (2)

The endpoint expansions of the quartic roots give

    phi(1+)=-5pi/6,             phi(infinity)=-2pi/3.               (3)

For the first limit, set q=(s-1)^(1/3). Then
lambda=1+4^(1/3)exp(i pi/3)q+O(q^2),
a=1-4^(1/3)q+O(q^2), and b=1+O(q^3). The arguments of
lambda-a, lambda-b, lambda-s tend to pi/6, pi/3, pi/3.
For the second, set e=s^(-1/3). Then lambda/s^(2/3) tends to
4^(1/3)exp(2pi i/3), b/s^(2/3) tends to 4^(1/3), and a stays bounded.
The corresponding three arguments tend to 2pi/3,5pi/6,pi.

In fact, we have the global derivative bound

    -1/2 < dphi/dtheta < 1/2.                                    (4)

Here is an algebraic proof. All four roots satisfy the Riccati equation
z'=(z^2+4(s-1)z-s)/(6s(s-1)). Subtraction at lambda and a real root
mu gives

    d/ds arg(lambda-mu)=Im(lambda)/(6s(s-1)).

Polynomial division also gives

    (lambda'-1)/(lambda-s)
      =(lambda+5s-4)/(6s(s-1))-1/(6(lambda-s)).

Differentiating (1), and using the proved formula for theta', yields

    dphi/dtheta=1/2-J,
    J=s(s-1)R^2/((R^2+s)|lambda-s|^2),  R=|lambda|.

We have J>0. To prove J<1, write r=R^2 and u=Re(lambda).
Vieta gives ab=s^2/r, a+b=4-2u, and

    u(s^2/r-r)+2r=2s^2.

The equality r=s would imply s=s^2, impossible for s>1. At s=2
we know r>s, so continuity proves r>s throughout. Thus

    u=2r(r-s^2)/(r^2-s^2).

Set w=r/s>1. Substitution gives the exact identity

    (r+s)|lambda-s|^2-s(s-1)r
      =s^2/(w-1) * [(w-1)^3+(s-1)(5w-1)] > 0.

This proves (4). Consequently Phi_n(s)=n theta(s)+phi(s) is strictly
increasing for every integer n>=1, with endpoint values

    -5pi/6,      2(n-1)pi/3=(d_n+ell_n/3)pi,
    d_n=floor(2(n-1)/3), ell_n=2n-3d_n-2.                         (5)

For every integer m strictly between these endpoint values in units
of pi, there is a unique s_(n,m)>1 with Phi_n(s_(n,m))=m pi.
This defines the phase grid for every n>=1. When ell_n=0 the last
endpoint d_n pi is attained only as s tends to infinity; it must not
be counted as a finite grid point.

For independent checking, the modulus also has an explicit real formula.
Vieta and the preceding expression for u give, with w=r/s>1,

    (w+w^(-1)-2)^3=16(s+s^(-1)-2).

Hence, if k=[4(sqrt(s)-1/sqrt(s))]^(1/3),

    h=(k+sqrt(k^2+4))/2,  R=sqrt(s) h.

Recover u from the displayed rational formula and Im(lambda)=sqrt(r-u^2)>0.
This formula is useful for evaluating the grid, but no floating-point
grid evaluation is a proof of a polynomial sign.

## The exact index offset for the endpoint near zero

Let F(x)=sum Catalan(k)x^k/(3k+1)! as in the endpoint note. Its zeros
r_1>r_2>... are simple and negative. We prove

    (sqrt(3)/2)(4|r_j|)^(1/3)=pi(j+1/3)+O(1/j).                   (6)

The additive constant 1/3 is part of the conclusion; reality and order
alone would not determine it.

We use the Catalan moment identity

    Catalan(k)=1/(2pi) integral_0^4 u^k sqrt((4-u)/u) du,

which follows by the beta integral. Define

    L(z)=integral_0^1 r^(-1/2)sqrt(1-r^3) exp(zr) dr.

Termwise integration of the entire series, followed by u=4r^3 and
the roots-of-unity filter for sum z^k/(3k+1)!, gives the exact identity

    F(-v^3/4)=2/(pi v) [2 Re(exp(-i pi/3)L(v exp(i pi/3)))-L(-v)],
                                                               v>0.

At r=1, the weight equals sqrt(3)(1-r)^(1/2)(1+O((1-r)^2)).
Watson's lemma, applied after replacing r by 1-r, gives

    L(z)=sqrt(3pi)/2 * exp(z) z^(-3/2)(1+O(1/z))

on the positive ray and the ray arg z=pi/3. The exponentially smaller
contribution from r near zero is harmless. This can also be proved
directly by splitting the integral at r=1/2 and bounding the Taylor
remainder near r=1. The same argument applies to differentiated
integrals. Consequently, with A=sqrt(3)v/2,

    F(-v^3/4)=2sqrt(3/pi) v^(-5/2)exp(v/2)
                   [cos(A-5pi/6)+O(1/v)],                        (7)

and the derivative of the normalized bracket with respect to A is
-sin(A-5pi/6)+O(1/v). Thus, for all large A, there is exactly one zero
in each small neighborhood of A=pi(k+1/3), with displacement O(1/k),
and no other zero between these neighborhoods.

The positive-ray roots-of-unity formula similarly gives

    F(v^3/4)=sqrt(3/pi) v^(-5/2) exp(v)(1+O(1/v)).                 (8)

The two other exponential terms have negative real exponent and are
only algebraic after integration near r=0.

For clarity, we determine the possible integer offset rather than
assuming that the k in (7) is the zero index. Equation (7), together
with simplicity and reality of all zeros, first gives

    |r_j|=A0 (j+c+O(1/j))^3,   A0=2pi^3/(3sqrt(3)),

for some real c congruent to 1/3 modulo an integer. Since F has order
1/3 and F(0)=1, its canonical product is product_j(1+x/|r_j|).
Choose J large enough that j+c>0 for j>=J and compare this tail with
product_(j>=J)(1+R^3/(j+c)^3), R=(x/A0)^(1/3). The logarithm of the
ratio is bounded uniformly for x>0: each difference is at most
|log(|r_j|/(A0(j+c)^3))|=O(1/j^2), a summable bound.

Put omega=exp(2pi i/3). The gamma product identity gives

    product_(j>=J)(1+R^3/(j+c)^3)
      =Gamma(J+c)^3 /
        [Gamma(J+c+R)Gamma(J+c+omega R)Gamma(J+c+omega^2 R)].

Stirling's formula on these three fixed rays, plus the J-1 initial
factors in the true canonical product, yields

    log F(v^3/4)=v-3(c+1/2)log v+O(1).

Comparison with (8) forces 3(c+1/2)=5/2, hence c=1/3. This proves (6).
In particular, for every sufficiently large integer M, F has exactly
M zeros in the interval

    -(1/4)[2pi(M+5/6)/sqrt(3)]^3 < x < 0.                         (9)

The endpoints of (9) are not zeros. This conclusion supplies the exact
count needed for joining the endpoint limit to the interior grid.

Analytic references: [Watson's lemma and its complex version](https://dlmf.nist.gov/2.4#i),
the [gamma infinite product](https://dlmf.nist.gov/5.8), and
[Stirling's expansion](https://dlmf.nist.gov/5.11#i). The application,
moment representation, and integer-offset argument here are our deductions.

## Explicit signs for the far endpoint

The endpoint functions are Psi_ell(x)=ell! sum (x/2)^h/(3h+ell)!,
ell=0,1,2. The same roots-of-unity filter gives the exact formula

    Psi_ell(-2v^3)=ell!/(3v^ell)
       [2exp(v/2)cos(sqrt(3)v/2-ell pi/3)+(-1)^ell exp(-v)].       (10)

At v_j=2pi(j+ell/3)/sqrt(3), every j>=0 with v_j>0 satisfies

    sign Psi_ell(-2v_j^3)=(-1)^j,

because 2exp(v_j/2)>exp(-v_j). When ell=j=0, use Psi_0(0)=1.
Successive grid values therefore bracket J distinct negative zeros
inside (-2v_J^3,0), for every J>=1. Their simplicity was proved in
the endpoint note; an exact upper count is unnecessary for the argument
below. This treatment includes all three residue classes.

## A precise sufficient interior estimate

Define the positive amplitude

    M_n(s)=2|kappa(s)||lambda(s)|^n n^(-3/2),
    delta(s)=2pi/3-theta(s).

The remaining sufficient sign assertion is:

    There exist integers K,N such that for n>=N and
    K<=m<=d_n-K,
       (-1)^m B_n(1-s_(n,m))>0.                                (11)

This asserts signs at explicitly defined algebraic-phase locations,
not real-rootedness as an assumption. A natural stronger analytic target is

    |B_n(1-s)/M_n(s)-cos(Phi_n(s))|
        <= C/(n theta(s)) + C/(n delta(s))                       (12)

for some C,L,N0, all n>=N0, and every s>1 with
n min(theta(s),delta(s))>=L. Neither (11) nor (12) is proved here.
The previously proved compact-uniform estimate does not imply them.

**Conditional counting theorem.** If (11) holds, then all sufficiently
large B_n have d_n distinct negative roots, and hence are real-rooted
with simple roots.

Proof: enlarge K if needed so (9) holds at M=K and so the phase grid is
defined. Equation (3) and the established theta endpoint expansions imply

    n^3(1-s_(n,K)) -> -(1/4)[2pi(K+5/6)/sqrt(3)]^3,

and, along the residue class ell,

    n^3/(1-s_(n,d_n-K)) -> -2[2pi(K+ell/3)/sqrt(3)]^3.

The locally uniform endpoint limits, simplicity of their zeros, and
nonvanishing at these boundaries give at least K distinct negative roots
between 1-s_(n,K) and zero, and at least K distinct negative roots to
the left of 1-s_(n,d_n-K), for all sufficiently large n. The latter
claim uses the K zeros bracketed by (10) in the reciprocal coordinate.
The interior signs (11) supply d_n-2K further distinct roots between
successive phase grid points. The three regions are disjoint, so their
counts add to d_n. A nonzero degree-d_n polynomial cannot have any
additional root or repeated root. This proves the conditional theorem.

To see that (12) implies (11), note that phi is bounded. At a phase
grid point with K<=m<=d_n-K, both n theta and n delta are at least
K pi-O(1), uniformly in n and the residue class. Choose K large enough
that this lower bound exceeds L and makes the right side of (12)
strictly less than one. The sign is then the sign of cos(m pi).

Even a proof of eventual real-rootedness must be supplemented by an
explicit threshold and exact verification below it, or by an independent
argument for the remaining indices, before claiming the all-index goal.
No such threshold or completion is asserted in this note.

There is also a sharper, entirely all-index sign target:

    For every n>=2 and every finite phase grid point s_(n,m),
       (-1)^m B_n(1-s_(n,m))>0.                                 (13)

This is a CONJECTURE, not a proved consequence of the endpoint estimates.
If true, it proves the full all-index root theorem directly: when ell_n>0
the finite grid has indices 0,...,d_n, and successive values bracket
d_n distinct roots. When ell_n=0 it has indices 0,...,d_n-1; these
bracket d_n-1 roots, and the sign (-1)^d_n of the positive-leading
polynomial at negative infinity supplies the last one. B_1=1 is separate.
No asymptotic threshold or finite exceptional range is needed for this
stronger route. This is the preferred target if an exact coefficient
integral can control the phase grid signs.

The companion JSON records exact symbolic checks of the Riccati quotient,
positive factorization for 1-J, modulus equation, and endpoint weight
expansion. A 55-digit numerical audit at all 492 finite grid points for
n=2,...,30,40,60,90,100 found no sign failure; the smallest signed value
after normalization was about 0.54186, at (n,m)=(3,1). This is a diagnostic
without interval enclosures, not an exact verification of (13), even in
that finite range. The hand proofs of (1)--(10) and the conditional
counting deductions do not depend on these numerical evaluations.

## Next proof obligation and a contour hazard

Near s=1, set q=(s-1)^(1/3). The relevant large parameter for a uniform
transfer argument is nq. The complex branch points and both real branch
points coalesce near z=1. The apparent pole z=1/s is removable, but is
only O(q^3) from the positive real branch point 1/b. Thus applying the
isolated square-root transfer theorem separately at that real branch
point is not uniform when nq is large but nq^3 is small.

For example, its separate local coefficient can be O(q^(-9/2)), versus
O(q^(-5/2)) at the dominant complex branch. A naive exponentially small
relative-error assertion that ignores this factor is unjustified.
One possible remedy is a contour staying a distance comparable to q
from z=1, retaining the rationalized generating function 2z/(A+sqrt(D))
and treating the neighborhood as a whole. This requires actual bounds
on that contour and its tails, not only pointwise expansions.

At infinity use e=s^(-1/3) and z=e^2 w. The discriminant becomes

    1-4e^2w+6ew^2-4w^3+e^2w^4.

Three branch points approach the same modulus with distinct arguments.
The third, positive-real contribution cannot be discarded uniformly
until ne is controlled. This is the other estimate required by (12).

Related Lean: #1646 supplies only the finite reciprocal-Pochhammer
simple-root corollary. This note's analytic infrastructure is separate.
Proposed future declarations under a single agreed B132 namespace:
`phase_eq`, `phase_tendsto_endpoints`, `phase_strictMono`,
`nearLimit_zero_asymptotic`, `farLimit_sign_grid`, and
`eventually_hasSimpleNegativeRoots_of_phase_grid_signs`.
The last theorem must retain (11) as an explicit hypothesis until it is
proved; it is not an unconditional B132 root theorem. Acceptance requires
the exact offsets 5/6,1/3 and ell/3, all three residue classes, disjoint
root-counting intervals, and the still-open uniform estimate clearly
separated from the proved endpoint and conditional results.
