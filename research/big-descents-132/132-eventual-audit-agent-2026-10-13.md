# Audit and a shorter eventual B132 proof

Owner: delegated eventual-proof audit agent; root theory owner integrates.
Status: paper audit and proof simplification. No Lean edits or builds.
The all-index B132 theorem remains open.

We audited the contour formula, endpoint estimates, phase normalization,
canonical-product index offset, and all three degree residue classes in
the following notes:

- `132-dominant-quartic-phase-2026-10-12.md`;
- `132-endpoint-limits-2026-10-13.md`;
- `132-phase-count-matching-2026-10-13.md`;
- `132-uniform-oscillation-2026-10-13.md`;
- `132-integral-domination-2026-10-13.md`.

We found no mathematical gap in the eventual-root argument. Its newest
far-endpoint comparison permits a substantial reduction: the eventual
theorem needs only the near-zero limit F. The reversed coefficient limit,
its uniform majorant, and the functions Psi_ell can be omitted. Exact beta
normalization also removes the gamma-ratio asymptotic from the oscillation
estimate. The remaining special-function asymptotics occur in the proof of
the exact index offset for the zeros of F.

## Exact beta normalization

Retain the quartic roots a,b,lambda,conj(lambda), and write

    R=|lambda|, theta=arg(lambda), Phi_n=n theta+phi,
    beta_n=integral_0^1 u^(n-1)sqrt(1-u) du,
    Mtilde_n=(4/sqrt(pi))|kappa|R^n beta_n.

For every integer n>=1, beta_n and Mtilde_n are positive. The exact
contour identity becomes

    B_n(1-s)/Mtilde_n
      =T_n/Mtilde_n+Re(exp(i Phi_n) I_n/beta_n).                 (1)

Thus

    |B_n(1-s)/Mtilde_n-cos(Phi_n)|
      <=T_n/Mtilde_n+|I_n/beta_n-1|.                           (2)

The integral recurrence gives the exact ratio

    Beta(n,5/2)/beta_n=3/(2n+3).

We also have the elementary bound

    beta_n >= 1/(6sqrt(2)) * n^(-3/2).                         (3)

Indeed, substitute v=1-u and restrict the integral to
0<=v<=1/(2n). Bernoulli's inequality gives
(1-v)^(n-1)>=1-(n-1)v>=1/2. Integration of sqrt(v)/2 proves (3).
This bound is sufficient wherever the old proof used a fixed-parameter
gamma-ratio asymptotic to bound a real-cut contribution.

Fix S>1. The near-one and compact estimates in the uniform-oscillation
note give a constant C_S such that

    |B_n(1-s)/Mtilde_n-cos(Phi_n)|
       <= C_S/(n theta(s))+C_S/n,
       n>=1, 1<s<=S.                                         (4)

For completeness, put q=(s-1)^(1/3) near one. The estimate
|H_s(u)-1|<=C(1-u)/q and the exact beta ratio bound the second
term of (2) by C/(nq). The real-cut bound T_n<=Cq^(-1)b^n,
the estimates |kappa|>=cq^(-5/2) and log(R/b)>=cq, and (3) give

    T_n/Mtilde_n<=C(nq)^(3/2)exp(-cnq)<=C/(nq).

Since theta is comparable to q, this proves (4) near one. On the
remaining compact interval, |H_s(u)-1|<=C(1-u) and T_n<=Cb^n;
the uniform bound b/R<=rho<1 gives an error
C/n+Cn^(3/2)rho^n<=C/n. This proves (4) throughout (1,S].

## A simpler uniform estimate at infinity

The far-endpoint comparison note uses

    J_n=integral_0^1 u^(n-1/2)sqrt(1-u^3) du.

Its uniform estimate for beta_n/J_n needs no asymptotic result. For
0<=u<=1,

    sqrt(u(1+u+u^2))>=u.

Consequently,

    J_n>=Beta(n+1,3/2)
       =2n/(2n+3) beta_n >= (2/5)beta_n.                        (5)

This gives the explicit bound beta_n/J_n<=5/2 for all n>=1.
Together with the uniform convergence of H_s to
sqrt(u(1+u+u^2))/sqrt(3), the proof in that note yields

    exists S>1, forall s>=S, forall n>=1,
      A_n(s)>0 and 0<T_n(s)<=3 A_n(s)/4,                       (6)

where A_n=(4/sqrt(pi))|kappa|R^n Re I_n. At every phase-grid
point with s>=S we therefore have

    (-1)^m B_n(1-s_(n,m))>0.                                 (7)

The quantifier over n in (6) is essential. A fixed-n limit would not
justify the simplification below.

## Eventual real-rootedness from one endpoint

We retain the already proved phase facts:

    Phi_n is strictly increasing,
    Phi_n(1+)=-5pi/6,
    Phi_n(infinity)=(d_n+ell_n/3)pi,
    d_n=floor(2(n-1)/3), ell_n in {0,1,2}.

The function phi is bounded. For every finite grid point with m>=K,

    n theta(s_(n,m))=m pi-phi(s_(n,m))>=K pi-C_0.              (8)

Choose S from (6). Choose a fixed integer K large enough that the first
term on the right of (4), using (8), is at most 1/3. Increase K if
needed so the near-limit zero count below holds. Then choose n large
enough that C_S/n<=1/3. Equations (4) and (7) give the desired sign at
**every** finite grid point with m>=K. There is no omitted far region.

The sole endpoint input is

    B_n(x/n^3)/n -> F(x)=sum_(k>=0) Catalan(k)x^k/(3k+1)!,

uniformly on each bounded real interval, together with the statement
that, for every sufficiently large integer K, F has K simple zeros in

    (-L_K,0),  L_K=(1/4)[2pi(K+5/6)/sqrt(3)]^3.                 (9)

The phase endpoint expansion gives

    n^3(1-s_(n,K)) -> -L_K.                                  (10)

Around each of the K simple real zeros in (9), choose a small disjoint
real interval on which F has opposite endpoint signs, with all interval
closures contained in (-L_K,0). Uniform convergence preserves these
signs. Equation (10) places all K intervals to the right of the scaled
phase-grid boundary for large n. The intermediate value theorem gives
K distinct negative roots of B_n between 1-s_(n,K) and zero.
No use of Rouche's theorem, complex root ordering, or derivative
convergence is needed for this step.

When ell_n>0, the finite phase-grid indices are 0,...,d_n. The signs
at K,...,d_n give d_n-K distinct roots to the left of the K-th grid
point. Together with the endpoint roots, there are d_n roots.

When ell_n=0, the finite indices are 0,...,d_n-1. These give
d_n-K-1 roots between the K-th and last grid points. The leading
coefficient of B_n is positive, so its sign sufficiently far to the
left is (-1)^d_n, opposite the sign (-1)^(d_n-1) at the last finite
grid point. The intermediate value theorem supplies one further root.
Again the total is K+(d_n-K-1)+1=d_n.

In either case the degree bound forces all roots to be real, strictly
negative, and simple. This proves eventual real-rootedness from the
one-endpoint input, (4), and (6).

## The endpoint index still needs a proof

The integer offset in (9) cannot be discarded. Oscillation alone only
locates all sufficiently late zeros near an arithmetic progression with
an undetermined integer shift. The canonical-product argument in the
phase-count note determines that shift correctly.

Writing the negative zeros as

    |r_j|=A_0(j+c+O(1/j))^3,
    A_0=2pi^3/(3sqrt(3)), c congruent to 1/3 modulo Z,

the relative displacement from A_0(j+c)^3 is O(j^(-2)). Hence the
logarithms of the true and model tail products differ by a uniformly
bounded quantity on the positive axis. The gamma-product computation
has logarithmic coefficient -3(J+c-1/2); the J-1 initial factors add
3(J-1). Their sum is -3(c+1/2), independent of J. Comparing with
the positive-ray power v^(-5/2) gives c=1/3, as claimed.

We found no replacement for this index calculation using only the
existing finite multiplier facts. A future simpler exact sign formula
for F at the points -L_K could replace it, provided it supplies at
least K sign changes before -L_K with the correct starting index.

## Formalization boundary

The final counting argument is a finite real-polynomial sign-count
lemma: ordered test points with alternating signs give distinct roots
in disjoint intervals; a degree upper bound then gives splitting and
simplicity. It is independent of quartics, contours, and asymptotics.
The Lean-library agent should identify its existing implementation
before any new declaration is proposed. A B132 application can consume
the separately proved analytic sign theorem.

The analytic work still includes the exact contour identity, uniform
parameter estimates, the quartic phase, and the one endpoint's precise
root count. These paper arguments are not automatically formalized by
the library's finite multiplier-sequence lemmas.

## Independent audit of the explicit comparison certificates

We subsequently checked
`132-simplify-integral-agent-2026-10-13.md` and
`132-effective-integral-certificate-2026-10-13.md`, without editing
either file. We found no missing hypothesis or incorrect constant in
the displayed sufficient inequalities. The checks below are symbolic
paper checks, with decimal constants interpreted as exact rationals.

For the far-parameter proof, epsilon=1/1000 gives

    |c-c_infinity|<=6 epsilon,
    |c/c(1)-c_infinity/sqrt(3)|<=8 epsilon.

Indeed the first square-root factor differs by at most epsilon, the
other factors each differ by at most epsilon and have modulus less
than 3/2, and the telescoping product estimate is smaller than
6 epsilon. Since |c_infinity(u)|<=sqrt(3), the quotient error is
at most 12 epsilon/(sqrt(3)-6 epsilon)<8 epsilon. The pole factor
differs from one by less than 2 epsilon, so the final error is at
most (10+16 epsilon)epsilon<11 epsilon. Together with (5), this
gives precisely the coefficient 55 epsilon/2 in the lower bound
for Re I_n.

The scaled quartic bounds also have sufficient slack. For
e<=1/1000, z=4^(1/3)-2e is greater than 1.49 and less than 1.6.
The negative term -2e*z*(z^2+z*4^(1/3)+4^(2/3)) is less than
-19e, while the positive remainder is less than 16e. Thus the
real-root enclosure used in that proof is valid. The estimate

    |aB-4^(1/3)/4|<=e/2+(8/5)e^3

and the derivative bound 5/2 give an error smaller than 2e for
rho. The real-part error is smaller than e+2e^2<2e. For the
imaginary part, the displayed constants give

    2(3.202+1.602)/1.29 < 8.

Consequently |L-4^(1/3)omega|<10e. Division by rho>1.498 gives
the asserted bounds 9e and 14e for the two normalized complex
root ratios. At e<=1/20000, these and R/s<2e,
sqrt(a/R)<e are each less than epsilon. The final ratio bound is
strictly below 3/5. Thus the explicit threshold s>=20000^3
correctly certifies every integer n>=1 in that parameter range.

For the effective distance certificate, the real-cut substitution
x=bu produces the factor b^(n+1)(b+R), so division by

    A_n=|c(1)|R^(n+2)Re I_n/[pi(s-1)|lambda-s|]

produces exactly the stated C*rho^n. There is no missing factor
of b, R, pi, or 2. If n>=3L, then

    3L/(2n+3)<=n/(2n+3)<1/2.

Thus 4C*rho^n<=1 gives the strict ratio T_n/A_n<1/2 even
when that sufficient inequality is an equality.

At s=3+2sqrt(2), the normalized roots give U=sqrt(2). The two
candidates defining L are bounded respectively by

    2(sqrt(2)+1)<5,
    sqrt(2)*(1+1+1/3+1)=(10/3)sqrt(2)<5.

The coarse bounds 3<b<4 and 5<s<6 give C<4 and rho<4/5.
The integer inequality 16*4^15<5^15 proves the required power
bound for every n>=15. These certificates establish parameter
regions; they do not furnish a finite exceptional degree range.

We recommend recording both certificates in the existing #1623
checkpoint. A separate issue for the large numerical cutoff would
fragment the same unresolved B132 proof. A reusable library issue is
justified only after isolating a sufficiently general integral or
finite sign-count lemma and checking that the library lacks it.

## Audit of the improved angular comparison: s>=1000

The later section `Sharper angular comparison: s>=1000` in
`132-simplify-integral-agent-2026-10-13.md` improves the preceding
large cutoff. We independently checked its proof and constants.
It establishes, for every integer n>=1 and every real s>=1000,

    A_n(s)>0,   0<T_n(s)/A_n(s)<625/648<35/36.

The argument applies first under pi/2<=theta<2pi/3. Write
beta=b/R, c=cos(theta), and Q=(u-beta exp(-i theta))
*(u-exp(-2i theta)). The coefficients D,E,F,G in the source
satisfy

    Q=u^2+D u+E+i(F u+G),
    F E-G D=beta sin(theta)*(-1-2beta c)<0.

We checked this identity by substituting
cos(3theta)=4c^3-3c and
sin(3theta)=sin(theta)(4c^2-1). Since beta+2c>0,
all four coefficients are nonnegative and D,F are positive.
The derivative numerator for arg Q is therefore negative. The
arguments of the two original factors have opposite signs and
sum to a number in (-pi,pi); Q in the first quadrant identifies
that sum with its principal argument. Thus the source's use of
the product argument has no branch ambiguity.

It follows that arg c(u) decreases and belongs to
[0,Gamma], where Gamma=3pi/2-2theta. The pole factor has
argument in [-eta,0], with eta=arg(s-conj(lambda)), so

    Re H(u)>=h |H(u)|,
    h=min(cos eta,-sin(2theta)).

We also checked both density comparisons. With q_1,q_2,q_3
defined in the source, q_1<=q_2 and beta*q_3<=q_1 imply
beta*q_3<=sqrt(q_1*q_2). The change of variables x=bu in
T_n gives the factor b^(n+1)R, whereas the absolute density
for A_n has factor R^(n+2). Thus the ratio of twice the real
density to the A density contains exactly beta^(n+1), as
written. This proves the uniform all-n bound

    T_n/A_n <= |lambda-s|/[2(s-b)h]

whenever h>0. Positivity on the part of the A integral below
a/b is also valid, so restricting that denominator integral
does not reverse the inequality.

For s>=1000, let e=s^(-1/3)<=1/10 and r=4^(1/3).
The scaled-root bracket r-4e/3<B<r follows from

    P_e(r-4e/3)/(e(r-4e/3)^2)
       <-4*(79/50)+6+(1/10)/(36/25)^2<0,

and P_e(r)>0. Both test points correspond to w>1. Together
with 1/4<a<0.251, this gives

    B>36/25, rho<5/3, U<-7/10, cos(theta)<-21/50.

In particular theta>pi/2. Its already known upper bound
theta<2pi/3 gives sin(theta)>sqrt(3)/2, so

    cos Gamma>(21/25)*(sqrt(3)/2)>18/25.

The remaining estimates are

    R/s<1/6, b/s<4/25,
    cos eta>6/7,
    |lambda-s|/(s-b)<(7/6)/(21/25)=25/18.

Hence h>18/25 and T_n/A_n<625/648. These rational bounds
have strict slack, including at s=1000. The earlier cutoff
20000^3 can be superseded by 1000 in the parent checkpoint.
The conservative proof remains valid historical material.

## Final cutoff refinement: s>=512

We also independently checked the subsequent section
`The shorter cutoff s>=512`. It replaces only the rational root
estimates in the audited angular argument. Its final conclusion is

    forall s>=512, forall integer n>=1,
      A_n(s)>0 and 0<T_n(s)/A_n(s)<63/64.

At e<=1/8 the identity

    P_e(7/5)=-1099/625+(294/25)e-(1247/125)e^2

is correct and negative even when its negative quadratic term is
dropped. Thus 7/5<B<8/5. The ensuing bounds
rho<17/10, U<-107/160, and cos(theta)<-107/272<-39/100
are valid. For the trigonometric lower bound, the exact square
comparison is

    49*4*1521*8479=2527725564>2500000000,

which proves 2*(39/100)*sqrt(1-(39/100)^2)>5/7.
Monotonicity on [0,1/2] gives cos Gamma>5/7.

The remaining squared norm bound is

    |s-lambda|^2/s^2<8049/6400<8100/6400=81/64.

Together with b/s<1/5 this gives h>5/7 and
|s-lambda|/(s-b)<45/32. Consequently the density comparison
gives T_n/A_n<63/64. The root estimates are shorter than those
for s>=1000; we recommend using this final version in the
consolidated #1623 checkpoint. All three audited cutoffs are
parameter cutoffs, not effective degree bounds.

## Independent audit of the uniform near-one theorem

We audited the main theorem in
`132-near-scaling-agent-2026-10-13.md`. Its conclusion is

    exists delta>0, forall integer n>=1, forall 1<s<1+delta,
      A_n(s)>0 and 0<T_n(s)/A_n(s)<4/5.

The paper argument is sound. We checked the relative factor estimate
uniformly over 0<=tau<=1/(rho q), including the end of that expanding
interval. Each reference factor has modulus at least c(1+tau), so
errors O(q)(1+tau) give O(q) relative errors. In fact the three
scaled square-root radicands have O(q) absolute errors, since the
term -tau is exact in u-mu/lambda; only the pole needs the weaker
O(q)(1+tau) error. For sufficiently small q, the actual and limiting
square-root radicands lie in the upper half-plane. Thus the square
roots have the claimed relative estimates with their stated branches.

We checked the identity for h^2 and the polynomial certificate giving
Re h>1/sqrt(3). The fixed sector also follows from the horizontal-cut
kernel in `132-near-limit-signs-agent-2026-10-13.md`:

    h(tau)=exp(-i pi/6)k(tau)/sqrt(3),
    Im(k(tau)^2)>0.

This gives arg h in (-pi/6,pi/3), hence Re h>=|h|/2 directly.
The source note's own sector proof is valid as well.

The double-scaling constants are correct. For v=rho*n*q fixed,

    T_n ~ rho^2 L(v)/(2pi q),
    A_n ~ sqrt(3)rho^2 exp(v/2)Re K(v)/(pi q).

In the real-cut integral, the substitution x=b-(b-a)t gives a
uniform integrable bound C sqrt((1-t)/t), which is no larger
than the source's C sqrt((1-t^3)/t). The nearby pole at s does
not obstruct this bound, because s-x>=b-x. The rescaled integrand
converges away from t=0 to the asserted density, so dominated
convergence is justified. The radial integrand is bounded by
C exp(-v*tau/2)(sqrt(tau)+tau) along every sequence tending to a
positive finite v. The limiting ratio is therefore at most
v exp(-v/2)<=2/exp(1)<4/5.

The two escaping-scale cases admit a shorter bound than the source
uses. Its uniform lower bound for A_n and the already established
T_n<=Cq^(-1)b^n imply directly

    T_n/A_n<=C(nq)^(3/2)exp(-cnq).

This tends to zero both when nq tends to zero and when it tends to
infinity. The refined factor min(1,(nq)^(-1/2)) is unnecessary.
Hence any sequence violating the desired 4/5 comparison near one
has v bounded above and bounded away from zero. A convergent
subsequence has n tending to infinity, and the joint limit gives
the contradiction claimed in the source.

Combined with the audited all-n far comparison and a compact
parameter estimate, this near theorem removes F and both endpoint
zero-count arguments entirely from the eventual B132 theorem. The
separately proved exact signs of F are a useful endpoint result but
are no longer required for this shorter proof. The near theorem
still has an unspecified delta, so it does not settle all indices.

## Audit of the effective near-one cutoff

We independently checked `132-near-kernel-agent-2026-10-13.md`,
which replaces the unspecified neighborhood by q<=1/200 and proves
T_n/A_n<15/16 for every n>=1. Its constants and argument pass.

The three Rouche disks of radius 2q have the stated lower bound
23q for the unperturbed quartic and upper bound 16q for the
perturbation. The resulting root enclosures give the four affine
relative-error bounds 8q,5q,5q,5q. Their logarithmic combination
is less than 15q, and exp(15q)-1<16q. Consequently
Re H>=(1-32q)Re h>1/2 throughout the full u interval.

We checked the stronger kernel lower bound used here:
Re h>sqrt(2/5). The exact polynomial identity in the near-scaling
note has zero symbolic residual, and its positive shifted
coefficients are correct. Independently, the existing Rust
`polytool bernstein --degree 6 --json` command gives the listed
positive coefficients for P(2t):

    288,96,1696/15,544/5,560/3,272/3,112.

The polynomial C(x)=(x-a)|x-lambda|^2 is increasing on [a,b]
by the previously proved angle range for lambda-a. This gives
the claimed exact beta-integral ratio and the moment bound
D(2n+1)exp(-ell*n). The root estimates imply

    D<(103/100)rq/sqrt(3),
    ell>(49/100)rq,
    exp(ell/2)<201/200.

Their final combination is exactly 621090/666400<15/16.
The compact parameter certificate may therefore use q=1/200
as its explicit lower endpoint.

## Compact certificate independently verified

The parent subsequently completed an exact compact certificate for
q in [1/200,8] and every n>=100. Our separately implemented exact
Fraction verifier replayed all 4,471 parameter intervals and
84,896 kernel rectangles, with no failed assertion and complete
coverage. See `132-compact-certificate-agent-2026-10-13.md` for
the arithmetic audit, artifact hash, and receipt. This changes the
remaining obligation from an unspecified eventual threshold to the
explicit finite range n<100, together with integration of the
already audited analytic premises.

## Rouche-free root localization independently audited

We checked the final appendix of
`132-near-kernel-agent-2026-10-13.md`, titled
`An elementary replacement for Rouche in the audited near region`.
It validly replaces the three complex-disk estimates for q<=1/200
by real polynomial signs and Vieta. The unchanged near comparison
T_n/A_n<15/16 therefore no longer needs Rouche's theorem.

The expansion of P_q(-r+cq)/q is correct. At c=1 its lower
bound 3/2-23q-3q^3 is positive; at c=3/2 its upper bound
-13/5+35q is negative. The unique negative scaled root satisfies

    -r+q<A<-r+3q/2,

while 0<B<q^2 follows from 1<b<s. The Vieta expressions then
give, with Z=U+iV=(lambda-1)/q and V_0=sqrt(3)r/2,

    (12/5)q-(4/5)q^2<V^2-V_0^2<(94/25)q,
    0<V-V_0<(376/255)q<3q/2,
    |U-r/2|<(4/5)q.

Thus |Z-r exp(i pi/3)|^2<(17q/10)^2, yielding the original
2q bound with slack. All downstream affine-factor, logarithm,
kernel, and moment estimates use only those original bounds, so
no constants or compact-certificate endpoints need to change.
