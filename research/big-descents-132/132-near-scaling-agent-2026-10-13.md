# Uniform integral comparison near s=1

Owner: delegated near-scaling theory audit for the academic lane.
Related issue: RealRooted #1623. Status: paper argument independently audited
by the eventual-proof agent; no Lean source, build, or GitHub changes.
We use the exact T_n, A_n,
H_s and quartic roots from `132-integral-domination-2026-10-13.md`.

## Result and notation

There exists delta>0 such that, for every integer n>=1 and every
1<s<1+delta, we have

    A_n(s)>0,       0<T_n(s)/A_n(s)<4/5.                         (1)

The constant delta is not made effective here. The argument gives a
uniform comparison over all n, rather than a fixed-n limit.

Put q=(s-1)^(1/3), rho=4^(1/3), eta=exp(i pi/3), and v=rho n q.
We retain a<b for the real roots and lambda for the upper complex root.
The root expansions are

    lambda=1+rho eta q+O(q^2),
    a=1-rho q+O(q^2),  b=1+3q^3/4+O(q^6).

In particular, log(|lambda|/b)>=c q for small positive q.

## The limiting radial factor has a fixed positive sector

Define, for tau>=0,

    h(tau)=eta/(i sqrt(3))
      *sqrt(eta+1-tau)*sqrt(eta-conj(eta)-tau)/sqrt(eta-tau),

using principal square roots. We have h(0)=1 and

    h(tau)^2=(2+eta^2 tau+eta/(eta-tau))/3.                       (2)

Write D=tau^2-tau+1 and h^2=A+iB. Then

    A=(-tau^3+5tau^2-6tau+6)/(6D),
    B=sqrt(3) tau^2(tau-1)/(6D).                                (3)

The function h is continuous. The imaginary part in (3) vanishes only
at tau=0,1, where A is positive. Thus h^2 never meets the nonpositive
real axis, and h is its square root with positive real part.

We have the two uniform bounds

    Re h(tau)>1/sqrt(3),       Re h(tau)>=|h(tau)|/2.             (4)

For 0<=tau<=1, A>=2/3, since

    6D(A-2/3)=(1-tau)(tau^2+2)>=0.

For tau>=1, set z=tau-1. Direct expansion gives

    36D^2(B^2+4A/3-4/9)
       =3z^6+4z^5+10z^4-4z^3+11z^2+8z+16>0.

The last inequality follows by grouping

    10z^4-4z^3+z^2=z^2(10(z-1/5)^2+3/5).

If A>=2/3 the first claim in (4) follows immediately. Otherwise the
displayed strict inequality gives |h^2|>2/3-A and hence
(Re h)^2=(|h^2|+A)/2>1/3.

For the sector bound, when tau<=1 we have A>0 and B<=0, so
|arg h|<pi/4. When tau>=1, B>=0 and

    sqrt(3) A+B=sqrt(3)(4tau^2-6tau+6)/(6D)>0.

Consequently arg(h^2)<2pi/3 and arg h<pi/3. This proves the second
claim in (4).

## Uniform transfer to the actual factor

Uniformly for 0<=tau<=1/(rho q),

    H_s(1-rho q tau)=h(tau)(1+O(q)).                             (5)

Here the O(q) is a complex relative error with an absolute constant
independent of tau. To justify the uniformity, write u=1-rho q tau.
After dividing by rho q, the three factors u-mu/lambda, for
mu=a,b,conj(lambda), have respective limits

    eta+1-tau,       eta-tau,       eta-conj(eta)-tau.

Each error is bounded by Cq(1+tau), and each displayed limit has modulus
at least c(1+tau), since its imaginary part is nonzero. The same argument
applies to the scaled pole denominator u lambda-s, whose limiting factor
is eta-tau. The normalization at u=1 has relative error O(q).
For sufficiently small q all three original square-root arguments are
in the upper half-plane. Their ratios to the limiting factors are
1+O(q); continuity of the chosen square roots gives the corresponding
relative estimate for each square root. Multiplication gives (5).

By the sector bound in (4), after decreasing q0>0 if needed,

    Re H_s(1-rho q tau)>=(1-Cq) Re h(tau)>=c0>0                 (6)

for every 0<q<=q0 and every allowed tau. In particular A_n>0 for
every n>=1 throughout this neighborhood. We also have
|h(tau)|<=C sqrt(1+tau), directly from its defining factors.

## The double-scaling ratio

Suppose q tends to zero, n tends to infinity, and rho n q tends to a
fixed v>0. Define

    L(v)=integral_0^1 exp(-vt) sqrt((1-t^3)/t) dt,
    K(v)=integral_0^infinity exp(-v tau) sqrt(tau) h(tau) dt.

Then

    T_n ~ rho^2 L(v)/(2pi q),
    A_n ~ sqrt(3)rho^2 exp(v/2) Re K(v)/(pi q),

and therefore

    T_n/A_n -> L(v)/(2sqrt(3)exp(v/2)Re K(v)).                   (7)

For T_n, substitute x=b-(b-a)t into its real-cut integral.
The denominator s-x is at least b-x, which gives the integrable
dominating density C sqrt((1-t^3)/t). Away from t=0 its rescaled
integrand converges to exp(-vt)sqrt((1-t^3)/t); dominated convergence
therefore gives the first limit. The identities rho^3=4 and

    (1-t)|t+eta|^2=1-t^3

give the stated density and prefactor.

For the radial integral put u=1-rho q tau. Equation (5) gives

    I_n/(rho q)^(3/2) -> K(v).

Its integrand is dominated by C exp(-v tau/2)(sqrt(tau)+tau)
along each sequence with rho n q tending to v. The coefficient satisfies

    |kappa|~sqrt(3)/(2sqrt(pi)rho) q^(-5/2),
    |lambda|^n -> exp(v/2).

These relations prove the second limit and all constants in (7).

We have L(v)<=sqrt(pi)/sqrt(v). By (4),

    Re K(v)>=(1/sqrt(3))Gamma(3/2)v^(-3/2).

Thus the ratio in (7) is at most

    v exp(-v/2)<=2/exp(1)<4/5.                                 (8)

The margin in (8) holds simultaneously for every v>0.

## The two scaling tails and the all-n quantifier

We supply uniform bounds to prevent the maximizing scale from escaping
to zero or infinity. The estimates below hold for all n>=1 and all
sufficiently small positive q, with constants independent of both.

From (6), the beta integral, and the coefficient expansion, we obtain

    A_n>=c q^(-5/2)|lambda|^n n^(-3/2).                         (9)

We used Beta(n,3/2)>=c n^(-3/2), which follows for n>=2 by restricting
the integral to u in [1-1/n,1], and is direct for n=1.

The already established real-cut bound is

    T_n<=C q^(-1)b^n.                                         (10)

Indeed, sqrt(x-a)|x-lambda|<=C q^(3/2), s-x>=b-x,
and integral_a^b (b-x)^(-1/2)dx=2sqrt(b-a)<=C sqrt(q).
Combining (9)--(10), log(|lambda|/b)>=c q, and v=rho n q, gives

    0<T_n/A_n<=C v^(3/2) exp(-c v).                            (11)

The right side tends to zero as v tends to zero or infinity.

If (1) failed arbitrarily close to s=1, choose q_j tending to zero and
integers n_j>=1 with T_(n_j)/A_(n_j)>=4/5. Equation (11) confines
v_j=rho n_j q_j to a fixed compact subinterval of (0,infinity).
Pass to a subsequence v_j->v in that interval. Then n_j->infinity,
so (7)--(8) give a limiting ratio at most 2/exp(1)<4/5, a
contradiction. This proves (1).

## Optional stronger numerical constant from exact algebra

The parent theory lane supplied the stronger exact bound
Re h>sqrt(2/5). It follows from (3) because

    36D^2(B^2+(8/5)A-16/25)=(3/25)P(tau),

where

    P(tau)=25tau^6-130tau^5+313tau^4-576tau^3
               +784tau^2-576tau+288.

On [0,2], the degree-six Bernstein coefficients of P, in order, are

    288, 96, 1696/15, 544/5, 560/3, 272/3, 112.

For tau=2+z with z>=0, its monomial coefficients in ascending order are

    112, 64, 440, 728, 513, 170, 25.

Thus P>0 on the nonnegative axis. If A>=4/5 there is nothing to show;
otherwise this gives |h^2|>4/5-A and (Re h)^2>2/5.
It improves (8) to sqrt(10/3)/exp(1), approximately 0.672. The
simpler bound (8) already proves (1). These are algebraic certificates,
not numerical root checks.

## Consequence for the main proof

This comparison supplies every phase-grid sign with s sufficiently close
to one, uniformly for all n. Together with the analogous far-endpoint
comparison and a compact-region O(1/n) estimate, it proves eventual full
real-rootedness without the endpoint entire functions or root-index
matching. The global all-n conjecture still requires effective constants
and finite checks, or a global comparison. No effective delta is claimed.
