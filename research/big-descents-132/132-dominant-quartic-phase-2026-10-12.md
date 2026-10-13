# A dominant quartic pair and asymptotically real zeros of B132

Owner: academic Codex theory lane. Related issue: RealRooted #1623.
Status: paper proofs using standard singularity analysis; not Lean verified.
These results concern the complete B_n family. They do not prove that every
B_n is real-rooted, or that all sufficiently large B_n are real-rooted.

## Statements

Let N_n be the number of distinct negative real roots of B_n, and let
D_n=deg B_n=floor(2(n-1)/3). Then

    N_n/D_n -> 1  as n -> infinity.                       (1)

In particular, for every epsilon>0, every sufficiently large B_n has at
least (1-epsilon)D_n distinct negative real roots. The number of roots
not accounted for by these distinct negative roots is o(n), not zero.

We also obtain an explicit limiting distribution. Define, for s>1,

    W_s(lambda)=lambda^4-4lambda^3+6s lambda^2-4s^2 lambda+s^2.

Let lambda(s) be its unique root in the upper half-plane and put

    R(s)=|lambda(s)|,  theta(s)=arg lambda(s) in (0,pi).

The function theta is strictly increasing, with limits 0 and 2pi/3 at
s=1 and infinity, respectively. For fixed 1<s_1<s_2,

    #{distinct roots of B_n in (1-s_2,1-s_1)}/n
      -> (theta(s_2)-theta(s_1))/pi.                     (2)

The same limit holds when roots are counted with multiplicity.

## Exact root geometry of W_s

Its discriminant is -6912s^4(s-1)^4<0. A real quartic with negative
nonzero discriminant has exactly two distinct real roots and one
nonreal conjugate pair. There are no negative real roots, since W_s(-x)
has positive coefficients for x>=0. Moreover

    W_s(0)=s^2>0, W_s(1)=-3(s-1)^2<0,
    W_s(s)=s^2(s-1)^2>0.

Thus its real roots a(s),b(s) satisfy

    0<a(s)<1<b(s)<s.                                    (3)

The important additional assertion is

    R(s)>b(s)>a(s),   for every s>1.                     (4)

Here is an algebraic exclusion of equality. Suppose a real root r>0 has
modulus equal to that of the nonreal pair. Write the other real root as
u r, with u>0, and the nonreal pair as roots of
lambda^2-2hr lambda+r^2, where -1<h<1. Vieta gives

    r(1+u+2h)=4,
    (1+u)(1+2h)=6 sqrt(u),
    (1+u+2hu)(1+u+2h)=16u.

The second equation follows from the lambda^2 coefficient and
s=r^2 sqrt(u)>0. Put q=sqrt(u). Substituting
2h=6q/(1+q^2)-1 in the third equation gives

    (q^3+q+6)(6q^3+q^2+1)-16q(1+q^2)^2
      =3(q-1)^4(2q^2+3q+2)=0.

Hence q=1 and h=1, contradicting a nonreal pair. Equality in (4) is
therefore impossible. All four roots are simple throughout s>1, so
these labeled real and upper-half-plane roots vary continuously.
At s=2, setting lambda=1+x gives x^4+6x^2-3. Thus b<2 whereas
R=sqrt(4+2sqrt(3))>2. Connectedness proves (4) throughout the interval.

## The phase is monotone and has the required range

A polynomial identity is

    6s(s-1) partial_s W_s
      +(lambda^2+4(s-1)lambda-s) partial_lambda W_s
      =4(lambda+4s-3)W_s.

Implicit differentiation at the simple upper root yields

    lambda'(s)=(lambda^2+4(s-1)lambda-s)/(6s(s-1)),
    theta'(s)=Im(lambda)(1+s/R^2)/(6s(s-1))>0.            (5)

At s=1, W_1=(lambda-1)^4, so theta tends to zero. At infinity,
rescale lambda=s^(2/3)v. The resulting monic polynomial tends to

    v(v^3-4).

Its four roots are distinct. The upper root consequently tends to
4^(1/3)exp(2pi i/3), giving theta -> 2pi/3. This proves the asserted
range, including strict monotonicity.

For orientation, theta=pi/2 occurs at s=3+2sqrt(2): substituting
lambda=iR into W_s gives R=s and s^2-6s+1=0.

The endpoint scales are also explicit. The simple-root expansions after
the indicated rescalings give

    theta(s) ~ sqrt(3) 2^(-1/3) (s-1)^(1/3),    s -> 1+;
    2pi/3-theta(s) ~ sqrt(3) 2^(-4/3) s^(-1/3), s -> infinity. (6)

For the first line, write lambda=1+x and e=s-1; the equation is
x^4+4ex+6ex^2-4e^2x-3e^2=0. Set x=e^(1/3)v, whose upper limiting
root satisfies v^3=-4. For the second, put e=s^(-1/3); the scaled
equation is v^4-4v+6ev^2-4e^2v^3+e^2=0. At the upper cube root v_0,
v=v_0-(v_0^2/2)e+O(e^2). These imply (6).

## Coefficient asymptotics for the complete B sequence

The established algebraic generating function is

    V(z,t)=sum_(n>=1) B_n(t)z^n
      =(A-sqrt(D))/(2tz(1-sz)),
    s=1-t,
    A=1-2z+sz^2,
    D=1-4z+6sz^2-4s^2z^3+s^2z^4,

with sqrt(D)=1 at z=0. The roots of D are the reciprocals of those of
W_s. Thus (4) makes zeta=1/lambda and its conjugate the unique dominant
singularities, both simple square-root branch points.

The apparent pole at z=1/s is removable. By (3), 1/s lies before the
first positive real zero 1/b of D. Along this positive segment sqrt(D)
is positive and equals A=1-1/s at z=1/s. Equivalently,

    V=2z/(A+sqrt(D)),

which is regular there. The point z=0 is regular as well. At the two
complex branch points the denominator 1-sz is nonzero and the
square-root coefficient is nonzero, so neither branch cancels.

For each compact interval I contained in (1,infinity), singularity
analysis gives, uniformly for s in I,

    B_n(1-s)=n^(-3/2) [kappa(s)lambda(s)^n
                          +conj(kappa(s)lambda(s)^n)]
               +O_I(R(s)^n n^(-5/2)),                         (7)

where kappa is a nonvanishing smooth complex function. Explicitly, let

    c(s)=product_(mu a root of W_s, mu != lambda)
                          sqrt(1-mu/lambda),
    kappa(s)=c(s)/(4 sqrt(pi) (1-s) zeta (1-s zeta)).

Each square root is continued radially from value one at z=0 before
setting z=zeta. Equivalently the factors here use their principal values:
for the real roots their arguments lie in the upper half-plane, while
1-conj(lambda)/lambda has positive real part. In particular c and kappa
are nonzero.

The analytic input is the transfer of a square-root local term to its
coefficient, [z^n](1-z)^1/2 ~ -n^(-3/2)/(2sqrt(pi)), with the next
half-integer term giving an O(n^(-5/2)) remainder. We use
Flajolet--Odlyzko, *Singularity analysis of generating functions*,
[Section 2 and Corollary 3](https://algo.inria.fr/flajolet/Publications/FlOd90b.pdf),
SIAM J. Discrete Math. 3 (1990), 216--240; paper-cache record 563.
Their introduction explicitly notes the extension to finitely many
singularities by composite contours. Here compactness and (4) give a
uniform modulus gap to the other two singularities, uniformly separated
branch points, and uniformly bounded local analytic factors. We can
therefore choose the two local Hankel contours uniformly after scaling
by R(s), with an outer contour of radius uniformly greater than one.
The same transfer estimates then give the uniform remainder in (7).
This compact-uniform argument is part of our proof, not a claim that the
paper states this parameterized application verbatim.

## Alternating signs prove (1) and (2)

Choose a smooth argument phi(s) of kappa on a fixed compact interval.
Divide (7) by the positive quantity 2|kappa|R^n n^(-3/2). We get

    normalized B_n(1-s)=cos(n theta(s)+phi(s))+O_I(1/n). (8)

The phase n theta+phi is strictly increasing for all sufficiently large
n: theta' has a positive minimum on the compact interval, and phi' is
bounded. At the points where this phase equals successive integers times
pi, the signs in (8) alternate once the uniform error is less than one.
The intermediate value theorem gives at least

    n(theta(s_2)-theta(s_1))/pi-O_I(1)

distinct negative roots in (1-s_2,1-s_1). This is an all-n eventual
bound on each fixed interval, not a numerical sampling assertion.

Let s_1 decrease to 1 and s_2 increase to infinity. The phase span tends
to 2pi/3, while D_n/n -> 2/3. The degree upper bound and the preceding
lower bound imply (1). To get the matching upper bound in (2), apply the
same lower bound on two disjoint intervals outside (s_1,s_2), then let
their exterior endpoints tend to 1 and infinity. Subtracting their root
counts from D_n leaves the upper bound in (2). This argument also bounds
multiplicities or roots at fixed endpoints; neither contributes positive
limiting mass beyond the stated distribution.

## Remaining work and formalization plan

This is a theorem about the complete target sequence, but it leaves the
full real-rootedness goal open. A vanishing proportion of unaccounted
roots can still include nonreal roots for every n. We have not shown an
O(1) bound on their number, and no finite range completes this theorem.

The next analytic target is uniform control at the two ends of (6),
where the compact-interval proof does not apply. These phase scales point
to t of order -n^(-3) near zero and of order -n^3 at the far left. A
proof must count every remaining root in these regimes, including the
three degree residue classes. The known multiplier and forest limits
may help identify the limiting edge functions, but they do not supply
uniform endpoint error bounds or the missing exact root count.

For formalization, keep two separate pieces under #1623:

1. An elementary algebraic leaf in `RealRooted.BigDescents132`, with data
   `reciprocalDiscriminantPolynomial s`, root-existence/uniqueness facts,
   and proposed `norm_upperRoot_gt_realRoot` for s>1. Reuse complex roots
   of a real polynomial and Vieta; the polynomial itself does NOT split
   over the reals. The no-equal-modulus certificate above is finite algebra.
2. The analytic layer needs simple-root differentiability, `upperRoot_arg`
   with the derivative (5), its endpoint limits, and a uniform two-point
   square-root coefficient-transfer theorem. Proposed application names
   `eventually_many_negative_roots` and `tendsto_negative_root_proportion`
   must have the exact epsilon/eventually and limit quantifiers in (1).
   Audit existing analysis APIs before implementing this substantially
   larger dependency. Do not substitute a caller-supplied B_n root theorem
   or claim the full conjecture from this proportion statement.

Acceptance: s>1 explicitly; real roots in (0,1) and (1,s); dominant pair
strictly larger in modulus; continuous phase in (0,2pi/3); removable pole
checked; kappa nonzero; compact-uniform error and phase monotonicity before
using alternating signs; degree D_n and all missing-root qualifications
retained. Claude owns all implementation and build checks.

Evidence: the companion JSON retains exact symbolic checks of the quartic
identity, discriminant, and equal-modulus factorization. Numerical sanity
checks at s=2,4,10 and n=30,60,100 agree with the oscillatory formula; they
are labeled numerical only and are not used as proof. No new polynomial
sequence generator is introduced: all B rows were already stored. No Lean
source edits or builds ran in this theory lane.
