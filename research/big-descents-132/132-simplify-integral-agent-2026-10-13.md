# An explicit far-parameter comparison for B132

Owner: delegated integral-theory agent; parent academic theory lane.
Status: elementary paper proof, not Lean checked. Related issue: #1623.
We use the quartic root geometry and exact integral formula already proved
in `132-uniform-oscillation-2026-10-13.md`. No Lean files were changed.

**Sharper result:** the final section proves the practical cutoff s>=512,
uniformly for every n>=1, with T_n/A_n<63/64. The earlier large cutoff
below is retained as an independent explicit comparison proof.

## Result

For every integer n>=1 and every real s>=20000^3, we have

    A_n(s)>0,             0<T_n(s)/A_n(s)<3/5.

Thus every phase grid point in this parameter range has the required sign.
The numerical cutoff 20000^3=8000000000000 is deliberately conservative.
It is a parameter cutoff, not a degree cutoff: this theorem does not prove
the original all-n real-rootedness statement by finite verification.

We retain 0<a<1<b<s, lambda in the upper half-plane, R=|lambda|>b,
and the definitions of c,H,I_n,kappa,T_n,A_n from the cited note.
Put omega=exp(2 pi i/3) and epsilon=1/1000.

## A comparison under explicit root bounds

We first prove the conclusion under these four inequalities:

    sqrt(a/R)<=epsilon,
    |b/lambda-omega^2|<=epsilon,
    |conj(lambda)/lambda-omega|<=epsilon,
    R/s<=epsilon.                                             (1)

Define

    c_infinity(u)=sqrt(u)*sqrt(u-omega^2)*sqrt(u-omega)
                =sqrt(u(u^2+u+1)),
    H_infinity(u)=c_infinity(u)/sqrt(3),
    J_n=integral_0^1 u^(n-1/2)*sqrt(1-u^3) du,
    beta_n=integral_0^1 u^(n-1)*sqrt(1-u) du.

All square roots of complex quantities are principal. The first factor
of c differs from sqrt(u) by at most epsilon: for any z with a principal
square root and real u>=0,

    |sqrt(z)-sqrt(u)|^2<=|z-u|,

because |sqrt(z)+sqrt(u)|>=|sqrt(z)-sqrt(u)|. Apply this to
z=u-a/lambda. Each of the other two square roots differs from its
limiting factor by at most epsilon. Indeed both radicands have real
part at least 1/2-epsilon, so the real part of the sum of the two
square roots is larger than 1. All these latter factors have modulus
less than 3/2. A telescoping product estimate gives, for 0<=u<=1,

    |c(u)-c_infinity(u)|<=6 epsilon,
    |c(1)|>=sqrt(3)-6 epsilon,
    |c(u)/c(1)-H_infinity(u)|<=8 epsilon.

The pole factor L(u)=(lambda-s)/(u lambda-s) satisfies
|L(u)-1|<=epsilon/(1-epsilon)<2 epsilon. Since H_infinity<=1,

    |H(u)-H_infinity(u)|<=11 epsilon.                          (2)

The elementary inequality sqrt(u(u^2+u+1))>=u implies

    J_n>=Beta(n+1,3/2)
       =[2n/(2n+3)] beta_n >=(2/5) beta_n.

The beta ratio follows by one integration by parts, so no gamma
asymptotic is needed. Integrating (2) gives

    Re I_n >= J_n*(1/sqrt(3)-55 epsilon/2)>0.                   (3)

The exact expression for kappa gives

    A_n=|c(1)| R^(n+2) Re I_n
        /[pi(s-1)|lambda-s|].

Hence

    A_n >= R^(n+2) J_n/[pi(s-1)s]
           *(sqrt(3)-6 epsilon)*(1/sqrt(3)-55 epsilon/2)
           /(1+epsilon).                                     (4)

In T_n, substitute x=b u. By (1),
|lambda/b-omega|<=epsilon/(1-epsilon)<2 epsilon. Since
|u-omega|>=1 and b/s<R/s<=epsilon,

    |u-lambda/b|<=(1+2 epsilon)|u-omega|,
    1/(1-bu/s)<=1/(1-epsilon).

We bound sqrt(u-a/b) by sqrt(u) and extend the integration interval
down to zero. Using sqrt(1-u)|u-omega|=sqrt(1-u^3), we get

    T_n <= b^(n+2) J_n/[2pi(s-1)s]
           *(1+2 epsilon)/(1-epsilon).                        (5)

Combining (4)--(5) and b/R<1 yields

    T_n/A_n <= (1/2)
      *(1+2 epsilon)*(1+epsilon)
      /[(1-epsilon)*(sqrt(3)-6 epsilon)
                       *(1/sqrt(3)-55 epsilon/2)] <3/5.       (6)

For the final rational bound, use 17/10<sqrt(3)<18/10 to see that
the product of the two last denominator factors is greater than
1-0.006/1.7-0.0275*1.8>0.946. The numerator is less than 1.004,
so (6) is less than 1.004/(2*0.999*0.946)<3/5.

## The quartic implies the root bounds

Put e=s^(-1/3), r=4^(1/3), B=e^2 b, rho=e^2 R, and
L=e^2 lambda=U+iV. We prove the following for 0<e<=1/1000:

    1/4<a<1/4+e^3,
    r-2e<B<r,
    |rho-r|<2e,
    |L-r omega|<10e.                                         (7)

First, W_s(1/4)>0. At x=1/4+1/s<=0.251, division by s^2 gives

    W_s(x)/s^2 =-4/s+6x^2/s-4x^3/s^2+x^4/s^2<0.

The unique root of W_s in (0,1) is a, proving the first bound.
The scaled polynomial is

    P_e(z)=e^8 W_s(z/e^2)
          =z^4-4z+6e z^2-4e^2 z^3+e^2.

At z=r it is positive. At z=r-2e, we have 1.49<z<1.6 and

    z^4-4z=-2e*z*(z^2+zr+r^2)<-19e,
    6e z^2-4e^2 z^3+e^2<16e.

Thus P_e(r-2e)<0. Since the corresponding w values exceed 1,
the unique root there is b, proving the second bound.

Vieta gives rho=(aB)^(-1/2). We have

    |aB-r/4|<=e/2+(8/5)e^3,
    aB>0.3725.

The derivative of x^(-1/2) has modulus less than 5/2 on
[0.3725,infinity), and (r/4)^(-1/2)=r. The mean value theorem
therefore gives |rho-r|<2e.

The sum of the roots gives

    U=2e^2-ae^2/2-B/2,
    |U+r/2|<2e.

Write V_0=sqrt(3)r/2>1.29. Since V>0 and V^2=rho^2-U^2,

    |V-V_0|
      <=[|rho-r|(rho+r)+|U+r/2|(|U|+r/2)]/V_0
      <[2e*3.202+2e*1.602]/1.29<8e.

Thus |L-r omega|<=|U+r/2|+|V-V_0|<10e, completing (7).
In particular rho>1.498, so

    |b/lambda-omega^2|
      <=(|B-r|+|L-r omega|)/rho<9e,
    |conj(lambda)/lambda-omega|
      <=2|L-r omega|/rho<14e,
    R/s=e rho<2e,
    sqrt(a/R)=e sqrt(a/rho)<e.

If e<=1/20000, all four quantities in (1) are at most 1/1000.
This proves the stated result for s>=20000^3.

## Formalization boundary

The proof after the known integral representation needs only elementary
real/complex inequalities, the mean value theorem, and positivity and
comparison of interval integrals. We can retain J_n and beta_n as named
integrals and avoid Gamma, Beta and their analytic continuation entirely.

Suggested declarations in the existing B132 namespace:
`realCut_lt_radialAmplitude_of_root_bounds` for (1)--(6),
`scaled_roots_close_of_parameter_ge` for (7), and
`realCut_lt_radialAmplitude_of_parameter_ge` for the explicit corollary.
The acceptance checks must retain every n>=1, the principal square-root
convention, and the existing exact contour identity as a dependency.
The region 1<s<20000^3 still needs an all-n argument.

## Sharper angular comparison: s>=1000

We now prove, for every n>=1 and every s>=1000,

    A_n(s)>0,             0<T_n(s)/A_n(s)<35/36.                (8)

The estimate uses the actual quartic geometry. Write

    beta=b/R, alpha=a/R, theta=arg(lambda),
    z=exp(i theta), c=cos(theta),
    eta=arg(s-conj(lambda)), Gamma=3pi/2-2theta.

We first work on pi/2<=theta<2pi/3. Vieta gives

    beta+2c=(4-a)/R>0.                                       (9)

The three principal square roots defining c(u) have argument sum

    arg c(u)=(1/2)arg(u-alpha exp(-i theta))
              +(1/2)arg Q(u),
    Q(u)=(u-beta exp(-i theta))*(u-exp(-2i theta)).

We show that this sum is nonnegative and decreasing. The first argument
is nonnegative and decreasing. For the second, put

    Q(u)=u^2+D u+E+i(F u+G),
    D=1-2c^2-beta c,        E=beta cos(3theta),
    F=sin(theta)*(beta+2c), G=-beta sin(3theta).

All four coefficients are nonnegative, and D,F are positive. Hence Q
lies in the closed first quadrant on [0,1]. The numerator of the
derivative of its argument is

    F*(u^2+D u+E)-(F u+G)*(2u+D)
      =-F u^2-2G u+(F E-G D),
    F E-G D=beta sin(theta)*(-1-2beta c)<=0.

The last inequality uses -1/2<=c<=0 and beta<1. This proves monotonicity.
There is no argument wrap: the two original arguments entering Q have
opposite signs, their sum lies in (-pi,pi), and Q is in the first
quadrant. At u=0,

    arg c(0)=(pi-theta)/2+(2pi-3theta)/2=Gamma.

Consequently 0<=arg c(u)<=Gamma and
0<=arg c(u)-arg c(1)<=Gamma for 0<=u<=1. The pole factor satisfies

    -eta<=arg((lambda-s)/(u lambda-s))<=0.

Indeed arg(s-u lambda) decreases from 0 to -eta as u increases from
0 to 1. Therefore

    -eta<=arg H(u)<=Gamma,
    Re H(u)>=h*|H(u)|,
    h=min(cos eta,cos Gamma)=min(cos eta,-sin(2theta)).          (10)

We shall apply this with h>0.

We next compare the two integral densities at the same scaled argument
u. For u>=a/b, define

    q_1=|u-beta exp(-i theta)|,
    q_2=|u-exp(-2i theta)|,
    q_3=|beta u-exp(i theta)|.

Since c<=0, we have |u-alpha exp(-i theta)|>=u. Also

    q_1^2<=q_2^2,
    q_1^2/beta^2-q_3^2
      =u^2*(beta^(-2)-beta^2)-2u c*(beta^(-1)-beta)>=0.

For the first inequality, beta c>=c>=cos(2theta), and beta^2<=1.
Thus beta*q_3/sqrt(q_1*q_2)<=1.

After substituting x=b u in T_n, the ratio of twice its density to
the density of A_n is

    beta^(n+1)*sqrt(u-a/b)*q_3/|c(u)|
      *|u lambda-s|/[(s-bu)*cos(arg H(u))].

Use |c(u)|>=sqrt(u)*sqrt(q_1*q_2), (10), and beta^n<=1 to obtain

    2*(T density)/(A density)
      <=|u lambda-s|/[(s-bu)*h]
      <=|lambda-s|/[(s-b)*h].

For the last inequality, |u lambda-s| increases with u since
Re(lambda)<=0, while s-bu decreases. We integrate over [a/b,1];
the A density is strictly positive on the remaining interval as well.
It follows that

    0<T_n/A_n <= |lambda-s|/[2(s-b)h].                        (11)

This is a useful algebraic sufficient condition in its own right. If
theta is in [pi/2,2pi/3), h>0, and |lambda-s|<2(s-b)h, then every
n>=1 satisfies T_n<A_n. Both cosine terms in h are algebraic in the
quartic roots: cos eta=(s-Re(lambda))/|s-lambda| and
-sin(2theta)=-2 Re(lambda) Im(lambda)/R^2. Thus interval arithmetic
can certify the criterion on any desired compact parameter interval.

### Elementary bounds for s>=1000

Put e=s^(-1/3)<=1/10, r=4^(1/3), B=e^2 b, rho=e^2 R, and
U=e^2 Re(lambda). We have 79/50<r<8/5. As above,

    1/4<a<1/4+e^3<=0.251,
    P_e(z)=z^4-4z+6e z^2-4e^2 z^3+e^2.

We claim r-4e/3<B<r. At z=r-4e/3>36/25,

    P_e(z)/(e z^2)
      =-(4/3)*(z+r+r^2/z)+6-4ez+e/z^2
      <=-4r+6+e/z^2
      <-4*(79/50)+6+(1/10)/(36/25)^2<0.

Here z+r^2/z>=2r. Also P_e(r)>0, since
6-4er>0. Both scaled arguments correspond to w>1, so the root
between them is b. In particular

    36/25<B<8/5,
    rho=(aB)^(-1/2)<5/3,
    U=2e^2-ae^2/2-B/2<-7/10,
    cos(theta)=U/rho<-21/50.

Together with theta<2pi/3 from the known quartic geometry, these
inequalities imply pi/2<theta<2pi/3 and

    cos Gamma=-2cos(theta)sin(theta)
      >(21/25)*(sqrt(3)/2)>18/25.

We also have R/s=e rho<1/6 and b/s=eB<4/25. Hence

    cos eta=(s-Re(lambda))/|s-lambda|>s/(s+R)>6/7>18/25,
    |lambda-s|/(s-b)<(1+1/6)/(1-4/25)=25/18.

Thus h>18/25. Substituting into (11) gives

    0<T_n/A_n <(1/2)*(25/18)/(18/25)=625/648<35/36,

which proves (8). This argument leaves the region 1<s<1000 open.
It needs no asymptotic constants, special-function estimates, or
numerical quadrature. The earlier exact contour identity and quartic
root order remain its dependencies.

### The shorter cutoff s>=512

We can shorten the root estimates and improve the parameter cutoff.
For every s>=512 and n>=1, we have

    A_n(s)>0,            0<T_n(s)/A_n(s)<63/64.                 (12)

Now e<=1/8. Direct evaluation gives

    P_e(7/5)=-1099/625+(294/25)e-(1247/125)e^2<0,

because -1099/625+(294/25)/8<0. Since P_e(r)>0 and both arguments
correspond to w>1, we get 7/5<B<r<8/5. Vieta and a>1/4 give

    rho=(aB)^(-1/2)<sqrt(20/7)<17/10,
    U=2e^2-ae^2/2-B/2<1/32-7/10=-107/160,
    cos(theta)=U/rho<-107/272<-39/100.

The quartic root geometry still gives cos(theta)>-1/2. The function
2k*sqrt(1-k^2) is increasing for 0<=k<=1/2. At k=39/100,
its square is greater than 25/49 by rational arithmetic. Therefore

    cos Gamma=-sin(2theta)>5/7.

Since R/s<17/80 and cos(theta)>-1/2, we have

    |s-lambda|^2/s^2
      =1-2cos(theta)*(R/s)+(R/s)^2
      <1+17/80+289/6400=8049/6400<81/64.

Thus |s-lambda|/s<9/8. Also b/s=eB<1/5. Consequently

    cos eta=(s-Re(lambda))/|s-lambda|>8/9>5/7,
    |s-lambda|/(s-b)<(9/8)/(4/5)=45/32.

Apply (11) with h>5/7 to obtain

    0<T_n/A_n<(1/2)*(45/32)/(5/7)=63/64.

The remaining parameter interval is now 1<s<512. No claim about the
number of exceptional degrees follows from this parameter cutoff.
