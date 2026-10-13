# An effective all-n comparison near s=1

Owner: delegated integral-theory agent; parent academic theory lane.
Status: paper proof using the exact contour identity, known quartic geometry,
and the independently derived limiting-kernel inequalities stated below.
Not Lean checked. Related issue: RealRooted #1623.

The final refinement extends the proved region to q<=1/100, with
T_n/A_n<99/100 uniformly for all n>=1.

## Result and dependencies

Put q=(s-1)^(1/3). For every integer n>=1 and every
0<q<=1/200, we prove

    A_n(s)>0,              0<T_n(s)/A_n(s)<15/16.               (1)

Equivalently, the parameter interval is
1<s<=1+1/8000000. This supplements the proved s>=512 region.

We use the definitions of A_n,T_n,H,c from
`132-uniform-oscillation-2026-10-13.md`, and the root order
0<a<1<b<s, lambda=U+iV with V>0, R=|lambda|>b.
We also use the proved angular range

    pi/6<arg(lambda-a)<2pi/3.

Put r=4^(1/3), eta=exp(i pi/3), and let h be the continuous square
root, h(0)=1, of

    h(tau)^2=(2+eta^2*tau+eta/(eta-tau))/3,       tau>=0.

The limiting-kernel calculation from the parallel theory lane proves

    Re h(tau)>=sqrt(2/5),           Re h(tau)>=|h(tau)|/2.      (2)

We retain (2) as an explicit dependency. The present note makes its
transfer to the actual finite-s kernel effective and closes the integral
comparison without a limiting argument.

## Explicit root bounds

The change w=1+qz gives

    q^(-4) W_s(1+qz)=P_q(z)
       =z^4+4z+6qz^2-3q^2-4q^3z.

For each z_0 in {-r,r eta,r conj(eta)}, the disk |z-z_0|<2q
contains exactly one zero of P_q. On its boundary,

    |z^4+4z|
      >=2q*(r-2q)*(r sqrt(3)-2q)^2>23q,
    |6qz^2-3q^2-4q^3z|<16q.

Here 79/50<r<8/5 and q<=1/200; for example r-2q>1.57 and
r sqrt(3)-2q>2.72, while |z|<1.61. Rouché's theorem proves
the assertion. The real disk contains a, and the upper disk contains
lambda. The existing inequality 1<b<s gives the remaining bound.
Therefore we can write

    lambda=1+q(r eta+delta_lambda),
    a=1+q(-r+delta_a),
    b=1+q delta_b,
    |delta_lambda|<=2q, |delta_a|<=2q, 0<delta_b<q^2.            (3)

In particular |lambda-1|<1.61q.

## Uniform relative control of H

Set u=1-rq tau, so 0<=tau<=1/(rq). Let

    L=(lambda-1)/q,
    d_1=(L-(a-1)/q)/r,      d_1^0=1+eta,
    d_2=(L-(b-1)/q)/r,      d_2^0=eta,
    d_3=(L-conj(L))/r,      d_3^0=i sqrt(3),
    d_4=(L-q^2)/r,          d_4^0=eta.

The normalized affine factors are

    f_j(tau)=(d_j-lambda*tau)/d_j,
    f_j^0(tau)=(d_j^0-tau)/d_j^0,
    R_j(tau)=f_j(tau)/f_j^0(tau).

We have

    H(u)^2=f_1*f_2*f_3/f_4^2,
    h(tau)^2=f_1^0*f_2^0*f_3^0/(f_4^0)^2.

From (3),

    |d_1-d_1^0|,|d_3-d_3^0|<(200/79)q,
    |d_2-d_2^0|,|d_4-d_4^0|<(127/100)q.

For d=x+iy with x>=0,y>0 and tau>=0, we use

    1/|d-tau|<=1/y,
    tau/|d-tau|<=|d|/y.

The second follows by squaring; the difference is
(x*tau-|d|^2)^2>=0. These inequalities and |lambda-1|<1.61q
give the following conservative bounds:

    |(d_1-lambda*tau)/(d_1^0-tau)-1|<6.2q,
    |(d_2-lambda*tau)/(d_2^0-tau)-1|<3.4q,
    |(d_3-lambda*tau)/(d_3^0-tau)-1|<3.1q,
    |(d_4-lambda*tau)/(d_4^0-tau)-1|<3.4q.

Also |d_j/d_j^0-1|<1.47q for j=1,3, and <1.27q for j=2,4.
Dividing by these normalizing factors yields

    |R_1-1|<=8q,
    |R_2-1|,|R_3-1|,|R_4-1|<=5q.                            (4)

All four disks in (4) avoid zero. Taking the continuous logarithms
which vanish at tau=0 gives

    log(H(u)/h(tau))
      =(log R_1+log R_2+log R_3)/2-log R_4.

There is no sign ambiguity: H(1)=h(0)=1 and all factors remain nonzero.
Since |log(1+z)|<=|z|/(1-|z|), (4) gives

    |log(H/h)|
      <=q*((8/(1-8q)+10/(1-5q))/2+5/(1-5q))<15q.

For 0<=x<=3/40, the series estimate
exp(x)-1<=x/(1-x/2) holds because k!>=2^(k-1). Thus

    |H(u)/h(tau)-1|<=exp(15q)-1<16q.                          (5)

By (2) and (5),

    Re H(u)>=(1-32q) Re h(tau)
            >=(21/25)*sqrt(2/5)>1/2.                         (6)

This holds uniformly for every u in [0,1].

## An exact beta-integral comparison

For x in [a,b], put C(x)=(x-a)|x-lambda|^2. Direct differentiation
gives

    C'(x)=3*(x-(a+2U)/3)^2+V^2-(U-a)^2/3>=0.

The final inequality follows from the stated range of arg(lambda-a).
Therefore sqrt(x-a)|x-lambda|<=sqrt(b-a)|b-lambda|. Since
s-x>=b-x, the exact real-cut integral satisfies

    T_n<=sqrt(b-a)|b-lambda|/[2pi(s-1)]
          *b^(n-1/2)*Beta(n,1/2).

By (6),

    A_n> |c(1)|R^(n+2)/[2pi(s-1)|lambda-s|]
            *Beta(n,3/2).

The beta ratio is Beta(n,1/2)/Beta(n,3/2)=2n+1, by integration
by parts. Hence, with ell=log(R/b)>0,

    T_n/A_n < D*(2n+1)*exp(-ell*n),
    D=|b-lambda|*sqrt(b-a)*|lambda-s|
           /[|c(1)|R^2*sqrt(b)].                             (7)

This formula uses the actual lower bound 1/2 in (6); no n-dependent
asymptotic is involved. The continuous maximum gives

    (2n+1)*exp(-ell*n)<=2/ell*exp(-1+ell/2).                  (8)

## Explicit constants in (7)--(8)

Since
|c(1)|=sqrt(|lambda-a||lambda-b||lambda-conj(lambda)|)/R^(3/2),
we can rewrite D as

    D=sqrt(|lambda-b|)*sqrt(b-a)*|lambda-s|
          /sqrt(R*b*|lambda-a|*|lambda-conj(lambda)|).

The bounds (3), R*b>1, and r>79/50 give

    D <= r*q/sqrt(3) * (1+(13/10)q)^2/(1-(3/2)q)
       <(103/100)*r*q/sqrt(3).                               (9)

For ell, use R>=Re(lambda)>=1+rq/2-2q^2 and b<=1+q^3.
The inequalities log(1+x)>=x-x^2/2 and log(1+x)<=x for x>=0
give

    ell >= rq/2-(2+r^2/8+q)q^2
          >(49/100)*r*q.

Indeed 2+r^2/8+q<2.325 and q<=1/200, while r>1.58.
Also R<=1+|lambda-1|<1+1.61q and b>1, so

    ell<1.61q<=0.00805,
    exp(ell/2)<201/200.

The latter follows, for example, from exp(x)<=1/(1-x) for 0<=x<1.
Combining (7)--(9), we obtain

    T_n/A_n
      < (206/49)*(201/200)/(exp(1)*sqrt(3))
      < (206/49)*(201/200)*(15/68)
      =621090/666400<15/16.

Here exp(1)>8/3 and sqrt(3)>17/10. This proves (1).

## Formalization boundary and remaining interval

The comparison depends on the exact contour identity, the quartic root
order and angular range, and the two algebraic inequalities (2) for h.
Its analytic ingredients are Rouché's theorem for three small disks,
elementary logarithm/exponential bounds, and monotonicity and comparison
of real interval integrals. Beta can be replaced everywhere by the
displayed elementary integrals and their integration-by-parts ratio.

Combining this result with s>=512 leaves the compact interval
1+1/8000000<s<512 for an all-n proof or an effective finite reduction.
No degree cutoff or full B132 theorem is asserted here.

## Refinement to q<=1/100

We can improve the root estimates without changing the argument. For
0<q<=1/100, use disks of radius (7/5)q instead of 2q. On their
boundaries,

    |z^4+4z|>(7/5)q*(1.56)*(2.71)^2>16q,
    |6qz^2-3q^2-4q^3z|<16q.

For the first inequality, r-(7/5)q>1.56 and
r sqrt(3)-(7/5)q>2.71. For the second, |z|<1.62, and
6*(1.62)^2+3/100+4*(1/100)^2*(1.62)<16.
Rouché now gives

    |delta_lambda|,|delta_a|<7q/5,
    0<delta_b<q^2,
    |lambda-1|<1.62q.                                       (10)

In the normalized affine-factor argument, (10) gives

    |d_1-d_1^0|,|d_3-d_3^0|<(1773/1000)q,
    |d_2-d_2^0|,|d_4-d_4^0|<(9/10)q.

Thus the four unnormalized relative errors are respectively bounded
by 5.3q, 2.92q, 2.65q, and 2.92q. The normalization errors are at
most 1.03q for j=1,3 and 0.9q for j=2,4. Dividing as before yields

    |R_1-1|<(13/2)q,
    |R_2-1|,|R_3-1|,|R_4-1|<4q.

Consequently

    |log(H/h)|
      <q*((6.5/(1-6.5q)+8/(1-4q))/2+4/(1-4q))<12q,
    |H/h-1|<exp(12q)-1<13q.

The last step uses exp(x)-1<=x/(1-x/2) for x<=0.12. Therefore

    Re H>=(1-26q)Re h
         >=(37/50)*sqrt(2/5)>7/15.                          (11)

We apply the same beta-integral comparison using 7/15 in place of
1/2. If D now denotes the constant in that comparison, (10) gives

    D <= (15/14)*rq/sqrt(3)
                  *(1+0.9q)^2/(1-1.03q)
       <(309/280)*rq/sqrt(3).

Indeed (1+0.009)^2/(1-0.0103)<103/100. For ell, we have

    ell>=rq/2-(1.4+r^2/8+q)q^2
        >rq/2-1.73q^2>(39/80)rq,
    ell<1.62q<=0.0162,
    exp(ell/2)<101/100.

The continuous maximum in (8) therefore gives

    T_n/A_n
      <(412/91)*(101/100)/(exp(1)*sqrt(3))
      <(412/91)*(101/100)*(110/513)
      =4577320/4668300<99/100.

Here exp(1)>27/10 and sqrt(3)>19/11. We have proved

    1<s<=1+1/1000000, n>=1
       ==> A_n(s)>0 and 0<T_n(s)/A_n(s)<99/100.

Combined with the far-parameter theorem, the remaining compact interval
is 1+1/1000000<s<512.

## Audit of the compact certificate and finite-row input

The parent lane's exact interval prototype uses Z=H(u)^2 and certifies

    E=(Im Z)^2+4h_0^2 Re Z-4h_0^4>0.

This condition implies Re H>h_0 on the actual interval. Indeed

    E=(|Z|+Re Z-2h_0^2)*(|Z|-Re Z+2h_0^2),

and the second factor is positive. Thus |Re H|>h_0. Continuity and
H(1)=1 select the positive sign. The principal square roots defining H
are continuous on the radial interval, and u lambda-s never vanishes.
For a parameter box q in [q_l,q_h], covering t in [0,1/q_l] contains
the entire required t=(1-u)/q interval for each q in that box.

The integer maximum used in the prototype is also exact. For
f(n)=(2n+1)rho^n with 0<rho<1,

    f(n+1)/f(n)=rho*(2n+3)/(2n+1).

Consequently a maximum over integers n>=N occurs at

    max(N,ceil((3rho-1)/(2(1-rho)))).

At equality of adjacent values either maximizing integer works. The
fourth power of the moment constant is

    D^4=|b-lambda|^2*(b-a)^2*|lambda-s|^4
           /[64h_0^4 |lambda-a|^2 V^2 R^2 b^2],

as used in the prototype. A completed certificate must additionally
verify the full parameter cover and every t cover, with exact replay
of its interval inequalities; a partially completed run proves only
the boxes already covered.

We independently checked the existing coefficient file
`/tmp/rr132-extended-E-B.json`, SHA256
`e33226a4362d6a49df9274fc5e93413df9df8f764e05a05ecf835db9eba10da9`.
Its rows B_0 through B_101 satisfy B_0=B_1=1, E_3=1+t, and the
proved coefficient recurrence

    (n+1)e_(n+1,k)=(4+6k)e_(n,k)+(4n-6k)e_(n,k-1)
                   +(n-3)(e_(n-1,k)-e_(n-1,k-1))

for n=3 through 101, followed by
B_n=E_(n+1)+(1-t)B_(n-1) for n=2 through 101. All equalities were
checked coefficientwise with integers. The coefficients of every stored
B row are nonnegative, their constant coefficients are positive, and
their degrees are floor(2(n-1)/3) for n>=1.

These checks establish provenance of the finite input through the proved
recurrence; they do not establish real-rootedness. That separate check
uses exact polynomial root arithmetic. Simplicity additionally needs a
distinct-root count or a squarefree check. This audit did not create a
new polynomial sequence generator; maintained Rust integration remains
the separately tracked task.

## An elementary replacement for Rouché in the audited near region

For the audited range 0<q<=1/200, we can prove (3) using real-root
signs and Vieta's formulas. This removes Rouché's theorem from the
dependencies of the bound T_n/A_n<15/16. We keep the earlier argument
above unchanged as a separate proof.

The scaled quartic is

    P_q(z)=z^4+4z+6qz^2-3q^2-4q^3z,
    r=4^(1/3),              3/2<r<8/5.

For a real parameter c, direct expansion gives

    P_q(-r+cq)/q
      =6r^2-12c
       +q*(6r^2*c^2-12r*c-3)
       +q^2*(-4r*c^3+6c^2+4r)
       +q^3*(c^4-4c).                                      (13)

At c=1, the constant term is greater than 3/2, the coefficient
of q is greater than -23, the coefficient of q^2 equals 6, and
the coefficient of q^3 equals -3. Thus

    P_q(-r+q)/q>3/2-23q-3q^3>0.

At c=3/2, the constant term is less than -13/5, the coefficient
of q is less than 35, the coefficient of q^2 is
27/2-(19/2)r<0, and the coefficient of q^3 is -15/16. Hence

    P_q(-r+3q/2)/q<-13/5+35q<0.

Both evaluation points are negative. The known quartic root order
implies that P_q has exactly one negative real root A=(a-1)/q.
The intermediate value theorem therefore gives

    -r+q<A<-r+3q/2.

Set d=A+r, so q<d<3q/2. The other real scaled root
B=(b-1)/q satisfies 0<B<q^2 by 1<b<s. Let Z=U+iV=(lambda-1)/q,
where V>0. Vieta gives

    U=-(A+B)/2=r/2-(d+B)/2,
    V^2=6q+3A^2/4+AB/2+3B^2/4.

Put V_0=sqrt(3)r/2. Substitution of A=-r+d yields

    V^2-V_0^2
      =6q-(3/2)r*d+(3/4)d^2+(1/2)(-r+d)B+(3/4)B^2.

Its lower bound is

    V^2-V_0^2>(12/5)q-(4/5)q^2>0,

by discarding the positive terms and using d<3q/2, r<8/5,
and B<q^2. For the upper bound, note that -r+d=A<0, so

    V^2-V_0^2
      <(15/4)q+(27/16)q^2+(3/4)q^4<(94/25)q.

Since V>V_0 and sqrt(3)>17/10,

    0<V-V_0
      =(V^2-V_0^2)/(V+V_0)
      <[(94/25)/(51/20)]q<3q/2.

Also

    |U-r/2|=(d+B)/2<4q/5.

Consequently

    |Z-r eta|^2<(4q/5)^2+(3q/2)^2=(17q/10)^2,
    |Z-r eta|<17q/10<2q,
    |A+r|<3q/2<2q.

Together with 0<B<q^2, these are exactly the bounds (3) used in
the audited near-region proof. Thus that proof needs only polynomial
evaluation, the intermediate value theorem, Vieta, and elementary
real/complex inequalities for root localization. All subsequent constants
and the final 15/16 comparison remain unchanged.
