# Super-Recurrence Eulerian Polynomials

Related lab record:
`/home/paxinum/Dropbox/AI-projects/projects/polynomial-interlacing-lab/projects/`
`super_recurrence_eulerian/`.

Related Rust probe:
`/home/paxinum/Dropbox/AI-projects/rust/experiments/src/bin/`
`super_recurrence_eulerian_probe.rs`.

Source: Umesh Shankar, *Log-concavity of rows of triangular arrays
satisfying a certain super-recurrence*, arXiv:2508.12467.

Related method notes:

- `working/p-eulerian-posets.md`: Wagner/Hadamard proper-position package and
  endpoint absorption cautions.
- `working/chow-polynomials.md`: \(\mathbb I_n\)-interlacing cone language for
  reciprocal endpoints.
- `working/hurwitz-mixed-genus.md`: gamma change-of-variables and reciprocal
  root-pair intuition.

## Definition

For an integer \(l \ge 1\), let \(E^{(l)}(n,k)\) be the row defined by
\[
E^{(l)}(1,0)=1
\]
and, for \(n\ge 2\),
\[
E^{(l)}(n,k)
  =(k+1)^l E^{(l)}(n-1,k)
  +(n-k)^l E^{(l)}(n-1,k-1).
\]
The one-variable polynomial is
\[
E_n^{(l)}(t)=\sum_{k=0}^{n-1} E^{(l)}(n,k)t^k .
\]
The source proves log-concavity and palindromicity, and records limited
evidence for real-rootedness when \(l\ge 2\).

Writing \(\theta=t\,d/dt\), the row recurrence is
\[
E_n^{(l)}(t)=
\left((\theta+1)^l+t(n-1-\theta)^l\right)E_{n-1}^{(l)}(t).
\]
This is the most compact scalar form, but it is not by itself a proof
mechanism; see the counterexample below.

## Block-Leader Product Formula

Let \(B\subseteq[n]\) be a block-leader set, so \(1\in B\).  Write
\[
c_n(B)=\#\{f:[n]\to[n]\ :\ f(i)\le i,\ \operatorname{bl}(f)=B\}.
\]
Then
\[
c_n(B)=\prod_{i=1}^n w_i(B),
\]
where, if \(r_i=|B\cap[i-1]|\),
\[
w_i(B)=
\begin{cases}
i-r_i, & i\in B,\\
r_i, & i\notin B.
\end{cases}
\]
Equivalently, if \(B=\{1=b_1<b_2<\dotsb<b_r\}\), then
\[
c_n(B)=
\prod_{j=1}^r (b_j-j+1)
\prod_{j=1}^r j^{b_{j+1}-b_j-1},
\qquad b_{r+1}=n+1.
\]

Thus
\[
E_n^{(l)}(t)
  =\sum_{\substack{B\subseteq[n]\\1\in B}}
     c_n(B)^l\,t^{|B|-1}.
\]
This formula is the correct last-entry surface.  The tempting model of
\(l\)-tuples of permutations with a common descent set is false: for
\(n=4,l=2\) it gives \([1,43,43,1]\), while the target row is
\([1,41,41,1]\).

## Main Target

The source asks for the following in the range \(l\ge2\); the proof below
actually gives the \(l\ge1\) statement:

\[
E_n^{(l)}(t) \text{ is real-rooted for all } l\ge 1,\ n\ge 1.
\]

The stronger consecutive-row target, also now proved below, is:

\[
E_{n-1}^{(l)}(t) \ll E_n^{(l)}(t)
\qquad (l\ge 1,\ n\ge 2).
\]

Since the rows are palindromic, we also define gamma polynomials
\[
E_n^{(l)}(t)
  =\sum_j \gamma_{n,j}^{(l)} t^j(1+t)^{n-1-2j},
\qquad
\Gamma_n^{(l)}(z)=\sum_j \gamma_{n,j}^{(l)}z^j.
\]
A stronger unnormalized gamma refinement, still separate and still open, is:

\[
\Gamma_n^{(l)}(z) \text{ is real-rooted, and }
\Gamma_{n-1}^{(l)}(z)\ll \Gamma_n^{(l)}(z).
\]

If \(\Gamma_n^{(l)}\) has only nonpositive real roots, then
\[
E_n^{(l)}(t)=(1+t)^{n-1}
\Gamma_n^{(l)}\left(\frac{t}{(1+t)^2}\right)
\]
has only real roots.  Thus gamma real-rootedness would give another proof of
the main real-rootedness target.

Throughout, \(f\ll g\) denotes the weak proper-position/interlacing relation
with the orientation used by the Garloff--Wagner two-pair Hadamard theorem.  We
allow repeated roots, zero roots, and degree differences of one, and use the
closed weak form obtained by limits.  For a fixed PF polynomial \(p\), the set
of \(q\) with \(p\ll q\) is a convex cone.

## Hadamard Normalization Proof of the Main Target

The main real-rootedness target has a short proof after the correct
normalization.  Put \(d=n-1\) and write
\[
  Q_n^{(l)}(t)
  =\sum_{i=0}^d
    \frac{E^{(l)}(n,i)}{\binom di^l}t^i .
\]
Then
\[
  E_n^{(l)}(t)
  =
  B_{d,l}(t)\odot Q_n^{(l)}(t),
  \qquad
  B_{d,l}(t)=\sum_{i=0}^d \binom di^l t^i .
\]
The binomial-power kernel \(B_{d,l}\) is the \(l\)-fold Hadamard product of
\((1+t)^d\) with itself, and hence has only nonpositive real roots by the
Schur--Polya--Wagner Hadamard product theorem.  A convenient reference is
Garloff--Wagner, *Hadamard products of stable polynomials are stable*,
J. Math. Anal. Appl. 202 (1996), Theorem 4(a).

It remains to prove that \(Q_n^{(l)}\) is also PF.  The normalized coefficients
satisfy
\[
  Q_n^{(l)}(t)
  =
  (1+t)
  \left(\frac{(\theta+1)(n-1-\theta)}{n-1}\right)^l
  Q_{n-1}^{(l)}(t).
\]
For \(N\ge0\), the operator \(N-\theta\) preserves polynomials with
nonnegative coefficients and only nonpositive real roots in degree at most
\(N\).  Indeed, after removing any zero root, write
\(p(t)=\prod_j(t+a_j)\), with \(a_j>0\), and \(m=\deg p\le N\).  Then
\[
  (N-\theta)p
  =
  (N-m)p+\sum_j a_j\,\frac{p}{t+a_j},
\]
which is a nonnegative combination of polynomials weakly interlacing \(p\).
The cone property gives nonpositive real-rootedness.  The operator
\(\theta+1\) also preserves this class since
\[
  (\theta+1)p=(tp)' ,
\]
and Rolle's theorem applies to \(tp\).  Multiplication by \(1+t\) only adds
the root \(-1\).  Induction from \(Q_1^{(l)}=1\) proves that every
\(Q_n^{(l)}\) is PF.

Applying the Hadamard product theorem once more to
\(B_{d,l}\odot Q_n^{(l)}\) proves that \(E_n^{(l)}(t)\) has only nonpositive
real roots.  This proves the main real-rootedness conjecture for all
\(l\ge1\), in particular for the \(l\ge2\) range emphasized in the source.

The same Hadamard normalization also proves consecutive row interlacing, as
explained next.  Cumulative last-leader prefix interlacing is proved below as a
further consequence of the endpoint theorem.  The gamma and normalized-row
interlacing refinements remain separate proof targets supported by exact
checks; they are not needed for the main real-rootedness theorem.

## Consecutive Row Interlacing

The stronger consecutive row interlacing
\[
  E_n^{(l)}(t)\ll E_{n+1}^{(l)}(t)
\]
also follows from the two-pair Hadamard theorem, specifically the weak
proper-position form of Garloff--Wagner, Theorem 4(b).  The weak closed form
allows the zero roots introduced by shifted reciprocals such as
\(I_{d+1}K_{d,l}\) and by \(tQ_n^{(l)}\).

Fix \(n\), put \(d=n-1\), and abbreviate
\[
  p(t)=E_n^{(l)}(t),\qquad
  A(t)=(\theta+1)^l p(t).
\]
Then the recurrence and palindromicity of \(p\) give
\[
  E_{n+1}^{(l)}(t)=A(t)+R(t),
  \qquad
  R(t)=t^n A(1/t).
\]
Indeed, if \(p(t)=\sum_{i=0}^d a_i t^i\) with \(a_i=a_{d-i}\), then,
for \(1\le j\le d+1\), the coefficient of \(t^j\) in \(R\) is
\[
  (d+2-j)^l a_{j-1},
\]
which is exactly the coefficient contributed by
\(t(n-\theta)^l p(t)\).  Both sides have zero constant term.

We now show that \(p\) interlaces both summands \(A\) and \(R\).  Let
\[
  K_{d,l}(t)=\sum_{i=0}^d (i+1)^l\binom di^l t^i,
  \qquad
  I_{d+1}h(t)=t^{d+1}h(1/t).
\]
With the normalized row \(Q_n^{(l)}\), we have
\[
  p=B_{d,l}\odot Q_n^{(l)},\qquad
  A=K_{d,l}\odot Q_n^{(l)}.
\]
Moreover, since \(Q_n^{(l)}\) is palindromic of degree \(d\),
\[
  R=(I_{d+1}K_{d,l})\odot tQ_n^{(l)}.
\]

It remains to compare the two kernel pairs.  Set
\[
  V_d(t)=(1+t)^d,\qquad
  U_d(t)=\sum_{i=0}^d (i+1)\binom di t^i
        =(1+t)^{d-1}(1+(d+1)t).
\]
The displayed factorization is for \(d\ge1\); the case \(d=0\) is trivial.
The roots show
\[
  V_d\ll U_d,\qquad V_d\ll I_{d+1}U_d.
\]
For the first relation, \(V_d\) has only the root \(-1\), while \(U_d\)
has \(-1\) with multiplicity \(d-1\) and the additional root
\(-1/(d+1)\).  For the second relation, \(I_{d+1}U_d\) has roots
\(-(d+1)\), \(-1\) with multiplicity \(d-1\), and \(0\).

Repeated application of the two-pair Hadamard interlacing theorem gives
\[
  B_{d,l}=V_d^{\odot l}\ll U_d^{\odot l}=K_{d,l}
\]
and
\[
  B_{d,l}=V_d^{\odot l}\ll (I_{d+1}U_d)^{\odot l}
          =I_{d+1}K_{d,l}.
\]
On the normalized-row side, \(Q_n^{(l)}\) is PF by the proof above, so
\[
  Q_n^{(l)}\ll Q_n^{(l)},\qquad
  Q_n^{(l)}\ll tQ_n^{(l)}.
\]
Applying the two-pair Hadamard theorem to these pairs yields
\[
  p=B_{d,l}\odot Q_n^{(l)}
    \ll K_{d,l}\odot Q_n^{(l)}=A
\]
and
\[
  p=B_{d,l}\odot Q_n^{(l)}
    \ll (I_{d+1}K_{d,l})\odot tQ_n^{(l)}=R.
\]
The cone of polynomials \(q\) satisfying \(p\ll q\) is convex.  Hence
\[
  p\ll A+R=E_{n+1}^{(l)}.
\]
This proves consecutive row interlacing for all \(l\ge1\), in particular for
the \(l\ge2\) range of the source.

## Wagner--Interlacing Pivot Audit

The proof route above is now the main route for the project.  It proves the
source's real-rootedness problem, and more:
\[
  E_n^{(l)} \text{ is PF},\qquad
  E_n^{(l)}\ll E_{n+1}^{(l)},\qquad
  P_{n,m-1}^{(l)}\ll P_{n,m}^{(l)}.
\]
All three statements use the same small package:

- the normalized rows \(Q_n^{(l)}\) are PF by the polar-derivative induction;
- the kernels \(V_d=(1+t)^d\), \(U_d=(1+t)^{d-1}(1+(d+1)t)\), and their
  shifted reciprocals give the required endpoint interlacings by root lists;
- Garloff--Wagner's two-pair Hadamard theorem transports these kernel
  interlacings to \(B_{d,l}\), \(K_{d,l}\), and the actual rows;
- convexity of a fixed-left interlacing cone turns the two boundary summands
  into consecutive row interlacing.

This is the part that should be polished first.  It is short, robust, and does
not require the normalized-gamma refinement.

### Paper-Ready Wagner--Hadamard Package

The clean proof can be extracted as the following theorem package.

**Theorem A.** For every \(l\ge1\) and \(n\ge1\), the polynomial
\[
  E_n^{(l)}(t)
\]
has only nonpositive real zeros.

**Theorem B.** For every \(l\ge1\) and \(n\ge1\),
\[
  E_n^{(l)}(t)\ll E_{n+1}^{(l)}(t).
\]

**Theorem C.** For every \(l\ge1\), \(n\ge1\), and \(1<m\le n\), the
cumulative block-leader prefixes satisfy
\[
  P_{n,m-1}^{(l)}(t)\ll P_{n,m}^{(l)}(t).
\]

Here is the minimal proof stack.

1.  **Normalized row lemma.**  Put \(d=n-1\) and
    \[
      Q_n^{(l)}(t)=
      \sum_{i=0}^d\frac{E^{(l)}(n,i)}{\binom di^l}t^i .
    \]
    Then
    \[
      Q_n^{(l)}(t)
      =
      (1+t)
      \left(\frac{(\theta+1)(n-1-\theta)}{n-1}\right)^l
      Q_{n-1}^{(l)}(t).
    \]
    The operators \(N-\theta\) and \(\theta+1\) preserve the cone of
    nonnegative polynomials with only nonpositive real roots in the relevant
    degree range: \(N-\theta\) is a polar-derivative/interlacing-cone
    combination, while \((\theta+1)p=(tp)'\).  Therefore every
    \(Q_n^{(l)}\) is PF.

2.  **Hadamard kernel lemma.**  Let
    \[
      B_{d,l}(t)=\sum_i\binom di^l t^i,\qquad
      K_{d,l}(t)=\sum_i(i+1)^l\binom di^l t^i .
    \]
    The kernel \(B_{d,l}\) is PF because it is the \(l\)-fold Hadamard power
    of \((1+t)^d\).  Moreover, with
    \[
      U_d(t)=\sum_i(i+1)\binom di t^i=(1+t)^{d-1}(1+(d+1)t),
    \]
    the root lists give
    \[
      (1+t)^d\ll U_d,\qquad
      (1+t)^d\ll I_{d+1}U_d,
    \]
    where \(I_{d+1}h=t^{d+1}h(1/t)\).  Garloff--Wagner's two-pair Hadamard
    theorem then gives
    \[
      B_{d,l}\ll K_{d,l},\qquad
      B_{d,l}\ll I_{d+1}K_{d,l}.
    \]
    The root list also gives \(U_d\ll I_{d+1}U_d\), hence
    \[
      K_{d,l}\ll I_{d+1}K_{d,l}.
    \]

3.  **Theorem A.**  We have
    \[
      E_n^{(l)}=B_{d,l}\odot Q_n^{(l)} .
    \]
    Since both factors are PF and have nonnegative coefficients, the
    Schur--Polya--Wagner Hadamard theorem proves Theorem A.

4.  **Theorem B.**  Let \(p=E_n^{(l)}\) and
    \(A=(\theta+1)^l p\).  By palindromicity,
    \[
      E_{n+1}^{(l)}(t)=A(t)+t^nA(1/t).
    \]
    The decompositions
    \[
      p=B_{d,l}\odot Q_n^{(l)},\qquad
      A=K_{d,l}\odot Q_n^{(l)},
    \]
    and
    \[
      t^nA(1/t)=(I_{d+1}K_{d,l})\odot tQ_n^{(l)}
    \]
    combine with the two kernel interlacings above and the trivial relations
    \(Q_n^{(l)}\ll Q_n^{(l)}\), \(Q_n^{(l)}\ll tQ_n^{(l)}\).  Garloff--Wagner
    gives \(p\ll A\) and \(p\ll t^nA(1/t)\), and convexity of the fixed-left
    interlacing cone gives \(p\ll E_{n+1}^{(l)}\).

5.  **Theorem C.**  The cumulative prefixes have the closed form
    \[
      P_{n,m}^{(l)}=(\theta+1)^{l(n-m)}E_m^{(l)}.
    \]
    The reciprocal endpoint
    \[
      A_m^{(l)}(t)\ll t^mA_m^{(l)}(1/t),
      \qquad A_m^{(l)}=(\theta+1)^lE_m^{(l)},
    \]
    follows from \(K_{d,l}\ll I_{d+1}K_{d,l}\) with \(d=m-1\), from
    \(Q_m^{(l)}\ll tQ_m^{(l)}\), and from Garloff--Wagner.  By convexity,
    \[
      A_m^{(l)}\ll E_{m+1}^{(l)}.
    \]
    Since \((\theta+1)^l\) is a proper-position preserver, applying
    \((\theta+1)^{l(n-m-1)}\) for \(m<n\) gives
    \[
      P_{n,m}^{(l)}\ll P_{n,m+1}^{(l)}.
    \]
    Replacing \(m\) by \(m-1\) gives the stated form of Theorem C.

This package is the right candidate for a clean written proof.  The reciprocal
endpoint statement
\[
  A_n^{(l)}(t)\ll t^nA_n^{(l)}(1/t),
  \qquad A_n^{(l)}(t)=(\theta+1)^lE_n^{(l)}(t),
\]
can be included either as a lemma before Theorem B or as an explanatory
corollary of the same Hadamard kernel argument.

### Polished Proof Draft

We now give the same argument in a form closer to a paper proof.  We use the
following standard form of the Schur--Polya--Wagner theorem: if \(f,g\) have
nonnegative coefficients and only nonpositive real zeros, then
\[
  f\odot g
\]
has only nonpositive real zeros.  We also use the two-pair form of
Garloff--Wagner: if \(f\ll g\) and \(h\ll k\), with all four polynomials in
the same nonnegative PF cone, then
\[
  f\odot h\ll g\odot k .
\]
All interlacing statements are interpreted in the weak closed sense, so zero
roots and degree differences of one are allowed.

First we prove that the normalized rows are PF.  Let \(d=n-1\) and set
\[
  Q_n^{(l)}(t)
  =
  \sum_{i=0}^{d}
  \frac{E^{(l)}(n,i)}{\binom di^l}t^i .
\]
The recurrence for \(E^{(l)}(n,i)\) is equivalent to
\[
  Q_n^{(l)}(t)
  =
  (1+t)
  \left(
    \frac{(\theta+1)(n-1-\theta)}{n-1}
  \right)^l
  Q_{n-1}^{(l)}(t),
  \qquad n\ge2.
\]
We claim that this recurrence preserves the PF cone.  Let \(p\) have
nonnegative coefficients, only nonpositive real zeros, and degree at most
\(N\).  After removing any zero root, write
\[
  p(t)=\prod_j(t+a_j),\qquad a_j>0,
\]
and put \(m=\deg p\).  Then
\[
  (N-\theta)p
  =
  (N-m)p+\sum_j a_j\frac{p}{t+a_j}.
\]
The summands on the right weakly interlace \(p\), and the coefficients are
nonnegative.  Hence \(N-\theta\) preserves the PF cone in degree at most
\(N\).  Also
\[
  (\theta+1)p=(tp)',
\]
so Rolle's theorem shows that \(\theta+1\) preserves this cone.  Multiplication
by \(1+t\) only appends the root \(-1\).  Starting from \(Q_1^{(l)}=1\), the
recurrence proves that every \(Q_n^{(l)}\) is PF.

Next define
\[
  B_{d,l}(t)=\sum_{i=0}^d \binom di^l t^i .
\]
Since \(B_{d,l}\) is the \(l\)-fold Hadamard product of \((1+t)^d\) with
itself, the Schur--Polya--Wagner theorem gives that \(B_{d,l}\) is PF.  The
Hadamard factorization
\[
  E_n^{(l)}(t)=B_{d,l}(t)\odot Q_n^{(l)}(t)
\]
therefore proves that \(E_n^{(l)}\) has only nonpositive real zeros.  This
proves the source's real-rootedness problem for all \(l\ge1\).

We now prove the consecutive interlacing.  Put
\[
  K_{d,l}(t)=\sum_{i=0}^d (i+1)^l\binom di^l t^i
\]
and
\[
  U_d(t)=\sum_{i=0}^d(i+1)\binom di t^i
        =(1+t)^{d-1}(1+(d+1)t)
\]
for \(d\ge1\), with the case \(d=0\) immediate.  The root lists give
\[
  (1+t)^d\ll U_d
  \quad\text{and}\quad
  (1+t)^d\ll I_{d+1}U_d,
\]
where \(I_{d+1}h=t^{d+1}h(1/t)\).  Indeed, \(U_d\) has roots
\(-1/(d+1)\) and \(-1\) with multiplicity \(d-1\), while \(I_{d+1}U_d\)
has roots \(0\), \(-(d+1)\), and \(-1\) with multiplicity \(d-1\).  Applying
Garloff--Wagner repeatedly gives
\[
  B_{d,l}\ll K_{d,l}
  \quad\text{and}\quad
  B_{d,l}\ll I_{d+1}K_{d,l}.
\]
The root list also gives \(U_d\ll I_{d+1}U_d\), and therefore
\[
  K_{d,l}\ll I_{d+1}K_{d,l}.
\]

Let
\[
  p(t)=E_n^{(l)}(t),\qquad A(t)=(\theta+1)^l p(t).
\]
By palindromicity of \(p\), the recurrence may be written as
\[
  E_{n+1}^{(l)}(t)=A(t)+R(t),
  \qquad R(t)=t^nA(1/t).
\]
Using the normalized row \(Q_n^{(l)}\), we have
\[
  p=B_{d,l}\odot Q_n^{(l)},\qquad
  A=K_{d,l}\odot Q_n^{(l)}.
\]
Since \(Q_n^{(l)}\) is palindromic of degree \(d\), we also have
\[
  R=(I_{d+1}K_{d,l})\odot tQ_n^{(l)}.
\]
The trivial PF relations
\[
  Q_n^{(l)}\ll Q_n^{(l)},\qquad Q_n^{(l)}\ll tQ_n^{(l)}
\]
combine with the two kernel interlacings and Garloff--Wagner to give
\[
  p\ll A,\qquad p\ll R.
\]
For a fixed PF polynomial \(p\), the set of \(q\) satisfying \(p\ll q\) is a
convex cone.  Hence
\[
  p\ll A+R=E_{n+1}^{(l)}.
\]
This proves
\[
  E_n^{(l)}\ll E_{n+1}^{(l)}
\]
for all \(l\ge1\) and \(n\ge1\).

The same ingredients also give the reciprocal boundary endpoint.  Since
\[
  A=K_{d,l}\odot Q_n^{(l)},\qquad
  R=(I_{d+1}K_{d,l})\odot tQ_n^{(l)},
\]
the interlacings
\[
  K_{d,l}\ll I_{d+1}K_{d,l},\qquad
  Q_n^{(l)}\ll tQ_n^{(l)}
\]
and Garloff--Wagner imply
\[
  A\ll R=t^nA(1/t).
\]
By convexity of the fixed-left cone, this also gives
\[
  A\ll A+R=E_{n+1}^{(l)}.
\]

Finally we record the cumulative-prefix consequence.  The block-leader
prefixes satisfy
\[
  P_{n,m}^{(l)}=(\theta+1)^{l(n-m)}E_m^{(l)}.
\]
The reciprocal endpoint just proved gives the boundary summand relation
\[
  (\theta+1)^lE_m^{(l)}\ll E_{m+1}^{(l)}.
\]
Since \((\theta+1)^l\) preserves weak proper position, applying
\((\theta+1)^{l(n-m-1)}\) gives
\[
  P_{n,m}^{(l)}\ll P_{n,m+1}^{(l)}
  \qquad(m<n).
\]
Equivalently,
\[
  P_{n,m-1}^{(l)}\ll P_{n,m}^{(l)}
  \qquad(1<m\le n).
\]
Thus the cumulative block-leader prefixes form an interlacing chain.  This
completes the proof of the clean Wagner--Hadamard package.

### Lean/Formalization Blueprint

This subsection is the intended blueprint for the Lean formalization and for a
paper write-up.  The gamma-refinement material below is not part of this
blueprint.

#### Objects and Notation

Work over univariate real polynomials.  We need the following definitions.

- `theta p = t * p'`.
- `hadamard p q` is coefficientwise product:
  \[
    (p\odot q)_i=p_iq_i.
  \]
  Coefficients are zero-extended outside the degree range.
- `reciprocalShift D p = t^D p(1/t)`, denoted \(I_Dp\).
- `PF p`: \(p\) has nonnegative coefficients and all zeros are real and
  nonpositive.
- `p << q`: weak proper position/interlacing in the Garloff--Wagner
  orientation.
- Super-recurrence rows:
  \[
    E^{(l)}(1,0)=1,\qquad
    E^{(l)}(n,k)=(k+1)^lE^{(l)}(n-1,k)
    +(n-k)^lE^{(l)}(n-1,k-1),
  \]
  with coefficients outside the valid row range interpreted as \(0\),
  and
  \[
    E_n^{(l)}(t)=\sum_{k=0}^{n-1}E^{(l)}(n,k)t^k.
  \]
- For \(d=n-1\),
  \[
    Q_n^{(l)}(t)=
    \sum_{i=0}^{d}\frac{E^{(l)}(n,i)}{\binom di^l}t^i,
  \]
  \[
    B_{d,l}(t)=\sum_{i=0}^{d}\binom di^l t^i,\qquad
    K_{d,l}(t)=\sum_{i=0}^{d}(i+1)^l\binom di^l t^i.
  \]
- Also
  \[
    V_d(t)=(1+t)^d,\qquad
    U_d(t)=\sum_{i=0}^{d}(i+1)\binom di t^i.
  \]

#### External or Earlier Theorem Inputs

The proof uses a small number of general real-rootedness/interlacing facts.
These should be isolated first in Lean.

1.  **Schur--Polya--Wagner PF preservation.**  If \(p\) and \(q\) are PF, then
    \(p\odot q\) is PF.

2.  **Garloff--Wagner two-pair theorem.**  If \(p\ll q\) and \(r\ll s\), with
    all four polynomials in the relevant nonnegative PF cone, then
    \[
      p\odot r\ll q\odot s.
    \]

3.  **Fixed-left cone convexity.**  If \(p\) is PF, \(p\ll q\), and \(p\ll r\),
    then
    \[
      p\ll aq+br
    \]
    for all \(a,b\ge0\).  We only need \(a=b=1\).

4.  **Proper-position preservation by \(\theta+1\).**  The operator
    \(\theta+1\), and hence every power \((\theta+1)^l\), preserves weak
    proper position on the nonnegative PF cone.

The first three are exactly the Wagner/Hadamard package.  The fourth follows
from \((\theta+1)p=(tp)'\) and the usual Rolle/interlacing theorem, but it may
be convenient to prove it as a separate lemma.

#### Lemma Order

The formal proof should proceed in the following order.

1.  **Normalized transfer identity.**
    Prove, for \(n\ge2\),
    \[
      Q_n^{(l)}
      =
      (1+t)
      \left(
        \frac{(\theta+1)(n-1-\theta)}{n-1}
      \right)^l Q_{n-1}^{(l)}.
    \]
    This is a coefficient calculation from the recurrence and the binomial
    identities
    \[
      \binom{n-1}{k}
      =
      \frac{n-1}{n-1-k}\binom{n-2}{k}
      =
      \frac{n-1}{k}\binom{n-2}{k-1}.
    \]
    The boundary cases \(k=0\) and \(k=n-1\) should be handled separately to
    avoid division by zero in the displayed identities.

2.  **Polar derivative PF lemma.**
    If \(p\) is PF and \(\deg p\le N\), then \((N-\theta)p\) is PF.  The proof
    is
    \[
      (N-\theta)p
      =
      (N-m)p+\sum_j a_j\,\frac{p}{t+a_j},
      \qquad p=\prod_j(t+a_j),\ a_j>0,\ m=\deg p,
    \]
    plus the interlacing cone property.  Zero roots are handled by factoring
    them out first or by weak limits.

3.  **\(\theta+1\) PF lemma.**
    If \(p\) is PF, then \((\theta+1)p=(tp)'\) is PF.

4.  **Normalized rows are PF.**
    Induct from \(Q_1^{(l)}=1\), using Lemmas 1--3 and multiplication by
    \(1+t\).

5.  **Palindromicity.**
    Prove
    \[
      E^{(l)}(n,k)=E^{(l)}(n,n-1-k)
    \]
    by induction on \(n\).  The recurrence is symmetric after replacing
    \(k\) by \(n-1-k\) and using the inductive hypothesis in row \(n-1\).
    Since \(\binom di=\binom d{d-i}\), this also proves that \(Q_n^{(l)}\) is
    palindromic of degree \(d=n-1\).

6.  **Hadamard factorization of actual rows.**
    Prove
    \[
      E_n^{(l)}=B_{n-1,l}\odot Q_n^{(l)}.
    \]

7.  **Binomial-power kernels are PF.**
    Prove
    \[
      B_{d,l}=V_d^{\odot l}.
    \]
    Since \(V_d=(1+t)^d\) is PF, Schur--Polya--Wagner proves \(B_{d,l}\) is
    PF.

8.  **Main real-rootedness theorem.**
    Combine Lemmas 4, 6, and 7 with Schur--Polya--Wagner to prove
    \(E_n^{(l)}\) is PF.

9.  **Kernel root-list interlacings.**
    For \(d\ge1\), prove
    \[
      U_d=(1+t)^{d-1}(1+(d+1)t).
    \]
    The root lists give
    \[
      V_d\ll U_d,\qquad V_d\ll I_{d+1}U_d,\qquad
      U_d\ll I_{d+1}U_d.
    \]
    The case \(d=0\) should be handled separately.

10. **Hadamard kernel interlacings.**
    Since
    \[
      K_{d,l}=U_d^{\odot l},\qquad
      I_{d+1}K_{d,l}=(I_{d+1}U_d)^{\odot l},
    \]
    repeated use of Garloff--Wagner gives
    \[
      B_{d,l}\ll K_{d,l},\qquad
      B_{d,l}\ll I_{d+1}K_{d,l},\qquad
      K_{d,l}\ll I_{d+1}K_{d,l}.
    \]

11. **Boundary decomposition of \(E_{n+1}^{(l)}\).**
    With \(p=E_n^{(l)}\) and \(A=(\theta+1)^lp\), prove
    \[
      E_{n+1}^{(l)}=A+t^nA(1/t).
    \]
    This is a direct coefficient check using Lemma 5.

12. **Summand decompositions.**
    For \(d=n-1\), prove
    \[
      p=B_{d,l}\odot Q_n^{(l)},\qquad
      A=K_{d,l}\odot Q_n^{(l)},
    \]
    and
    \[
      t^nA(1/t)=(I_{d+1}K_{d,l})\odot tQ_n^{(l)}.
    \]
    The last identity uses palindromicity of \(Q_n^{(l)}\), from Lemma 5.

13. **Consecutive row interlacing.**
    Use Lemma 10, the trivial relations
    \[
      Q_n^{(l)}\ll Q_n^{(l)},\qquad Q_n^{(l)}\ll tQ_n^{(l)},
    \]
    and Garloff--Wagner to prove
    \[
      E_n^{(l)}\ll A,\qquad
      E_n^{(l)}\ll t^nA(1/t).
    \]
    Then use fixed-left cone convexity and Lemma 11 to prove
    \[
      E_n^{(l)}\ll E_{n+1}^{(l)}.
    \]

14. **Reciprocal boundary endpoint.**
    Use
    \[
      K_{d,l}\ll I_{d+1}K_{d,l},\qquad
      Q_n^{(l)}\ll tQ_n^{(l)}
    \]
    and Garloff--Wagner to prove
    \[
      A\ll t^nA(1/t).
    \]
    Convexity then gives \(A\ll E_{n+1}^{(l)}\).

15. **Cumulative prefix closed form.**
    Prove
    \[
      P_{n,m}^{(l)}=(\theta+1)^{l(n-m)}E_m^{(l)}.
    \]
    This follows because after the last allowed block leader, all later
    positions are acted on by \((\theta+1)^l\).

16. **Cumulative prefix interlacing.**
    Apply Lemma 14 with \(m\) in place of \(n\), then apply
    \((\theta+1)^{l(n-m-1)}\).  This proves
    \[
      P_{n,m}^{(l)}\ll P_{n,m+1}^{(l)}
      \qquad(m<n),
    \]
    equivalently
    \[
      P_{n,m-1}^{(l)}\ll P_{n,m}^{(l)}
      \qquad(1<m\le n).
    \]

#### Final Theorems to State

The Lean-facing final theorem list should be:

- `super_recurrence_eulerian_real_rooted`:
  \(E_n^{(l)}\) is PF for \(l\ge1\), \(n\ge1\).
- `super_recurrence_eulerian_consecutive_interlacing`:
  \(E_n^{(l)}\ll E_{n+1}^{(l)}\) for \(l\ge1\), \(n\ge1\).
- `super_recurrence_eulerian_boundary_reciprocal_interlacing`:
  \[
    A_n^{(l)}(t)\ll t^nA_n^{(l)}(1/t),
    \qquad A_n^{(l)}=(\theta+1)^lE_n^{(l)}.
  \]
- `super_recurrence_eulerian_prefix_interlacing`:
  \[
    P_{n,m-1}^{(l)}\ll P_{n,m}^{(l)}
    \qquad(1<m\le n).
  \]

This is the single proof blueprint to use before starting Lean.  The remaining
gamma sections below are intentionally excluded from the formalization plan.

The normalized-gamma interlacing problem should now be treated as an optional
refinement, not as the main proof route.  The local \(h\)-certificate and
tail-packet machinery below are useful evidence, but they are becoming too
large for a clean first proof.  If the gamma refinement is revisited, the
next attempt should look for another small interlacing principle, preferably a
Wronskian/Sturm route or a Wagner-style statement restricted to the actual
normalized rows.

One natural broad shortcut has already failed.  Let
\[
  L_d(t^i)=\frac{(i+1)(d+1-i)}{d+1}t^i .
\]
It is false that every palindromic PF polynomial \(p\) satisfies
\[
  p\ll (1+t)L_d^l p .
\]
For \(d=4\), \(l=5\), and
\[
  p(t)=1+5t+8t^2+5t^3+t^4,
\]
the image is, after clearing denominators,
\[
  3125+166965t+636232t^2+636232t^3+166965t^4+3125t^5,
\]
and exact `polynomial-tools` reports `do_not_interlace`.  Thus any
Wagner-style gamma proof must use the actual normalized-row constraints, not
only palindromicity and PF.

## Normalized Gamma Refinements

The gamma and normalized-row interlacing statements below are now stronger
refinements rather than prerequisites for consecutive row interlacing.  The
broad normalized operator statement is false for arbitrary PF inputs: for
example, with \(N=3\) and \(p(t)=t+18/7\), the polynomial
\[
  (1+t)(\theta+1)(N-\theta)p(t)
\]
has roots \(-27/14\) and \(-1\), so \(p\) does not interlace it in the needed
direction.  The proof of any gamma-level refinement must use the actual
normalized-row structure.

There is a useful gamma-basis calculation.  For
\[
  e_{d,j}(t)=t^j(1+t)^{d-2j}
\]
and \(L_{d+1}=(\theta+1)(d+1-\theta)\), one has
\[
  L_{d+1}e_{d,j}
  =
  (j+1)(d+1-j)e_{d,j}
  +(d-2j)(d-2j-1)e_{d,j+1},
\]
where the second term is omitted outside the gamma range.  Thus \(L_{d+1}\)
acts by a nonnegative bidiagonal matrix in the gamma basis.  This calculation
underlies the partial-iterate route below, but by itself it is not enough:
broad operator-level interlacing shortcuts are false.

A sharper formulation is to work directly with the normalized gamma polynomials
\[
  Q_n^{(l)}(t)
  =(1+t)^{n-1}
  G_n^{(l)}\left(\frac{t}{(1+t)^2}\right).
\]
The lab now records the bridge: for palindromic PF polynomials
\(p=(1+t)^dG(z)\) and \(r=(1+t)^dH(z)\), the shifted relation
\[
  p(t)\ll (1+t)r(t)
\]
is equivalent to the corresponding directed interlacing of \(G\) and \(H\).
Under this bridge, the normalized gamma-refinement target becomes
\[
  G_{n-1}^{(l)}\ll G_n^{(l)}.
\]
The partial-iterate induction below is the current proof target for this
refinement; it is not yet closed.

The bridge is elementary.  If
\[
  G(z)=\prod_i(1+c_i z),\qquad c_i\ge0,
\]
then
\[
  (1+t)^dG\left(\frac{t}{(1+t)^2}\right)
\]
factors, up to a power of \(1+t\), into quadratics
\[
  (1+t)^2+c_i t.
\]
For \(c_i>0\), the two roots of this quadratic are reciprocal negative
numbers, one below \(-1\) and one above \(-1\).  As \(c_i\) increases, this
pair moves monotonically outward away from \(-1\).  Therefore interlacing of
the gamma roots is exactly interlacing of these reciprocal pairs after the
extra central root \(-1\) from the factor \(1+t\) is inserted.  The cases
\(c_i=0\) and repeated roots follow by taking weak limits.

This cannot be promoted to an arbitrary gamma-PF cone statement; the lab
records a small counterexample.  The proof must use the actual normalized
rows.

For this normalized gamma refinement, the proof route is an induction on interlacing
chains of partial gamma iterates.  Put
\[
  F_d^{(l)}(z)=G_{d+1}^{(l)}(z).
\]
Let \(M_d\) be the gamma-basis operator
\[
  M_d z^j
  =
  \frac{(j+1)(d+1-j)}{d+1}z^j
  +
  \frac{(d-2j)(d-2j-1)}{d+1}z^{j+1}.
\]
Then the gamma recurrence is
\[
  F_{d+1}^{(l)}=M_d^lF_d^{(l)}.
\]
Define the partial iterates
\[
  F_{d,s}^{(l)}=M_d^sF_d^{(l)},\qquad 0\le s\le l.
\]
The induction target is that, for every \(d\),
\[
  F_{d,0}^{(l)}\ll F_{d,1}^{(l)}\ll \dotsb \ll F_{d,l}^{(l)}
\]
as a directed interlacing chain, or preferably pairwise in this order.  This
immediately implies the desired normalized gamma interlacing because
\[
  G_{d+1}^{(l)}=F_{d,0}^{(l)},\qquad
  G_{d+2}^{(l)}=F_{d,l}^{(l)}.
\]

Thus the gamma-refinement proof should focus on the local induction step
\[
  (F_{d,0}^{(l)},\dotsc,F_{d,l}^{(l)})
  \quad\Longrightarrow\quad
  (F_{d+1,0}^{(l)},\dotsc,F_{d+1,l}^{(l)}),
\]
using the positive bidiagonal action of \(M_d\) and the interlacing cone
relations.  The base case \(d=0\) is trivial.

The checked data supports a stronger adjacent-chain invariant: the union
\[
  C_d\cup C_{d+1},
  \qquad C_d=(F_{d,0}^{(l)},\dotsc,F_{d,l}^{(l)}),
\]
is pairwise compatible.  This is stronger than the single-chain target, but
unlike global compatibility across all \(d\), it still matches the actual
data.  The induction should therefore try to propagate adjacent compatibility
\[
  C_d\cup C_{d+1}
  \quad\Longrightarrow\quad
  C_{d+1}\cup C_{d+2}.
\]

There is also a concrete spectral form of this induction surface.  The
operator \(M_d\) has eigenvalues
\[
  \lambda_{d,r}=\frac{(r+1)(d+1-r)}{d+1},
  \qquad 0\le r\le \lfloor d/2\rfloor,
\]
with an explicit triangular eigenbasis \(P_{d,r}\).  Under the palindromic
lift
\[
  G(z)\longmapsto (1+t)^dG\left(\frac{t}{(1+t)^2}\right),
\]
the eigenvector \(P_{d,r}\) is just the symmetric monomial pair
\[
  t^r+t^{d-r}
\]
with the usual one-term interpretation at the center.  Thus the spectral
coordinates of \(F_d^{(l)}\) are the positive symmetric coefficients of the
normalized row \(Q_{d+1}^{(l)}\).

This also proves the spectral decomposition without calculation: the lifted
operator is the diagonal operator
\[
  t^i\longmapsto
  \frac{(i+1)(d+1-i)}{d+1}t^i,
\]
and the two monomials \(t^r\) and \(t^{d-r}\) have the same eigenvalue.

The same basis has the positive branching rule
\[
  P_{d,r}=P_{d+1,r}+P_{d+1,r+1}
\]
away from the boundary, with boundary variants
\[
  P_{2m,m}=P_{2m+1,m},\qquad
  P_{2m+1,m}=P_{2m+2,m}+2P_{2m+2,m+1}.
\]
Indeed, after multiplying the degree-\(d\) lift by \(1+t\), the pair
\((1+t)(t^r+t^{d-r})\) splits into the two adjacent degree-\(d+1\)
symmetric pairs.
It follows by induction that the actual rows \(F_d^{(l)}\) have positive
coordinates in the \(P_{d,r}\)-basis normalized by the lowest nonzero
coefficient.  Indeed, applying \(M_d^l\) only multiplies these coordinates by
the positive numbers \(\lambda_{d,r}^l\), and then the branching rule expands
nonnegatively in the next basis.

There is an equivalent lifted form which is often cleaner.  Let
\[
  \widetilde Q_d^{(l)}(t)=Q_{d+1}^{(l)}(t),
  \qquad
  \Phi_d(G)=(1+t)^dG\left(\frac{t}{(1+t)^2}\right),
\]
and let \(D_d\) be the diagonal coefficient operator
\[
  D_d(t^i)=\frac{(i+1)(d+1-i)}{d+1}t^i .
\]
Then
\[
  \Phi_d(F_{d,s}^{(l)})=D_d^s\widetilde Q_d^{(l)}
  \qquad (0\le s\le l),
\]
and the normalized recurrence becomes
\[
  \widetilde Q_{d+1}^{(l)}
  =(1+t)D_d^l\widetilde Q_d^{(l)}.
\]
Thus the adjacent-chain invariant can be viewed as an ordinary interlacing
problem for the lifted diagonal orbits
\[
  D_d^s\widetilde Q_d^{(l)}
  \quad\text{and}\quad
  D_{d+1}^r\widetilde Q_{d+1}^{(l)}.
\]
The gamma bridge gives the precise translation for the cross-degree
relations.

The lifted form gives one proved dimension-shift comparison.  If \(f\) is
gamma-PF in the degree-\(d\) range, then
\[
  M_df\ll M_{d+1}f.
\]
Equivalently, for \(p=\Phi_d(f)\),
\[
  D_dp\ll D_{d+1}((1+t)p).
\]
To see this, put \(R=(d+1-\theta)p\).  Then
\[
  D_dp=\frac{(\theta+1)R}{d+1}
\]
and
\[
  D_{d+1}((1+t)p)
  =
  \frac{\theta+1}{d+2}\bigl(p+(1+t)R\bigr).
\]
The same polar-derivative argument used in the normalized-row proof gives
\[
  R\ll p.
\]
Also \(R\ll (1+t)R\), and hence by convexity
\[
  R\ll p+(1+t)R.
\]
Since \(\theta+1\) preserves proper position, the lifted comparison follows;
the gamma bridge translates it back to \(M_df\ll M_{d+1}f\).

The dimension-shift comparison is one useful adjacent comparison.  A second
useful ingredient is the single-operator restricted preserver statement
\[
  f\ll g \quad\Longrightarrow\quad M_df\ll M_dg
\]
for gamma-PF pairs in the degree-\(d\) range.  However, these two ingredients
do not by themselves close the adjacent-chain induction.  The tempting
argument would extend adjacent links such as
\[
  h_l\ll M_{d+1}h_l\ll M_{d+2}h_l
\]
to all cross-relations in \(C_{d+1}\cup C_{d+2}\), but that uses transitivity
of weak proper position.  Weak proper position is not transitive: polynomial
tools verifies
\[
  t+6\ll t+5,\qquad t+5\ll (t+5)^2,
\]
while \(t+6\) does not weakly interlace \((t+5)^2\).  Thus a proof of the
local step
\[
  C_d\cup C_{d+1}\quad\Longrightarrow\quad C_{d+1}\cup C_{d+2}
\]
still needs a direct finite-orbit or common-interlacing cone argument for the
actual normalized rows.

A natural one-sided repair is also false.  The implication
\[
  f\ll g \quad\Longrightarrow\quad f\ll M_dg
\]
does not hold abstractly in the gamma-PF cone.  For \(d=4\), take
\[
  f(z)=5+z,\qquad g(z)=1+6z.
\]
Then \(f\ll g\), but
\[
  M_4g=1+12z+\frac{12}{5}z^2
\]
is not compatible with \(f\): after clearing denominators, the pencil
\[
  12f+M_4g
\]
has discriminant \(-48/5\).  Hence the missing lemma must use the actual
normalized-row structure, not just the abstract \(M_d\)-preserver.

The global version of this preserver lemma has a finite-symbol form.  Put
\[
  m=\left\lfloor\frac d2\right\rfloor,\qquad
  a_j=\frac{(j+1)(d+1-j)}{d+1},\qquad
  b_j=\frac{(d-2j)(d-2j-1)}{d+1}.
\]
The Borcea--Branden symbol of \(M_d\) in degree \(m\) is
\[
  \mathcal M_d(u,v)
  =
  \sum_{j=0}^m \binom mj
  \left(a_j u^j+b_j u^{j+1}\right)v^{m-j}.
\]
For \(m\ge2\), this factors as \((u+v)^{m-2}\) times a cubic.  More
precisely, for \(d=2m\),
\[
  \mathcal M_{2m}(u,v)
  =
  \frac{(u+v)^{m-2}}{2m+1}B_{2m}(u,v),
\]
where
\[
\begin{aligned}
  B_{2m}(u,v)
  ={}&(m+1)^2u^2+(2m^2+3m+2)uv+(2m+1)v^2  \\
     &+2m\,u^2v+2m(2m-1)uv^2,
\end{aligned}
\]
and for \(d=2m+1\),
\[
  \mathcal M_{2m+1}(u,v)
  =
  \frac{(u+v)^{m-2}}{2(m+1)}B_{2m+1}(u,v),
\]
where
\[
\begin{aligned}
  B_{2m+1}(u,v)
  ={}&(m+1)(m+2)u^2+2(m^2+2m+2)uv+2(m+1)v^2\\
     &+6m\,u^2v+2m(2m+1)uv^2 .
\end{aligned}
\]
The full symbol-stability shortcut fails in both parity families.  For
\(m=2\),
\[
  B_4(-4+i,-1.8261676022347393+0.01807627944817964 i)=0
\]
and
\[
  B_5(1+i,-0.8094317636283898+0.06371146270451353 i)=0,
\]
with both variables in the upper half-plane.  Thus \(M_d\) is not a global
proper-position preserver by the ordinary finite-symbol criterion.  The
statement we need is genuinely a restricted one on the gamma-PF cone, not a
plain Borcea--Branden corollary.  Exact-rational random stress tests of
interlacing pairs in the nonpositive-root cone found no failures for
\(d\le13\), but that is only evidence for the restricted statement.

The useful replacement is a positive-cone compatibility argument plus a short
orientation check.  Suppose \(f\ll g\) are gamma-PF in the degree-\(d\) gamma
range.  Every nonnegative combination
\[
  h=\alpha f+\beta g,\qquad \alpha,\beta\ge0,
\]
is again gamma-PF.  Therefore \(\Phi_d(h)\) is PF.  The lifted identity and
the single-polynomial preservation of \(D_d\) give
\[
  \Phi_d(M_dh)=D_d\Phi_d(h),
\]
which is PF.  Hence \(M_dh\) is gamma-PF.  Since
\[
  M_dh=\alpha M_df+\beta M_dg,
\]
the pair \(M_df,M_dg\) is compatible.

It remains to orient the compatible pair.  For compatible PF pairs, the
directed weak proper-position orientation is characterized by the standard
coefficient-ratio test, with the usual limiting interpretation when zero
coefficients or common factors occur.  Thus, if
\[
  f(t)=\sum_i f_i t^i,\qquad g(t)=\sum_i g_i t^i,
\]
and \(f\ll g\), then the overlapping ratios \(g_i/f_i\) are weakly increasing;
conversely, for a compatible pair this weak increase selects the \(f\ll g\)
orientation.  If \(\deg f=\deg g=r\), then \(M_d\) either raises both degrees
by one with the same top multiplier \(b_r\), or preserves both top degrees
with the same top multiplier \(a_r\); in both cases the constant terms are
unchanged, so the endpoint coefficient ratio selecting the orientation is
preserved.  If \(\deg g=\deg f+1<m\), where \(m=\lfloor d/2\rfloor\), then
the degree difference is preserved, so the compatible image pair is oriented
from the lower-degree polynomial to the higher-degree polynomial.  The only
boundary case is
\(\deg f=m-1\), \(\deg g=m\).  Then both images have degree \(m\), and
\[
  [t^m]M_df=b_{m-1}f_{m-1},
\]
while
\[
  [t^m]M_dg=a_mg_m+b_{m-1}g_{m-1}.
\]
The ratio monotonicity gives
\[
  \frac{g_{m-1}}{f_{m-1}}\ge \frac{g_0}{f_0},
\]
and the positive term \(a_mg_m\) only increases the top ratio.  Thus the
endpoint ratio again has the orientation \(M_df\ll M_dg\).  Consequently,
\[
  f\ll g \quad\Longrightarrow\quad M_df\ll M_dg
\]
for gamma-PF pairs in the degree-\(d\) range.

The restricted \(M_d\)-preserver and the dimension-shift comparison therefore
give many adjacent comparisons, but they do not yet prove pairwise
compatibility of a whole finite orbit.  The remaining normalized-gamma target
is to prove the adjacent-chain invariant directly:
\[
  C_d\cup C_{d+1}\text{ is pairwise compatible for all }d.
\]
The exact checks support this invariant, and the first-to-last relation would
imply
\[
  G_{d+1}^{(l)}=F_{d,0}^{(l)}\ll F_{d,l}^{(l)}=G_{d+2}^{(l)}.
\]
At present this should be treated as a plausible refinement, not as a closed
proof.

For the consecutive normalized-gamma theorem alone, the adjacent-chain
invariant is stronger than necessary.  It would be enough to prove the
internal actual-orbit statement
\[
  F_{d,a}^{(l)}\ll F_{d,b}^{(l)}
  \qquad(0\le a\le b\le l).
\]
In spectral coordinates, this asks for
\[
  \sum_r c_{d,r}^{(l)}\lambda_{d,r}^aP_{d,r}
  \ll
  \sum_r c_{d,r}^{(l)}\lambda_{d,r}^bP_{d,r},
\]
where the \(c_{d,r}^{(l)}\) are the actual coordinates of \(F_d^{(l)}\).
The case \(a=0,b=l\) gives \(G_{d+1}^{(l)}\ll G_{d+2}^{(l)}\).

The cleanest positive formulation for the stronger adjacent-chain invariant is
the following mixed lifted cone target.
Let
\[
  \widetilde Q_d^{(l)}=\Phi_d(F_d^{(l)})=Q_{d+1}^{(l)}.
\]
It would suffice to prove that, for every \(0\le s,r\le l\), every
nonnegative pencil between
\[
  D_d^s\widetilde Q_d^{(l)}
  \qquad\text{and}\qquad
  D_{d+1}^r\bigl((1+t)D_d^l\widetilde Q_d^{(l)}\bigr)
\]
is PF, with the coefficient-ratio orientation giving the displayed left
polynomial before the displayed right polynomial.  This would give all
cross-relations directly by Obreschkoff and would avoid transitivity
entirely.

This lifted recurrence also explains a small parity feature in the data.  The
polynomial \(\widetilde Q_d^{(l)}\) has a central factor \(1+t\) when \(d\) is
odd, and at least \((1+t)^2\) when \(d\) is even and \(d\ge2\).  Indeed
\(D_d\) preserves palindromicity, and multiplication by \(1+t\) adds the next
central factor; a palindromic polynomial of odd degree already vanishes at
\(-1\).  Equivalently, \(F_d^{(l)}\) has actual degree at most
\(\lfloor(d-1)/2\rfloor\), so even \(d\) starts one gamma degree below the
ambient basis and the first partial iterate introduces the new far-left root.

The spectral picture is the most plausible repair target.  A useful, but
false if stated for arbitrary positive coordinates, lemma would be: if
\[
  f=\sum_r c_r P_{d,r},\qquad c_r>0,
\]
with the specific coefficient constraints coming from the normalized rows,
then
\[
  f,\ M_df,\ M_d^2f,\dotsc
\]
is a directed interlacing chain.  The actual-row version should relate to total
positivity of the power kernel \((\lambda_{d,r}^s)_{s,r}\), together with a
sign-regular or Sturm property of the spectral basis \(P_{d,r}\).  Positivity
of the coordinates alone is not enough: the lab records a positive-coordinate
gamma-PF counterexample, so the missing ingredient must use the additional
coefficient constraints of the actual normalized rows.

The first nontrivial spectral window is already informative.  In degree
\(d=4\), the relevant degree-drop slice has coordinates
\[
  (c_0,c_1,c_2)=(1,A,2A-2).
\]
Then
\[
  F=A z-4z+1,
\]
and for the \(l=2\) endpoint \(M_4^2F\), the discriminant of the pencil
\[
  F+\lambda M_4^2F
\]
as a quadratic in \(\lambda\) has discriminant
\[
  -\frac{32}{625}(17A-56)(39A^2-190A+112).
\]
The bad positive-coordinate example has \(A=94/23\), for which
\[
  39A^2-190A+112=-\frac{6928}{529}<0.
\]
The actual \(l=2\) row has \(A=45/4\), for which the same expression is
\[
  \frac{46567}{16}>0.
\]
Thus the missing hypothesis is a genuine actual-row root-window inequality,
not positivity of the spectral coordinates.  The focused probe is
`working/super-recurrence-eulerian/spectral_internal_orbit_probe.py`, and the
lab record is `d4_spectral_degree_drop_window_2026_06_05`.

The same calculation now gives a more useful \(d=4\) certificate template.  For
the actual row,
\[
  A=A_l=1+2^{l+1}+\left(\frac32\right)^l,
\]
and the \(s\)-th internal spectral iterate has the form
\[
  F_s(z)
  =
  1+(Au_s-4)z+
  2\bigl((A-1)v_s-Au_s+1\bigr)z^2,
  \qquad
  u_s=\left(\frac85\right)^s,\quad
  v_s=\left(\frac95\right)^s.
\]
For \(0\le a<b\le l\), the discriminant of the pencil
\[
  F_a+\lambda F_b
\]
is a quadratic in \(\lambda\).  Its three coefficients are
\[
\begin{aligned}
  &A^2u_b^2-8Av_b+8v_b+8,\\
  &2\bigl(A^2u_au_b-4Av_a-4Av_b+4v_a+4v_b+8\bigr),\\
  &A^2u_a^2-8Av_a+8v_a+8.
\end{aligned}
\]
Writing \(b=a+h\), \(x=(8/5)^a\), \(y=(9/5)^a\),
\(r=(8/5)^h\), and \(s=(9/5)^h\), the discriminant of this quadratic in
\(\lambda\), divided by \(32\), is
\[
  -A^2x^2(r-1)^2
  -A^2(A-1)x^2y(r-1)(s-r)
  +2(A-1)^2y^2(s-1)^2.
\]
This is exactly the shape one wants: two negative terms and one positive term.
Since \(y^2\le x^2y\), it is enough to prove
\[
  A^2(r-1)(s-r)>2(A-1)(s-1)^2.
\]
For the actual \(A_l\), this inequality is already easy in the checked range
and has a short elementary proof: \(h=1\) follows from
\(A_l\ge A_2=45/4\), \(h=2\) follows by direct substitution, and for
\(h\ge3\) the lower bound \(A_l\ge A_h\ge2^{h+1}\) dominates the threshold
\[
  \frac{2(s-1)^2}{(r-1)(s-r)}
  \le
  \frac{1458}{217}\left(\frac98\right)^h.
\]
The remaining coefficient signs follow from the same large-\(A_l\) estimates,
for instance \(A_l(8/9)^l>8\) for \(l\ge2\).

Thus the \(d=4\) case reduces to elementary exponential inequalities rather
than a new interlacing theorem.  The script verifies the full strong
certificate, including all pairs \(0\le a<b\le l\), for \(2\le l\le12\).
The direct proof below turns this into the first proved local model for the
general spectral root-window proof.

There is an even cleaner way to finish the \(d=4\) model.  Write
\(\alpha=8/5\), \(\beta=9/5\), \(h=b-a\), and put
\[
  X=A\alpha^a,\qquad Y=(A-1)\beta^a,\qquad
  p=\alpha^h,\qquad q=\beta^h .
\]
The direct root-order certificate for \(F_a\) and \(F_b\) reduces to
\[
  I_{a,h}=XY(q-p)+3X(p-1)-4Y(q-1)\ge0
\]
and
\[
  J_{a,h}
  =
  X^2(p-1)\bigl((p-1)+Y(q-p)\bigr)
  -2Y^2(q-1)^2\ge0 .
\]
The \(I\)-inequality follows from
\[
  \frac{4(q-1)}{q-p}\le16
\]
and \(X\ge A(8/5)>16\).  For \(J\), it suffices to prove the scalar bound
\[
  \frac{(q-1)^2}{(p-1)(q-p)}
  \le
  \frac{16}{3}\left(\frac98\right)^{h-1}.
\]
Equivalently,
\[
  \frac{(1-(5/9)^h)^2}
       {(1-(5/8)^h)(1-(8/9)^h)}
  \le \frac{128}{27},
\]
with equality at \(h=1\).  This last inequality is immediate from finite
geometric sums.  If \(\eta=5/9\), \(b=5/8\), and \(c=8/9\), so that
\(\eta=bc\),
then
\[
  \frac{(1-\eta^h)^2}{(1-b^h)(1-c^h)}
  =
  \frac{(1-\eta)^2}{(1-b)(1-c)}
  \frac{\left(\sum_{i=0}^{h-1}b^ic^i\right)^2}
       {\left(\sum_{i=0}^{h-1}b^i\right)
        \left(\sum_{i=0}^{h-1}c^i\right)}.
\]
Cauchy's inequality gives the last fraction at most \(1\), since
\[
  \left(\sum_i b^ic^i\right)^2
  \le
  \left(\sum_i b^{2i}\right)\left(\sum_i c^{2i}\right)
  \le
  \left(\sum_i b^i\right)\left(\sum_i c^i\right).
\]

The remaining estimates are elementary.  The case \(F_0\) versus \(F_b\)
reduces to monotonicity of
\[
  L_b=A(A-2)\alpha^b-2(A-1)\beta^b-A^2+4A-2,
\]
because \(F_b(-1/(A-4))=-L_b/(A-4)^2\).  Here
\[
  L_{b+1}-L_b
  =
  \frac{3A(A-2)\alpha^b-8(A-1)\beta^b}{5}>0
\]
for \(b\le l-1\), using \(A=A_l\ge2^{l+1}\) and \(l\ge2\).  For
\(1\le a<b\), the inequality \(4(q-1)/(q-p)\le16\) gives
\(I_{a,h}>0\) from \(X\ge A_l(8/5)>16\).  The scalar bound gives
\(J_{a,h}\ge0\), because
\[
  \frac{X^2}{Y}
  =
  \frac{A_l^2}{A_l-1}\left(\frac{64}{45}\right)^a
  \ge
  \frac{64A_l}{45}
  \ge
  \frac{32}{3}\left(\frac98\right)^{h-1}
\]
for \(h\le l-a\).  This proves the full \(d=4\) actual internal-orbit
interlacing lemma.

The next degree has the same shape.  For \(d=5\), the actual orbit is still
quadratic:
\[
  F_s(z)=1+\left(A_l\left(\frac53\right)^s-5\right)z+
  \left(5-3A_l\left(\frac53\right)^s+B_l2^s\right)z^2,
\]
where
\[
  A_l=1+\left(\frac85\right)^l+\left(\frac{12}{5}\right)^l
      +2\left(\frac{16}{5}\right)^l
\]
and
\[
  B_l=\left(\frac85\right)^l+\left(\frac{12}{5}\right)^l
      +2\left(\frac{27}{10}\right)^l
      +2\left(\frac{16}{5}\right)^l
      +4\left(\frac{18}{5}\right)^l .
\]
The same exact quadratic-pencil test passes for all \(0\le a<b\le l\) and
\(2\le l\le12\).  In fact, the same elementary estimates prove this
quadratic case for all \(l\ge2\).  Put
\[
  X=A_l\left(\frac53\right)^a,\qquad
  Y=B_l2^a,\qquad
  p=\left(\frac53\right)^h,\qquad
  q=2^h,
  \qquad h=b-a.
\]
Then
\[
  F_a=1+(X-5)z+(5-3X+Y)z^2
\]
and \(F_b\) is obtained by replacing \(X,Y\) by \(Xp,Yq\).  The actual
coordinates satisfy two simple bounds:
\[
  \frac{B_l}{A_l}\ge3,\qquad
  \frac{A_l^2}{B_l}\ge\frac{15}{4}\left(\frac65\right)^l .
\]
For the first, write \(r=(8/5)^l\), \(s=(12/5)^l\),
\(u=(27/10)^l\), \(t=(16/5)^l\), and \(v=(18/5)^l\).  Then
\[
  B_l-3A_l
  =-3-2r-2s+2u-4t+4v>0
\]
for \(l\ge2\): the positive terms \(2u-2s\) and
\[
  4(v-t)
  \ge \frac{17}{16}t
\]
leave at least \((17/16)t-2r-3>0\), an increasing expression after
\(l=2\).  For the second bound, the case \(l=2\) is direct.  For \(l\ge3\),
use \(A_l\ge2(16/5)^l\) and \(B_l\le10(18/5)^l\), giving
\[
  \frac{A_l^2}{B_l}
  \ge
  \frac25\left(\frac{128}{45}\right)^l
  \ge
  \frac{15}{4}\left(\frac65\right)^l.
\]

Now consider the nonnegative pencil \(F_a+\lambda F_b\).  Its discriminant,
as a polynomial in \(\lambda\), has coefficients
\[
\begin{aligned}
  &X^2p^2+2Xp-4Yq+5,\\
  &2\bigl(X^2p+Xp+X-2Yq-2Y+5\bigr),\\
  &X^2+2X-4Y+5.
\end{aligned}
\]
All three are positive.  Indeed, if \(\tau=Y/X\), then
\[
  \frac{X}{\tau}
  =
  \frac{X^2}{Y}
  =
  \frac{A_l^2}{B_l}\left(\frac{25}{18}\right)^a
  \ge
  \frac{15}{4}\left(\frac65\right)^h,
\]
since \(h\le l-a\).  This dominates both \(4\) and
\(2(q+1)/p\).  The discriminant of this quadratic in \(\lambda\) is
negative once
\[
  \frac{X^2}{Y}
  >
  \frac{(q-1)^2}{(q-p)(p-1)}.
\]
The scalar ratio is bounded by the same geometric-sum argument as above:
\[
  \frac{(q-1)^2}{(q-p)(p-1)}
  =
  \left(\frac65\right)^h
  \frac{(1-2^{-h})^2}
       {(1-(5/6)^h)(1-(3/5)^h)}
  \le
  \frac{15}{4}\left(\frac65\right)^h.
\]
Thus every nonnegative pencil is real-rooted.  Finally, the coefficient-ratio
orientation is the desired one: the linear coefficient ratio is \(>1\), and
the top coefficient ratio is larger because
\[
  (5-3Xp+Yq)(X-5)-(5-3X+Y)(Xp-5)>0.
\]
The last inequality follows from
\[
  X(q-p)>5(q-1),
\]
using \((q-1)/(q-p)\le3\) and \(X>15\).  This proves the \(d=5\) actual
internal-orbit interlacing lemma.  The first genuinely new local model is
therefore the cubic case.

For \(d=6\), write
\[
  F_s(z)=1+\left(A_l\left(\frac{12}{7}\right)^s-6\right)z
  +\left(9-4A_l\left(\frac{12}{7}\right)^s
          +B_l\left(\frac{15}{7}\right)^s\right)z^2
\]
\[
  \qquad
  +\left(-2+2A_l\left(\frac{12}{7}\right)^s
          -2B_l\left(\frac{15}{7}\right)^s
          +C_l\left(\frac{16}{7}\right)^s\right)z^3 .
\]
Here
\[
  A_l=1+\left(\frac53\right)^l+\left(\frac83\right)^l
      +4^l+2\left(\frac{16}{3}\right)^l,
\]
\[
\begin{aligned}
  B_l={}&\left(\frac53\right)^l+\left(\frac83\right)^l
      +\left(\frac{16}{5}\right)^l+4^l
      +\left(\frac{24}{5}\right)^l
      +2\left(\frac{16}{3}\right)^l  \\
      &+2\left(\frac{27}{5}\right)^l
      +2\left(\frac{32}{5}\right)^l
      +4\left(\frac{36}{5}\right)^l,
\end{aligned}
\]
and
\[
  C_l=2\left(
      \left(\frac{16}{5}\right)^l
      +\left(\frac{24}{5}\right)^l
      +2\left(\frac{27}{5}\right)^l
      +2\left(\frac{32}{5}\right)^l
      +4\left(\frac{36}{5}\right)^l\right).
\]
Equivalently, the three coordinates satisfy the degree-drop relation
\[
  C_l=2(B_l-A_l+1).
\]
Thus \(F_0\) is quadratic, while \(F_s\) is cubic for \(s>0\).
The focused probe verifies the following exact certificate for
\(2\le l\le10\): every coefficient of the quartic discriminant of
\(F_a+\lambda F_b\) is positive, and the coefficient ratios of \(F_b/F_a\)
are weakly increasing.  Since \(\lambda\ge0\), coefficientwise positivity of
the quartic discriminant gives real-rootedness of every pencil; the ratio
condition gives the orientation.  Thus the first cubic proof target is now
specific: prove these five mixed-discriminant coefficient inequalities and
the coefficient-ratio inequalities from actual-coordinate bounds on
\((A_l,B_l,C_l)\).

The coefficient-ratio part has a useful partial reduction.  Put
\[
  X=A_l\left(\frac{12}{7}\right)^a,\quad
  Y=B_l\left(\frac{15}{7}\right)^a,\quad
  Z=C_l\left(\frac{16}{7}\right)^a,
\]
and
\[
  p=\left(\frac{12}{7}\right)^h,\quad
  q=\left(\frac{15}{7}\right)^h,\quad
  r=\left(\frac{16}{7}\right)^h .
\]
Then the first nontrivial ratio inequality is
\[
  (9-4Xp+Yq)(X-6)-(9-4X+Y)(Xp-6)\ge0,
\]
or
\[
  Y\bigl(X(q-p)-6(q-1)\bigr)+15X(p-1)\ge0.
\]
This follows immediately from \(X>16\) and
\((q-1)/(q-p)\le8/3\).  The second ratio inequality becomes
\[
\begin{aligned}
  {}&-6XYp+6XYq+4XZp-4XZr+10Xp-10X\\
   &\qquad -YZq+YZr-16Yq+16Y+9Zr-9Z\ge0.
\end{aligned}
\]
This is the orientation inequality that belongs with the five quartic
mixed-discriminant coefficient inequalities in the \(d=6\) proof target.

There is a useful region lemma for the discriminant part.  For a normalized
convex pencil, write
\[
  1+(x-6)z+(9-4x+y)z^2+(-2+2x-2y+\zeta)z^3
\]
and put
\[
  T=\frac yx,\qquad R=\frac{x^2}{y},\qquad
  K=\frac{y^2}{x\zeta}.
\]
The cubic discriminant equals
\[
\begin{aligned}
  \Delta={}&x^4\left(T^2-\frac{4T^2}{K}+8\right)
  +x^3\left(\frac{18T^3}{K}-4T^3-42T\right)\\
  &+x^2\left(-\frac{27T^4}{K^2}+\frac{54T^2}{K}+36T^2+9\right)
  -108xT+108 .
\end{aligned}
\]
Hence, if
\[
  T\ge15,\qquad R=\frac{x}{T}\ge2000,\qquad K\ge8,
\]
then
\[
  \Delta
  \ge
  R^2T^2\left(
    T^4\left(\frac{R^2}{2}-4R-\frac{27}{64}\right)
    -42RT^2-\frac{108}{R}
  \right)>0 .
\]
Thus the discriminant part of the \(d=6\) proof would follow from the three
region bounds \(T\ge15\), \(R\ge2000\), and \(K\ge8\) for all normalized
convex pencils.

These bounds have explicit one-variable reductions.  For the pencil between
the \(a\)-th and \(b\)-th iterates, put \(h=b-a\) and
\[
  p=\left(\frac{12}{7}\right)^h,\quad
  q=\left(\frac{15}{7}\right)^h,\quad
  r=\left(\frac{16}{7}\right)^h .
\]
With \(0\le\tau\le1\), the normalized pencil has
\[
  x=X(1+\tau(p-1)),\quad
  y=Y(1+\tau(q-1)),\quad
  \zeta=Z(1+\tau(r-1)).
\]
Therefore
\[
  T\ge \frac{B_l}{A_l}\left(\frac54\right)^a,
\]
\[
  R=
  \frac{A_l^2}{B_l}\left(\frac{48}{35}\right)^a
  \frac{(1+\tau(p-1))^2}{1+\tau(q-1)},
\]
and
\[
  K=
  \frac{B_l^2}{A_lC_l}\left(\frac{75}{64}\right)^a
  \frac{(1+\tau(q-1))^2}
       {(1+\tau(p-1))(1+\tau(r-1))}.
\]
The minimum of the \(R\)-factor is explicit:
\[
  \min_{0\le\tau\le1}
  \frac{(1+\tau(p-1))^2}{1+\tau(q-1)}
  =
  \min\left\{1,\frac{p^2}{q},
  \frac{4(p-1)(q-p)}{(q-1)^2}\right\},
\]
where the last term is included only when the critical point lies in
\([0,1]\).  The logarithmic derivative of the \(K\)-factor is linear in
\(\tau\), so its minimum is obtained at an endpoint or at one rational
critical point.  Exact minimization with these formulas up to \(l=30\) puts
the worst cases at \(l=6\), with \(T>15\), \(R>2000\), and \(K>8\).  The
remaining proof task is to turn this finite-looking minimization into clean
inequalities in \(l,a,h\).

Two of the three region bounds are now elementary.  First,
\[
  B_l-15A_l\ge0\qquad(l\ge6).
\]
Indeed, write this difference as
\[
\begin{aligned}
  B_l-15A_l={}&
  \left(4\left(\frac{36}{5}\right)^l
        +2\left(\frac{32}{5}\right)^l
        -28\left(\frac{16}{3}\right)^l\right)\\
  &+\left(2\left(\frac{27}{5}\right)^l
        +\left(\frac{24}{5}\right)^l
        -14\cdot4^l\right)\\
  &+\left(\frac{16}{5}\right)^l
        -14\left(\frac83\right)^l
        -14\left(\frac53\right)^l-15 .
\end{aligned}
\]
The second parenthesis is positive for \(l\ge6\).  The first parenthesis is at
least \(2(16/3)^l\), again by checking \(l=6\) and observing that the relevant
bases are \(>1\).  Thus the first and third lines together are at least
\[
  2\left(\frac{16}{3}\right)^l
  -14\left(\frac83\right)^l
  -14\left(\frac53\right)^l-15>0
\]
for \(l\ge6\), since after division by \((8/3)^l\) this is implied by
\[
  2\cdot2^l>14+14\left(\frac58\right)^l
       +15\left(\frac38\right)^l .
\]
Consequently \(T\ge B_l/A_l\ge15\).

For \(R\), use the rough actual-coordinate bounds
\[
  A_l\ge2\left(\frac{16}{3}\right)^l,\qquad
  B_l\le15\left(\frac{36}{5}\right)^l .
\]
The one-variable factor satisfies
\[
  \min_{0\le\tau\le1}
  \frac{(1+\tau(p-1))^2}{1+\tau(q-1)}
  \ge
  \frac{75}{64}\left(\frac45\right)^h .
\]
For the critical value this is the finite-geometric-sum inequality
\[
  \frac{4(p-1)(q-p)}{(q-1)^2}
  \ge
  \frac{75}{64}\left(\frac45\right)^h;
\]
after writing
\[
  p=\left(\frac{12}{7}\right)^h,\qquad
  q=\left(\frac{15}{7}\right)^h,
\]
it becomes
\[
  \frac{(1-(7/12)^h)(1-(4/5)^h)}
       {(1-(7/15)^h)^2}
  \ge
  \frac{75}{256}.
\]
This follows because \(7/15=(7/12)(4/5)\) and
\[
  \left(\sum_i (7/12)^i\right)
  \left(\sum_i (4/5)^i\right)
  \ge
  \left(\sum_i (7/15)^i\right)^2 .
\]
Therefore, since \(h\le l-a\),
\[
\begin{aligned}
  R&\ge
  \frac{4}{15}\left(\frac{640}{81}\right)^l
  \left(\frac{48}{35}\right)^a
  \frac{75}{64}\left(\frac45\right)^h\\
  &\ge
  \frac{5}{16}\left(\frac{512}{81}\right)^l
  \left(\frac{12}{7}\right)^a
  \ge
  \frac{5}{16}\left(\frac{512}{81}\right)^6>2000 .
\end{aligned}
\]
Thus \(R\ge2000\) for all \(l\ge6\).

It remains to prove \(K\ge8\).  We first record two coordinate consequences.
Put \(u=B_l/A_l\).  Since
\[
  C_l=2(B_l-A_l+1)=2A_l\left(u-1+\frac1{A_l}\right),
\]
we have
\[
  \frac{B_l^2}{A_lC_l}
  =
  \frac{u^2}{2(u-1+1/A_l)}.
\]
The already proved inequality \(u\ge15\), together with \(A_l>16\), gives
\[
  \frac{B_l^2}{A_lC_l}\ge8.
\]
Indeed this is equivalent to
\[
  u^2-16u+16-\frac{16}{A_l}\ge0,
\]
and the left hand side is at least \(1-16/A_l>0\).

We also need the exponential lower bound
\[
  \frac{B_l^2}{A_lC_l}\ge\left(\frac{27}{20}\right)^l .
\]
It is enough to show
\[
  B_l\ge 2\left(\frac{27}{20}\right)^l A_l,
\]
because then \(C_l<2B_l\) and hence
\[
  \frac{B_l^2}{A_lC_l}>\frac{B_l}{2A_l}
  \ge \left(\frac{27}{20}\right)^l .
\]
After expanding and cancelling the two top terms, the desired inequality
follows from
\[
  \left(\frac53\right)^l\ge
  2\left(\frac{27}{20}\right)^l,\qquad
  \left(\frac83\right)^l\ge
  2\left(\frac94\right)^l,
\]
and
\[
  \left(\frac{16}{5}\right)^l+4^l
  \ge2\left(\frac{18}{5}\right)^l .
\]
The first two inequalities hold for \(l\ge6\).  The third is
\[
  \left(\frac89\right)^l+\left(\frac{10}{9}\right)^l\ge2,
\]
after division by \((18/5)^l\), and follows by expanding
\((1-1/9)^l+(1+1/9)^l\).

We now split according to the gap \(h\).  The one-variable \(K\)-factor has
endpoint values \(1\) and \(q^2/(pr)>1\), and its possible interior critical
value is
\[
  \frac{4(q-p)(r-q)}{(r-p)^2}.
\]
Consequently it is always at least the minimum of \(1\) and this critical
value.  Moreover,
\[
  \frac{4(q-p)(r-q)}{(r-p)^2}
  \ge
  \frac45\left(\frac{15}{16}\right)^h,
\]
with equality at \(h=1\).  To see this, divide by \(r\) and put
\[
  \alpha=\left(\frac45\right)^h,\qquad
  \beta=\left(\frac{15}{16}\right)^h .
\]
The inequality becomes
\[
  5(1-\alpha)(1-\beta)\ge(1-\alpha\beta)^2 .
\]
Since \(\alpha\beta=(3/4)^h\), this follows after writing each difference as
a finite geometric sum.

For \(1\le h\le9\), the \(K\)-factor is in fact at least \(1\) on
\([0,1]\).  Indeed,
\[
\begin{aligned}
  &(1+\tau(q-1))^2
  -(1+\tau(p-1))(1+\tau(r-1))\\
  &\qquad =
  \tau\left(
    2q-p-r+
    \bigl((q-1)^2-(p-1)(r-1)\bigr)\tau
  \right),
\end{aligned}
\]
and the two coefficients in parentheses are nonnegative for
\(1\le h\le9\), by direct exact checking of these nine integer inequalities.
Therefore in this range
\[
  K\ge \frac{B_l^2}{A_lC_l}\ge8.
\]

For \(h\ge10\), we use the exponential lower bound.  Since \(h\le l-a\),
\[
\begin{aligned}
  K
  &\ge
  \left(\frac{27}{20}\right)^l
  \left(\frac{75}{64}\right)^a
  \frac45\left(\frac{15}{16}\right)^h\\
  &\ge
  \frac45
  \left(\frac{81}{64}\right)^l
  \left(\frac54\right)^a
  \ge
  \frac45\left(\frac{81}{64}\right)^{10}>8.
\end{aligned}
\]
This proves \(K\ge8\) for all \(l\ge6\), completing the large-region
discriminant proof for the \(d=6\) normalized pencils.

The same region bounds also prove the remaining coefficient-ratio orientation
inequality for \(l\ge6\).  Recall that this inequality is
\[
\begin{aligned}
  {}&-6XYp+6XYq+4XZp-4XZr+10Xp-10X\\
   &\qquad -YZq+YZr-16Yq+16Y+9Zr-9Z\ge0.
\end{aligned}
\]
Write
\[
  Y=TX,\qquad X=RT,\qquad Z=\frac{T^2X}{K}.
\]
After multiplying by the positive factor \(K/(RT)\), the left hand side
becomes
\[
\begin{aligned}
  S={}&RT^2\left(6K(q-p)+T^2(r-q)-4T(r-p)\right)\\
  &+K\left(10(p-1)-16T(q-1)\right)+9T^2(r-1).
\end{aligned}
\]
We shall show \(S>0\) under the same hypotheses
\[
  T\ge15,\qquad R\ge2000,\qquad K\ge8.
\]
We use three elementary consequences of finite geometric sums:
\[
  q-1\le\frac83(q-p),\qquad
  q-p\le3(r-q),\qquad
  q-1\le8(r-q).
\]
For example,
\[
  q-p=\frac{15^h-12^h}{7^h}
  =\frac3{7^h}\sum_{i=0}^{h-1}15^{h-1-i}12^i
\]
and
\[
  r-q=\frac{16^h-15^h}{7^h}
  =\frac1{7^h}\sum_{i=0}^{h-1}16^{h-1-i}15^i,
\]
so \(q-p\le3(r-q)\) follows termwise; the other two are identical.

First, \(S\) is increasing in \(K\).  Indeed,
\[
  \frac{\partial S}{\partial K}
  =
  6RT^2(q-p)+10(p-1)-16T(q-1)>0,
\]
because \(RT\ge30000\) and \(q-1\le(8/3)(q-p)\).  Next, \(S\) is increasing
in \(R\).  It is enough to prove
\[
  6K(q-p)+T^2(r-q)-4T(r-p)>0.
\]
Since \(K\ge8\) and \(r-p=(r-q)+(q-p)\), the left hand side is at least
\[
  (T^2-4T)(r-q)+(48-4T)(q-p).
\]
For \(T\ge15\), the coefficient \(48-4T\) is nonpositive, so
\[
\begin{aligned}
  (T^2-4T)(r-q)+(48-4T)(q-p)
  &\ge (T^2-16T+144)(r-q)>0,
\end{aligned}
\]
using \(q-p\le3(r-q)\).

Thus \(S\) is minimized, in this region, at \(R=2000\) and \(K=8\).  At these
values,
\[
\begin{aligned}
  S
  &\ge
  2000T^2(T^2-16T+144)(r-q)-128T(q-1)\\
  &\ge
  \left(2000\cdot129\,T^2-1024T\right)(r-q)>0,
\end{aligned}
\]
where we used \(T\ge15\) and \(q-1\le8(r-q)\).  This proves the remaining
orientation inequality for \(l\ge6\).

The finite cases \(2\le l\le5\) are closed by exact rational arithmetic in
`working/super-recurrence-eulerian/spectral_internal_orbit_probe.py`.  For
each \(l\) and each \(0\le a<b\le l\), the script checks that all
coefficients of the quartic discriminant of \(F_a+\lambda F_b\) are positive
and that all adjacent coefficient-ratio minors are nonnegative.  A compact
sanity run gives the smallest discriminant coefficient
\[
  \frac{1185077894674432}{11390625}
\]
and the smallest orientation minor
\[
  \frac{3770}{63},
\]
both at \(l=2\) and \((a,b)=(0,1)\).  Together with the large-region proof
above, this proves the \(d=6\) actual internal-orbit certificate.

The next cubic slice is \(d=7\).  Here
\[
  F_s(z)=1+\left(A_l\left(\frac74\right)^s-7\right)z
  +\left(14-5A_l\left(\frac74\right)^s
          +B_l\left(\frac94\right)^s\right)z^2
\]
\[
  \qquad
  +\left(-7+5A_l\left(\frac74\right)^s
          -3B_l\left(\frac94\right)^s
          +C_l\left(\frac52\right)^s\right)z^3 .
\]
The actual coordinates are
\[
  A_l=1+\left(\frac{12}{7}\right)^l+\left(\frac{20}{7}\right)^l
      +\left(\frac{32}{7}\right)^l+\left(\frac{48}{7}\right)^l
      +2\left(\frac{64}{7}\right)^l,
\]
\[
\begin{aligned}
  B_l={}&\left(\frac{12}{7}\right)^l+\left(\frac{20}{7}\right)^l
      +\left(\frac{25}{7}\right)^l+\left(\frac{32}{7}\right)^l
      +\left(\frac{40}{7}\right)^l
      +2\left(\frac{48}{7}\right)^l
      +2\left(\frac{64}{7}\right)^l\\
      &+\left(\frac{60}{7}\right)^l+\left(\frac{72}{7}\right)^l
      +2\left(\frac{80}{7}\right)^l+2\left(\frac{81}{7}\right)^l
      +2\left(\frac{96}{7}\right)^l+4\left(\frac{108}{7}\right)^l,
\end{aligned}
\]
and
\[
\begin{aligned}
  C_l={}&\left(\frac{25}{7}\right)^l+\left(\frac{40}{7}\right)^l
      +\left(\frac{48}{7}\right)^l
      +2\left(\frac{256}{35}\right)^l
      +\left(\frac{60}{7}\right)^l+\left(\frac{72}{7}\right)^l\\
      &+2\left(\frac{384}{35}\right)^l
      +2\left(\frac{80}{7}\right)^l+2\left(\frac{81}{7}\right)^l
      +4\left(\frac{432}{35}\right)^l
      +2\left(\frac{96}{7}\right)^l\\
      &+4\left(\frac{512}{35}\right)^l
      +4\left(\frac{108}{7}\right)^l
      +8\left(\frac{576}{35}\right)^l .
\end{aligned}
\]
The updated probe verifies the same cubic certificate for \(2\le l\le8\):
the quartic discriminant of \(F_a+\lambda F_b\) has positive coefficients,
and the coefficient-ratio orientation is correct for every
\(0\le a<b\le l\).  A first region scan suggests a clean split at
\(l\ge5\).  In the normalized pencil
\[
  1+(x-7)z+(14-5x+y)z^2+(-7+5x-3y+\zeta)z^3,
\]
with \(T=y/x\), \(R=x^2/y\), and \(K=y^2/(x\zeta)\), the exact minima over
\(5\le l\le30\) are already beyond
\[
  T>38,\qquad R>2900,\qquad K>11.
\]
These thresholds are enough for a large-region lemma.  For the discriminant,
one computes
\[
  K^2\Delta=K^2C_2+KC_1-27R^2T^6,
\]
where
\[
\begin{aligned}
  C_2={}&R^4T^4(T^2+2T+5)
  +R^3(-4T^6-8T^5-24T^4+8T^3)\\
  &+R^2(16T^4-30T^3+18T^2)+R(-56T^2+28T)+49
\end{aligned}
\]
and
\[
  C_1=-4R^4T^6+R^3(18T^6-6T^5)
      +R^2(36T^5+24T^4)-14RT^3 .
\]
If \(T\ge38\) and \(R\ge2900\), then
\[
  C_2\ge\frac12R^4T^6,\qquad C_1\ge-5R^4T^6.
\]
Therefore, for \(K\ge11\),
\[
  K^2\Delta
  \ge
  \left(\frac{K^2}{2}-5K\right)R^4T^6-27R^2T^6>0.
\]

The orientation inequalities also follow in the same region.  The first
coefficient-ratio inequality reduces to
\[
  RT\left(RT^2(q-p)-7T(q-1)+21(p-1)\right)\ge0,
\]
which follows from
\[
  q-1\le\frac52(q-p).
\]
For the second ratio inequality, after substituting
\[
  Y=TX,\qquad X=RT,\qquad Z=\frac{T^2X}{K},
\]
and multiplying by \(K/(RT)\), the left hand side becomes
\[
\begin{aligned}
  S={}&R\left(10KT^2(q-p)+T^4(r-q)-5T^3(r-p)\right)\\
  &+K\left(35(p-1)-35T(q-1)\right)+14T^2(r-1).
\end{aligned}
\]
Here \(p=(7/4)^h\), \(q=(9/4)^h\), and \(r=(5/2)^h\).  The finite-geometric
sum bounds
\[
  q-1\le\frac52(q-p),\qquad q-p\le2(r-q),\qquad q-1\le5(r-q)
\]
are termwise.  They show first that \(S\) is increasing in \(K\), and then
that it is increasing in \(R\), since
\[
  10KT^2(q-p)+T^4(r-q)-5T^3(r-p)
  \ge T^2(T^2-15T+220)(r-q)>0.
\]
At \(K=11\) and \(R=2900\), the same bounds give
\[
  S\ge
  \left(2900T^2(T^2-15T+220)-1925T\right)(r-q)>0.
\]
Thus the \(d=7\) large-region discriminant and orientation proof is reduced
to the three actual-coordinate bounds \(T\ge38\), \(R\ge2900\), and
\(K\ge11\) for \(l\ge5\), plus exact finite handling of \(l=2,3,4\).

Two of these three actual-coordinate bounds are already elementary.  First,
\[
  B_l\ge38A_l\qquad(l\ge5).
\]
Indeed, \(B_l-38A_l\) has top block
\[
  4\left(\frac{108}{7}\right)^l
  +2\left(\frac{96}{7}\right)^l
  +2\left(\frac{81}{7}\right)^l
  -74\left(\frac{64}{7}\right)^l.
\]
For \(l\ge5\), this block is at least \(2(64/7)^l\), by checking
\(l=5\) after division by \((64/7)^l\).  The negative lower tail is bounded
above by
\[
  37\left(\frac{32}{7}\right)^l
  +37\left(\frac{20}{7}\right)^l
  +37\left(\frac{12}{7}\right)^l+38
  \le 2\left(\frac{64}{7}\right)^l,
\]
again by checking \(l=5\) after division by \((64/7)^l\).  The remaining
terms of \(B_l-38A_l\) are nonnegative.  Hence \(T\ge B_l/A_l\ge38\).

For the \(R\)-bound, the coordinate factor satisfies
\[
  \frac{A_l^2}{B_l}\ge
  \frac45\left(\frac{1024}{189}\right)^l
  \qquad(l\ge5).
\]
This is an exact exponential-dominance check: after expanding
\[
  A_l^2-\frac45\left(\frac{1024}{189}\right)^lB_l,
\]
each negative term is dominated from \(l=5\) onward by a positive term with a
larger base.  The one-variable \(R\)-factor satisfies
\[
  \min_{0\le\tau\le1}
  \frac{(1+\tau(p-1))^2}{1+\tau(q-1)}
  \ge\frac89
  \qquad(1\le h\le4),
\]
by direct exact checking, while for \(h\ge5\) its critical-value formula gives
\[
  \min_{0\le\tau\le1}
  \frac{(1+\tau(p-1))^2}{1+\tau(q-1)}
  \ge
  \frac{11}{4}\left(\frac79\right)^h.
\]
The latter follows from
\[
  16\left(1-\left(\frac47\right)^h\right)
    \left(1-\left(\frac79\right)^h\right)
  \ge
  11\left(1-\left(\frac49\right)^h\right)^2,
\]
which is weakest at \(h=5\).  Therefore, if \(h\le4\),
\[
  R\ge
  \frac45\left(\frac{1024}{189}\right)^l\frac89
  \ge
  \frac{32}{45}\left(\frac{1024}{189}\right)^5>2900,
\]
and if \(h\ge5\), then \(h\le l-a\) gives
\[
\begin{aligned}
  R&\ge
  \frac45\left(\frac{1024}{189}\right)^l
  \left(\frac{49}{36}\right)^a
  \frac{11}{4}\left(\frac79\right)^h\\
  &\ge
  \frac{11}{5}\left(\frac{7168}{1701}\right)^l
  \left(\frac74\right)^a
  \ge
  \frac{11}{5}\left(\frac{7168}{1701}\right)^5>2900.
\end{aligned}
\]
Thus \(R\ge2900\) for all \(l\ge5\).

It remains to prove \(K\ge11\).  We use a finite-tail dominance certificate
for the coordinate factor.  Exact rational arithmetic gives
\[
  B_l^2-11A_lC_l>0\qquad(5\le l\le39),
\]
with the smallest value at \(l=5\), namely
\[
  \frac{70059773340203267900686}{126105021875}.
\]
It also gives
\[
  B_l^2-\frac9{10}\left(\frac{405}{256}\right)^lA_lC_l>0
  \qquad(6\le l\le39),
\]
with the smallest value at \(l=6\), namely
\[
  \frac{5566960549300769166967656314873990575531}
       {5565679989352822818734080}.
\]
For the tail \(l\ge40\), the top-term bounds
\[
  A_l\le\frac{201}{100}\left(\frac{64}{7}\right)^l,\qquad
  C_l\le\frac{167}{20}\left(\frac{576}{35}\right)^l,\qquad
  B_l\ge4\left(\frac{108}{7}\right)^l
\]
give
\[
  \frac{B_l^2}{A_lC_l}
  \ge
  \frac{32000}{33567}\left(\frac{405}{256}\right)^l
  >
  \frac9{10}\left(\frac{405}{256}\right)^l .
\]
Thus \(B_l^2/(A_lC_l)\ge11\) for all \(l\ge5\), and the stronger
exponential lower bound holds for all \(l\ge6\).

Now write
\[
  K=
  \frac{B_l^2}{A_lC_l}
  \left(\frac{81}{70}\right)^a g_h(\tau),
\]
where
\[
  g_h(\tau)=
  \frac{(1+\tau(q-1))^2}
       {(1+\tau(p-1))(1+\tau(r-1))}.
\]
For \(1\le h\le5\), exact checking of the linear logarithmic derivative shows
that \(g_h(\tau)\ge1\) on \([0,1]\).  Hence \(K\ge11\) in this range.  For
\(h\ge6\), the critical value gives
\[
  g_h(\tau)\ge
  \frac{4(q-p)(r-q)}{(r-p)^2}
  =
  4\left(\frac9{10}\right)^h
  \frac{(1-(7/9)^h)(1-(9/10)^h)}
       {(1-(7/10)^h)^2}.
\]
The last fraction is at least \(3/8\): for \(h=6\) this is an exact rational
check, and for \(h\ge7\) it follows already from
\[
  \left(1-\left(\frac79\right)^h\right)
  \left(1-\left(\frac9{10}\right)^h\right)
  \ge\frac38 .
\]
Therefore \(g_h(\tau)\ge(3/2)(9/10)^h\) for \(h\ge6\).  Since \(h\le l-a\),
\[
\begin{aligned}
  K&\ge
  \frac9{10}\left(\frac{405}{256}\right)^l
  \left(\frac{81}{70}\right)^a
  \frac32\left(\frac9{10}\right)^h\\
  &\ge
  \frac{27}{20}
  \left(\frac{729}{512}\right)^l
  \left(\frac97\right)^a
  \ge
  \frac{27}{20}
  \left(\frac{729}{512}\right)^6>11 .
\end{aligned}
\]
This proves \(K\ge11\) for all \(l\ge5\).  Combining the \(T\), \(R\), and
\(K\) bounds with the large-region lemma proves the \(d=7\) internal-orbit
certificate for all \(l\ge5\).

The remaining finite cases \(l=2,3,4\) are covered by the exact rational
probe `working/super-recurrence-eulerian/spectral_internal_orbit_probe.py`.
For every \(0\le a<b\le l\), it checks positivity of all quartic
discriminant coefficients and all adjacent coefficient-ratio minors.  Thus
the \(d=7\) actual internal-orbit certificate is proved for all \(l\ge2\).

The next slice is \(d=8\).  It is the first genuine quartic slice.  With
\[
\begin{aligned}
  P_0&=1-8z+20z^2-16z^3+2z^4,\\
  P_1&=z-6z^2+9z^3-2z^4,\\
  P_2&=z^2-4z^3+2z^4,\qquad
  P_3=z^3-2z^4,\qquad P_4=z^4,
\end{aligned}
\]
the actual orbit has the form
\[
  F_s=P_0+A_l\left(\frac{16}{9}\right)^sP_1
      +B_l\left(\frac73\right)^sP_2
      +C_l\left(\frac83\right)^sP_3
      +D_l\left(\frac{25}{9}\right)^sP_4 .
\]
Equivalently,
\[
\begin{aligned}
  F_s={}&1+\left(A_l\left(\frac{16}{9}\right)^s-8\right)z\\
  &+\left(20-6A_l\left(\frac{16}{9}\right)^s
          +B_l\left(\frac73\right)^s\right)z^2\\
  &+\left(-16+9A_l\left(\frac{16}{9}\right)^s
          -4B_l\left(\frac73\right)^s
          +C_l\left(\frac83\right)^s\right)z^3\\
  &+\left(2-2A_l\left(\frac{16}{9}\right)^s
          +2B_l\left(\frac73\right)^s
          -2C_l\left(\frac83\right)^s
          +D_l\left(\frac{25}{9}\right)^s\right)z^4 .
\end{aligned}
\]
The coefficients \(A_l,B_l,C_l,D_l\) are positive exponential sums obtained
by the same exact spectral-coordinate extraction used above; the script keeps
them generated rather than writing the long sums into the note.  The current
probe checks, by exact isolating intervals and coefficient-ratio minors, that
\[
  F_a\ll F_b\qquad(0\le a<b\le l)
\]
for \(2\le l\le12\).  This is evidence only, but it gives a clean next
target.  The coordinate identity
\[
  D_l=2A_l-2B_l+2C_l-2
\]
is equivalent to the vanishing of the \(z^4\)-coefficient in \(F_0\), and is
the first coupling relation that should be used in the proof.

The natural normalized quartic parameters are
\[
  T=\frac yx,\qquad R=\frac{x^2}{y},\qquad
  K=\frac{y^2}{x\zeta},\qquad
  L=\frac{\zeta^2}{y\omega},
\]
where \(x,y,\zeta,\omega\) denote the four nonconstant spectral-coordinate
contributions after fixing the left endpoint \(a\).  Over the checked range
\(2\le l\le12\), the minima occur at small \(l\):
\[
  T>16,\qquad R>44,\qquad K>4,\qquad L>2 .
\]
For a theorem-ready large-region split, it is better to treat
\(l=2,3,4\) finitely.  Starting at \(l=5\), the same scan gives the much
cleaner bounds
\[
  T>136,\qquad R>12935,\qquad K>19,\qquad L>3.97 .
\]
Thus the next concrete proof task is a quartic Hermite--Obreschkoff region
lemma: prove that sufficiently large \(T,R,K,L\) force the Hermite minors of
every pencil \(F_a+\lambda F_b\) to have the required signs for
\(\lambda\ge0\), and then prove the actual \(d=8\) coordinates enter that
region for \(l\ge5\).

There is a sharper reduction that should be used before attacking the full
quartic region.  Since \(M_8\) preserves proper position on gamma-PF pairs, it
is enough to prove
\[
  F_0\ll F_h\qquad(1\le h\le l).
\]
Indeed, applying \(M_8^a\) to this relation gives \(F_a\ll F_{a+h}\).
For these base pairs put
\[
  p=\left(\frac{16}{9}\right)^h,\quad
  q=\left(\frac73\right)^h,\quad
  r=\left(\frac83\right)^h,\quad
  u=\left(\frac{25}{9}\right)^h,
\]
and use
\[
  T=\frac{B_l}{A_l},\qquad H=\frac{C_l}{B_l},\qquad R=\frac{A_l}{T}.
\]
Then \(A_l=RT\), \(B_l=RT^2\), \(C_l=RT^2H\), and the coupling relation gives
the top coefficient of \(F_h\) as
\[
  2RT\bigl((u-p)+T(q-u)+TH(u-r)\bigr)+2(1-u).
\]
The coefficient-ratio orientation minors begin with
\[
  RT(p-1),
\]
and the other two have dominant positive terms involving \(q-p\) and
\((r-q,\,u-r)\).  Thus the orientation side is now a concrete
finite-geometric inequality problem.

The same variables isolate the large-\(R\) tail.  The nonzero limiting roots
of \(F_0\) are governed by
\[
  Q_0=1+(T-6)z+\bigl(T(H-4)+9\bigr)z^2,
\]
while those of \(F_h\) are governed by
\[
  Q_h=1+\left(\frac{Tq}{p}-6\right)z
      +\left(\frac{T(Hr-4q)}{p}+9\right)z^2
      +\frac{2\bigl((u-p)+T(q-u+H(u-r))\bigr)}{p}z^3 .
\]
For actual coordinates, an exact rational scan through \(l\le80\) shows that
every coefficient of the cubic discriminant of \(Q_0+\lambda Q_h\) is positive
and that the coefficient-ratio orientation is correct for every \(1\le h\le l\).
Writing \(K=T/H=B_l^2/(A_lC_l)\), a more precise stress test suggests the
following gap-dependent sufficient conditions:
\[
  H\ge 2\left(\frac{32}{27}\right)^{\max(h,5)},
  \qquad
  K\ge \frac12\left(\frac{59049}{32256}\right)^{\max(h,5)}.
\]
On this lower curve, exact rational evaluation of the cubic-discriminant
coefficients and orientation terms is positive through \(h\le300\); independent
upward scalings of \(H\) and \(K\) also pass through \(h\le150\).  The actual
coordinates satisfy stronger versions of these lower bounds for \(l\ge5\).
Indeed, the \(H\)-bound is
\[
  \frac{C_l}{B_l}\ge 2\left(\frac{32}{27}\right)^l .
\]
After expanding \(C_l-2(32/27)^lB_l\), the leading terms cancel and the
largest remaining term is \(4(270/7)^l\).  This single positive term dominates
the entire negative tail from \(l=5\) onward; it is enough to check \(l=5\),
because all negative bases are smaller.  Similarly,
\[
  \frac{B_l^2}{A_lC_l}\ge
  \frac12\left(\frac{59049}{32256}\right)^l .
\]
Equivalently,
\[
  2B_l^2-\left(\frac{59049}{32256}\right)^lA_lC_l\ge0.
\]
The leading positive term in this difference is
\[
  16\left(\frac{59049}{49}\right)^l,
\]
and it dominates the full negative tail from \(l=5\) onward, again by checking
the endpoint \(l=5\).
Even better, after substituting
\[
  H=2\left(\frac{32}{27}\right)^{\max(h,5)}(1+x),
  \qquad
  K=\frac12\left(\frac{59049}{32256}\right)^{\max(h,5)}(1+y),
\]
the numerators of all five cubic-discriminant coefficients and the three tail
orientation terms expand with nonnegative coefficients in \(x,y\) for every
checked \(1\le h\le15\).  The intended proof is to identify and prove this
geometric coefficient pattern uniformly in \(h\).
This has a compact exact certificate.  For \(h\ge5\), each coefficient of
the shifted \(x,y\)-expansion is a finite exponential sum in \(h\).  There
are \(197\) such coefficients across the five discriminant coefficients and
three orientation terms.  For each negative exponential base \(\rho\), the
sum of positive terms with base at least \(\rho\) dominates the sum of
negative terms with base at least \(\rho\) at a finite cutoff; the domination
then persists for all larger \(h\).  The largest cutoff is \(h=9\), with
cutoff distribution
\[
  (5:138),\quad (6:34),\quad (7:10),\quad (8:10),\quad (9:5).
\]
The cases \(1\le h\le4\) are direct shifted coefficient-positivity checks
using the same \(\max(h,5)\) lower curve.
Hence the tail pair \(Q_0,Q_h\) is directed compatible under the displayed
lower bounds on \(H\) and \(K\).  The remaining step is the large-\(R\)
perturbation which restores the small roots of \(F_0\) and \(F_h\) and lifts
the tail interlacing to the full base pair.

A clean perturbation statement is now visible.  Write
\[
  F_0=RTzQ_0+c_0,\qquad F_h=RTp\,zQ_h+c_h,
\]
where
\[
  c_0=1-8z+20z^2-16z^3,\qquad
  c_h=c_0+2(1-u)z^4 .
\]
It should be enough to prove the following shifted Hermite certificate.  Put
\[
  R=\left(\frac32\right)^h(1+w),\quad
  H=2\left(\frac{32}{27}\right)^{\max(h,5)}(1+x),\quad
  K=\frac12\left(\frac{59049}{32256}\right)^{\max(h,5)}(1+y).
\]
For \(P_\lambda=F_0+\lambda F_h\), let \(\Delta_2,\Delta_3,\Delta_4\)
be the nontrivial leading principal Hermite minors of the quartic
\(P_\lambda\).  The top coefficient of \(F_h\), the three coefficient-ratio
orientation minors, \(\Delta_2\), \(\Delta_3\), and \(\Delta_4\) have exact
shifted finite-tail certificates for \(h\ge5\).
Using the corrected full bases
\[
\begin{gathered}
  A:\frac{729}{224},\quad B:\frac{177147}{25088},\quad
  C:\frac{6561}{784},\quad Ap:\frac{81}{14},\\
  Bq:\frac{59049}{3584},\quad Cr:\frac{2187}{98},\quad
  U:\frac{25}{9},\quad Au:\frac{2025}{224},\\
  Bu:\frac{492075}{25088},\quad Cu:\frac{18225}{784},
\end{gathered}
\]
the matched positive-base dominance certificate gives positivity for all
shifted coefficients.  The counts and largest cutoffs are:
\[
  \text{top}:24,\ h\le6;\qquad
  O_0:8,\ h=5;\qquad O_1:48,\ h=5;\qquad O_2:90,\ h=5;
\]
\[
  \Delta_2:315,\ h\le9;\qquad
  \Delta_3:2475,\ h\le9;\qquad
  \Delta_4:7007,\ h\le9 .
\]
For \(\Delta_4\), the exact script
`working/super-recurrence-eulerian/d8_delta4_certificate.py` expands the
quartic discriminant into \(2689\) unshifted exponential monomials and then
checks \(7007\) shifted coefficient slots.  The cutoff distribution is
\[
  (5:3900),\quad (6:1397),\quad (7:1056),\quad (8:500),\quad (9:154).
\]
This proves the full perturbation certificate for every gap \(h\ge5\).

The small gaps \(h=1,2,3,4\) require the actual coordinate sums rather than
the coarse rectangular lower region.  Using
\[
\begin{aligned}
 A_l={}&1+\left(\frac74\right)^l+3^l+5^l+8^l+12^l+2\cdot16^l,\\
 B_l={}&\left(\frac74\right)^l+3^l+\left(\frac{27}{7}\right)^l+5^l
        +\left(\frac{45}{7}\right)^l+8^l+\cdots
        +4\left(\frac{243}{7}\right)^l,\\
 C_l={}&\left(\frac{27}{7}\right)^l+\left(\frac{45}{7}\right)^l
        +\left(\frac{225}{28}\right)^l+\cdots
        +8\left(\frac{288}{7}\right)^l,
\end{aligned}
\]
and \(D_l=2A_l-2B_l+2C_l-2\), the companion script
`working/super-recurrence-eulerian/d8_small_gap_certificate.py` expands the
top coefficient, the three orientation minors, and
\(\Delta_2,\Delta_3,\Delta_4\) as exact exponential sums in \(l\).  For each
fixed \(1\le h\le4\), every coefficient is certified already at cutoff
\(l=5\); the seven \(\lambda\)-coefficients of \(\Delta_4\) have at most
\(11264\) exponential bases after collection.  This proves the base-pair
relations \(F_0\ll F_h\) for all \(l\ge5\) and \(1\le h\le4\).

Together with the exact finite check for \(l=2,3,4\), this completes the
\(d=8\) actual internal-orbit proof.  Since \(M_8\) preserves proper position
on gamma-PF pairs, applying \(M_8^a\) to the base-pair relation
\(F_0\ll F_h\) gives \(F_a\ll F_{a+h}\).  Thus
\[
  F_a\ll F_b\qquad(0\le a<b\le l)
\]
for every \(l\ge2\) in the \(d=8\) slice.

The next slice \(d=9\) is again quartic, but it no longer has the special
\(d=8\) endpoint degree drop.  The spectral basis is
\[
\begin{aligned}
  P_0&=1-9z+27z^2-30z^3+9z^4,\\
  P_1&=z-7z^2+14z^3-7z^4,\qquad
  P_2=z^2-5z^3+5z^4,\\
  P_3&=z^3-3z^4,\qquad P_4=z^4.
\end{aligned}
\]
Thus
\[
  F_s=P_0+A_l\left(\frac95\right)^sP_1
      +B_l\left(\frac{12}{5}\right)^sP_2
      +C_l\left(\frac{14}{5}\right)^sP_3
      +D_l3^sP_4 .
\]
Equivalently,
\[
\begin{aligned}
F_s={}&1+\left(A_l\left(\frac95\right)^s-9\right)z\\
&+\left(27-7A_l\left(\frac95\right)^s
          +B_l\left(\frac{12}{5}\right)^s\right)z^2\\
&+\left(-30+14A_l\left(\frac95\right)^s
          -5B_l\left(\frac{12}{5}\right)^s
          +C_l\left(\frac{14}{5}\right)^s\right)z^3\\
&+\left(9-7A_l\left(\frac95\right)^s
          +5B_l\left(\frac{12}{5}\right)^s
          -3C_l\left(\frac{14}{5}\right)^s+D_l3^s\right)z^4 .
\end{aligned}
\]
The focused script
`working/super-recurrence-eulerian/d9_frontier_probe.py` checks by exact
isolating intervals and coefficient-ratio minors that
\[
  F_a\ll F_b\qquad(0\le a<b\le l)
\]
for \(2\le l\le8\).  The same probe records the first coordinate ratios:
at \(l=2\),
\[
  \frac{B_l}{A_l}>30,\qquad
  \frac{C_l}{B_l}>5.9,\qquad
  \frac{D_l}{C_l}>2.2,\qquad
  \frac{A_l^2}{B_l}>79 .
\]
The asymptotic lower curves suggested by the top terms are
\[
 A_l\ge 2\left(\frac{256}{9}\right)^l,\quad
 \frac{B_l}{A_l}\gtrsim 2\left(\frac{729}{256}\right)^l,\quad
 \frac{C_l}{B_l}\gtrsim 2\left(\frac{256}{189}\right)^l,\quad
 \frac{D_l}{C_l}\gtrsim 2\left(\frac{25}{24}\right)^l .
\]
However, the naive independent lower-corner tail region is false.  If one
sets
\[
  T=2\left(\frac{729}{256}\right)^h,\quad
  H=2\left(\frac{256}{189}\right)^h,\quad
  J=2\left(\frac{25}{24}\right)^h,
\]
then the cubic tail \(Q_0\) is not real-rooted for \(h=1,2,3\); for
\(h\ge5\) the tail discriminant signs are positive, but the directed
coefficient-ratio orientation still fails at this coarse corner.  Thus the
\(d=9\) proof should preserve actual-coordinate correlations, just as the
\(d=8\) proof eventually did for small gaps.

There is, however, a cleaner large-\(l\) route for the quartic discriminant.
The leading bases of the actual coordinates are
\[
  A_l\sim 2\left(\frac{256}{9}\right)^l,\quad
  B_l\sim 4\cdot81^l,\quad
  C_l\sim 8\left(\frac{768}{7}\right)^l,\quad
  D_l\sim 16\left(\frac{800}{7}\right)^l .
\]
In the quartic discriminant of \(F_0+\lambda F_h\), the unique largest
coordinate base in every \(\lambda\)-coefficient comes from the positive
monomial \(A_l^2B_l^2C_l^2\), namely
\[
  \left(\frac{256}{9}\right)^{2l}81^{2l}
  \left(\frac{768}{7}\right)^{2l}
  =
  \left(\frac{3131031158784}{49}\right)^l .
\]
The next possible coordinate base is \(A_l^2B_l^3D_l\), and the exact ratio is
\[
  \frac{A_l^2B_l^3D_l\text{ base}}
       {A_l^2B_l^2C_l^2\text{ base}}
  =
  \frac{1575}{2048}.
\]
Thus a large-\(l\) discriminant proof should be possible by top-term
dominance, without expanding all actual coordinate products.  A quick fixed
\(h=1\) prototype also shows that the top coefficient and all four
coefficient-ratio orientation minors are certifiable by actual-coordinate
finite-tail dominance; the \(\Delta_4\) substitution needs a more optimized
implementation before it should be promoted to a proof artifact.

The more structural recurrence refinement seems to live in the ordinary gamma
coefficient tails, not in the spectral coordinates.  Write
\[
  F_d^{(l)}(z)=\sum_{i=0}^{\lfloor d/2\rfloor} a_i z^i
\]
and define the cumulative gamma tails
\[
  T_{d,k}^{(l)}(z)=\sum_{i\ge k}a_i z^i.
\]
The new focused probe
`working/super-recurrence-eulerian/tail_packet_refinement_probe.py` checks
that every nonzero tail has an all-gap directed internal orbit:
\[
  M_d^aT_{d,k}^{(l)}\ll M_d^bT_{d,k}^{(l)}
  \qquad(0\le a<b\le l).
\]
This passes for
\[
  4\le d\le10,\qquad 2\le l\le7,
\]
including the \(d=9\) quartic slice.  The same probe now separately checks
the attached-packet coefficient-ratio inequalities needed to orient the
common-interlacing packet, and these pass on the same range.  The case
\(k=0\) is exactly the desired internal actual-orbit statement.  However, the
higher-tail all-gap statement is not global: for \((d,l,k)=(21,2,5)\), the
factored tail \(H_{21,5}^{(2)}=z^{-5}T_{21,5}^{(2)}\) has a nonreal conjugate
pair, approximately
\[
  -0.3805777228683027\pm0.0209703357975033i .
\]
Thus higher tails are still useful as an attachment surface, but not as a
global PF/interlacing cone in their own right.

The reason this is a recurrence-native object is the following exact
factorization.  Put \(D=d-2k\).  Then
\[
  M_d(z^k g)
  =
  z^k\left(
    \frac{D+1}{d+1}M_Dg
    +
    \frac{k(d-k+2)}{d+1}g
  \right).
\]
Indeed, on \(z^{k+j}\), the raising coefficient becomes
\[
  \frac{(D-2j)(D-2j-1)}{d+1},
\]
and the diagonal coefficient splits as
\[
  \frac{(k+j+1)(d+1-k-j)}{d+1}
  =
  \frac{(j+1)(D+1-j)}{d+1}
  +
  \frac{k(d-k+2)}{d+1}.
\]
Equivalently, the residual tail operator is
\[
  N_{d,k}
  =
  \beta_{d,k}I+c_{d,k}M_{d-2k},
  \qquad
  c_{d,k}=\frac{d-2k+1}{d+1},\quad
  \beta_{d,k}=\frac{k(d-k+2)}{d+1}.
\]
Its eigenvalues are exactly the spectral tail eigenvalues:
\[
  \beta_{d,k}+c_{d,k}\lambda_{d-2k,r}=\lambda_{d,k+r}.
\]
Thus a proof can try to use the actual tails, after removing \(z^k\), as a
lower-dimensional recurrence surface for the shifted operator \(N_{d,k}\).
The surface must be an attachability cone rather than a cone of PF tails,
because the higher tails are not all real-rooted.  This still avoids treating
the spectral coordinates independently.

The same identity has a recursive attachment form.  Write
\[
  H_{d,k}^{(l)}(z)=z^{-k}T_{d,k}^{(l)}(z)
  =a_k+zH_{d,k+1}^{(l)}(z).
\]
Then
\[
  N_{d,k}(1)=\lambda_{d,k}+\rho_{d,k}z,
  \qquad
  N_{d,k}(zh)=zN_{d,k+1}h,
\]
where
\[
  \lambda_{d,k}=\frac{(k+1)(d+1-k)}{d+1},
  \qquad
  \rho_{d,k}=\frac{(d-2k)(d-2k-1)}{d+1}.
\]
Consequently
\[
  N_{d,k}(a+zh)
  =
  \lambda_{d,k}a
  +z\left(\rho_{d,k}a+N_{d,k+1}h\right).
\]
This is the tail analogue of the cumulative prefix recurrence: the \(k\)-tail
is obtained by attaching one constant coefficient to the \((k+1)\)-tail, and
the operator sends this attached form to another attached form.  Thus the
eventual induction should not be on \(d=9,d=10,\dotsc\) discriminants, but on
successively attaching coefficients while preserving an attachability cone.

Iterating the attachment recurrence gives an explicit lower-tail formula:
\[
\begin{aligned}
  N_{d,k}^s(a+zh)
  ={}& \lambda_{d,k}^s a\\
     &+z\left(
       N_{d,k+1}^s h
       +\rho_{d,k}a
        \sum_{i=0}^{s-1}
          \lambda_{d,k}^i
          N_{d,k+1}^{s-1-i}1
     \right).
\end{aligned}
\]
The probe verifies this identity on monomial bases for \(d\le14\) and
\(s\le5\).  Therefore the attached orbit is controlled by adding a
geometrically weighted lower-tail packet and then attaching a constant term.
This is the first genuinely recurrence-shaped alternative to quartic
discriminant expansion.

The all-gap conclusion still requires care.  A tempting reduction would prove
only the one-step relation \(g\ll N_{d,k}g\) and then iterate.  This is not
logically sufficient, because weak proper position is not transitive.  The
right target is stronger: prove that every finite conic sum of the attached
orbit is real-rooted, using the explicit constant-attachment formula above,
and then orient the packet by coefficient-ratio inequalities.  Random stress
tests for \(D\le12\) found no failures of the shifted operator
\[
  M_D+\frac{D+3}{D+1}I
\]
on directed PF interlacing pairs, but this is only supporting evidence for
the corrected attachability picture, not a proof by itself.

A more precise way to state the missing attachment lemma is the following.
Let \(H_{d,k}=a+zh\), put \(L=N_{d,k+1}\), and abbreviate
\(\lambda=\lambda_{d,k}\), \(\rho=\rho_{d,k}\).  The orbit formula says that
\[
  N_{d,k}^sH_{d,k}
  =
  \lambda^s a+zB_s,
\]
where
\[
  B_s
  =
  L^s h+\rho a
  \sum_{i=0}^{s-1}\lambda^iL^{s-1-i}1 .
\]
Thus every nonnegative combination of the attached orbit has the form
\[
  a\sum_s c_s\lambda^s
  +
  z\sum_s c_sB_s .
\]
For a PF polynomial \(U\) with nonnegative coefficients, define the attachment
threshold
\[
  \tau(U)
  =
  \sup\{A\ge0:A+zU(z)\text{ has only real nonpositive zeros}\}.
\]
Since \(zU\) has only real nonpositive zeros, the allowable constants form the
initial interval \(0\le A\le\tau(U)\); equivalently \(\tau(U)\) is the first
positive critical value of \(-zU(z)\) at a negative critical point of
\(zU(z)\).  The desired attached-packet criterion is therefore:
if the coupled packet \(\{B_0,\dotsc,B_l\}\) is compatible, and if for every
nonnegative vector \((c_0,\dotsc,c_l)\) one has
\[
  a\sum_s c_s\lambda^s
  \le
  \tau\left(\sum_s c_sB_s\right),
\]
then all nonnegative combinations of
\(\{N_{d,k}^sH_{d,k}:0\le s\le l\}\) are real-rooted.  The standard
compatibility/common-interlacing criterion then gives a common interlacing
cone for the whole attached packet.  Notice that this criterion does not ask
the individual factored higher tails \(H_{d,k}\) to be real-rooted.  That
extra assumption is false globally.

For \(k=0\), this coupled packet has a much simpler description.  If
\[
  F_s=M_d^sF_0
      =\sum_r c_r^{(l)}\lambda_{d,r}^sP_{d,r},
\]
then \(B_s=(F_s-1)/z\).  The spectral basis satisfies
\[
  P_{d,r+1}=zP_{d-2,r},
  \qquad
  \frac{P_{d,0}-1}{z}
  =
  -\sum_r\binom d{r+1}P_{d-2,r}.
\]
Thus
\[
  B_s
  =
  \sum_r
  \left(c_{r+1}^{(l)}\lambda_{d,r+1}^s-\binom d{r+1}\right)
  P_{d-2,r}.
\]
So the remaining \(k=0\) compatibility target can be stated without the
attachment convolution: it is a compatibility/PF statement for a packet with
shifted spectral coordinate matrix
\[
  C_{s,r}=c_{r+1}^{(l)}\lambda_{d,r+1}^s-\binom d{r+1}.
\]
The probe verifies this direct spectral formula against the recurrence-built
packet for \(d\le14\), \(2\le l\le5\).  It also checks that all \(C_{s,r}\)
are nonnegative for \(d\le30\), \(2\le l\le8\), and that the minors of
\((C_{s,r})\) through order \(3\) are nonnegative for \(d\le14\),
\(2\le l\le6\).  This suggests a total-positivity route for the last
compatibility input.

Equivalently, the same simplification can be stated in the ordinary
palindromic lift, where the signs of the spectral basis disappear.  Put
\(D=d-2\), let
\[
  f(x)=\sum_s a_sx^s,\qquad a_s\ge0,
\]
and let \(q_i\) be the coefficient of \(t^i\) in
\(\Phi_d(F_0)\).  Since
\[
  \Phi_d(zG)=t\Phi_{d-2}(G),
\]
we have
\[
\begin{aligned}
  \Phi_D\left(\sum_s a_sB_s\right)
  &=
  \frac{1}{t}\left(
    \sum_s a_s\Phi_d(F_s)-f(1)(1+t)^d
  \right)\\
  &=
  \sum_{j=0}^D
  \left(q_{j+1}f(\lambda_{d,j+1})
        -\binom d{j+1}f(1)\right)t^j .
\end{aligned}
\]
Using
\[
  \lambda_{d,j+1}-1
  =
  \frac{d-1}{d+1}\lambda_{d-2,j},
\]
this can also be written as
\[
  \frac{d(d-1)}{d+1}
  \sum_{j=0}^D
  \binom Dj
  \frac{
    (q_{j+1}/\binom d{j+1})f(\lambda_{d,j+1})-f(1)
  }{\lambda_{d,j+1}-1}
  t^j .
\]
The remaining \(k=0\) compatibility input is therefore equivalent to a
Loewner-type coefficient-kernel statement: for every nonnegative-coefficient
polynomial \(f\) of degree at most \(l\), this lifted polynomial is real-rooted
with nonnegative coefficients.  The probe verifies both displayed formulas
for \(d\le14\), \(2\le l\le5\).
At least the coefficientwise nonnegativity in this kernel is elementary.  Let
\[
  q_{d,i}^{(l)}=[t^i]Q_{d+1}^{(l)}.
\]
The normalized recurrence gives
\[
  q_{d,i}^{(l)}
  =
  \left(\frac{(i+1)(d-i)}d\right)^l q_{d-1,i}^{(l)}
  +
  \left(\frac{(d+1-i)i}d\right)^l q_{d-1,i-1}^{(l)} .
\]
The two displayed weights are at least \(1\).  Hence, for \(l\ge1\), induction
from the boundary and the case \(l=1\) weights gives
\[
\begin{aligned}
  q_{d,i}^{(l)}
  &\ge
  \frac{(i+1)(d-i)}d\binom{d-1}{i}
  +
  \frac{(d+1-i)i}d\binom{d-1}{i-1}  \\
  &=
  \binom di
  \left(1+\frac{i(d-2)(d-i)}{d^2}\right)
  \ge
  \binom di .
\end{aligned}
\]
Thus every coefficient
\[
  q_{j+1}f(\lambda_{d,j+1})-\binom d{j+1}f(1)
\]
is nonnegative whenever \(f\) has nonnegative coefficients, because
\(\lambda_{d,j+1}\ge1\).  The remaining difficulty is therefore not
coefficient positivity, but real-rootedness/common interlacing.

For the total-positivity problem, it is useful to record a stronger dominance
estimate.  For \(d\ge4\), \(l\ge2\), and \(0\le i\le d\),
\[
  q_{d,i}^{(l)}
  \ge
  \binom di\lambda_{d,i}^l,
  \qquad
  \lambda_{d,i}=\frac{(i+1)(d+1-i)}{d+1}.
\]
Equivalently, in the notation
\(\beta_i=\binom di/q_{d,i}^{(l)}\), we have
\[
  \beta_i\le \lambda_{d,i}^{-l}.
\]
The proof is by induction on \(d\), starting from the explicit \(d=4\)
coordinates.  In the induction step, put
\[
  A=\frac{(i+1)(d-i)}d,\qquad
  B=\frac{(d+1-i)i}{d},\qquad
  L=\frac{(i+1)(d+1-i)}{d+1}.
\]
Using
\[
  \binom{d-1}{i}=\frac{d-i}{d}\binom di,\qquad
  \binom{d-1}{i-1}=\frac{i}{d}\binom di,
\]
the induction hypothesis gives
\[
  \frac{q_{d,i}^{(l)}}{\binom di}
  \ge
  \frac{d-i}{d}A^{2l}+\frac{i}{d}B^{2l}.
\]
By Jensen's inequality, the right-hand side is at least
\[
  \left(\frac{d-i}{d}A^2+\frac{i}{d}B^2\right)^l.
\]
Finally
\[
\begin{aligned}
  \frac{d-i}{d}A^2+\frac{i}{d}B^2-L
  =
  \frac{i(d-i)}{d^3(d+1)}
  \left(
    d(d^2-d-3)+i(d-i)(d-4)(d+1)
  \right),
\end{aligned}
\]
which is nonnegative for \(d\ge4\).  This proves the claim.

The same lower-lift formula also exposes an affine recurrence.  Let
\[
  S_d=I+\frac{d-1}{d+1}D_{d-2},
\]
acting on degree-\((d-2)\) palindromic lifts, and put
\[
  K_s=\Phi_{d-2}(B_s).
\]
Since
\[
  \lambda_{d,j+1}
  =
  1+\frac{d-1}{d+1}\lambda_{d-2,j}
\]
and
\[
  \binom d{j+1}(\lambda_{d,j+1}-1)
  =
  \frac{d(d-1)}{d+1}\binom{d-2}{j},
\]
we get
\[
  K_{s+1}
  =
  S_dK_s+\frac{d(d-1)}{d+1}(1+t)^{d-2}.
\]
Moreover, for \(f(x)=\sum_s a_sx^s\),
\[
  K_f=\Phi_{d-2}\left(\sum_s a_sB_s\right)
  =
  f(S_d)K_0
  +
  \frac{d(d-1)}{d+1}
  \frac{f(S_d)-f(1)}{S_d-1}(1+t)^{d-2}.
\]
The quotient is polynomial because
\((f(x)-f(1))/(x-1)\) has nonnegative coefficients when \(f\) does.  Finally,
the base term itself is inherited from the previous dimension:
\[
  K_0(d,l)=(1+t)K_l(d-1,l).
\]
Thus the remaining compatibility theorem can be attacked as an induction for
an affine orbit under the shifted diagonal operator \(S_d\).  A direct proof
that all \(K_s\) are compatible with \((1+t)^{d-2}\) is too strong and already
fails in the first case \(d=4,l=2,s=1\).  Even the sharper source-splitting
condition that \((1+t)^{d-2}\) be compatible with \(S_dK_s\) fails at
\(d=4,l=2,s=0\).  Thus the induction must keep the coupled form above, not
split it into two independent compatible packets.  The probe verifies the
displayed affine recurrence for \(d\le14\), \(2\le l\le5\).

The operator \(S_d\) itself is harmless: it is a finite multiplier sequence.
Writing \(D=d-2\), its symbol is
\[
  S_d(1+t)^D
  =
  \frac{(1+t)^{D-2}}{D+3}
  \left(
    2(D+2)(1+t^2)+(D^2+3D+8)t
  \right).
\]
The quadratic factor has positive coefficients and discriminant
\[
  (D^2+3D+8)^2-16(D+2)^2>0
\]
for \(D\ge2\), so it has two negative roots.  Therefore \(S_d\) preserves PF
polynomials in degree at most \(D\).  What is still missing is a common-cone
statement for the affine orbit \(K_{s+1}=S_dK_s+A(1+t)^D\), not preservation
of individual real-rootedness by \(S_d\).

The better common-cone target is obtained by folding the palindromic lower
lifts.  Write \(D=d-2\), \(m=\lfloor D/2\rfloor\), and set
\[
  y=t+t^{-1}.
\]
For even \(D=2m\), write
\[
  K_s(t)=t^mR_s(y),
\]
and for odd \(D\) divide out the unavoidable factor \(1+t\) before the same
folding.  The lower-lift basis \(t^r+t^{D-r}\) becomes a Chebyshev-type basis
in \(y\).  On the interval \((-\infty,-2)\), this is a sign-regular Sturm
basis.  Thus the natural proof route is:
\[
  \text{TP of }(C_{s,r})
  \quad+\quad
  \text{sign-regular folded basis}
  \quad\Longrightarrow\quad
  R_0,R_1,\dotsc,R_l\text{ is a Sturm chain}.
\]
Then Obreschkoff, equivalently the Chudnovsky--Seymour common-interlacing
criterion, gives real-rootedness of every nonnegative conic sum, and folding
back gives the desired PF property of \(K_f\).

This route matches the evidence better than the affine boundary cone.  For
example, in the first nontrivial even folded case \(d=6,l=2,s=1\), one has
\[
  K_1(t)=t^2R_1(y),\qquad
  R_1(y)=\frac{2}{525}(36125y^2+256870y+379556).
\]
The boundary polynomial \((1+t)^4\) folds to \((y+2)^2\), and
\[
  \operatorname{disc}_y\bigl((y+2)^2+uR_1(y)\bigr)
  =
  \frac{16u(37121183u-36106)}{3675},
\]
which is negative for small positive \(u\).  Thus the folded Sturm route also
explains why compatibility with the boundary binomial packet is the wrong
cone.  The main algebraic sublemma is now the full total positivity of
\[
  C_{s,r}=q_{r+1}\lambda_{d,r+1}^s-\binom d{r+1},
\]
or equivalently the rank-one interpolation inequalities
\[
  \beta_R^TV^{-1}{\bf 1}\le1
\]
for every square minor.
This should not be strengthened to bivariate stability of the generating
polynomials \(\sum_s u^sB_s(z)\) or \(\sum_s u^sF_s(z)\).  A line-slice check
already fails at \(d=4\), \(l=2\): setting \(u=z=t\) gives
\[
  \sum_s t^sB_s(t)
  =
  \frac{1082t^3+2770t^2+1400t+725}{100},
\]
which has a nonreal conjugate pair; the analogous slice for the \(F_s\)-packet
also has nonreal roots.  The right target is therefore constant-coefficient
common interlacing/PF of conic sums, not full two-variable stability.

There is an even more concrete form of the same target.  Write
\[
  q_r=c_{r+1}^{(l)},\qquad
  \mu_r=\lambda_{d,r+1},\qquad
  b_r=\binom d{r+1},\qquad
  \beta_r=\frac{b_r}{q_r}.
\]
Then
\[
  C_{s,r}=q_r(\mu_r^s-\beta_r).
\]
For any square submatrix with row set \(S\) and column set \(R\), let
\[
  V_{s,r}=\mu_r^s\qquad(s\in S,\ r\in R).
\]
The determinant lemma gives
\[
  \det(C_{S,R})
  =
  \left(\prod_{r\in R}q_r\right)\det(V)
  \left(1-\beta_R^T V^{-1}{\bf 1}\right).
\]
Since \(\det(V)>0\) is a generalized Vandermonde determinant, the
total-nonnegativity problem has been reduced to the scalar interpolation
bound
\[
  \beta_R^T V^{-1}{\bf 1}\le1
\]
for every choice of \(S\) and \(R\).  This is a useful simplification because
the small parameters \(\beta_r\) carry all of the actual-row information, and
the remaining matrix is the standard power kernel.  In the exact checks
through order \(3\), the smallest scalar margin is \(841/1845\), occurring at
the base case \(d=4\), \(l=2\), \(|S|=|R|=2\), \(S=(0,1)\), \(R=(0,1)\).
Thus the same base-case domination pattern seen in the \(\tau\)-bound appears
in the compatibility input as well.

There is a sharper way to package the scalar interpolation bound.  Fix
\[
  1< x_1<\dotsb<x_m,\qquad S=\{s_1<\dotsb<s_m\}\subseteq\mathbb R_{\ge0},
\]
and write \(V_{i,j}=x_j^{s_i}\).  If \(u>0\), then
\[
  x_j^{s_i}-x_j^{-u}
\]
has positive determinant.  Indeed, after multiplying column \(j\) by
\(x_j^u\), the determinant becomes
\[
  \det(x_j^{s_i+u}-1).
\]
This is the generalized Vandermonde determinant for the exponents
\[
  0<s_1+u<\dotsb<s_m+u
\]
at the nodes \(1<x_1<\dotsb<x_m\), after subtracting the first column and
expanding along the exponent-\(0\) row.  Consequently
\[
  (x_1^{-u},\dotsc,x_m^{-u})^T V^{-1}{\bf 1}<1.
\]
By linearity, the same inequality holds for every subprobability mixture
\[
  \beta(x)=\int_0^\infty x^{-u}\,d\nu(u),
  \qquad \nu([0,\infty))\le1 .
\]
Equivalently, if \(g(y)=\beta(e^y)\) is completely monotone on
\([0,\infty)\) and \(g(0)\le1\), then Bernstein's theorem writes
\[
  g(y)=\int_0^\infty e^{-uy}\,d\nu(u),
\]
and the rank-one interpolation bound follows by integrating the pure
exponential case.
Thus a sufficient condition for all rank-one inequalities is:
for every fixed \(d,l\), the actual vector
\[
  \left(\beta_r\right)_r
  =
  \left(\binom d{r+1}/c_{r+1}^{(l)}\right)_r
\]
lies in the inverse-power moment cone on the nodes
\(\mu_r=\lambda_{d,r+1}\).

This is stronger and cleaner than the pointwise estimate
\(\beta_r\le\mu_r^{-l}\).  That estimate proves coefficient positivity, but
it cannot by itself prove total positivity: the interpolation weights
\(V^{-1}{\bf 1}\) have mixed signs as soon as \(S=(0,1)\) and there are at
least two nodes.  This failure is already exact at \(d=4,l=2\).  The nodes
are \((8/5,9/5)\), and the artificial choice
\[
  \beta=\left(\frac{25}{64},0\right)
  \le
  \left(\left(\frac85\right)^{-2},
        \left(\frac95\right)^{-2}\right)
\]
gives, for \(S=(0,1)\),
\[
  \det
  \begin{pmatrix}
    1-\beta_0 & 1-\beta_1\\
    \frac85-\beta_0 & \frac95-\beta_1
  \end{pmatrix}
  =
  -\frac9{80}.
\]
The new target is therefore not pointwise domination, but membership of the
actual \(\beta\)-data in the inverse-power moment cone.  Finite checks support
this: the divided differences of \(\beta_r\), viewed either as a function of
\(\mu_r\) or of \(\log\mu_r\), have the alternating signs expected of a
completely monotone function through \(d\le30\), \(2\le l\le8\).
Even after adjoining the anchor
\[
  \beta(1)=1,
\]
the same alternating-divided-difference screen passes through \(d\le30\),
\(2\le l\le10\).  This is the finite form one would expect if the actual
\(\beta\)-data comes from a probability mixture of inverse powers
\(x^{-u}\).

There is a slightly weaker finite interpolation route which avoids the
logarithmic moment representation.  Suppose \(f\) has the finite anchored
complete-monotonicity signs at the nodes
\[
  x_0=1<x_1<\dotsb<x_m,
  \qquad
  (-1)^r f[x_0,\dotsc,x_r]\ge0
  \quad(0\le r\le m),
\]
and let \(P\) be the generalized polynomial
\[
  P(x)=\sum_{s\in S} a_s x^s,\qquad S\subseteq\mathbb Z_{\ge0},
\]
which interpolates \(f\) at the right-hand nodes \(x_1,\dotsc,x_m\), where
\(|S|=m\).  The needed rank-one inequality is exactly
\[
  P(1)\le1.
\]
This inequality is in fact a finite total-positivity consequence.  Let
\[
  N_r(x)=\prod_{j=0}^{r-1}(x-x_j)
\]
be the Newton basis, and expand the powers in this basis on the nodes
\(x_0,\dotsc,x_m\):
\[
  x^s=\sum_{r=0}^m H_{r,s}N_r(x).
\]
For integer \(s\ge0\),
\[
  H_{r,s}
  =
  [x_0,\dotsc,x_r]\,x^s
  =
  h_{s-r}(x_0,\dotsc,x_r),
\]
with \(h_a=0\) for \(a<0\).  The matrix
\[
  H=(H_{r,s})_{0\le r\le m,\ s\in S}
\]
is a flagged complete-homogeneous matrix.  Its minors are flagged Schur
functions, or equivalently Lindstrom--Gessel--Viennot path determinants, and
are therefore nonnegative for positive nodes.

Now write \(c_r=f[x_0,\dotsc,x_r]\).  The interpolation error has the
determinantal form
\[
  f(x_0)-P(x_0)
  =
  \frac{\det(f(x_j),x_j^s)_{\substack{0\le j\le m\\ s\in S}}}
       {\det(x_j^s)_{\substack{1\le j\le m\\ s\in S}}}.
\]
Substituting \(f=\sum_r c_rN_r\) in the first column gives
\[
  f(x_0)-P(x_0)
  =
  \kappa\sum_{r=0}^m(-1)^r D_r\,c_r,
  \qquad
  D_r=\det H_{\widehat r,S},
\]
where \(H_{\widehat r,S}\) is obtained from \(H\) by deleting row \(r\), and
\[
  \kappa=
  \frac{\prod_{0\le i<j\le m}(x_j-x_i)}
       {\det(x_j^s)_{\substack{1\le j\le m\\ s\in S}}}
  >0.
\]
Since every \(D_r\ge0\), the signs \((-1)^rc_r\ge0\) imply
\[
  f(1)-P(1)\ge0.
\]
Thus finite anchored complete monotonicity in the ordinary \(x\)-variable is
already enough for the rank-one interpolation bounds with integer exponent
sets.

For the initial exponent set \(S=\{0,1,\dotsc,m-1\}\), the same statement
specializes to the usual Newton interpolation error formula:
\[
  f(1)-P(1)
  =
  f[1,x_1,\dotsc,x_m]\prod_{j=1}^m(1-x_j)\ge0,
\]
but the determinant argument proves the required integer-Muntz version
directly.  Consequently it is enough to prove the anchored ordinary-\(\mu\)
complete monotonicity of the actual \(\beta\)-data.  The needed finite
statement is the all-subset version: for every selected set of right-hand
nodes \(1<\mu_{i_1}<\dotsb<\mu_{i_k}\),
\[
  (-1)^k[1,\mu_{i_1},\dotsc,\mu_{i_k}]\beta\ge0.
\]
This is not, however, a new family-specific condition.  By the standard
positive knot-insertion formula for divided differences, the divided
difference over any subset of a fixed ordered node set is a nonnegative
linear combination of divided differences of the same order over consecutive
blocks in the refined node set.  Concretely, inserting a knot \(y\) into
\(x_0<\dotsb<x_k\) gives
\[
  f[x_0,\dotsc,x_k]
  =
  \frac{y-x_0}{x_k-x_0}
  f[x_0,\dotsc,y,\dotsc,x_{k-1}]
  +
  \frac{x_k-y}{x_k-x_0}
  f[x_1,\dotsc,y,\dotsc,x_k],
\]
with the knots in each divided difference written in increasing order.
Repeating this insertion expresses any selected-node divided difference as a
convex combination of consecutive-block divided differences.  Hence it is
enough to prove the ordinary
consecutive divided-difference table for the anchored data
\[
  (1,1),\quad(\mu_i,\beta_i)\quad(1\le i\le\lfloor d/2\rfloor).
\]
This is an exact rational finite statement, unlike the logarithmic moment
representation.

There is a sharper finite target which appears to be the right one.  Define
\[
  h_i=\mu_i\beta_i,\qquad h_0=1.
\]
Exact checks support anchored complete monotonicity of \(h\) in the same
\(\mu\)-variable:
\[
  (-1)^k[\mu_{i_0},\dotsc,\mu_{i_k}]h\ge0
\]
for the anchored first-half data.  This statement implies the desired
complete monotonicity of \(\beta\).  Indeed, \(\beta(\mu)=\mu^{-1}h(\mu)\),
and the divided-difference product rule gives
\[
  (\mu^{-1}h)[x_0,\dotsc,x_k]
  =
  \sum_{r=0}^k
  (\mu^{-1})[x_0,\dotsc,x_r]\,h[x_r,\dotsc,x_k].
\]
Since \(\mu^{-1}\) is completely monotone on positive nodes, each summand has
sign \((-1)^k\) if \(h\) is completely monotone.  Thus
\((-1)^k[\mu_{i_0},\dotsc,\mu_{i_k}]\beta\ge0\).

The same sharpening has a clean total-positivity interpretation.  The shifted
coordinate matrix
\[
  C_{s,i}=q_i\mu_i^s-b_i
\]
was previously considered for rows \(s\ge0\).  Allowing the one Laurent row
\(s=-1\) is exactly the \(h=\mu\beta\) version, because
\[
  q_i\mu_i^s-b_i
  =
  q_i\mu_i^{-1}\left(\mu_i^{s+1}-\mu_i\beta_i\right)
  \qquad(s\ge-1).
\]
Thus the sharpened target says that this Laurent-shifted matrix should be TNN
for \(s\ge-1\).  The shift is also sharp: the next row \(s=-2\) would require
anchored complete monotonicity of \(\mu_i^2\beta_i\), and this already fails
at \(d=4,l=2\).  The data
\[
  \mu^2\beta=\left(1,\frac{1024}{1125},\frac{972}{1025}\right)
\]
has adjacent first divided differences
\[
  -\frac{101}{675},\qquad \frac{1756}{9225}.
\]

It may also be useful to change variables to the square grid
\[
  \rho_i=(d-2i)^2,\qquad
  \mu_i=1+\frac{d^2-\rho_i}{4(d+1)}.
\]
Since this is an affine change with negative slope, alternating divided
differences in the increasing \(\mu\)-nodes are the same as ordinary
nonnegative divided differences in the \(\rho\)-variable.  In other words,
anchored \(\mu\)-complete monotonicity is equivalent to absolute monotonicity
on the even/odd Racah-type square grid.

There is a useful determinant reformulation of this last target.  Put
\[
  q_i=c_i^{(l)},\qquad b_i=\binom di,\qquad
  \mu_i=\lambda_{d,i},\qquad \beta_i=\frac{b_i}{q_i},
\]
with the anchored column \(i=0\), so that \(q_0=b_0=\mu_0=\beta_0=1\).
Define the augmented matrix
\[
  Y_{-1,i}=b_i,\qquad
  Y_{s,i}=q_i\mu_i^s\quad(s\ge0).
\]
For \(R=\{i_1<\dotsb<i_k\}\), let \(x_0=1\) and
\(x_j=\mu_{i_j}\).  Factoring \(q_i\) from the columns gives
\[
  \det Y_{\{-1,0,\dotsc,k-1\},\{0\}\cup R}
  =
  \left(\prod_{j=1}^kq_{i_j}\right)
  \prod_{0\le a<b\le k}(x_b-x_a)\,
  (-1)^k[1,x_1,\dotsc,x_k]\beta .
\]
Thus anchored \(\mu\)-complete monotonicity on a selected node set is
equivalent to nonnegativity of these initial minors of \(Y\).  By the
knot-insertion observation, the family-specific target can be restricted to
the solid initial minors, where the selected columns form a consecutive block
in the full anchored node list.

There is also a scalar form which may be useful for a non-network proof.
Since
\[
  \mu_i=1+\frac{i(d-i)}{d+1},
  \qquad
  \mu_j-\mu_i=\frac{(j-i)(d-i-j)}{d+1},
\]
the barycentric formula gives, for any selected indices
\(i_0<\dotsb<i_k\),
\[
  (-1)^k[\mu_{i_0},\dotsc,\mu_{i_k}]\beta
  =
  (d+1)^k
  \sum_{r=0}^k
  \frac{(-1)^r}
       {w_{d,i_r}
        \prod_{a\ne r}|i_r-i_a|(d-i_r-i_a)},
\]
where \(w_{d,i}=q_{d,i}^{(l)}/\binom di\).  For consecutive blocks this is an
explicit alternating finite difference of \(1/w_{d,i}\) with the quadratic-grid
weights.  A proof from this formula would avoid the local fan-in obstruction
in the recurrence network.

The recurrence for \(Y\) also has the right total-positivity shape.  Since
\[
  q_{d,i}=A^lq_{d-1,i}+B^lq_{d-1,i-1},
  \qquad
  \binom di=\binom{d-1}i+\binom{d-1}{i-1},
\]
where \(A=\lambda_{d-1,i}\), \(B=\lambda_{d-1,i-1}\), and
\(L=\lambda_{d,i}\), we have the following recurrence after mirror-extending
the folded previous row by the symmetry \(q_{d-1,i}=q_{d-1,d-1-i}\).  This
convention only matters when \(d\) is even and \(i=d/2\), where the two
incoming branches coincide and give a doubled central contribution:
\[
  Y^{(d)}_{-1,i}=Y^{(d-1)}_{-1,i}+Y^{(d-1)}_{-1,i-1},
\]
and, for \(s\ge0\),
\[
  Y^{(d)}_{s,i}
  =
  A^l\sum_{r=0}^s\binom sr(L-A)^{s-r}Y^{(d-1)}_{r,i}
  +
  B^l\sum_{r=0}^s\binom sr(L-B)^{s-r}Y^{(d-1)}_{r,i-1}.
\]
On the relevant first half of the row,
\[
  L-A=\frac{i(i+1)}{d(d+1)}\ge0,\qquad
  L-B=\frac{(d-i)(d+1-i)}{d(d+1)}\ge0.
\]
The row chips are therefore nonnegative Pascal-translation kernels.  This
suggests looking for a total-positivity proof of the solid initial-minor
positivity of \(Y\), and hence of the anchored \(\mu\)-complete monotonicity
of \(\beta\).  There is, however, a local obstruction to the most naive LGV
realization of this recurrence.  In the natural incoming column order
\((i-1,i)\), the two branch chips into column \(i\) have the row-\(0,1\)
minor
\[
  \det\begin{pmatrix}
    B^l & A^l\\
    B^l(L-B) & A^l(L-A)
  \end{pmatrix}
  =
  A^lB^l(B-A)
  =
  -A^lB^l\frac{d-2i}{d},
\]
which is negative in the relevant first half.  The reason is that
\[
  L-B=\frac{(d-i)(d+1-i)}{d(d+1)}
  >
  \frac{i(i+1)}{d(d+1)}
  =
  L-A,
\]
so the larger translation shift comes from the left branch.  Thus the
recurrence is not simply a product of planar TNN fan-in layers; a proof needs
either a more subtle cancellation/network model or a different route to the
consecutive beta divided-difference signs.  The augmented \(Y\)-surface still
appears better aligned with the desired determinant signs than the defect
recurrence for \(\mu_i^{-l}-\beta_i\), since it works before taking
reciprocals.

The first solid-minor case does have a clean induction.  Let
\[
  M_{d,i}=b_{d,i}q_{d,i+1}-b_{d,i+1}q_{d,i},
  \qquad b_{d,i}=\binom di,
\]
so \(M_{d,i}\ge0\) is the monotonicity \(w_{d,i}\le w_{d,i+1}\).  Write
\[
  u_j=\lambda_{d-1,j}^l,\qquad
  b_j=b_{d-1,j},\qquad q_j=q_{d-1,j}.
\]
Expanding the two adjacent recurrences gives
\[
\begin{aligned}
  M_{d,i}
  ={}&
  \frac{b_i+b_{i-1}}{b_i}\,u_{i+1}
  \bigl(b_iq_{i+1}-b_{i+1}q_i\bigr) \\
  &+
  \frac{b_{i+1}+b_i}{b_i}\,u_{i-1}
  \bigl(b_{i-1}q_i-b_iq_{i-1}\bigr) \\
  &+
  \frac{q_i}{b_i}
  \Bigl[
    b_ib_{i-1}(u_i-u_{i-1})
    +b_ib_{i+1}(u_{i+1}-u_i)
    +b_{i-1}b_{i+1}(u_{i+1}-u_{i-1})
  \Bigr].
\end{aligned}
\]
All coefficients are nonnegative on the first half, since the eigenvalues
\(\lambda_{d-1,j}\) increase there.  This proves the order-one beta sign by
induction.  The obstruction starts at the next solid minors: a branchwise
expansion has negative summands already for \(d=4\), so higher order needs
an additional cancellation or condensation idea.

Condensation gives the right next formulation, but not a proof by itself.
Let
\[
  M_{d,k,j}
  =
  \det Y_{\{-1,0,\dotsc,k-1\},\{j,j+1,\dotsc,j+k\}}
\]
be the solid augmented \(Y\)-minor, and let
\[
  V_{d,k,j}
  =
  \det (q_c\mu_c^r)_{\substack{0\le r\le k-1\\ j\le c\le j+k-1}}
\]
be the pure moment minor on the same consecutive block length.  The
Desnanot--Jacobi identity gives
\[
  M_{d,k,j}V_{d,k-1,j+1}
  =
  V_{d,k,j+1}M_{d,k-1,j}
  -
  V_{d,k,j}M_{d,k-1,j+1}.
\]
For \(k=2\), this is
\[
  M_{d,2,j}
  =
  q_{j+2}(\mu_{j+2}-\mu_{j+1})M_{d,1,j}
  -
  q_j(\mu_{j+1}-\mu_j)M_{d,1,j+1}.
\]
Equivalently, after putting \(w_i=q_i/b_i\) and
\(h_i=\mu_{i+1}-\mu_i\), the next beta sign is
\[
  \frac{\beta_j-\beta_{j+1}}{h_j}
  \ge
  \frac{\beta_{j+1}-\beta_{j+2}}{h_{j+1}},
\]
or, after clearing the positive reciprocal denominators,
\[
  h_{j+1}w_{j+2}(w_{j+1}-w_j)
  -
  h_jw_j(w_{j+2}-w_{j+1})\ge0 .
\]
Thus the \(k=2\) case asks for monotonicity of the normalized first beta
slopes, not merely positivity of the first minors.  For \(k=3\), condensation
already gives the same pattern one level higher:
\[
\begin{aligned}
  M_{d,3,j}={}&
  q_{j+3}(\mu_{j+3}-\mu_{j+1})(\mu_{j+3}-\mu_{j+2})
  M_{d,2,j} \\
  &-
  q_j(\mu_{j+1}-\mu_j)(\mu_{j+2}-\mu_j)
  M_{d,2,j+1}.
\end{aligned}
\]
The formula is exact but subtractive.  Hence induction on \(k\) needs a
monotonicity statement for suitably normalized lower minors, which is
essentially the next divided-difference sign.  Small exact lower-\(d\)
expansions suggest that \(k=2\) may still admit a positive local recurrence
after using the old \(k=2\) inequalities, but a single same-order lower minor
is not enough in higher order.

For \(k=2\), the local recurrence has a useful two-case reduction.  Write
the old consecutive values as
\[
  u_{j-1}=X,\qquad u_j=X+a,\qquad
  u_{j+1}=X+a+b,\qquad u_{j+2}=X+a+b+c,
\]
where \(X,a,b,c\ge0\).  If
\[
  H_i=\lambda_{d-1,i+1}-\lambda_{d-1,i},
\]
then the two old \(k=2\) hypotheses on this four-point window are exactly
\[
  H_j\,a(X+a+b)-H_{j-1}Xb\ge0
\]
and
\[
  H_{j+1}\,b(X+a+b+c)-H_j(X+a)c\ge0.
\]
Now write the three new values as
\[
  W_j=A_0X+B_0(X+a),\quad
  W_{j+1}=A_1(X+a)+B_1(X+a+b),
\]
and
\[
  W_{j+2}=A_2(X+a+b)+B_2(X+a+b+c),
\]
where the coefficients are the positive two-branch weights coming from the
dimension-\((d-1)\) eigenvalues and binomial ratios.  The new cleared
\(k=2\) numerator is
\[
  \mathcal N(c)
  =
  h_{j+1}W_{j+2}(W_{j+1}-W_j)
  -
  h_jW_j(W_{j+2}-W_{j+1}).
\]
It is affine in \(c\), with
\[
  [c]\mathcal N
  =
  B_2\bigl(h_{j+1}W_{j+1}-(h_j+h_{j+1})W_j\bigr).
\]
If this coefficient is nonnegative, the worst case is \(c=0\).  If it is
negative, the second old \(k=2\) inequality gives the upper boundary
\[
  c=
  \frac{H_{j+1}b(X+a+b)}
       {H_j(X+a)-H_{j+1}b},
\]
whenever the denominator is positive; if the denominator is nonpositive, the
second old inequality imposes no upper bound and the affine coefficient must
be nonnegative in the feasible region.  Thus the interior \(k=2\) induction
has been reduced to two explicit quadratic inequalities in \(X,a,b\), under
the first old constraint.  This is the precise constrained-quadratic target.

The first endpoint has an especially simple certificate in the noncentral
interior cases checked: after setting \(c=0\), one can write
\[
  \mathcal N(0)=\gamma_{d,j,l}\,
  \bigl(H_j\,a(X+a+b)-H_{j-1}Xb\bigr)+R_{d,j,l}(X,a,b),
\]
where \(\gamma_{d,j,l}\ge0\) and \(R_{d,j,l}\) has nonnegative coefficients.
Thus the difficult part of the noncentral interior step is the boundary
endpoint coming from the old \(N_j=0\) constraint, together with the linear
condition \([c]\mathcal N<0\).

The folded central boundary has to be handled separately.  For \(d=2m\) and
\(j=m-2\), mirror symmetry reduces the old window to
\[
  X,\qquad X+a,\qquad X+a+b,
\]
and the old \(k=2\) condition becomes
\[
  a(X+a+b)\ge2Xb .
\]
After scaling \(X=1\), put \(s=a/X\) and \(r=b/X\).  The new central
numerator is a convex quadratic in \(r\).  Hence the central case reduces to
checking its value at the constraint boundary
\[
  r=\frac{s(1+s)}{2-s}\qquad(0\le s<2)
\]
and checking that, when the vertex lies in the feasible interval, the vertex
value is nonnegative.  Exact symbolic tests support this reduction in the
same range as the interior tests.

The boundary value in the last display has a uniform certificate.  Factor out
the top old eigenvalue power and write
\[
  x=\left(1-\frac{2}{m(m+1)}\right)^l,\qquad
  y=\left(1-\frac{6}{m(m+1)}\right)^l .
\]
Since \(1-6/(m(m+1))\le(1-2/(m(m+1)))^3\), we have \(y\le x^3\).  On the
boundary \(r=s(1+s)/(2-s)\), after clearing the positive denominator
\((2-s)^2\), the numerator is decreasing in
\[
  z=2-3x+y.
\]
Thus the worst case is \(y=x^3\).  With \(t=2-s\), the remaining numerator
factors as \((3-t)E_m(x,t)\) on \(0\le x\le1\), \(0\le t\le2\).  The
polynomial \(E_m(x,2T)\), in the rectangle \(0\le x,T\le1\), has
nonnegative Bernstein coefficients of bidegree \((4,3)\); the only zero
coefficients are harmless boundary coefficients, and the remaining
coefficients are positive for \(m\ge3\).  Hence the central boundary endpoint
is proved.  The only central subcase still requiring a scalar inequality is
the possible interior vertex of this convex quadratic.

This remaining central vertex also has a clean certificate.  Keep the same
normalization, divide by the top old eigenvalue power, and write
\[
  x=\left(1-\frac{2}{m(m+1)}\right)^l,\qquad
  y=\left(1-\frac{6}{m(m+1)}\right)^l .
\]
The three folded central update values are
\[
  U_0=\frac{m-2}{2m}y+\frac{m+2}{2m}x(1+s),
\]
\[
  U_1=\frac{m-1}{2m}x(1+s)+\frac{m+1}{2m}(1+s+r),
  \qquad
  U_2=1+s+r .
\]
The central numerator is
\[
  \widehat N=U_2(U_1-U_0)-3U_0(U_2-U_1).
\]
Since
\[
  \partial_y\widehat N
  =
  \frac{m-2}{4m^2}
  \left(3(m-1)x(1+s)-(5m-3)(1+s+r)\right)\le0,
\]
the worst case is again \(y=x^3\).

After setting \(y=x^3\), write
\[
  \widehat N=A r^2+B r+C,\qquad A=\frac{m+1}{2m}.
\]
The vertex value is nonnegative if and only if the discriminant is
nonpositive.  More precisely,
\[
  B^2-4AC=\frac{x^2(m-2)}{16m^4}P_m(x,s).
\]
Thus \(m=2\) is immediate, and for \(m\ge3\) it remains to prove
\(P_m(x,s)\le0\) in the feasible vertex region.

For \(0\le s<2\), put
\[
  r_b=\frac{s(1+s)}{2-s},\qquad
  G_m=-4m^2B,\qquad
  H_m=4m^2(2-s)\,\partial_r\widehat N(x,s,r_b).
\]
The vertex is feasible exactly when \(G_m\ge0\) and \(H_m\ge0\).  Direct
expansion gives the identity
\[
  -P_m(x,s)=2mH_m(x,s)+m(1-x)G_m(x,s)+R_m(x,s).
\]
With \(S=s/2\), the polynomial \(R_m(x,2S)\) has nonnegative Bernstein
coefficients in the basis \(B_i^4(x)B_j^2(S)\).  The coefficient matrix is
\[
\begin{pmatrix}
3(m^3+4m^2-7m+6) & 3(7m^3+16m^2-21m+18)
  & 9(11m^3+20m^2-21m+18)\\
(17m^3+71m^2-102m+72)/4 & 22m^3+55m^2-69m+54
  & 3(125m^3+227m^2-246m+216)/4\\
5m^3+13m^2-16m+12 & 22m^3+41m^2-47m+42
  & 3(29m^3+43m^2-46m+48)\\
3m(3m^2-4m+4) & (89m^3+11m^2+18m+72)/4
  & (155m^3+119m^2-102m+216)/2\\
0 & 4m(m^2+m+6) & 4(11m^3+8m^2+3m+18)
\end{pmatrix},
\]
whose entries are nonnegative for \(m\ge2\).  Hence \(-P_m\ge0\)
throughout the feasible central vertex region.

For \(s\ge2\), there is no upper boundary.  In this range
\[
  \partial_sP_m
  =
  6\left(-(5m^3+8m^2-7m+6)s
  +(m^3+12m^2-15m+6)x^2
  -5m^3-8m^2+7m-6\right)<0
\]
on \(0\le x\le1\), and the Bernstein coefficients of \(-P_m(x,2)\)
are
\[
\begin{gathered}
27(5m^3+8m^2-7m+6),\quad
27(5m^3+8m^2-7m+6),\\
12(11m^3+15m^2-12m+12),\quad
18(7m^3+6m^2-3m+6),\\
4(23m^3+20m^2+3m+18),
\end{gathered}
\]
all positive for \(m\ge2\).  Thus \(P_m(x,s)\le P_m(x,2)\le0\).
This closes the folded central \(k=2\) case.

Equivalently, before changing to increments one may write
\[
  u_{j-1}=a,\qquad u_j=b,\qquad u_{j+1}=c,\qquad u_{j+2}=e,
\]
and write the three new values as
\[
  W_j=Aa+Bb,\qquad W_{j+1}=Cb+Dc,\qquad W_{j+2}=Ec+Fe,
\]
with the same branch coefficients.  Then the same new numerator is
\[
  \mathcal N(e)
  =
  h_{j+1}W_{j+2}(W_{j+1}-W_j)
  -
  h_jW_j(W_{j+2}-W_{j+1}),
\]
which is affine in \(e\), with
\[
  [e]\mathcal N
  =
  F\bigl(h_{j+1}W_{j+1}-(h_j+h_{j+1})W_j\bigr).
\]
If this coefficient is nonnegative, the worst case is \(e=c\).  If the
coefficient is negative, the old \(k=2\) inequality at \(j\) bounds \(e\)
above; substituting the boundary value
\[
  e=
  \frac{H_jbc}{(H_j+H_{j+1})b-H_{j+1}c},
  \qquad H_i=\lambda_{d-1,i+1}-\lambda_{d-1,i},
\]
leaves an inequality in \(a,b,c\), to be proved using the old \(k=2\)
inequality at \(j-1\).  Random exact tests of this case split find no
counterexample in the first nontrivial ranges.  Thus a plausible proof of the
second divided-difference sign is now a finite algebraic lemma for this
two-branch map: reciprocal convexity on the old quadratic grid should be
preserved under the super-recurrence update.

This last sentence is false in the stated generality.  The two-branch update
does not preserve the local reciprocal-convexity cone defined only by the two
old \(k=2\) inequalities.  In the noncentral case \(d=32\), \(j=12\),
\(l=2\), with old gaps
\[
  H_{j-1}=\frac14,\qquad H_j=\frac{3}{16},\qquad
  H_{j+1}=\frac18,
\]
take normalized old values
\[
  u_{j-1}=\frac{497}{893},\qquad
  u_j=1,\qquad
  u_{j+1}=\frac{497}{200},\qquad
  u_{j+2}=\frac{497}{2}.
\]
Both old \(k=2\) inequalities are saturated, and the \(c\)-coefficient of the
new numerator is negative, but the saturated endpoint gives
\[
  \mathcal N
  =
  -\frac{1369701097696401953}{2636841484288000}<0 .
\]
Equivalently, the local reciprocal data \(\beta_i=1/u_i\) are affine in the
old spectral node \(\mu_i\), so all nonanchored higher divided differences of
\(\beta\) vanish.  The failure is therefore not repaired by assuming old
nonanchored complete monotonicity of \(\beta\).

The obstruction points to the sharper invariant found above.  For
\(h_i=\mu_i\beta_i=\mu_i/u_i\), the same example has a negative second
divided difference.  Thus the proof should be recentered on anchored
complete monotonicity of \(h=\mu\beta\), which implies the desired
complete monotonicity of \(\beta\) by the divided-difference product rule with
\(\mu^{-1}\).  The old beta-convexity local surface is only a necessary
shadow of the actual induction surface, not the right invariant.

The local form of this sharper invariant gives simple barriers.  On an old
row, write the old spectral nodes as
\[
  \nu_i=\lambda_{d-1,i},
\]
and normalize a four-point window by
\[
  w_j=1,\qquad
  r=\frac{w_{j-1}}{w_j},\qquad
  q=\frac{w_{j+1}}{w_j},\qquad
  e=\frac{w_{j+2}}{w_j}.
\]
For \(h_i=\nu_i/w_i\), the adjacent second divided-difference signs
\[
  [\nu_{j-1},\nu_j,\nu_{j+1}]h\ge0,\qquad
  [\nu_j,\nu_{j+1},\nu_{j+2}]h\ge0
\]
give, whenever the displayed denominators are positive,
\[
  q\le
  \frac{\nu_{j+1}}
  {\nu_j+
  \frac{\nu_{j+1}-\nu_j}{\nu_j-\nu_{j-1}}
  \left(\nu_j-\frac{\nu_{j-1}}{r}\right)}
\]
and
\[
  e\le
  \frac{\nu_{j+2}}
  {\frac{\nu_{j+1}}q+
  \frac{\nu_{j+2}-\nu_{j+1}}{\nu_{j+1}-\nu_j}
  \left(\frac{\nu_{j+1}}q-\nu_j\right)}.
\]
These bounds exactly exclude the artificial beta-convexity counterexample:
there \(r=497/893\), \(q=497/200\), \(e=497/2\), and the \(h\)-barriers give
\[
  q_{\max}=2.304857\ldots<2.485,\qquad
  e_{\max}=\frac{213}{4}<248.5.
\]
By contrast, the actual old row at \(d-1=31\), \(j=12\), \(l=2\) has
\[
  (r,q,e)\approx(0.481145,1.694679,2.386129),
\]
while the same barriers give
\[
  q_{\max}\approx4.27743,\qquad e_{\max}\approx3.05880.
\]
An exact screen of all local windows \(d\le50\), \(2\le l\le10\) supports the
full local \(h\)-complete-monotonicity packet through order three.  However,
this packet alone is still not the right abstract preservation surface.  There
is an exact affine-from-anchor counterexample at \(d=35\), \(j=13\), \(l=2\):
on the old nodes
\[
  \nu_{12}=\frac{299}{35},\qquad
  \nu_{13}=\frac{44}{5},\qquad
  \nu_{14}=9,\qquad
  \nu_{15}=\frac{64}{7},
\]
set
\[
  h(\nu)=1-\frac{1-1/1000}{\nu_{15}-1}(\nu-1),
  \qquad w_i=\frac{\nu_i}{h(\nu_i)} .
\]
Then old \(h\) is affine from the anchor, so its old second divided
differences vanish, and the local beta \(k=2\) numerators are positive.  But
the new \(h\)-convexity numerator after the two-branch update is
\[
  -\frac{2250221443203110862626374517}
  {47284010991951331136}<0.
\]
Thus \(h\)-complete monotonicity alone is insufficient.

There also appears to be an auxiliary ratio barrier:
\[
  w_i^2\ge w_{i-1}w_{i+1}.
\]
An exact screen for \(d\le30\), \(2\le l\le7\), over all internal first-half
windows verifies this log-concavity with positive margin.  This condition is
not a substitute for the \(h\)-complete-monotonicity packet, but it rules out
large last-ratio excursions of the kind in the affine counterexample.  In that
example the consecutive \(w\)-ratios are approximately
\[
  1.7847,\qquad 2.3773,\qquad 18.8204,
\]
so both local log-concavity inequalities fail.

A corrected local stress test supports the combined finite algebra lemma:
old local \(h\)-complete monotonicity through order three, together with
log-concavity of \(w\), should imply the new \(k=2\) sign for \(h\) after the
two-branch update.  Across \(d=6,\dotsc,79\), \(l\in\{2,3,5,10\}\), and all
noncentral first-half \(j\), \(1{,}842{,}037\) randomly sampled feasible local
packets produced no negative new \(h\)-convexity numerator.  This is only a
guide for the finite algebra lemma, not a proof.

There is now a much sharper exact certificate template.  Use ratio variables
\[
  A=\frac{w_j}{w_{j-1}},\qquad
  Y=\frac{w_j}{w_{j+1}},\qquad
  Z=\frac{w_j}{w_{j+2}} .
\]
Then the old \(h\)-values on the four-point window are linear:
\[
  \nu_{j-1}A,\qquad \nu_j,\qquad \nu_{j+1}Y,\qquad \nu_{j+2}Z.
\]
Let \(H_i=\nu_{i+1}-\nu_i\), and define
\[
  K_0=H_j(\nu_{j-1}A-\nu_j)
      -H_{j-1}(\nu_j-\nu_{j+1}Y),
\]
\[
  K_1=H_{j+1}(\nu_j-\nu_{j+1}Y)
      -H_j(\nu_{j+1}Y-\nu_{j+2}Z).
\]
The adjacent \(h\)-convexity signs are \(K_0\ge0\), \(K_1\ge0\), while the
third divided-difference sign is
\[
  K_0\ge
  \frac{H_{j-1}(H_{j-1}+H_j)}
       {H_{j+1}(H_j+H_{j+1})}K_1.
\]
Thus we may write
\[
  K_0=
  \frac{H_{j-1}(H_{j-1}+H_j)}
       {H_{j+1}(H_j+H_{j+1})}K_1+P,\qquad P\ge0,
\]
and solve linearly for \(A\).

In the present grid these constants have closed forms.  Since
\[
  \nu_i=\lambda_{d-1,i}=\frac{(i+1)(d-i)}d,
\]
we have
\[
  H_{j-1}=\frac{d-2j}{d},\qquad
  H_j=\frac{d-2j-2}{d},\qquad
  H_{j+1}=\frac{d-2j-4}{d},
\]
and therefore
\[
  \frac{H_{j-1}(H_{j-1}+H_j)}
       {H_{j+1}(H_j+H_{j+1})}
  =
  \frac{(d-2j)(d-2j-1)}
       {(d-2j-4)(d-2j-3)}.
\]

The log-concavity and monotonicity of \(w\) give
\[
  Y^2\le Z\le\frac{\nu_{j+1}}{\nu_{j+2}}Y,
  \qquad 0\le Y\le\frac{\nu_j}{\nu_{j+1}}.
\]
The lower bound from \(K_1\ge0\) is
\[
  Z\ge
  L(Y):=
  \frac{(H_j+H_{j+1})\nu_{j+1}Y-H_{j+1}\nu_j}
      {H_j\nu_{j+2}}.
\]
The curves \(Z=Y^2\) and \(Z=L(Y)\) meet at \(Y=1\) and at a smaller root
\(Y_0\).  Hence the feasible region splits into two rectangles after the
substitutions
\[
  0\le Y\le Y_0,\qquad
  Z=Y^2+S\left(\frac{\nu_{j+1}}{\nu_{j+2}}Y-Y^2\right),
\]
and
\[
  Y_0\le Y\le\frac{\nu_j}{\nu_{j+1}},\qquad
  Z=L(Y)+S\left(\frac{\nu_{j+1}}{\nu_{j+2}}Y-L(Y)\right),
\]
with \(0\le S\le1\).  In each piece, after using a Bernstein coordinate
\(T\) for \(Y\), the cleared new \(h\)-convexity numerator is linear in the
slack \(P\).  Exact checks through \(d\le35\), \(l\in\{2,3,5,10\}\), show
that both coefficients of \(P\) have nonnegative Bernstein coefficients in
\((T,S)\), in both pieces.  This is the first certificate that simultaneously
survives the beta-convexity and affine-\(h\) counterexamples.

The split endpoints also have closed forms:
\[
  Y_0=
  \frac{(d-j)(j+1)(d-2j-4)}
       {(j+3)(d-2j-2)(d-j-2)},
\]
\[
  \frac{\nu_j}{\nu_{j+1}}
  =
  \frac{(d-j)(j+1)}{(j+2)(d-j-1)},\qquad
  \frac{\nu_{j+1}}{\nu_{j+2}}
  =
  \frac{(j+2)(d-j-1)}{(j+3)(d-j-2)}.
\]
The check is now reproducible in
`working/super-recurrence-eulerian/local_h_certificate_probe.py`; running
`python3 working/super-recurrence-eulerian/local_h_certificate_probe.py screen
--d-max 35 --ells 2,3,5,10` verifies all \(1680\) certificate cases.
The same screen also passes for
\[
  l\in\{2,3,4,5,6,7,8,9,10,12,15,20\},
\]
giving \(5040\) exact certificate cases through \(d\le35\).  A separate
coefficientwise monotonicity screen suggests a possible reduction in the
power parameter: through \(d\le20\), every Bernstein coefficient in both
pieces is nondecreasing as \(l\) runs from \(2\) to \(10\).  Thus a plausible
uniform proof strategy is to prove the Bernstein coefficient signs at
\(l=2\), and then prove coefficientwise monotonicity in \(l\).
An extended screen through \(d\le25\) and \(2\le l\le20\) again finds
coefficientwise monotonicity in \(l\), over \(180\) window/piece families.
However, this monotonicity is not atomwise in the exponential products
\(\lambda_a^l\lambda_b^l\), and a simple Abel-summation test using sorted
product bases is too strong: it already fails in small high-piece controls.
Thus the monotonicity proof must use a more tailored grouping of the
exponential terms.
The useful form is to write
\[
  \nu_i=\lambda_{d-1,j-1+i}\qquad(0\le i\le3),
\]
\[
  R_i=\frac{\nu_{i+1}}{\nu_i},\qquad
  X=R_0^l,\quad Y=R_1^l,\quad Z=R_2^l .
\]
For each fixed Bernstein control \(B_l\), the forward difference has the form
\[
  B_{l+1}-B_l
  =
  \nu_0^{2l}\sum c_{abc}X^aY^bZ^c,
\]
with support contained in
\[
  (1,0,0),(1,1,0),(1,1,1),(2,0,0),
  (2,1,0),(2,1,1),(2,2,0),(2,2,1).
\]
Exact sign-pattern screens through \(d\le20\) show that the only negative
monomials in this eight-term catalogue are
\[
  XY,\qquad XYZ,\qquad X^2YZ.
\]
A broader catalogue audit through \(d\le25\), using both the first-difference
and second-difference modes, finds \(4410\) controls and \(8\) distinct support
patterns in each mode; the same three monomial classes are the only possible
negative ones.
The ratio data are special:
\[
  R_0>R_1>R_2>1.
\]
Indeed,
\[
  R_0-1=\frac{r+4}{j(j+r+5)},\quad
  R_1-1=\frac{r+2}{(j+1)(j+r+4)},\quad
  R_2-1=\frac{r}{(j+2)(j+r+3)},
\]
and
\[
  R_0-R_1=
  \frac{2j^2+2jr+10j+r^2+8r+16}
       {j(j+1)(j+r+4)(j+r+5)},
\]
\[
  R_1-R_2=
  \frac{2j^2+2jr+10j+r^2+6r+12}
       {(j+1)(j+2)(j+r+3)(j+r+4)} .
\]
However, the stronger-looking inequality \(R_0\ge R_1R_2\) is not uniform.
In fact
\[
  R_0-R_1R_2
  =
  \frac{
  -j^2r+2j^2-jr^2-3jr+10j+r^2+8r+16}
  {j(j+1)(j+r+4)(j+r+5)} ,
\]
so this difference is positive on the edge slices \(r=2\) and \(j=1\), but
can become negative deeper in the region.  Thus the ratio-block catalogue must
use the exact rational bases, not a generic cone such as \(X\ge YZ\).
Thus the monotonicity proof should be a finite ratio-block positivity
catalogue.  The hard top block has the typical shape
\[
  X^2YZ\left(
    aR_2^{-l}+b\left(\frac{R_1}{R_2}\right)^l+cR_1^l-n
  \right),
\]
possibly with lower-block help at small \(l\).  This is a finite collection of
one-variable exponential inequalities with explicit rational bases, rather
than a generic cone argument.
The probe script now exposes these catalogues via
`python3 working/super-recurrence-eulerian/local_h_certificate_probe.py
catalogue d j --mode diff`; the modes `base` and `convex` print the analogous
catalogues for \(B_l\) and for the second forward difference.

There is a substantial simplification in the ordered cone.  Write
\[
  Z=1+w,\qquad Y=Z+v,\qquad X=Y+u,
\]
so \(u,v,w\ge0\) encodes the generic order \(X\ge Y\ge Z\ge1\).  An ordered
cone audit through \(d\le25\) shows that all first-difference and
second-difference catalogues are coefficientwise nonnegative in \(u,v,w\),
except for four high-piece \(P^0\) boundary controls:
\[
  B(4,0),\qquad B(4,1),\qquad B(4,2),\qquad B(3,0).
\]
For these exceptional controls, the only negative ordered-cone coefficient is
very restricted: in first-difference mode the negative monomials are among
\[
  w,\qquad w^2,\qquad uw,
\]
and in second-difference mode they are among \(w\) and \(w^2\).  Thus the
monotonicity proof splits naturally: the ordered cone handles all generic
controls, and the four high-piece boundary controls require exact
Eulerian-ratio compensation.

There is also a useful convexity diagnostic.  Exact checks through \(d\le25\)
and \(2\le l\le11\) show
\[
  B_{l+2}-2B_{l+1}+B_l\ge0
\]
for every Bernstein control \(B_l\).  If this discrete convexity can be proved
uniformly, then monotonicity reduces to checking the first forward difference
\(B_3-B_2\).  This is not yet a proof, but it may give a smaller certificate
than proving \(B_{l+1}-B_l\ge0\) directly for all \(l\).
The script now has a reproducible command for this check:
`python3 working/super-recurrence-eulerian/local_h_certificate_probe.py
ell-convex --d-max 25 --ell-min 2 --ell-max 11`.

The ratio catalogue can be compressed further.  Across the \(49\) Bernstein
controls in each noncentral window, the first-difference and second-difference
catalogues use only eight support templates.  The possible negative monomials
are still only \(XY\), \(XYZ\), and \(X^2YZ\), and the extra \(XY\) sign has a
simple split:
\[
  r=d-2j-4,\qquad [XY]F_l<0
  \quad\Longleftrightarrow\quad
  [XY]F_l\ne0\text{ and }j\ge r+2 .
\]
This rule was checked exactly through \(d\le35\) in both first-difference and
second-difference modes.  The probe now exposes this information with
`catalogue-summary` and `xy-condition`; for example,
`local_h_certificate_probe.py xy-condition --d-max 35 --mode diff` verifies
the sign split.

A better monotonicity normalization was found.  Let
\[
  F_l=\nu_0^{-2l}(B_{l+1}-B_l)
       =\sum c_{abc}X^aY^bZ^c
\]
for a fixed Bernstein control, where \(X=R_0^l\), \(Y=R_1^l\), and
\(Z=R_2^l\).  Instead of normalizing by the largest negative monomial
\(X^2YZ\), normalize by the monomial \(X^2Y=(R_0^2R_1)^l\).  Then
\[
\begin{aligned}
  \frac{F_l}{X^2Y}
  ={}& \frac{c_{100}}{XY}+\frac{c_{110}}{X}
      +c_{111}\frac ZX+\frac{c_{200}}Y+c_{210}\\
     &+c_{211}Z+c_{220}Y+c_{221}YZ .
\end{aligned}
\]
Equivalently, this is an exponential sum in the fixed bases
\((R_0R_1)^{-1}\), \(R_0^{-1}\), \(R_2/R_0\), \(R_1^{-1}\), \(1\),
\(R_2\), \(R_1\), and \(R_1R_2\).  These bases separate into decaying terms,
one constant term, and the three growing bases \(R_2<R_1<R_1R_2\).  Exact
screening through \(d\le30\) and \(2\le l\le24\) shows that this normalized
expression is minimized at \(l=2\) for every one of the \(7056\) checked
controls.  The same is true for the alternative normalization by \(XYZ\), and
also for the shorter normalization by \(X^2\) in the same screen.  The latter
backup is not obviously simpler for a proof, because it introduces the base
\(R_1R_2/R_0\), whose comparison with \(1\) changes sign in the noncentral
region.  By contrast, the seemingly natural normalization by \(X^2YZ\) is
false as a one-dip monotonicity statement: for
example, a high-piece \(P^1\) \(B(3,0)\) control at \(d=22,j=8\) still
decreases from \(l=3\) to \(l=4\), and the observed minimum for this
normalization can occur as late as \(l=5\) in the same screen.  Thus the
current preferred monotonicity target is:
\[
  \frac{F_2}{X_2^2Y_2}\ge0,\qquad
  \frac{F_{l+1}}{X_{l+1}^2Y_{l+1}}
  \ge
  \frac{F_l}{X_l^2Y_l}
  \qquad(l\ge2),
\]
together with the already proved \(B_2\ge0\) base certificate for the controls
themselves.  The first inequality is the base first-difference
\(B_3-B_2\ge0\), not the same statement as \(B_2\ge0\).
Simple coefficient absorptions such as
\([X^2Y^2]F_l+[X^2YZ]F_l\ge0\) or
\([X^2Y^2]F_l+[X^2Y^2Z]F_l+[X^2YZ]F_l\ge0\) fail in many windows, so the
remaining proof still has to use the exact Eulerian ratio gaps, not only the
coefficient signs.

There is an even sharper diagnostic.  Put
\[
  G_l=\frac{F_l}{X^2Y}.
\]
The probe command `normalized-increment-min` checks the first increments
\(G_{l+1}-G_l\).  Through \(d\le30\) and \(2\le l\le24\), all \(7056\)
checked controls have their minimum increment at \(l=2\), and no negative
increment occurs.  Thus the remaining monotonicity proof can be split into
three statements:
\[
  G_2\ge0,\qquad
  G_3-G_2\ge0,\qquad
  G_{l+2}-2G_{l+1}+G_l\ge0\quad(l\ge2).
\]
The normalized increment has only nine sign/support templates.  Its negative
relative bases are among
\[
  (XY)^{-1},\qquad X^{-1},\qquad Y^{-1},\qquad Z,
\]
while the positive terms include \(Z/X\), \(Y\), and \(YZ\).  The growing
block with bases \(Z,Y,YZ\) is already nonnegative at \(l=2\) for every
checked control, and after factoring \(Z^l\) it is increasing because
\(Y/Z=R_1/R_2>1\) and \(YZ/Z=R_1>1\).  The generic block
``negative decays + growing block'' is nonnegative except for the already
known high-piece top edge
\[
  P^0 B(4,0),\qquad P^0 B(4,1),\qquad P^0 B(4,2).
\]
Those three controls have identical catalogues in the checked range and are
now the only remaining exceptional family for the first normalized-increment
block split.

For normalized convexity, the second difference
\[
  K_l=G_{l+2}-2G_{l+1}+G_l
\]
has coefficients \(c(q-1)^2\) in the relative bases \(q\).  A cleaner
allocation was found.  The positive \(YZ\)-term dominates the negative
\(Z\)-term at \(l=2\) for every checked control, and this dominance improves
for larger \(l\), since \((YZ)/Z=Y>1\).  After removing this pair, all
remaining negative terms are contained in the five-term block
\[
  A_l+D_l+F_l-B_l-C_l,
\]
where the bases are
\[
  A=(XY)^{-1},\qquad B=X^{-1},\qquad C=Z/X,\qquad
  D=Y^{-1},\qquad F=Y,
\]
with the corresponding catalogue coefficients attached.  Exact screening
through \(d\le30\) and \(2\le l\le24\) finds this five-term block
nonnegative in all \(7056\) controls.  Its minimum is not always at \(l=2\);
for the high-piece top edge it drifts outward as \(j\) grows.  Thus the
remaining symbolic convexity problem has been reduced to a single
coefficient-decorated exponential inequality of the form
\[
  aA^l+dD^l+fF^l\ge bB^l+cC^l,\qquad l\ge2,
\]
where \(A<B\), \(B<C\), and \(F>1\), while the relative order of \(C\) and
\(D\) is governed by the sign-changing ratio \(R_1R_2/R_0\).
The command
`local_h_certificate_probe.py normalized-obligations --d-max 30 --ell-min 2
--ell-max 24` reproduces the current finite screen for \(G_2\), \(G_3-G_2\),
the \(YZ\)-versus-\(Z\) pair, and this five-term residual block.
A tempting shortcut is to use the reciprocal pair \(D^l\) and
\(F^l=D^{-l}\), but this is too weak.  Exact screening through \(d\le35\)
shows that even the sufficient inequality obtained from
\[
  dD^l+fF^l\ge2\sqrt{df}
\]
after adding the \(aA^2\) contribution fails in \(798\) of \(10290\) controls.
Thus the final argument needs to use the actual five-term coefficient
structure rather than a coefficient-blind AM--GM bound.

The useful structure is obtained by factoring out \(D^l\).  Since
\[
  A=BD,\qquad C=D\frac{R_1R_2}{R_0},\qquad F=D\,R_1^2,
\]
the five-term block is \(D^l\) times
\[
  S_l
  =
  d+aR_0^{-l}+fR_1^{2l}
  -b\left(\frac{R_1}{R_0}\right)^l
  -c\left(\frac{R_1R_2}{R_0}\right)^l .
\]
The pair
\[
  fR_1^{2l}
  -c\left(\frac{R_1R_2}{R_0}\right)^l
\]
is increasing in \(l\) in the exact screens, and \(R_1^2>
R_1R_2/R_0\) follows from \(R_0R_1>R_2\).  It is tempting to freeze this
surplus at \(l=2\) and prove the three-term inequality
\[
  D_0+aR_0^{-l}
  \ge b\left(\frac{R_1}{R_0}\right)^l,\qquad
  D_0=d+fR_1^4-c\left(\frac{R_1R_2}{R_0}\right)^2.
\]
This gives a useful but ultimately insufficient one-dip test.  Its continuous
minimum is explicit:
for \(p=R_0^{-1}\) and \(u=R_1/R_0\), the critical point satisfies
\[
  \left(\frac up\right)^l
  =
  \frac{a|\log p|}{b|\log u|}.
\]
A high-precision continuous-minimum screen through \(d\le40\) found no
negative minima among \(14161\) controls; the largest observed critical point
was near \(l=296\) on the high-piece \(P^0B(4,0)\) top edge.  This explains
the drifting finite minima.  The following elementary envelope explains why
the shortcut works for this initial range.  Put
\[
  q=\frac pu,\qquad A=\frac ab.
\]
Then the only possible loss is
\[
  b u^l-a p^l = b u^l(1-Aq^l).
\]
If \(b=0\), there is nothing to prove.  If \(D_0\ge b u^2\), then
\[
  D_0+a p^l-bu^l\ge D_0-bu^l\ge D_0-bu^2\ge0
\]
for all \(l\ge2\).  The remaining cases are covered by a logarithm-free
square-root certificate.  If \(a\ge b>0\), \(p\ge u^3\), and
\[
  27aD_0^2\ge4b^3,
\]
then \(D_0+a p^l\ge b u^l\) for all \(l\ge2\).  Indeed, writing
\(u=q^\gamma\), the inequality \(p=uq\ge u^3\) gives \(\gamma\ge1/2\).  Since
\(A\ge1\), the maximum of \(t^\gamma(1-At)\) for \(0\le t\le1\) is at most
the \(\gamma=1/2\) maximum, namely \(2/(3\sqrt{3A})\).  Thus
\[
  bu^l(1-Aq^l)\le \frac{2b}{3\sqrt{3A}},
\]
and the displayed rational inequality is exactly the square of
\(D_0\ge 2b/(3\sqrt{3A})\).

The exact classifier
`local_h_certificate_probe.py normalized-onedip-classify --d-max 40`
checks this route on the same range: among \(14161\) controls, \(5780\) have
\(b=0\), \(8331\) satisfy \(D_0\ge bu^2\), and the remaining \(50\) satisfy
the square-root certificate.

However this frozen-surplus shortcut is false in general.  Running
`local_h_certificate_probe.py normalized-onedip --d-max 60 --precision 80`
finds \(15\) failures; the first is
\[
  d=50,\quad j=22,\quad \text{low }P^0B(5,0),\quad
  l\approx339.282,
\]
where the frozen one-dip value is about \(-2.43\cdot10^{10}\).  At the same
point the live five-term block is positive.  For example
`local_h_certificate_probe.py normalized-five-term-dump 50 22 339 high 0 0,0`
shows a frozen value about \(-6.39\cdot10^{14}\) but a live five-term value
about \(6.37\cdot10^{17}\).  Thus the final proof must keep the increasing
surplus
\[
  fR_1^{2l}-c\left(\frac{R_1R_2}{R_0}\right)^l
\]
live; freezing it at \(l=2\) loses the main compensation on the boundary
families.
The command
`local_h_certificate_probe.py normalized-onedip --d-max 40 --precision 80`
reproduces the older continuous-minimum diagnostic.

There is a clean live replacement.  To avoid overloading the dimension, write
the constant coefficient in \(S_l\) as \(\delta\), so
\[
  S_l=\delta+a p^l+fw^l-bu^l-cv^l,
  \qquad
  p=\frac1{R_0},\quad
  u=\frac{R_1}{R_0},\quad
  v=\frac{R_1R_2}{R_0},\quad
  w=R_1^2 .
\]
Let \(q=p/u=1/R_1\) and
\[
  D_0=\delta+fw^2-cv^2.
\]
Define
\[
  m=
  \begin{cases}
    fw^2(w-1), & v\le1,\\
    fw^2(w-1)-cv^2(v-1), & v\ge1 .
  \end{cases}
\]
For \(v\le1\), Bernoulli gives
\[
  fw^l-cv^l\ge fw^2-cv^2+(l-2)fw^2(w-1).
\]
For \(v\ge1\), the same linear lower bound holds with the second value of
\(m\), provided \(m\ge0\), since \(w/v>1\) makes the successive increments at
least \(m\).  Thus it is enough to prove
\[
  D_0+a p^l-bu^l+(l-2)m\ge0.
\]
This follows from the following rational alternatives:
\[
  b=0,\quad D_0\ge0,\quad m\ge0;
\]
\[
  D_0\ge bu^2,\quad m\ge0;
\]
or
\[
  a\ge b,\qquad m\ge b(1-q),\qquad D_0\ge2b(1-q).
\]
Indeed, in the last case
\[
  bu^l-a p^l
  =u^l(b-aq^l)
  \le b(1-q^l)
  \le l\,b(1-q)
  \le D_0+(l-2)m.
\]
The exact command
`local_h_certificate_probe.py normalized-live-linear-classify --d-max 60`
checks \(35721\) controls: \(14580\) satisfy \(b=0\), \(20981\) satisfy
\(D_0\ge bu^2\), and the remaining \(160\) satisfy the live-linear
certificate; no control has \(m<0\), and there are no hard cases.  The
live-linear cases are concentrated on \(P^0\) boundary controls, mostly
\(r=2\), with a few \(r=3\) top-edge controls entering by \(d=50\).
This live-linear certificate is not yet the final all-parameter proof: on the
\(r=2\) slice, for instance, the residual \(D_0-2b(1-q)\) eventually becomes
negative for low \(P^0B(5,0)\) and high \(P^0B(0,0)\).  It is best viewed as
a finite and midrange certificate, not the asymptotic mechanism.

The apparent large-parameter mechanism is a more general live envelope.  Again
put \(q=R_1\) and \(y=q^l\).  From
\[
  p=\frac1{R_0}=1-\frac{r+4}{(j+1)(j+r+4)},\qquad
  q=R_1=1+\frac{r+2}{(j+1)(j+r+4)},
\]
we have \(pq^2\ge1\), while weighted AM--GM gives
\[
  p^{r+2}q^{r+4}\le1.
\]
Moreover \(R_2\le R_0\), so \(v=R_1R_2/R_0\le q\), and \(w=R_1^2=q^2\).
Therefore
\[
  p^l\ge y^{-2},\qquad
  u^l=(pq)^l\le y^{-2/(r+2)},\qquad
  v^l\le y,\qquad
  w^l=y^2.
\]
Thus
\[
  S_l\ge
  \delta+a y^{-2}+f y^2-b y^{-2/(r+2)}-cy .
\]
Equivalently, with \(t=y^{1/(r+2)}\), it is enough to prove
\[
  f t^{4r+8}-c t^{3r+6}+\delta t^{2r+4}
  -b t^{2r+2}+a\ge0,\qquad t\ge1.
\]
This is the current large-parameter target.  It stays strongly positive in
the large-\(j\) top-edge cases where the live-linear certificate fails.

For a complementary view of the \(r=2\) boundary, which is exactly
where the frozen failures occur, set
\[
  N=(j+1)(j+6),\qquad q=R_1=1+\frac4N,\qquad y=q^l .
\]
Then
\[
  p=R_0^{-1}=1-\frac6N,\qquad
  v=\frac{R_1R_2}{R_0}=1-\frac{36}{N^2},\qquad
  w=R_1^2=q^2 .
\]
For \(j\ge2\) we have \(p q^2\ge1\), while weighted AM--GM gives
\(p^4q^6\le1\).  Hence, for \(l\ge2\),
\[
  p^l\ge y^{-2},\qquad p^l\le y^{-3/2},\qquad v^l\le1.
\]
Consequently the live block satisfies the lower bound
\[
  S_l
  \ge
  d-c+a y^{-2}+f y^2-b y^{-1/2}.
\]
Writing \(z=\sqrt y\), this becomes
\[
  E(z)=d-c+a z^{-4}+f z^4-bz^{-1},\qquad z\ge1.
\]
Moreover \(E'(z)z^5=4fz^8+bz^3-4a\), so \(E\) has at most one critical
point on \([1,\infty)\).  Thus the hard \(r=2\) boundary reduces to a
one-minimum algebraic inequality.  A high-precision screen of this envelope on
the full \(r=2\) catalogue through \(j\le120\) found no failures.  The
asymptotic envelopes for the observed boundary families have positive
margins; for example the proportional high \(P^0B(0,0)\) and low \(P^0B(5,0)\)
families tend to
\[
  y^2+\frac32y^{-2}-\frac23y^{-1/2}-\frac32+\frac5{12},
\]
whose minimum on \(y\ge1\) is positive.

The useful template form is slightly sharper than the first coarse
ratio bounds.  We should bound \(K=(c-\delta)/f\) directly, rather than
bounding \(c/f\) and \(\delta/f\) separately.  For the proportional pair
\[
  \text{low }P^0B(5,0),\qquad \text{high }P^0B(0,0),
\]
the template, now proved symbolically for \(j\ge17\), is
\[
  \frac af\ge1,\qquad \frac bf\le\frac23,\qquad
  \frac{c-\delta}{f}\le\frac{117}{100}.
\]
It gives the elementary lower bound
\[
  \frac{E(z)}f
  \ge
  z^4+z^{-4}-\frac23z^{-1}-\frac{117}{100}
  \ge
  2-\frac23-\frac{117}{100}
  =
  \frac{49}{300}.
\]
There are also three actual high-piece interior controls with separate
templates:
\[
\begin{array}{c|ccc|c}
  \text{control} & a/f & b/f & (c-\delta)/f & j\text{-range}\\
  \hline
  P^0B(1,0) & \ge1 & \le1 & \le1 & j\ge10\\
  P^0B(2,0) & \ge2 & \le6/5 & \le1 & j\ge13\\
  P^0B(3,0) & \ge3 & \le5/3 & \le1 & j\ge10 .
\end{array}
\]
With \(x=1/z\), the corresponding lower envelopes become
\[
  1+x^8-x^5-x^4,\qquad
  1+2x^8-\frac65x^5-x^4,\qquad
  1+3x^8-\frac53x^5-x^4 .
\]
These are nonnegative on \(0\le x\le1\): the first two have nonnegative
degree-\(8\) Bernstein coefficients
\[
  1,1,1,1,\frac{69}{70},\frac{51}{56},\frac{19}{28},\frac18,0
\]
and
\[
  1,1,1,1,\frac{69}{70},\frac{127}{140},\frac{23}{35},\frac1{20},\frac45,
\]
while the third has nonnegative degree-\(9\) Bernstein coefficients
\[
  1,1,1,1,\frac{125}{126},\frac{179}{189},
  \frac{101}{126},\frac49,\frac1{27},\frac43.
\]
The proportional pair itself also has a direct certificate valid for all
\(j\ge1\), not only the ratio-template range \(j\ge17\).  Together with two
additional controls that enter the live-linear fallback at larger \(j\), the
directly certified \(r=2\) controls are
\[
  \text{low }P^0B(5,0),\quad \text{high }P^0B(0,0),\quad
  \text{high }P^0B(3,1),\quad \text{low }P^0B(4,0).
\]
the actual lower envelope
\[
  1-Kx^4-Bx^5+Ax^8,\qquad
  A=\frac af,\quad B=\frac bf,\quad K=\frac{c-\delta}{f},
\]
has all degree-\(8\) Bernstein coefficients nonnegative after the shift
\(j=J+1\).  This is checked symbolically by
`local_h_certificate_probe.py r2-envelope-symbolic`, without replacing these
coefficients by coarser constants.
For the hard high-piece top edge
\[
  \text{high }P^0B(4,0),\quad
  \text{high }P^0B(4,1),\quad
  \text{high }P^0B(4,2),
\]
the template, now proved symbolically for \(j\ge7\), is
\[
  \frac af\ge4,\qquad \frac bf\le\frac52,\qquad
  \frac{c-\delta}{f}\le1.
\]
Thus
\[
  \frac{E(z)}f
  \ge
  z^4+4z^{-4}-\frac52z^{-1}-1.
\]
With \(x=1/z\), positivity on \(z\ge1\) is equivalent to positivity of
\[
  1-x^4-\frac52x^5+4x^8
  \qquad (0\le x\le1).
\]
In degree \(11\), its Bernstein coefficients are
\[
  1,1,1,1,\frac{329}{330},\frac{905}{924},
  \frac{71}{77},\frac{103}{132},\frac{28}{55},
  \frac{17}{110},\frac1{11},\frac32,
\]
so this one-variable inequality is proved.  The exact rational command
`local_h_certificate_probe.py r2-envelope-template --j-max 120` verifies the
expanded ratio templates through \(j\le120\): \(111\) \(B(1,0)\) controls,
\(108\) \(B(2,0)\) controls, \(111\) \(B(3,0)\) controls, \(342\) top-edge
controls, \(208\) proportional-pair controls, and no failures.  The stronger
command
`local_h_certificate_probe.py r2-envelope-symbolic` proves these templates
uniformly by extracting the relevant Bernstein controls and checking shifted
positive coefficients in \(j\), and also proves the direct Bernstein-envelope
families above.  A coverage screen through \(d\le55\) found \(124\)
live-linear fallback controls, all \(124\) accounted for by these \(r=2\)
certificates or by the noncentral high-edge split.  Thus the \(r=2\) boundary
families are reduced to the already covered finite ranges below these
thresholds, together with the live-linear midrange certificate.

The noncentral range has a useful two-parameter form.  Write
\[
  d=2j+r+4,\qquad j\ge1,\qquad r\ge2.
\]
Then
\[
  H_{j-1}=\frac{r+4}{d},\qquad
  H_j=\frac{r+2}{d},\qquad
  H_{j+1}=\frac rd,
\]
and
\[
  \alpha=\frac{(r+4)(r+3)}{r(r+1)}.
\]
The split constants become
\[
  Y_0=
  \frac{(j+r+4)(j+1)r}
       {(j+3)(r+2)(j+r+2)},\qquad
  Y_{\max}=
  \frac{(j+r+4)(j+1)}
       {(j+2)(j+r+3)},
\]
and
\[
  U=\frac{\nu_{j+1}}{\nu_{j+2}}
  =
  \frac{(j+2)(j+r+3)}
       {(j+3)(j+r+2)} .
\]
Moreover,
\[
  Y_{\max}-Y_0
  =
  \frac{(j+1)(j+r+4)D}
       {(j+2)(j+3)(r+2)(j+r+2)(j+r+3)},
\]
where
\[
  D=2j^2+2jr+10j+r^2+6r+12.
\]
On the high piece, with
\[
  Y=Y_0+T(Y_{\max}-Y_0),
\]
the vertical width also factors positively:
\[
  UY-L(Y)
  =
  \frac{r(1-T)(j+1)(j+r+4)D}
       {(j+3)^2(r+2)^2(j+r+2)^2}.
\]
This is the preferred coordinate system for the remaining algebra.

The shared interlacing notes are useful here mainly as a warning: this
last step should not be forced through transitivity of weak proper position
or through a generic PF cone.  The proof surface is a certificate for the
actual boundary controls in the finite common-cone/ratio catalogue.  For the
noncentral live envelope, put
\[
  A=\frac af,\qquad C=\frac cf,\qquad L=\frac{b-\delta}{f}.
\]
The high-piece top-edge controls \(P^0B(4,0)\), \(P^0B(4,1)\), and
\(P^0B(4,2)\) are again identical on the relevant boundary face.  The
general live envelope gives the lower bound
\[
  x^4-Cx^3-Lx^2+A,\qquad x\ge1,
\]
after using \(t^{2r+2}\le t^{2r+4}=x^2\) when \(b\ge0\).  A direct
symbolic boundary-face extraction gives the clean global bounds
\[
  C\le\frac85,\qquad L\le\frac12
  \qquad (r\ge3,\ j\ge1).
\]
The naive stronger inequalities \(c\le f\) and \(\delta\ge b\) are false
asymptotically; for example on the proportional \(r=3\) boundary,
\(c/f\) eventually exceeds \(1\) and \((\delta-b)/f\) becomes negative.
Thus the noncentral proof needs the full four-term envelope, not the
simpler \(x^4-x^3\) certificate.

The high-edge split is now closed.  The command
`local_h_certificate_probe.py noncentral-high-edge-symbolic` verifies, by
shifted positive coefficients, that
\[
  C\le\frac85,\qquad L\le\frac12,\qquad
  r\ge j\Rightarrow L\le0,\qquad
  j\ge r\Rightarrow A-4\ge4L .
\]
Hence \(L>0\) forces \(j>r\), and then \(A\ge4+4L>4\).  In this branch the
proved bounds give
\[
  x^4-\frac85x^3-\frac12x^2+4>0
  \qquad (x\ge1).
\]
Indeed, the only critical point in \([1,\infty)\) is
\[
  x=\frac{6+\sqrt{61}}{10},
\]
and the value there is
\[
  \frac{32319}{10000}-\frac{61\sqrt{61}}{625}>0
\]
(squaring reduces the last inequality to \(986410625>0\)).  Thus the
\(L>0\) branch of the noncentral high-edge envelope is closed.

For the \(L\le0\) branch, the term \(-Lx^2\) is nonnegative, so it remains
to prove
\[
  x^4-Cx^3+A\ge0,\qquad x\ge1 .
\]
The same symbolic command verifies the additional inequalities
\[
  C\le\frac43\quad(r\ge4),\qquad
  A+1-C\ge0\quad(r\ge3),\qquad
  A\ge1\quad(r=3,\ j\ge4).
\]
For \(r=3\) and \(j=1,2,3\), it checks directly that
\[
  \frac43-C\in
  \left\{
    \frac{55708}{50421},
    \frac{24649489}{33816576},
    \frac{5444}{10875}
  \right\}.
\]
If \(C\le4/3\), then the derivative \(4x^3-3Cx^2\) is nonnegative for
\(x\ge1\), so the minimum is at \(x=1\), where the value is
\(A+1-C\ge0\).  The only remaining cases have \(r=3\) and \(j\ge4\);
there \(A\ge1\) and \(C\le8/5\), hence
\[
  A\ge1>\frac{432}{625}
  =\frac{27}{256}\left(\frac85\right)^4
  \ge \frac{27}{256}C^4.
\]
Minimizing \(x^4-Cx^3\) now gives \(x^4-Cx^3+A>0\) on \(x\ge1\).
Thus the \(L\le0\) branch is also closed, and the noncentral high-edge
boundary controls \(P^0B(4,k)\), \(k=0,1,2\), are proved.

The fixed-\(r\) asymptotic ratios support exactly this split:
\[
  A\to
  \frac{4(r+3)^3}{(r+1)(r+2)^2},\qquad
  \frac bf\to\frac{(r+4)^2}{(r+2)^2},\qquad
  C\to\frac{32}{(r+1)(r+2)},\qquad
  \frac\delta f\to\frac{r+3}{r+1}.
\]

A first symbolic check in this coordinate system was encouraging: on both
one-parameter boundary slices \(r=2\) and \(j=1\), every Bernstein control
numerator has nonnegative coefficients in the remaining positive parameter.
The full \(l=2\) symbolic certificate now proves the corresponding
two-variable statement.  Clear the same positive denominator as in
`working/super-recurrence-eulerian/local_h_certificate_probe.py` and orient the
numerator by the interior sample used there.  Then every Bernstein control
numerator lies in \(\mathbb Z_{\ge0}[j,r]\).  The counts are exactly the
controls from the full certificate:
\[
  \text{low piece: }18+8,\qquad
  \text{high piece: }15+8,
\]
where the two summands are the \(P^0\)- and \(P^1\)-coefficients.  Thus the
finite \(d\)-screen has been removed from the \(l=2\) base; the remaining task
is the coefficientwise monotonicity in \(l\).

A side symbolic extraction identifies the likely hardest \(l=2\) controls.
After removing elementary positive factors, these controls become residual
polynomials with strictly positive integer coefficients:
\[
  B_{\mathrm{low},P^0,(5,0)}
  \sim_+
  2(j+3)(r+1)^2(r+3)(j+r+4) R_{19,15},
\]
\[
  B_{\mathrm{low},P^1,(3,0)}
  \sim_+
  (j+3)^2(r+1)^2(r+2)(j+r+2)(2j+r+4)^2 R_{16,13},
\]
\[
  B_{\mathrm{low},P^1,(2,0)}
  \sim_+
  \frac{(j+3)^2(r+1)(r+2)^3(j+r+2)^2(2j+r+4)^2}{3}
  R_{15,11},
\]
\[
  B_{\mathrm{high},P^0,(4,0)}
  \sim_+
  2(r+1)(r+2)^2(r+3)(j+r+4)R_{12,7},
\]
and
\[
  B_{\mathrm{high},P^1,(3,0)}
  \sim_+
  (r+1)(2j+r+4)^2 R_{15,9}.
\]
Here \(R_{a,b}\) denotes a polynomial of \(j\)-degree \(a\) and \(r\)-degree
\(b\) with positive coefficients.  The residuals above have respectively
\(331,347,348,146,\) and \(166\) monomials.  Finite minima through \(d\le35\)
come from the same boundary Bernstein controls: low \(P^0\) at \((5,0)\),
high \(P^0\) at \((4,0)\), low \(P^1\) mostly at \((3,0)\) with a central
switch to \((2,0)\), and high \(P^1\) mostly at \((0,0)\) with a small-\(j\)
switch to \((3,0)\).  This suggests proving the full set of controls by
mechanical positive-coefficient residuals, with these five families as the
audit cases.

The \(l=2\) base certificate is now fully checked in this symbolic form.  After
the same denominator clearing and orientation as in the probe, all \(18\)
low-piece Bernstein controls of the \(P^0\)-coefficient and all \(8\) controls
of the low-piece \(P^1\)-coefficient have numerators in
\(\mathbb Z_{\ge0}[j,r]\).  In the low \(P^1\) run, the eight numerator
polynomials have total degree \(30\) and \(418\)--\(420\) monomial terms each.
The high-piece \(P^1\)-coefficient is also checked: its eight controls have
total degree \(35\) and \(529\)--\(559\) monomial terms, all nonnegative.
Finally, the high-piece \(P^0\)-coefficient has \(15\) controls, each with
total degree \(34\) or \(35\) and \(509\)--\(560\) monomial terms, all
nonnegative.  Thus, for \(l=2\), the two-piece local \(h\)-certificate is
proved by positive-coefficient residuals.  The remaining proof task is the
coefficientwise monotonicity in \(l\), for which the ratio-block catalogue
above is the current route.

### Current Local-\(h\) Monotonicity Kernel

After the crash-recovery audit, the local \(h\)-certificate should not be
expanded again as raw rational functions.  The finite symbolic screens and the
current proof split point to the following smaller kernel.  For each Bernstein
control, write
\[
  F_l=\nu_0^{-2l}(B_{l+1}-B_l)
      =\sum c_{abc}X^aY^bZ^c,\qquad
  G_l=\frac{F_l}{X^2Y},
\]
where \(X=R_0^l\), \(Y=R_1^l\), and \(Z=R_2^l\).  It is enough to prove
\[
  G_2\ge0,\qquad G_3-G_2\ge0,\qquad
  G_{l+2}-2G_{l+1}+G_l\ge0\quad(l\ge2).
\]
The first two inequalities are finite symbolic base checks in the ratio
catalogue.  The last one is the normalized convexity statement.  After the
positive \(YZ\)-term is paired with the negative \(Z\)-term, the only live
residual is the five-term inequality
\[
  aA^l+dD^l+fF^l\ge bB^l+cC^l,
\]
with
\[
  A=(XY)^{-1},\quad B=X^{-1},\quad C=Z/X,\quad
  D=Y^{-1},\quad F=Y.
\]
Equivalently, after factoring out \(D^l\), this is
\[
  \delta+aR_0^{-l}+fR_1^{2l}
  -b\left(\frac{R_1}{R_0}\right)^l
  -c\left(\frac{R_1R_2}{R_0}\right)^l\ge0.
\]

The recovery reruns support exactly this split:
`normalized-min --d-max 24 --ell-min 2 --ell-max 16 --normalization 2,1,0`
and `normalized-increment-min --d-max 24 --ell-min 2 --ell-max 16
--normalization 2,1,0` both put every minimum at \(l=2\), while
`normalized-obligations --d-max 24 --ell-min 2 --ell-max 16` has no failures
for \(G_2\), \(G_3-G_2\), the \(YZ\)-versus-\(Z\) convexity pair, or the
five-term residual.  The same audit rechecked the two symbolic boundary
closures: `r2-envelope-symbolic` and `noncentral-high-edge-symbolic` both have
no failures.  A small live-linear run through \(d\le20\) is entirely covered by
the easy cases \(b=0\) and \(D_0\ge bu^2\), which confirms that live-linear is
a midrange certificate rather than the final large-parameter proof.

Thus the next proof pass should prove normalized convexity of \(G_l\) in the
ratio catalogue, not the raw monotonicity of \(B_l\).  The non-exceptional
catalogue terms should be handled by the ordered cone
\[
  Z=1+w,\qquad Y=Z+v,\qquad X=Y+u,
\]
where the coefficients are already nonnegative.  The exceptional high-piece
\(P^0\) boundary controls are precisely the families already covered by the
\(r=2\) envelope and the noncentral high-edge envelope.  What remains to make
this a proof is a uniform statement that this ordered-cone plus boundary
envelope split exhausts every coefficient in the normalized convexity
catalogue.

A direct finite test of the first part of this exhaustion statement now also
passes.  Clearing the Laurent powers in the normalized convexity catalogue by
the positive monomial \(XY\), then substituting
\[
  Z=1+w,\qquad Y=1+w+v,\qquad X=1+w+v+u,
\]
gives coefficientwise nonnegative polynomials in \(u,v,w\) for all \(3136\)
controls with \(d\le22\).  The extended audit through \(d\le30\) checks all
\(7056\) controls in the same range as `normalized-obligations` and again has
no failures:
`ORDERED-NORMALIZED-CONVEXITY checked=7056 d<=30 failures=0`.  The ordered
polynomials have at most \(23\) monomials and total degree at most \(4\) in
\(u,v,w\).  This is stronger than the older ordered-cone screen for the raw
catalogues, because it tests the actual normalized convexity expression
\(G_{l+2}-2G_{l+1}+G_l\).  A support profile through \(d\le18\) shows that the
global ordered support is exactly
\[
\begin{gathered}
1,w,w^2,w^3,w^4,\quad
v,vw,vw^2,vw^3,\quad
v^2,v^2w,v^2w^2,\quad
v^3,v^3w,\\
u,uw,uw^2,uw^3,\quad
uv,uvw,uvw^2,\quad
uv^2,uv^2w.
\end{gathered}
\]
Thus the ordered substitution gives a small fixed support after the \(XY\)
clearing.  This is useful as a diagnostic, but it is not yet a \(23\)-case
proof: each Bernstein control still has its own rational coefficient on these
monomials.  The next proof pass should look for a common positive
factorization or a structural reason for the ordered coefficients to be
nonnegative, rather than expanding all of them by hand.

A separate dominance proof gives a possible induction surface for this moment
claim.  Put
\[
  w_{d,i}=\frac{q_{d,i}^{(l)}}{\binom di},
  \qquad L=\lambda_{d,i},
  \qquad A=\lambda_{d-1,i},
  \qquad B=\lambda_{d-1,i-1},
  \qquad p=\frac{d-i}{d}.
\]
Then
\[
  w_{d,i}
  =
  pA^l w_{d-1,i}+(1-p)B^l w_{d-1,i-1}.
\]
For the dominance defect \(E_{d,i}=w_{d,i}-L^l\), this becomes
\[
\begin{aligned}
  E_{d,i}
  ={}&pA^lE_{d-1,i}+(1-p)B^lE_{d-1,i-1}\\
     &+\bigl(pA^{2l}+(1-p)B^{2l}-L^l\bigr).
\end{aligned}
\]
Consequently
\[
  \mu_i^{-l}-\beta_i
  =
  \frac{E_{d,i}}{w_{d,i}L^l}.
\]
The exact probe also finds alternating divided differences for this defect
sequence, in both \(\mu_i\) and \(\log\mu_i\), through the same range.  This
is useful evidence for the stronger inverse-power moment picture, but the
reciprocal form of \(\beta_i=1/(L^l+E_{d,i})\) makes the defect recurrence a
less direct proof surface than the augmented \(Y\)-minor formulation above.

There is also a combinatorial way to see what \(w_{d,i}\) measures.  Let
\[
  \mathcal B_{d,i}
  =
  \{B\subseteq[d+1]:1\in B,\ |B|=i+1\},
  \qquad N_{d,i}=\binom di,
\]
and let \(c_{d+1}(B)\) be the block-leader product weight from the first
section.  The block-leader formula gives
\[
  q_{d,i}^{(l)}
  =
  \frac{1}{N_{d,i}^l}
  \sum_{B\in\mathcal B_{d,i}} c_{d+1}(B)^l .
\]
Hence
\[
  w_{d,i}
  =
  \frac1{N_{d,i}}
  \sum_{B\in\mathcal B_{d,i}}
  \left(\frac{c_{d+1}(B)}{N_{d,i}}\right)^l,
  \qquad
  \beta_i=\frac1{w_{d,i}}.
\]
Thus the stronger moment-cone theorem is a statement about reciprocal
moments of the explicit random variable \(c_{d+1}(B)/\binom di\), with
\(B\) uniform among block-leader sets of size \(i+1\).  A possible proof route
is to show that these reciprocal moments are log-completely-monotone in the
spectral node \(\lambda_{d,i}\), perhaps by a coupling or total-positivity
property of the block-leader product distribution as \(i\) varies.
The most direct versions of this idea fail.  The natural coupling obtained by
adding one block leader is not conditionally monotone: at \(d=4\), \(i=1\),
and \(B=\{1,2\}\), the normalized weight is \(2\), while averaging over the
possible insertions gives \(11/6\).  The fixed-size block-leader distribution
kernel is not TP2/MLR; for \(d=5\), comparing sizes \(i=1,2\) and the
normalized weights \(27/10<16/5\), the mass minor is \(-2/25\).  Even the
\(k=2\) beta-convexity numerator, expanded as a signed exponential sum in
\(l\) over products of block-leader weights, is not atomwise positive after
grouping equal bases.  These obstructions do not disprove the beta
complete-monotonicity statement, but they show that a proof from the
block-leader formula must use cancellation rather than a pointwise coupling
or standard stochastic-order argument.

The probe also checks the needed \(k=0\) coupled packet \(\{B_s\}\) directly;
it is compatible for
\[
  d\le14,\qquad 2\le l\le5 .
\]
The directed order is supplied separately by coefficient-ratio inequalities,
\[
  \lambda^{t-s}
  \le
  \frac{[z^0]B_t}{[z^0]B_s}
  \le
  \frac{[z^1]B_t}{[z^1]B_s}
  \le\dotsb,
  \qquad 0\le s<t\le l,
\]
with the usual zero conventions.  This formulation uses no transitivity of
weak proper position; it proves all finite-orbit pencils directly.

The \(\tau\)-inequality has a useful elementary lower bound.  If
\[
  U(z)=u_0\prod_i(1+\alpha_i z)
\]
is PF and \(R=\sum_i\alpha_i=u_1/u_0\), then at
\(z=-1/(2R)\) we get
\[
  -zU(z)
  =
  \frac{u_0}{2R}
  \prod_i\left(1-\frac{\alpha_i}{2R}\right)
  \ge
  \frac{u_0}{2R}\left(1-\frac12\right)
  =
  \frac{u_0^2}{4u_1}.
\]
Thus
\[
  \tau(U)\ge\frac{u_0^2}{4u_1}.
\]
For the \(k=0\) packet, \(a=\lambda=1\).  Hence a sufficient condition for
all conic sums is
\[
  \left(\sum_s c_sx_s\right)^2
  \ge
  4\left(\sum_s c_s\right)\left(\sum_s c_sy_s\right),
  \qquad
  x_s=[z^0]B_s,\quad y_s=[z^1]B_s .
\]
The pairwise coefficient inequalities
\[
  x_s^2\ge4y_s,\qquad
  x_sx_t\ge2(y_s+y_t)
  \quad(s<t)
\]
imply this copositivity condition by expansion.  The probe verifies these
exact inequalities for \(4\le d\le30\), \(2\le l\le8\); a focused ad hoc run
also passed through \(d\le40\), \(2\le l\le8\).  This reduces the analytic
part of the attachment proof to a first-two-coefficient inequality for the
coupled \(B_s\)-packet.

This inequality has a compact spectral-coordinate form.  Write the first two
nontrivial spectral coordinates of the actual row as \(A\) and \(B\), so that
the first two coefficients of the actual orbit are
\[
  [z]F_s=A\alpha^s-d,
  \qquad
  [z^2]F_s=
  \frac{d(d-3)}2-(d-2)A\alpha^s+B\delta^s,
\]
where
\[
  \alpha=\frac{2d}{d+1},\qquad
  \delta=\frac{3(d-1)}{d+1}.
\]
Since \(F_s=1+zB_s\), these are exactly \(x_s=[z^0]B_s\) and
\(y_s=[z^1]B_s\).  Therefore the diagonal and pairwise first-two inequalities
become
\[
  A^2\alpha^{2s}+2A(d-4)\alpha^s
  -4B\delta^s-d^2+6d\ge0
\]
and
\[
  A^2\alpha^{s+t}
  +A(d-4)(\alpha^s+\alpha^t)
  -2B(\delta^s+\delta^t)-d^2+6d\ge0 .
\]
Thus the tau part of the proof has been reduced to showing that the first
spectral coordinate dominates the second strongly enough along the two
geometric progressions \(\alpha^s\) and \(\delta^s\).
In the exact checks, the smallest defect in these inequalities always occurs
in the diagonal base case \(l=2\), \(s=0\).  Thus a plausible final route for
the tau part is to prove monotonicity in \(l\) and in the orbit indices, and
then verify only this base spectral-coordinate inequality.  The probe now
checks this minimum-at-base statement for \(4\le d\le30\), \(2\le l\le8\).

For the diagonal defects, monotonicity in \(s\) has a simple sufficient
condition.  Since
\[
  \alpha^2-\delta
  =
  \frac{d^2+3}{(d+1)^2}>0,
\]
we have
\[
\begin{aligned}
  D_{s+1}-D_s
  ={}&A^2\alpha^{2s}(\alpha^2-1)
     +2A(d-4)\alpha^s(\alpha-1)\\
     &-4B\delta^s(\delta-1).
\end{aligned}
\]
Thus \(D_{s+1}\ge D_s\) follows from
\[
  \frac{A^2}{B}
  \ge
  \frac{4(\delta-1)}{\alpha^2-1}
  =
  \frac{8(d-2)(d+1)}{(3d+1)(d-1)} .
\]
The checked minimum of \(A^2/B\) occurs at \(l=2\), and even there it is far
larger than the right-hand side.  The pairwise defects require a similar but
slightly sharper comparison, because \(\delta>\alpha\), so their monotonicity
must use the growth of \(A^2/B\) with \(l\).

For the pairwise defects, comparison with the base defect gives
\[
\begin{aligned}
  P_{s,t}-D_0
  ={}&A^2(\alpha^{s+t}-1)
     +A(d-4)(\alpha^s+\alpha^t-2)\\
     &-2B(\delta^s+\delta^t-2).
\end{aligned}
\]
Thus it is enough to prove
\[
  \frac{A^2}{B}
  \ge
  \frac{2(\delta^s+\delta^t-2)}{\alpha^{s+t}-1}
  \qquad(0\le s<t\le l).
\]
The right-hand side is maximised at \((s,t)=(0,l)\), so a sufficient single
inequality is
\[
  \frac{A^2}{B}
  \ge
  \frac{2(\delta^l-1)}{\alpha^l-1}.
\]
This maximisation is elementary and needs only \(1<\alpha<\delta\).  Put
\[
  R_n=\frac{\delta^n-1}{\alpha^n-1}.
\]
The quotients \(R_n\) increase with \(n\); for instance, after writing both
numerator and denominator as geometric sums, \(R_n\) is a weighted average of
the increasing ratios \((\delta/\alpha)^i\).  Hence for
\(0\le s<t\le l\),
\[
  \delta^s+\delta^t-2
  =
  (\delta^s-1)+(\delta^t-1)
  \le
  R_l\bigl((\alpha^s-1)+(\alpha^t-1)\bigr).
\]
Moreover
\[
  \alpha^{s+t}-1
  \ge
  (\alpha^s-1)+(\alpha^t-1).
\]
Therefore
\[
  \frac{2(\delta^s+\delta^t-2)}{\alpha^{s+t}-1}
  \le
  2R_l
  =
  \frac{2(\delta^l-1)}{\alpha^l-1},
\]
as claimed.

The remaining inequality has a direct exponential-sum route.  From the
first-coefficient
recurrence,
\[
  A=\sum_{j=1}^d\left(\frac{2^{d-j}j}{d}\right)^l .
\]
The two largest bases are both \(2^{d-1}/d\).  Similarly, \(B\) is a sum over
\(1\le j<m\le d\) with bases
\[
  \frac{3^{d-m}2^{m-1-j}j(m-1)}{\binom d2},
\]
and the largest base is
\[
  \frac{8\cdot3^{d-3}}{d(d-1)},
\]
attained, for example, at \((m,j)=(3,1),(3,2),(4,1),(4,2)\).  Hence
\[
  \frac{A^2}{B}
  \ge
  \frac{4}{\binom d2}
  \left(
    \frac{2^{2d-5}(d-1)}{d\,3^{d-3}}
  \right)^l .
\]
For \(d\ge6\), this lower bound is already larger at \(l=2\) than
\[
  \frac{2(\delta^2-1)}{\alpha^2-1}
  =
  \frac{8(d-2)(2d-1)}{(d-1)(3d+1)},
\]
Indeed the ratio is
\[
  \frac{2^{4d-7}3^{6-2d}(d-1)^2(3d+1)}
       {8d^3(d-2)(2d-1)},
\]
which is already \(>1\) at \(d=6\), and its successive ratio is \(>1\) for
\(d\ge6\).  Since
\[
  \frac{2^{2d-5}(d-1)}{d\,3^{d-3}}
  >
  \frac{\delta}{\alpha}
\]
for \(d\ge6\), the inequality then propagates to all \(l\ge2\).  The
remaining cases \(d=4,5\) are small: \(d=4\) follows from the explicit
relation \(B=2A-2\), since \(A/2>2^l>2(9/8)^l\); for \(d=5\), the exact
\(l=2\) value is
\[
  \frac{A^2}{B}=\frac{44402}{4761}>\frac{27}{8}
  =
  \frac{2(\delta^2-1)}{\alpha^2-1},
\]
and for \(l\ge3\) the bound
\[
  \frac{A^2}{B}
  \ge
  \frac25\left(\frac{128}{45}\right)^l
  >
  2\left(\frac65\right)^l
  >
  \frac{2(\delta^l-1)}{\alpha^l-1}
\]
applies.

The base inequality is now explicit.  The first two spectral coordinates are
particularly simple: if \(E_{d,i}^{(l)}\) denotes the \(i\)-th coefficient of
the unnormalised row, then
\[
  A=\frac{E_{d,1}^{(l)}}{d^l},
  \qquad
  B=\frac{E_{d,2}^{(l)}}{\binom d2^l}.
\]
Indeed, for a palindromic polynomial \(Q(t)=\sum_iq_it^i\), the first gamma
coefficients are \(q_0\), \(q_1-dq_0\), and
\[
  q_2-\binom d2q_0-(d-2)(q_1-dq_0),
\]
while the first spectral basis vectors have gamma beginnings
\[
  P_{d,0}=1-dz+\frac{d(d-3)}2z^2+\dotsb,\quad
  P_{d,1}=z-(d-2)z^2+\dotsb,\quad
  P_{d,2}=z^2+\dotsb .
\]
Since the normalisation divides by \(q_0\), the first two spectral
coordinates are \(q_1/q_0\) and \(q_2/q_0\), which are the displayed
normalised row coefficients.

For \(l=2\), set \(r_d=E_{d,1}^{(2)}\) and \(p_d=E_{d,2}^{(2)}\).  The row
recurrence gives
\[
  r_d=4r_{d-1}+d^2,\qquad
  p_d=9p_{d-1}+(d-1)^2r_{d-1},
\]
with \(r_1=1\) and \(p_1=0\).  Hence
\[
  r_d=\frac{20\cdot4^d-9d^2-24d-20}{27},
\]
and
\[
\begin{aligned}
  p_d={}&\frac{1}{2764800}\bigl(
  692793\cdot9^d
  -409600\cdot4^dd^2
  -655360\cdot4^dd\\
  &\hspace{4em}
  -851968\cdot4^d
  +115200d^4+364800d^3\\
  &\hspace{4em}
  +479200d^2+314200d+159175
  \bigr).
\end{aligned}
\]
Substituting \(A=r_d/d^2\) and
\[
  B=\frac{p_d}{\binom d2^2}
\]
into the base defect
\[
  A^2+2A(d-4)-4B-d^2+6d
\]
gives \(N_d/(4665600d^4(d-1)^2)\).  After collecting powers, the numerator is
\[
\begin{aligned}
N_d={}&2560000\cdot16^d(d-1)^2
      +4^dP(d)
      -18705411\cdot9^dd^2
      +R(d),
\end{aligned}
\]
where
\[
\begin{aligned}
P(d)={}&6912000d^5-32716800d^4+78366720d^3\\
       &+219136d^2+4096000d-5120000
\end{aligned}
\]
is positive for \(d\ge1\), and \(R(d)\ge-4665600d^8\) for \(d\ge4\).
Moreover,
\[
  2560000\cdot16^d(d-1)^2
  -18705411\cdot9^dd^2
  -4665600d^8>0
\]
for all \(d\ge5\): at \(d=5\) the left side is
\[
  13513777606525>0,
\]
the ratio of the \(16^d(d-1)^2\) term to the \(9^dd^2\) term is already
larger than \(3/2\) and increases with \(d\), and
\(16^d(d-1)^2/d^8\) is increasing for \(d\ge5\).  The remaining case
\(d=4\) gives defect \(841/16>0\).  Thus the \(l=2,s=0\) base defect is
proved for all \(d\ge4\).

The coefficient-side pattern that appears to survive is complete monotonicity
of adjacent tail ratios.  If
\[
  H_{d,k}^{(l)}(z)=\sum_i b_i z^i
\]
after trimming trailing zero coefficients, set \(r_i=b_{i+1}/b_i\).  Exact
checks in the probe find
\[
  (-1)^j\Delta^jr_i\ge0
\]
for all valid \(i,j\), throughout \(d\le30\), \(2\le l\le8\).  A wider
high-precision scan found no failures through \(d\le60\), \(2\le l\le8\).
This is stronger than ordinary log-concavity, but it does not imply that the
tail itself is PF; the \((21,2,5)\) tail above is the first numerical
obstruction found.  Thus the next concrete problem is to connect this
complete-monotone ratio cone to the threshold inequality
\[
  a\sum_s c_s\lambda^s
  \le
  \tau\left(\sum_s c_sB_s\right).
\]

The first local model also shows what kind of cone is needed.  For the
residual operator \(N=M_5+\frac43I\) and a quadratic
\[
  g=1+Sz+Pz^2,
\]
the alternation of \(g\) with \(Ng\) is controlled by the resultant factor
\[
  9P^2-2PS^2+28PS+100P-6S^3-21S^2\le0.
\]
The simple sufficient inequality \(P\le S^2/5\) makes this expression
nonpositive term by term.  The actual quadratic tails checked so far satisfy
this margin with room.  This suggests that the right induction cone should be
an attachability cone controlled by strengthened adjacent-ratio inequalities,
rather than a PF cone of the tails themselves.

The same constant \(1/5\) persists in the symbolic odd-dimensional quadratic
model.  Let \(D=2m+1\), \(m\ge2\), and
\[
  N_m=M_D+\frac{m+2}{m+1}I.
\]
For \(g=1+Sz+Pz^2\), direct calculation gives
\[
\begin{aligned}
  \frac{(m+1)^2}{P}\operatorname{Res}_z(g,N_mg)
  ={}&(2m-1)^2P^2-m(m-1)PS^2\\
     &+4(4m^2-5m+1)PS+(8m-6)^2P\\
     &-m(4m-5)S^3-(16m^2-24m+5)S^2 .
\end{aligned}
\]
As a quadratic in \(P\), the maximum on \(0\le P\le S^2/5\) occurs at an
endpoint.  At \(P=0\) it is negative, and at \(P=S^2/5\) it becomes
\[
 -\frac{S^2}{25}\left(
  (m^2-m-1)S^2+5(4m^2-5m-4)S
  +5(16m^2-24m-11)
 \right),
\]
which is nonpositive for \(m\ge2\).  Thus \(P\le S^2/5\) is a uniform
sufficient condition for the first quadratic tail alternation test.  The next
step is to identify the higher-degree analogue of this strengthened
log-concavity condition.

This tail refinement is more selective than two tempting broader statements.
First, raw spectral prefixes are not the right packets: already at \(d=9\),
\(l=2\), the first spectral prefix is
\[
  P_0=1-9z+27z^2-30z^3+9z^4,
\]
which is outside the nonnegative gamma cone.  Second, the abstract self-step
claim
\[
  f\text{ gamma-PF}\quad\Longrightarrow\quad f\ll M_df
\]
is false.  For \(d=4\), \(f=(1+z)^2\) gives
\[
  M_4f=1+\frac{28}{5}z+\frac{13}{5}z^2,
\]
and polynomial-tools reports that \(f\) and \(M_4f\) do not weakly interlace.
Low gamma prefixes are also too small for all-gap statements: for \(d=9\),
\[
  M_9^2(1)=1+\frac{504}{25}z+\frac{756}{25}z^2,
\]
so the constant prefix cannot interlace its second iterate.  Thus the current
best recurrence target is the actual-row gamma-tail cone, not arbitrary PF
polynomials and not low prefixes.

As a representative exact check in the new cone, for \(d=9\), \(l=2\), the
first nontrivial tail is
\[
  T_{9,1}^{(2)}
  =
  \frac{z}{15876}
  (151854872z^3+1590806268z^2+876900717z+37909536).
\]
The pair \(T_{9,1}^{(2)}, M_9^2T_{9,1}^{(2)}\) is verified by
polynomial-tools to weakly interlace, and the script checks the directed
coefficient-ratio orientation.  This is a better next proof route than another
quartic discriminant expansion: prove that the recurrence preserves this
tail-separated cone, then take \(k=0\).

Another tempting shortcut is also false.  One might try to prove compatibility
of the finite orbit by applying the finite Borcea--Branden symbol criterion to
\[
  \mathcal S_{d,l}(y,z)
  =
  \sum_{s=0}^l \binom ls M_d^sF_d^{(l)}(z)y^{l-s}.
\]
This symbol is not stable in general.  Already for \(l=2\) and \(d=2\),
\[
  9\mathcal S_{2,2}(y,z)
  =(12y+14)z+9(y+1)^2.
\]
Taking \(y=-31/30+i/60\), the unique \(z\)-root is
\[
  -\frac1{260}+\frac{7}{1040}i,
\]
which lies in the upper half-plane.  Thus the finite-symbol PF-preserver route
is too strong; the proof must use the local adjacent-chain induction rather
than a full orbit-preservation theorem.

The Wronskian observations are now only parked evidence.  For reference, if
\[
  W_{n,l}(z)
  =
  G_{n-1}^{(l)'}(z)G_n^{(l)}(z)
  -
  G_{n-1}^{(l)}(z)G_n^{(l)'}(z),
\]
then a real-line sign would also imply interlacing.  We do not use this as
the main route.

## Exact Evidence

The Rust probe uses exact integer arithmetic and the `polynomial-tools`
weak-interlacing checks.  The polynomial lab contains the detailed checked
ranges and commands.  The useful records for the proved consecutive-row route
are:

- `binomial_kernel_interlaces_linear_diagonal_kernel`;
- `binomial_kernel_interlaces_shifted_linear_diagonal_kernel`;
- `binomial_power_kernel_interlaces_diagonal_kernel`;
- `binomial_power_kernel_interlaces_shifted_diagonal_kernel`;
- `row_interlaces_boundary_left_summand`;
- `row_interlaces_boundary_right_summand`;
- `boundary_summands_imply_consecutive_row_interlacing`;
- `consecutive_row_interlacing_hadamard_summand_proof_2026_06_04`.

The useful records for the stronger gamma-refinement route are:

- `normalized_gamma_interlacing_checked_2026_06_04`;
- `normalized_gamma_partial_iterate_chain_checked_2026_06_04`;
- `adjacent_partial_iterate_chains_checked_2026_06_04`;
- `normalized_gamma_partial_iterate_recurrence`;
- `normalized_gamma_partial_iterate_chain_interlacing`;
- `adjacent_partial_iterate_chains_compatible`;
- `adjacent_partial_iterate_chain_local_induction_step`;
- `adjacent_local_step_proves_adjacent_chain_compatibility`;
- `partial_iterate_chain_local_induction_step`;
- `local_induction_step_proves_partial_iterate_chain`;
- `partial_iterate_chain_implies_normalized_gamma_interlacing`;
- `gamma_bidiagonal_operator_spectral_decomposition`;
- `gamma_spectral_basis_branching_rule`;
- `normalized_gamma_lifted_diagonal_orbit`;
- `gamma_operator_dimension_shift_interlacing`;
- `gamma_operator_preserves_proper_position`;
- `dimension_shift_and_preserver_imply_adjacent_local_step`;
- `gamma_operator_preserves_pf_positive_cone_compatibility`;
- `pf_proper_position_coefficient_ratios_monotone`;
- `positive_cone_and_coefficient_ratios_prove_gamma_operator_preserver`;
- `false_weak_proper_position_transitivity_shortcut`;
- `partial_iterate_root_sign_inequality`;
- `root_sign_and_dimension_shift_imply_adjacent_local_step`;
- `gamma_operator_preserves_one_positive_root_class`;
- `one_positive_preserver_implies_gamma_operator_proper_position_preserver`;
- `normalized_row_central_factor_parity`;
- `normalized_gamma_positive_spectral_coordinates`;
- `positive_spectral_coordinates_imply_partial_iterate_chain`;
- `d4_actual_internal_orbit_interlacing`;
- `d4_actual_internal_orbit_certificate_2026_06_05`;
- `d4_scalar_windows_imply_d4_internal_orbit`;
- `d5_actual_internal_orbit_interlacing`;
- `d5_actual_internal_orbit_certificate_2026_06_05`;
- `d5_quadratic_certificate_implies_d5_internal_orbit`;
- `d6_actual_internal_orbit_interlacing`;
- `d6_actual_internal_orbit_cubic_certificate_2026_06_05`;
- `d6_large_region_discriminant_reduction_2026_06_05`;
- `d6_T_R_region_bounds_proof_2026_06_05`;
- `d6_K_region_bound_proof_2026_06_05`;
- `d6_region_bounds_imply_large_l_discriminant`;
- `d6_large_region_orientation_proof_2026_06_05`;
- `d6_region_bounds_imply_large_l_orientation`;
- `d6_finite_l_2_to_5_exact_certificate_2026_06_05`;
- `d6_large_region_and_finite_certificate_imply_d6_internal_orbit`;
- `prove_d6_cubic_certificate`;
- `prove_d6_region_bounds_l_ge_6`;
- `d7_actual_internal_orbit_interlacing`;
- `d7_actual_internal_orbit_cubic_probe_2026_06_05`;
- `d7_large_region_discriminant_orientation_reduction_2026_06_05`;
- `d7_T_R_region_bounds_proof_2026_06_05`;
- `d7_K_region_bound_reduction_2026_06_05`;
- `d7_K_region_bound_proof_2026_06_05`;
- `d7_region_bounds_imply_large_l_internal_orbit`;
- `d7_finite_l_2_to_4_exact_certificate_2026_06_05`;
- `d7_large_region_and_finite_certificate_imply_d7_internal_orbit`;
- `prove_d7_cubic_certificate`;
- `prove_d7_region_bounds_l_ge_5`;
- `false_finite_borcea_branden_orbit_symbol_stability`;
- `false_gamma_operator_full_symbol_stability`;
- `prove_partial_iterate_chain_by_interlacing_induction`.

The first few \(l=3\) rows match the source:
\[
E_3^{(3)}(t)=1+16t+t^2,
\qquad
E_4^{(3)}(t)=1+155t+155t^2+t^3.
\]

The same probe now checks the cumulative last-leader prefix chain.  Define
\[
P_{n,m}^{(l)}(t)=
\sum_{\substack{B\subseteq[n]\\1\in B,\ \max B\le m}}
  c_n(B)^l t^{|B|-1}.
\]
The checked strengthening is
\[
P_{n,m-1}^{(l)}(t)\ll P_{n,m}^{(l)}(t),
\qquad 2\le m\le n.
\]
This holds in the same exact ranges:

- \(l=2,\dotsc,6\), \(n\le14\);
- \(l=7\), \(n\le12\).

The prefix polynomials have the closed form
\[
P_{n,m}^{(l)}(t)=(\theta+1)^{l(n-m)}E_m^{(l)}(t),
\]
because after the last block leader all later positions must choose from the
existing image.

## Endpoint Reciprocal Reduction

Let
\[
A_n^{(l)}(t)=(\theta+1)^lE_n^{(l)}(t).
\]
Since \(E_n^{(l)}\) is palindromic of degree \(n-1\), the new-block-leader
summand in \(E_{n+1}^{(l)}\) is the shifted reciprocal
\[
t^nA_n^{(l)}(1/t).
\]
Thus
\[
E_{n+1}^{(l)}(t)
  =A_n^{(l)}(t)+t^nA_n^{(l)}(1/t).
\]
The Hadamard cone route below proves the stronger endpoint statement
\[
A_n^{(l)}(t)\ll t^nA_n^{(l)}(1/t).
\]
This implies the boundary lemma
\[
A_n^{(l)}(t)\ll E_{n+1}^{(l)}(t)
\]
by the interlacing cone property.

This is exactly the \(\mathbb I_n\)-interlacing condition used in the
Chow-polynomial/TN-matrix literature: for \(I_n(f)=t^nf(1/t)\),
\[
\mathbb I_n=\{f\in\mathbb R_{\ge0}[t]\colon f\ll I_n(f)\}.
\]
Thus the endpoint target is simply
\[
A_n^{(l)}\in\mathbb I_n.
\]
The Chow-Eulerian framework proves preservation of related
\(\mathbb I_n\)-interlacing sequences under certain TN-matrix recurrences.
Our recurrence is not yet identified as an instance of that theorem, but the
language and cone lemmas are directly relevant.

In root language, if
\[
A_n^{(l)}(t)=C\prod_{i=1}^{n-1}(t+\rho_i),
\qquad 0<\rho_1\le\dotsb\le\rho_{n-1},
\]
then the reciprocal statement says that the roots of \(A_n^{(l)}\) interlace
the roots \(0,-1/\rho_{n-1},\dotsc,-1/\rho_1\).  Equivalently, the useful
root inequalities are
\[
\rho_i\rho_{n-i}<1<\rho_{i+1}\rho_{n-i}
\]
for the admissible indices, with the second inequality omitted at the last
endpoint.  This is a concrete analytic form of the endpoint lemma.

### Wronskian Form of the Endpoint

Let
\[
R_n^{(l)}(t)=t^nA_n^{(l)}(1/t).
\]
With the orientation used here, the endpoint relation
\[
A_n^{(l)}\ll R_n^{(l)}
\]
has Wronskian
\[
W_n^{(l)}(t)
  =\frac{d}{dt}A_n^{(l)}(t)\,R_n^{(l)}(t)
   -A_n^{(l)}(t)\,\frac{d}{dt}R_n^{(l)}(t).
\]
The Rust probe checks a more arithmetic-looking invariant: every coefficient
of \(W_n^{(l)}(t)\) is nonpositive.  This holds in the same exact ranges as
the endpoint reciprocal check:

- \(l=2,\dotsc,6\), \(n\le14\);
- \(l=7\), \(n\le12\).

This coefficientwise Wronskian sign should not be treated as a complete proof
of interlacing by itself, since proper position is a global statement on the
real line.  It does, however, turn the endpoint into an explicit coefficient
inequality problem.

Write
\[
E_n^{(l)}(t)=\sum_{i=0}^{n-1}e_i t^i,
\qquad e_i=e_{n-1-i}.
\]
Then
\[
A_n^{(l)}(t)=\sum_{i=0}^{n-1}(i+1)^l e_i t^i
\]
and
\[
R_n^{(l)}(t)=\sum_{i=0}^{n-1}(i+1)^l e_i t^{n-i}.
\]
The coefficient of \(t^m\) in \(W_n^{(l)}\) is
\[
C_m=
\sum_i
(2i-m-1)(i+1)^l(n-m+i)^l e_i e_{m-i},
\]
where the sum is over the valid indices.  Pairing \(i<j=m-i\), the paired
contribution is
\[
\left(
  -(j-i+1)(i+1)^l(n-j)^l
  +(j-i-1)(j+1)^l(n-i)^l
\right)e_i e_j,
\]
with a negative diagonal term when \(i=j\).  The paired coefficient can be
positive for arbitrary \(i,j\), so a proof must use special inequalities
satisfied by the row coefficients \(e_i\), presumably coming from the
block-leader product formula or a hidden total-positivity structure.

### Audit of the Wronskian Route

The coefficientwise Wronskian sign is a useful invariant, but it is not by
itself an endpoint-interlacing criterion.  For example,
\[
  A(t)=10+91t+9t^2,\qquad R(t)=t^3A(1/t)=9t+91t^2+10t^3
\]
are both real-rooted, and
\[
  A'(t)R(t)-A(t)R'(t)
  =-90-1820t-8500t^2-1820t^3-90t^4
\]
has all coefficients nonpositive.  Nevertheless exact interlacing checks give
\[
  A\not\ll R.
\]
Thus the Wronskian coefficient sign should be treated as a supporting
coefficient inequality, not as the reciprocal boundary lemma.

There is, however, a clean route to proving the coefficient sign itself.  Let
\(d=n-1\), put
\[
  b_i=\binom di^l,\qquad q_i=e_i/b_i,
\]
and write \(j=m-i\).  The normalized row \(q_i\) satisfies
\[
  q_{n,k}
  =
  \left(\frac{(k+1)(n-1-k)}{n-1}\right)^l q_{n-1,k}
  +
  \left(\frac{k(n-k)}{n-1}\right)^l q_{n-1,k-1}.
\]
Equivalently, if \(Q_n(t)=\sum_k q_{n,k}t^k\), then
\[
  Q_n(t)
  =
  (1+t)
  \left(\frac{(\theta+1)(n-1-\theta)}{n-1}\right)^l
  Q_{n-1}(t).
\]
As proved in the Hadamard normalization section, \(Q_n\) has only nonpositive
real roots.  As a weaker consequence, \(q_i\) is log-concave.  Hence, for fixed
\(m\), the products
\[
  q_iq_{m-i}
\]
increase as \(i\) moves inward toward \(m/2\).

The remaining coefficient calculation is independent of the row.  For \(i<j\),
define the off-diagonal baseline term
\[
  S_i^{(m)}
  =
  \left(
    -(j-i+1)(i+1)^l(n-j)^l
    +(j-i-1)(j+1)^l(n-i)^l
  \right)b_ib_j,
  \qquad j=m-i .
\]
If \(i=j\), the diagonal term is instead
\[
  S_i^{(m)}=-(i+1)^l(n-i)^l b_i^2.
\]
The suffix sums of the \(S_i^{(m)}\), ordered by increasing \(i\le j\), are
nonpositive.  Indeed, the positive part of the \(i\)-term is dominated by the
negative part of the \((i+1)\)-term, since for \(i+1<j\),
\[
  (j+1)(n-i)\binom di\binom dj
  \le
  (i+2)(n-j+1)\binom d{i+1}\binom d{j-1}.
\]
This inequality follows by dividing the right side by the left side:
\[
  \frac{(i+2)j}{(i+1)(j+1)}
  \cdot
  \frac{(n-j+1)(n-1-i)}{(n-j)(n-i)}
  \ge 1.
\]
Summation by parts with the increasing weights \(q_iq_{m-i}\) then gives
\[
  [t^m]\bigl(A'R-AR'\bigr)\le 0.
\]
This proves the observed coefficientwise Wronskian sign using the normalized
real-rootedness/log-concavity lemma for \(Q_n\).

The endpoint statement is therefore sharper than the Wronskian sign: it asks
that the diagonal operator
\[
  D_{l,d}\left(\sum_i q_i t^i\right)
  =
  \sum_i (i+1)^l\binom di^l q_i t^i
\]
sends the particular normalized rows \(Q_n\), together with the binomial
Hadamard kernel, into the reciprocal-interlacing cone
\[
  \mathbb I_{d+1}
  =
  \{f: f\ll t^{d+1}f(1/t)\}.
\]
This is stronger than the Wronskian coefficient sign, and the Hadamard cone
route below supplies this boundary lemma.

A tempting simplification is false: it is not enough to prove that
\((\theta+1)^l\) sends every palindromic negative-rooted polynomial into the
reciprocal-interlacing cone.  Already for \(l=2\),
\[
  H(t)=1+\frac{13}{6}t+t^2
\]
is palindromic and real-rooted, but
\[
  (\theta+1)^2H(t)=1+\frac{26}{3}t+9t^2
\]
does not interlace its shifted reciprocal.  Clearing denominators, exact
`polynomial-tools` gives `do_not_interlace` for
\[
  3+26t+27t^2
  \quad\text{and}\quad
  27t+26t^2+3t^3 .
\]
Thus the binomial Hadamard factor in \(D_{l,d}\) is genuinely part of the
boundary mechanism.

### Hadamard Cone Route

The endpoint can be rephrased in a way that isolates a standard closure
property.  Let \(d=n-1\) and define
\[
  K_{d,l}(t)=\sum_{i=0}^d (i+1)^l\binom di^l t^i .
\]
Then
\[
  A_n^{(l)}(t)=K_{d,l}(t)\odot Q_n^{(l)}(t),
\]
where \(\odot\) denotes coefficientwise, or Hadamard, product.  The normalized
row \(Q_n^{(l)}\) is palindromic and negative-rooted by the recurrence above.
The closure input is Wagner's two-pair Hadamard theorem:
if \(f\ll g\) and \(h\ll k\), with all four polynomials having nonnegative
coefficients and only nonpositive roots, then
\[
  f\odot h \ll g\odot k .
\]
Equivalently, the Hadamard product of two directed interlacing pairs is again
a directed interlacing pair.  In the notation of Garloff--Wagner, this is
Theorem 4(b) of *Hadamard products of stable polynomials are stable*.

This theorem gives the needed reciprocal-cone closure.  If
\(p,r\in\mathbb I_{d+1}\), then
\[
  p\odot r
  \ll
  t^{d+1}(p\odot r)(1/t),
\]
because the right side is \(I_{d+1}(p)\odot I_{d+1}(r)\).  If \(q\) is
palindromic, nonnegative, and negative-rooted of degree \(d\), then
\(I_{d+1}(q)=tq\), and \(q\ll tq\) is immediate from the added zero root.
Hence such \(q\) also lies in \(\mathbb I_{d+1}\).

The diagonal kernel lies in the same cone by an elementary factorization.  Put
\[
  U_d(t)=\sum_{i=0}^d (i+1)\binom di t^i .
\]
For \(d\ge1\),
\[
  U_d(t)=(1+t)^{d-1}(1+(d+1)t).
\]
The case \(d=0\) is trivial.  For \(d\ge1\), the roots of \(U_d\) are
\(-1\) with multiplicity \(d-1\) and \(-1/(d+1)\), while the roots of
\(I_{d+1}(U_d)\) are
\(-(d+1)\), \(-1\) with multiplicity \(d-1\), and \(0\).  Thus
\(U_d\in\mathbb I_{d+1}\).  Since
\[
  K_{d,l}=U_d\odot U_d\odot\cdots\odot U_d
  \quad(l\text{ factors}),
\]
Hadamard closure gives \(K_{d,l}\in\mathbb I_{d+1}\) for every \(l\ge1\).

Putting this together, \(Q_n^{(l)}\in\mathbb I_{d+1}\) by palindromicity and
the normalized-row real-rootedness lemma, and \(K_{d,l}\in\mathbb I_{d+1}\)
by the preceding paragraph.  Therefore
\[
  A_n^{(l)}=K_{d,l}\odot Q_n^{(l)}\in\mathbb I_{d+1},
\]
which is exactly the boundary endpoint
\[
  A_n^{(l)}(t)\ll t^n A_n^{(l)}(1/t).
\]
The polynomial lab now records this as the strengthened Hadamard route.  The
remaining exposition task is only to adapt notation and orientation carefully
if this is moved into a paper proof.

## False Scalar Shortcut

The scalar operator
\[
T_{m,l}(p)=((\theta+1)^l+t(m+1-\theta)^l)p
\]
does not preserve real-rootedness on arbitrary real-rooted
positive-coefficient inputs.

For \(l=3\), take
\[
p(t)=(6t+1)^2(7t+1)
     =1+19t+120t^2+252t^3.
\]
Then
\[
T_{3,3}(p)
 =1+216t+3753t^2+17088t^3+252t^4,
\]
and the exact Sturm check says this image is not real-rooted.  Equivalently,
its quartic discriminant is
\[
-272275196270935104.
\]

Therefore the proof cannot simply invoke a general finite-symbol or
multiplier-sequence theorem for \(T_{m,l}\).

## False Gamma-Positivity Shortcut

The homogeneous differential recurrence is symmetric, but the induced operator
on the gamma basis is not entrywise positive once \(l=3\).

For example, applying the \(l=3\), input-degree \(3\) operator to
\((s+t)^3\) gives gamma expansion
\[
(s+t)^4+84st(s+t)^2-12(st)^2.
\]
Thus the \(l=2\) gamma-basis proof from the source does not directly extend to
all \(l\).

## Exact Last-Leader Pieces Are Too Fine

Let
\[
L_{n,m}^{(l)}(t)=
\sum_{\substack{B\subseteq[n]\\1\in B,\ \max B=m}}
  c_n(B)^l t^{|B|-1}.
\]
The exact pieces \(L_{n,m}^{(l)}\) are not pairwise compatible.  The first
small obstruction is
\[
L_{3,1}^{(2)}(t)=1,\qquad
L_{3,3}^{(2)}(t)=4t+t^2.
\]
The combination
\[
1+a(4t+t^2)
\]
has discriminant \(4a(4a-1)\), which is negative for
\(0<a<1/4\).  Hence the cumulative prefix \(P_{n,m}\), not the exact
last-leader piece \(L_{n,m}\), is the right refinement to pursue.

## Cumulative Last-Leader Prefix Chain

The recurrence counts \(l\)-tuples of subexceedant functions with common block
leader set.  The exact maximum-block-leader pieces are too fine, but their
cumulative prefixes form an interlacing chain:
\[
P_{n,1}^{(l)}\ll P_{n,2}^{(l)}\ll \dotsb \ll P_{n,n}^{(l)}.
\]
Since \(P_{n,n}^{(l)}=E_n^{(l)}\), this also gives another structured proof
surface for the row theorem.

The useful recurrence is
\[
P_{n+1,m}^{(l)}=(\theta+1)^lP_{n,m}^{(l)}
\quad (m\le n),
\]
and
\[
P_{n+1,n+1}^{(l)}
 =P_{n+1,n}^{(l)}+
  t(n-\theta)^lP_{n,n}^{(l)}.
\]
This gives a short proof from the endpoint theorem.  Put
\[
  T=(\theta+1)^l,\qquad A_m^{(l)}=TE_m^{(l)}.
\]
The endpoint theorem gives
\[
  A_m^{(l)}\ll t^mA_m^{(l)}(1/t).
\]
By the interlacing cone property,
\[
  A_m^{(l)}
  \ll
  A_m^{(l)}+t^mA_m^{(l)}(1/t)
  =
  E_{m+1}^{(l)}.
\]
Finally, \(T\) preserves weak proper position, since it is the diagonal
operator with multiplier sequence \(((k+1)^l)_{k\ge0}\).  Applying
\(T^{n-m-1}\) gives
\[
  P_{n,m}^{(l)}
  =
  T^{n-m-1}A_m^{(l)}
  \ll
  T^{n-m-1}E_{m+1}^{(l)}
  =
  P_{n,m+1}^{(l)}.
\]
Thus
\[
P_{n,1}^{(l)}\ll P_{n,2}^{(l)}\ll \dotsb \ll P_{n,n}^{(l)}
\]
for all \(l\ge1\).

## Normalized Gamma Refinement Status

The main real-rootedness theorem, consecutive row interlacing, boundary
reciprocal interlacing, and cumulative prefix interlacing are now proved.  The
normalized-gamma and original-gamma consecutive interlacing refinements remain
separate proof targets.  For the original gamma rows one may still ask for

\[
\Gamma_{n-1}^{(l)}(z)\ll \Gamma_n^{(l)}(z).
\]

The normalized-gamma refinement works with
\[
  Q_n^{(l)}(t)
  =(1+t)^{n-1}G_n^{(l)}\left(\frac{t}{(1+t)^2}\right)
\]
and asks for
\[
  G_{n-1}^{(l)}\ll G_n^{(l)}.
\]
The induction surface is the adjacent partial-iterate chain
\[
  C_d\cup C_{d+1},\qquad
  C_d=(F_{d,0}^{(l)},\dotsc,F_{d,l}^{(l)}),
\]
where \(F_{d,s}^{(l)}=M_d^sF_d^{(l)}\).  The desired local step is
\[
  C_d\cup C_{d+1}\text{ compatible}
  \quad\Longrightarrow\quad
  C_{d+1}\cup C_{d+2}\text{ compatible}.
\]
The current proved ingredients are the lifted diagonal identity, preservation
of the positive gamma-PF compatibility cone by \(M_d\), coefficient-ratio
orientation for PF proper-position pairs, and the dimension-shift comparison
\[
  M_df\ll M_{d+1}f.
\]
They are not sufficient by themselves: weak proper position is not transitive,
so adjacent links do not automatically give pairwise compatibility of the whole
finite orbit.  After the pivot audit, the gamma refinement is parked as a
secondary target.  The narrower internal-orbit lemma
`spectral_actual_row_internal_orbit_interlacing` and the stronger adjacent-chain
target `mixed_lifted_actual_row_cone_compatibility` remain plausible, but they
should not be the default next proof pass unless the main Wagner--Hadamard
proof has already been polished.  A cleaner future gamma attempt should first
try the Wronskian/Sturm route, since the lab records exact evidence for
negative normalized-gamma Wronskians and gamma real-rootedness is already
proved from the normalized-row PF theorem.  The spectral and local-\(h\)
machinery below should be treated as parked evidence unless a smaller
interlacing principle emerges.
