module

public import RealRooted.Bezoutian.LowDegree
public import RealRooted.Bezoutian.RootEvaluation
public import RealRooted.Bezoutian.StrictInterleaving
public import RealRooted.Bezoutian.Successor
public import RealRooted.Bezoutian.WronskianConverse
public import RealRooted.Mathlib.Algebra.Polynomial.Bezoutian
public import RealRooted.Wronskian.Algebra
public import RealRooted.Wronskian.Converse

/-!
# Bézoutian and Wronskian criteria for interlacing

<!-- realrooted-catalog
version = 1
kind = "method"
section = "theorems"
slug = "bezoutian"
formalized = "2026-10-06"
references = [
  "Fisk2006x",
]
authors = ["Hermite", "Krein", "Naimark", "Fisk"]
years = [1856, 1936, 2006]

[[definitions]]
name = "Polynomial.bezoutMatrix"
module = "RealRooted.Mathlib.Algebra.Polynomial.Bezoutian"
label = "Bézout matrix"

[[definitions]]
name = "RealRooted.StrictInterlSameDegree"
module = "RealRooted.Bezoutian.StrictInterleaving"
label = "Strict interlacing of equal-degree polynomials"

[[theorems]]
name = "RealRooted.strictInterlSameDegree_iff_bezoutMatrix_posDef"
module = "RealRooted.Bezoutian.LowDegree"
label = "Equal degree: the roots strictly interlace iff the Bézout matrix is positive definite"
headline = true
symcat = "bezoutMatrix"

[[theorems]]
name = "RealRooted.bezoutMatrix_posDef_iff_interlaces_succ"
module = "RealRooted.Bezoutian.Successor"
label = "Successor degree: g ≪ f without common roots iff the Bézout matrix is positive definite"

[[theorems]]
name = "RealRooted.bezoutMatrix.wronskian_pos_of_posDef"
module = "RealRooted.Bezoutian.RootEvaluation"
label = "A positive definite Bézout matrix gives a positive Wronskian"

[[theorems]]
name = "RealRooted.strictInterl_iff_wronskian_eval_nonneg"
module = "RealRooted.Wronskian.Converse"
label = "Wronskian criterion: g ≪ f iff f′g − fg′ ≥ 0 and a multiplicity bound holds"
symcat = "wronskianCriterion"

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_eval_nonneg_of_nodup"
module = "RealRooted.Wronskian.Converse"
label = "If f has simple roots, f′g − fg′ ≥ 0 alone gives g ≪ f"

[[theorems]]
name = "RealRooted.exists_wronskian_eval_nonneg_not_strictInterl"
module = "RealRooted.Wronskian.Converse"
label = "The multiplicity bound cannot be dropped: x³ and (x − 1)³"

[[theorems]]
name = "RealRooted.StrictInterlSameDegree.of_wronskian_pos"
module = "RealRooted.Bezoutian.WronskianConverse"
label = "A positive Wronskian gives strict interlacing in equal degree"

[[theorems]]
name = "RealRooted.strictInterl_of_wronskian_pos_succ"
module = "RealRooted.Bezoutian.WronskianConverse"
label = "A positive Wronskian gives interlacing in successor degree"

[[theorems]]
name = "RealRooted.laguerre_form_nonneg"
module = "RealRooted.Wronskian.Algebra"
label = "Laguerre's inequality p′² − p p″ ≥ 0 for real-rooted p"
-->

<!-- realrooted-catalog-content -->
# Bézoutian and Wronskian criteria for interlacing

Two real-rooted polynomials $g$ and $f$ with positive leading coefficients satisfy $g\ll f$
exactly when the Wronskian $f'g-fg'$ is nonnegative and a multiplicity condition holds. Strict
interlacing is positive definiteness of the Bézout matrix, a finite test that needs no root
computation.

## Results

For real polynomials $p,q$ let $W(p,q)=q'p-qp'$. For $p,q$ of degree at most $n$ the
*Bézout matrix* $B_n(q,p)=(b_{ij})_{0\le i,j<n}$ is the symmetric matrix with
$$
\frac{q(x)\,p(y)-q(y)\,p(x)}{x-y}=\sum_{i,j=0}^{n-1}b_{ij}\,x^iy^j .
$$

**Theorem (Hermite).** Let $p$ and $q$ have degree $n$ and positive leading coefficients. Then
$p$ and $q$ are real-rooted with roots $\alpha_1<\beta_1<\alpha_2<\dotsb<\alpha_n<\beta_n$,
where $\alpha_i$ are the roots of $p$ and $\beta_i$ those of $q$, if and only if $B_n(q,p)$ is
positive definite.

**Theorem (successor degree).** [@Fisk2006x, Cor. 9.145] Let $\deg f=d+1$ and $\deg g=d$, with
positive leading coefficients. Then $B_{d+1}(f,g)$ is positive definite if and only if
$g\ll f$ and $f,g$ have no common root.

If $B_n(q,p)$ is positive definite, then $W(p,q)>0$ on $\mathbb R$.

**Theorem (Wronskian criterion).** Let $f,g$ be real-rooted with positive leading coefficients
and $\deg g\le\deg f\le\deg g+1$. Then $g\ll f$ if and only if $W(g,f)\ge0$ on $\mathbb R$ and
every real $r$ is a root of $f$ of multiplicity at most one more than its multiplicity in $g$.
If the roots of $f$ are simple, $W(g,f)\ge0$ alone implies $g\ll f$. The multiplicity condition
is needed: $W(x^3,(x-1)^3)=3x^2(x-1)^2\ge0$, but $x^3\ll(x-1)^3$ fails.

**Theorem (strict converses).** Let $p,q$ be real-rooted with positive leading coefficients and
$W(p,q)>0$ on $\mathbb R$. If $\deg p=\deg q$, the roots alternate strictly as in Hermite's
theorem. If $\deg q=\deg p+1$, then $p\ll q$.

**Corollary (Laguerre's inequality).** If $p$ is real-rooted, then $p'(t)^2-p(t)p''(t)\ge0$ for
all real $t$, that is, $W(p',p)\ge0$.

## Use

The Wronskian criterion turns interlacing into a polynomial inequality, which suits families
given by differential recurrences, and the Bézout matrix decides strict interlacing by a
positive definiteness test.

## Proof

Evaluating the Bézoutian at the roots of $p$ gives values of the Wronskian, so congruence with a
Vandermonde matrix diagonalizes $B_n(q,p)$ with entries of the sign of $W(p,q)$ at those roots;
these are positive exactly when the roots interlace. A positive definite Bézout matrix excludes
non-real roots because its Hermitian form would vanish on a conjugate pair. For the Wronskian
criterion, common roots are removed one at a time using $W(hg,hf)=h^2W(g,f)$.

## References

C. Hermite, “Sur le nombre des racines d'une équation algébrique comprise entre des limites
données,” *J. Reine Angew. Math.* 52 (1856), 39–51; M. G. Krein and M. A. Naimark, “The method
of symmetric and Hermitian forms in the theory of the separation of the roots of algebraic
equations” (1936), English translation in *Linear and Multilinear Algebra* 10 (1981), 265–308;
[@Fisk2006x, Cor. 9.145]. See also the [Bézout matrix](sf:bezoutMatrix) and the
[Wronskian criterion](sf:wronskianCriterion) on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->
-/
