module

import RealRooted.CoefficientDominance.NewtonDefectRoots

/-!
# Local Newton defects and roots

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "local-newton-defect-roots"
formalized = "2026-10-11"
authors = ["Karpenko", "Vishnyakova", "Akian", "Gaubert", "Sharify"]
tags = []
references = [
  "KarpenkoVishnyakova2017",
  "AkianGaubertSharify2017",
]

[[theorems]]
name = "RealRooted.NewtonDefectRoots.esym_sq_sub_sq_esym_le"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Off-diagonal elementary-symmetric bound"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.leadingRatio_mem_linear_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Linear box for the leading-subset ratio"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.defectConstant_le_leadingRatio"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Quadratic lower bound for the leading-subset ratio"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.rootParameter_mem_linear_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Linear local-defect box for a root parameter"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.rootParameter_mem_quadratic_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Quadratic local-defect box for a root parameter"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.rootParameter_div_succ_le"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Adjacent root-parameter separation"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.factorPolynomial_rootParameter_mem_linear_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Linear box in polynomial coefficients"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.factorPolynomial_rootParameter_mem_quadratic_box"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Quadratic box in polynomial coefficients"

[[theorems]]
name = "RealRooted.NewtonDefectRoots.factorPolynomial_rootParameter_isEquivalent_coefficientRatio"
module = "RealRooted.CoefficientDominance.NewtonDefectRoots"
label = "Root parameters asymptotic to coefficient ratios"
headline = true
-->

<!-- realrooted-catalog-content -->
# Local Newton defects and roots

For a polynomial with only negative roots, the ratio $a_i/a_{i+1}$ of consecutive coefficients
approximates the modulus of the $(i+1)$st root closest to the origin. Explicit bounds hold when
the local Newton defects $a_{k-1}a_{k+1}/a_k^2$ at $k=i,i+1$ are small, and the approximation
becomes asymptotically exact as these defects tend to $0$.

## Results

Let $x_0\ge x_1\ge\dots>0$, let $e_k$ be the $k$th elementary symmetric polynomial of
$x_0,\dots,x_{n-1}$, and let $L_k=x_0\cdots x_{k-1}$. Put $\eta_i=x_i^{-1}$ and
$\rho_i=e_i/e_{i+1}$, so the roots of $\prod_{i<n}(1+x_iX)$ are $-\eta_0,\dots,-\eta_{n-1}$ with
$\eta_0\le\dots\le\eta_{n-1}$. The *local Newton defect* is
$\delta_k=e_{k-1}e_{k+1}/e_k^2$ for $0<k<n$ and $\delta_k=0$ otherwise. Put
$C(u)=(1+\sqrt{1-4u})/2$.

**Theorem (off-diagonal estimate).** For nonnegative $x_i$ and all $n,k$,
$$e_k^2-\sum_{|S|=k}\prod_{i\in S}x_i^2\le2\,e_{k-1}e_{k+1}.$$

**Theorem (leading subset).** For $k\le n$,
$$1-2\delta_k\le\frac{L_k}{e_k}\le1.$$
If $\delta_k\le\frac14$, then $C(\delta_k)\le L_k/e_k$.

**Theorem (root parameters).** Let $i<n$. If $1-2\delta_{i+1}>0$, then
$$(1-2\delta_i)\,\rho_i\le\eta_i\le\frac{\rho_i}{1-2\delta_{i+1}}.$$
If $\delta_i,\delta_{i+1}\le\frac14$, then
$$C(\delta_i)\,\rho_i\le\eta_i\le\frac{\rho_i}{C(\delta_{i+1})}.$$
If $i+1<n$ and $\delta_{i+1}\le\frac14$, then
$$\frac{\eta_i}{\eta_{i+1}}\le\frac{1-C(\delta_{i+1})}{C(\delta_{i+1})}.$$

**Theorem (polynomial form).** Let $a_0>0$ and $p=a_0\prod_{i<n}(1+x_iX)$ with coefficients
$a_k$. The two-sided bounds for $\eta_i$ above hold with $\rho_i$ replaced by $a_i/a_{i+1}$ and
$\delta_k$ by $a_{k-1}a_{k+1}/a_k^2$ (and $0$ for $k=0$ or $k\ge n$).

**Theorem (asymptotics).** Fix $i$. Let $p^{(a)}=a_0^{(a)}\prod_{j<n_a}(1+x^{(a)}_jX)$ be a
family indexed along a filter, for example a sequence, with $a_0^{(a)}>0$, each $x^{(a)}$
positive and decreasing, and eventually $i<n_a$. If the defects of $p^{(a)}$ at $i$ and $i+1$
tend to $0$, then $\eta^{(a)}_i\sim a^{(a)}_i/a^{(a)}_{i+1}$.

## References

- [@KarpenkoVishnyakova2017]
- [@AkianGaubertSharify2017]
<!-- /realrooted-catalog-content -->
-/
