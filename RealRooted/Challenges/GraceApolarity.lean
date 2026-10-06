import RealRooted.Apolarity
import RealRooted.BorceaBranden.Applications.PolarizationIff
import RealRooted.GraceHalfPlane
import RealRooted.LiebSokal
import RealRooted.Polarization

/-!
# Grace apolarity challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "grace-apolarity"
authors = ["Grace", "Szegő", "Lieb", "Sokal", "Borcea", "Brändén"]
years = [1902, 1922, 1981, 2009]

[[definitions]]
name = "RealRooted.binomialLift"
module = "RealRooted.Apolarity"
label = "Polynomial with binomial-weighted coefficients"

[[definitions]]
name = "RealRooted.AreApolar"
module = "RealRooted.Apolarity"
label = "Apolar polynomials"

[[definitions]]
name = "RealRooted.polarization"
module = "RealRooted.Polarization"
label = "Polarization"

[[definitions]]
name = "RealRooted.diagonalProjection"
module = "RealRooted.Polarization"
label = "Diagonal of a multivariate polynomial"

[[definitions]]
name = "RealRooted.BorceaBranden.blockwisePolarizationDegreeBoxGeneral"
module = "RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization"
label = "Blockwise polarization in a degree box"

[[definitions]]
name = "RealRooted.applyNegDifferential"
module = "RealRooted.LiebSokalOperator"
label = "Differential action F(−∂)G"

[[theorems]]
name = "RealRooted.Challenges.GraceApolarity.exists_isRoot_mem_closedBall_of_areApolar"
label = "Grace's apolarity theorem for closed disks"
headline = true

[[theorems]]
name = "RealRooted.Challenges.GraceApolarity.mvUpperHalfPlaneStable_polarization"
label = "Polarization preserves stability"
headline = true

[[theorems]]
name = """RealRooted.Challenges.GraceApolarity.\
mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero"""
label = "Grace–Walsh–Szegő: a symmetric multiaffine polynomial is stable iff its diagonal is"
headline = true

[[theorems]]
name = "RealRooted.Challenges.GraceApolarity.mvRealStable_iff_aeval_X_ne_zero_and_splits"
label = "Grace–Walsh–Szegő, real form: real stable iff the diagonal is real-rooted"

[[theorems]]
name = "RealRooted.Challenges.GraceApolarity.polarization_diagonalProjection"
label = "A symmetric multiaffine polynomial is the polarization of its diagonal"

[[theorems]]
name = """RealRooted.Challenges.GraceApolarity.\
mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral_iff"""
label = "Blockwise polarization preserves and reflects stability"

[[theorems]]
name = "RealRooted.Challenges.GraceApolarity.exists_isRoot_le_im_of_areApolar"
label = "Grace's apolarity theorem for closed half-planes"

[[theorems]]
name = "RealRooted.Challenges.GraceApolarity.applyNegDifferential_eq_zero_or_stable"
label = "Lieb–Sokal theorem for multiaffine polynomials"
-->

<!-- realrooted-catalog-content -->
# Grace's apolarity theorem

Fix $n \geq 0$. For coefficient sequences $a = (a_k)$ and $b = (b_k)$, put
$$
F(z) = \sum_{k=0}^n \binom{n}{k} a_k z^k
\quad\text{and}\quad
G(z) = \sum_{k=0}^n \binom{n}{k} b_k z^k .
$$
In Lean, $F$ is `binomialLift n f`, where $f = \sum_k a_k z^k$. The
polynomials $F$ and $G$ are **apolar** if
$$
\sum_{k=0}^n (-1)^k \binom{n}{k} a_k b_{n-k} = 0 .
$$

**Theorem** (Grace). Let $F$ and $G$ be apolar polynomials of degree exactly
$n$. If all zeros of $F$ lie in a closed disk $\{z : |z - c| \leq r\}$ with
$r \geq 0$, or in a closed half-plane $\{z : \operatorname{Im} z \geq b\}$,
then $G$ has a zero in the same set.

The **polarization** of a polynomial $p(z) = \sum_{k \leq n} p_k z^k$ of
degree at most $n$ is the symmetric multiaffine polynomial
$$
\operatorname{Pol}_n(p)(z_1, \dotsc, z_n) =
\sum_{k=0}^n \binom{n}{k}^{-1} p_k\, e_k(z_1, \dotsc, z_n),
$$
where $e_k$ is the elementary symmetric polynomial; its diagonal
specialization $z_1 = \dotsb = z_n = z$ is $p(z)$.

**Theorem** (polarization). Let $p \in \mathbb{C}[z]$ have degree at most $n$
and no zeros in the open upper half-plane. Then $\operatorname{Pol}_n(p)$ is
stable: it does not vanish when all $z_i$ lie in the open upper half-plane.

**Theorem** (Grace–Walsh–Szegő). Let $P \in \mathbb{C}[z_1, \dotsc, z_n]$ be
symmetric and multiaffine. Then $P = \operatorname{Pol}_n(p)$ for its diagonal
$p(z) = P(z, \dotsc, z)$, and $P$ is stable if and only if $p$ has no zeros
in the open upper half-plane. If $P$ has real coefficients, then $P$ is real
stable if and only if $p$ is nonzero and has only real zeros.

More generally, let $P \in \mathbb{C}[z_i : i \in \sigma]$, with $\sigma$
finite, have degree at most $\kappa_i$ in $z_i$. Replacing each $z_i$ by a
block of $\kappa_i$ new variables and polarizing $P$ in each block gives a
multiaffine polynomial.

**Theorem.** The blockwise polarization of $P$ is stable if and only if $P$
is stable.

**Theorem** (Lieb–Sokal, multiaffine case). Let $F$ and $G$ be stable
multiaffine polynomials in $\mathbb{C}[z_1, \dotsc, z_m]$. Then
$F(-\partial)\, G$, the result of substituting $-\partial/\partial z_i$ for
$z_i$ in $F$ and applying it to $G$, is zero or stable.

## Proof idea

Grace's theorem is proved by induction on $n$. Apolarity is invariant under
the polar derivative of $F$ with a pole $\zeta$ outside the disk, which lowers
the degree by one and, by Laguerre's theorem, keeps the zeros in the disk. The
half-plane case uses the same induction, with Laguerre's theorem for closed
lower half-planes, followed by the reflection $z \mapsto -z$. For
polarization, we fix a point $z$ in the product of open upper half-planes. The
equation $\operatorname{Pol}_n(p)(z) = 0$ says that $p$ is apolar to
$\prod_i (w - z_i)$. All zeros of $p$ lie in the closed lower half-plane, so
Grace's theorem would put some $z_i$ there, which is impossible. A symmetric
multiaffine polynomial is a linear combination of elementary symmetric
polynomials, so it is the polarization of its diagonal; this gives the
Grace–Walsh–Szegő theorem. For the real form, a real polynomial without zeros
in the open upper half-plane has no nonreal zeros, since these come in
conjugate pairs. Identifying the variables of each block recovers $P$ from its
blockwise polarization, and identifying variables preserves stability. The
Lieb–Sokal theorem
follows by pairing the variables of $F$ and $G$ and contracting each pair, an
operation that preserves stability of multiaffine polynomials.

## References

J. H. Grace, “The zeros of a polynomial,” *Proc. Cambridge Philos. Soc.* 11
(1902), 352–357; G. Szegő, “Bemerkungen zu einem Satz von J. H. Grace über die
Wurzeln algebraischer Gleichungen,” *Math. Z.* 13 (1922), 28–55; Q. I. Rahman
and G. Schmeisser, *Analytic Theory of Polynomials*, Oxford University Press,
2002; E. H. Lieb and A. D. Sokal, “A general Lee–Yang theorem for
one-component and multicomponent ferromagnets,” *Comm. Math. Phys.* 80 (1981),
153–179; J. Borcea and P. Brändén, “The Lee–Yang and Pólya–Schur programs. II.
Theory of stable polynomials and applications,” *Comm. Pure Appl. Math.* 62
(2009), 1595–1631; A. Gribinski and A. W. Marcus, “A rectangular additive
convolution for polynomials,” Theorem 2.4. See
[apolar polynomials](https://www.symmetricfunctions.com/stablePolynomials.htm#apolarPolynomial)
and [polarization](https://www.symmetricfunctions.com/stablePolynomials.htm#polarizationDefinition)
on symmetricfunctions.com.
<!-- /realrooted-catalog-content -->

This module exposes Grace's theorem for closed disks and closed upper
half-planes, univariate and blockwise polarization, the Grace–Walsh–Szegő
characterization of stable symmetric multiaffine polynomials, and the
multiaffine Lieb–Sokal theorem. The proofs live in `RealRooted.Apolarity`,
`RealRooted.GraceHalfPlane`, `RealRooted.Polarization`,
`RealRooted.BorceaBranden.Applications.PolarizationIff` and
`RealRooted.LiebSokal`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace GraceApolarity

/-- **Grace's apolarity theorem**, closed-disk case: if `F` and `G` are apolar
of degree `n` and all zeros of `F` lie in a closed disk, then `G` has a zero
in that disk. -/
theorem exists_isRoot_mem_closedBall_of_areApolar {n : ℕ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) {f g : ℂ[X]} (hf : (binomialLift n f).natDegree = n)
    (hg : (binomialLift n g).natDegree = n) (hap : AreApolar n f g)
    (hroots : ∀ z, (binomialLift n f).IsRoot z → z ∈ Metric.closedBall c r) :
    ∃ z ∈ Metric.closedBall c r, (binomialLift n g).IsRoot z := by
  obtain ⟨z, hz, hmem⟩ := grace_apolarity_closedBall hr hf hg hap hroots
  exact ⟨z, hmem, hz⟩

/-- **Grace's apolarity theorem**, closed half-plane case: if `F` and `G` are
apolar of degree `n` and all zeros of `F` satisfy `b ≤ Im z`, then so does
some zero of `G`. -/
theorem exists_isRoot_le_im_of_areApolar {n : ℕ} {b : ℝ} {f g : ℂ[X]}
    (hf : (binomialLift n f).natDegree = n) (hg : (binomialLift n g).natDegree = n)
    (hap : AreApolar n f g) (hroots : ∀ z, (binomialLift n f).IsRoot z → b ≤ z.im) :
    ∃ z, b ≤ z.im ∧ (binomialLift n g).IsRoot z := by
  obtain ⟨z, hz, hmem⟩ := grace_apolarity_upperHalf hf hg hap hroots
  exact ⟨z, hmem, hz⟩

/-- **Polarization preserves stability**: the degree-`n` polarization of a
polynomial of degree at most `n` without zeros in the open upper half-plane
is stable. -/
theorem mvUpperHalfPlaneStable_polarization {n : ℕ} {p : ℂ[X]} (hdeg : p.natDegree ≤ n)
    (hstable : ∀ w : ℂ, 0 < w.im → p.eval w ≠ 0) :
    MvUpperHalfPlaneStable (polarization n p) :=
  RealRooted.mvUpperHalfPlaneStable_polarization hdeg hstable

/-- A symmetric multiaffine polynomial is the polarization of its diagonal. -/
theorem polarization_diagonalProjection {n : ℕ} {P : MvPolynomial (Fin n) ℂ}
    (hsym : P.IsSymmetric) (hma : MvPolynomial.IsMultiaffine P) :
    polarization n (diagonalProjection n P) = P :=
  RealRooted.polarization_diagonalProjection hsym hma

/-- **Grace–Walsh–Szegő**: a symmetric multiaffine polynomial is stable if and
only if its diagonal has no zeros in the open upper half-plane. -/
theorem mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero {n : ℕ}
    {P : MvPolynomial (Fin n) ℂ} (hsym : P.IsSymmetric) (hma : MvPolynomial.IsMultiaffine P) :
    MvUpperHalfPlaneStable P ↔ ∀ w : ℂ, 0 < w.im → (diagonalProjection n P).eval w ≠ 0 :=
  RealRooted.mvUpperHalfPlaneStable_iff_eval_diagonalProjection_ne_zero hsym hma

/-- **Grace–Walsh–Szegő**, real form: a real symmetric multiaffine polynomial
is real stable if and only if its diagonal is nonzero and splits over `ℝ`. -/
theorem mvRealStable_iff_aeval_X_ne_zero_and_splits {n : ℕ} {P : MvPolynomial (Fin n) ℝ}
    (hsym : P.IsSymmetric) (hma : MvPolynomial.IsMultiaffine P) :
    MvRealStable P ↔
      MvPolynomial.aeval (fun _ => (X : ℝ[X])) P ≠ 0 ∧
        (MvPolynomial.aeval (fun _ => (X : ℝ[X])) P).Splits :=
  RealRooted.mvRealStable_iff_aeval_X_ne_zero_and_splits hsym hma

/-- Blockwise polarization in the degree box `κ` preserves and reflects
stability. -/
theorem mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral_iff {σ : Type*}
    [Fintype σ] (κ : σ → ℕ) (p : MvPolynomial.degreeOfLE σ ℂ κ) :
    MvUpperHalfPlaneStable (BorceaBranden.blockwisePolarizationDegreeBoxGeneral κ p).1 ↔
      MvUpperHalfPlaneStable p.1 :=
  BorceaBranden.mvUpperHalfPlaneStable_blockwisePolarizationDegreeBoxGeneral_iff κ p

/-- **Lieb–Sokal**, multiaffine case: for stable multiaffine `F` and `G`, the
polynomial `F(-∂) G` is zero or stable. -/
theorem applyNegDifferential_eq_zero_or_stable {σ : Type*} [Fintype σ]
    {F G : MvPolynomial σ ℂ} (hF : MvUpperHalfPlaneStable F) (hG : MvUpperHalfPlaneStable G)
    (hF_ma : MvPolynomial.IsMultiaffine F) (hG_ma : MvPolynomial.IsMultiaffine G) :
    applyNegDifferential F G = 0 ∨ MvUpperHalfPlaneStable (applyNegDifferential F G) :=
  hF.liebSokal_multiaffine hG hF_ma hG_ma

end GraceApolarity
end Challenges
end RealRooted
