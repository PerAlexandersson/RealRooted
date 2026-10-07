import RealRooted.Derivative.FamilyClosure
import RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks
import RealRooted.Derivative.Interlacing
import RealRooted.Derivative.RootCounting
import RealRooted.ObreschkoffConverse.Derivative

/-!
# Derivative interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "derivative-interlacing"
authors = ["Rolle", "Jensen", "Obreschkoff", "Fisk"]
years = [1691, 1913, 1963, 2006]

[[theorems]]
name = "RealRooted.Challenges.DerivativeInterlacing.derivative_interlaces"
label = "The derivative of a real-rooted polynomial interlaces it"
headline = true

[[theorems]]
name = "RealRooted.Challenges.DerivativeInterlacing.interl_derivative"
label = "Differentiation preserves interlacing"
headline = true

[[theorems]]
name = "RealRooted.Challenges.DerivativeInterlacing.exists_mem_Ioo_isRoot_derivative"
label = "Rolle's theorem for polynomials"

[[theorems]]
name = "RealRooted.Challenges.DerivativeInterlacing.splits_derivative"
label = "The derivative of a real-rooted polynomial is real-rooted"

[[theorems]]
name = "RealRooted.Challenges.DerivativeInterlacing.strictInterl_derivative"
label = "Differentiation preserves interlacing of nonconstant polynomials"

[[theorems]]
name = "Polynomial.exists_mem_jensenDisk_of_isRoot_derivative"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.JensenDisks"
label = "Jensen: non-real zeros of p' lie in Jensen disks"
-->

<!-- realrooted-catalog-content -->
# Derivative interlacing

**Rolle's theorem.** If $a < b$ are zeros of a real polynomial $p$, then
$p'(c) = 0$ for some $c$ with $a < c < b$.

**Theorem.** Let $f$ be a real-rooted polynomial of degree $d \geq 1$, with
zeros $r_1 \leq \dotsb \leq r_d$ listed with multiplicity. Then $f'$ is
real-rooted of degree $d - 1$, and its zeros $s_1 \leq \dotsb \leq s_{d-1}$
interlace those of $f$:
$$
r_1 \leq s_1 \leq r_2 \leq s_2 \leq \dotsb \leq s_{d-1} \leq r_d .
$$
In the notation of the [interlacing page](/RealRooted/concepts/interlacing/), this is
`Interlaces f' f`. In particular, the derivative of every real-rooted
polynomial, including a constant one, is again real-rooted.

**Theorem** (differentiation preserves interlacing). If $f \ll g$, then
$f' \ll g'$. Here we use the zero-aware relation `Interl`, which holds
whenever one side vanishes; if $f$ is nonconstant, both derivatives are
nonzero and $f' \ll g'$ holds in the strict sense `StrictInterl`.

**Theorem** (Jensen). Let $p$ be a nonconstant real polynomial. Every
non-real zero of $p'$ lies in a *Jensen disk* of $p$: the closed disk whose
diameter is the segment from a non-real zero $z$ of $p$ to $\bar z$.  In
particular, if $p$ is real-rooted then so is $p'$.

## Proof idea

For the first theorem, we sort the zeros of $f$. A zero of multiplicity $m$
is a zero of $f'$ of multiplicity $m - 1$, and Rolle's theorem places one
further zero of $f'$ strictly between any two consecutive distinct zeros of
$f$. This gives $d - 1$ zeros of $f'$, counted with multiplicity, in the
required positions, and $f'$ has no others since its degree is $d - 1$.

For the second theorem, we use Obreschkoff's theorem: $f \ll g$ implies that
every real linear combination $\lambda f + \mu g$ is zero or real-rooted.
Differentiating the combinations shows that the same holds for $f'$ and
$g'$, and the converse direction of Obreschkoff's theorem returns
interlacing. A degree count fixes the orientation.

For Jensen's theorem, if $p'(w) = 0 \neq p(w)$ then
$\sum_k 1/(w - z_k) = 0$ over the zeros of $p$. Pairing each zero with its
conjugate, a point $w$ outside every Jensen disk makes every term have
imaginary part of sign opposite to $\operatorname{Im} w$, which is impossible.

## References

S. Fisk, [*Polynomials, roots, and
interlacing*](https://arxiv.org/abs/math/0612833), arXiv:math/0612833 (2006),
Chapter 1; N. Obreschkoff, *Verteilung und Berechnung der Nullstellen reeller
Polynome*, VEB Deutscher Verlag der Wissenschaften, Berlin, 1963. J. L. W. V. Jensen,
*Recherches sur la théorie des équations*, Acta Math. 36 (1913), 181–195. The
statement $f' \ll f$ is the remark after
[Wagner's lemma on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#wagnerLemma).
<!-- /realrooted-catalog-content -->

This module exposes Rolle's theorem, derivative interlacing in all positive
degrees, and the preservation of interlacing under differentiation.  The
root-list construction lives in `RealRooted.Derivative.Interlacing`; the
preservation theorem is proved in `RealRooted.ObreschkoffConverse.Derivative`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace DerivativeInterlacing

/-- **Rolle's theorem** for real polynomials: between two zeros of `p` lies a
zero of `p'`. -/
theorem exists_mem_Ioo_isRoot_derivative {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c ∈ Set.Ioo a b, p.derivative.IsRoot c := by
  obtain ⟨c, hac, hcb, hc⟩ := exists_root_derivative_between hab ha hb
  exact ⟨c, ⟨hac, hcb⟩, hc⟩

/-- **Derivative interlacing**: the derivative of a nonconstant real-rooted
polynomial interlaces it. -/
theorem derivative_interlaces {f : ℝ[X]} (hf : f.Splits) (hdeg : f.natDegree ≠ 0) :
    Interlaces f.derivative f :=
  derivative_interlaces_of_natDegree_ne_zero hf hdeg

/-- The derivative of a real-rooted polynomial is real-rooted. -/
theorem splits_derivative {p : ℝ[X]} (hp : p.Splits) : p.derivative.Splits := by
  rcases eq_zero_or_splits_derivative (Or.inr hp) with h | h
  · rw [h]
    exact Splits.zero
  · exact h

/-- Differentiation preserves zero-aware interlacing (Rolle–Obreschkoff). -/
theorem interl_derivative {f g : ℝ[X]} (h : Interl f g) :
    Interl f.derivative g.derivative :=
  derivativePreservesInterl h

/-- Differentiation preserves interlacing of nonzero polynomials when the
left polynomial is nonconstant. -/
theorem strictInterl_derivative {f g : ℝ[X]} (h : StrictInterl f g)
    (hf : f.natDegree ≠ 0) :
    StrictInterl f.derivative g.derivative := by
  have hg : g.natDegree ≠ 0 := by
    rcases h.natDegree_eq_or_eq_succ with hfg | hfg <;> lia
  exact (derivativePreservesInterl h.toInterl).toStrictInterl_of_ne
    (derivative_ne_zero.mpr hf) (derivative_ne_zero.mpr hg)

end DerivativeInterlacing
end Challenges
end RealRooted
