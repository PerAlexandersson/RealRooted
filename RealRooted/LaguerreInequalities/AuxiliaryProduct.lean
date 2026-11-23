module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Topology.MetricSpace.Algebra.FiniteProduct
import Mathlib.Analysis.Calculus.Deriv.Mul
import RealRooted.Mathlib.Analysis.Complex.TranslateProductNonzero

/-!
# Translated products attached to a real auxiliary polynomial

If `g = product (X + alpha_j)` is monic, its complex roots are `-alpha_j`.
The product below is therefore Cardon's `product f(x + alpha_j*t)`, with every
root counted with multiplicity. The coefficients use ordinary Taylor normalization.
-/

public section

open Complex Filter Polynomial

namespace RealRooted

/-- The translated product attached to all complex roots of an auxiliary
polynomial, with multiplicity. Monicity is unnecessary for this definition. -/
@[expose] noncomputable def auxiliaryProduct (g : ℝ[X]) (f : ℂ → ℂ)
    (x : ℝ) (z : ℂ) : ℂ :=
  ((g.map ofRealHom).roots.map fun r ↦ f ((x : ℂ) - r * z)).prod

/-- The ordinary Taylor coefficient of the auxiliary translated product.
Structural reality is established separately when using real inequalities. -/
@[expose] noncomputable def auxiliaryCoefficient (g : ℝ[X]) (f : ℂ → ℂ)
    (x : ℝ) (k : ℕ) : ℝ :=
  (iteratedDeriv k (auxiliaryProduct g f x) 0).re / k.factorial

/-- Finite auxiliary products of an entire function are entire. -/
theorem differentiable_auxiliaryProduct {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (g : ℝ[X]) (x : ℝ) : Differentiable ℂ (auxiliaryProduct g f x) := by
  exact Complex.differentiable_translateProduct hf _ _

/-- Locally uniform limits pass through finite auxiliary products. -/
theorem tendstoLocallyUniformly_auxiliaryProduct {ι : Type*} {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {l : Filter ι} (hF : TendstoLocallyUniformly F f l)
    (hf : Continuous f) (g : ℝ[X]) (x : ℝ) :
    TendstoLocallyUniformly (fun i ↦ auxiliaryProduct g (F i) x)
      (auxiliaryProduct g f x) l := by
  apply TendstoLocallyUniformly.multiset_prod (s := (g.map ofRealHom).roots)
  · intro r _
    exact hF.comp (fun z : ℂ ↦ (x : ℂ) - r * z) (by fun_prop)
  · intro r _
    exact hf.comp (by fun_prop)

end RealRooted
