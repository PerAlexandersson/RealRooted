module

public import RealRooted.LaguerreInequalities.Analytic
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.LaguerreInequalities.DerivativeFormula
import RealRooted.LaguerreInequalities.ZeroFree
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.RootDivision
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.Hermite.GeneratingFunction

/-!
# Equality in the first Laguerre inequality

Removing an actual real zero contributes a positive square to the first
Laguerre form. Consequently equality at a nonzero value excludes all zeros.
The zero-free LP classification then identifies the remaining exponential
exception in the Craven–Csordas multiplicity argument.
-/

public section

open Complex
open scoped ComplexConjugate

namespace RealRooted

/-- A real linear factor contributes the square of the cofactor value to
the first Laguerre coefficient. -/
theorem laguerreCoefficient_one_linear_mul {g : ℂ → ℂ} (hg : IsLaguerrePolya g)
    (r x : ℝ) :
    laguerreCoefficient (fun z => (z - r) * g z) x 1 =
      (g x).re ^ 2 + (x - r) ^ 2 * laguerreCoefficient g x 1 := by
  let f := fun z : ℂ => (z - r) * g z
  have hd (z : ℂ) : HasDerivAt f (g z + (z - r) * _root_.deriv g z) z := by
    simpa only [one_mul] using ((hasDerivAt_id' z).sub_const (r : ℂ)).fun_mul
      (hg.differentiable z).hasDerivAt
  have hder : _root_.deriv f = fun z => g z + (z - r) * _root_.deriv g z :=
    funext fun z => (hd z).deriv
  have hder2 (z : ℂ) : _root_.deriv (_root_.deriv f) z =
      2 * _root_.deriv g z + (z - r) * _root_.deriv (_root_.deriv g) z := by
    rw [hder]
    rw [((hg.differentiable z).hasDerivAt.fun_add
      (((hasDerivAt_id' z).sub_const (r : ℂ)).fun_mul
        (hg.deriv.differentiable z).hasDerivAt)).deriv]
    ring
  have hfd : Differentiable ℂ f := fun z => (hd z).differentiableAt
  have hfc : ∀ z, f (conj z) = conj (f z) := by
    intro z
    change (conj z - r) * g (conj z) = conj ((z - r) * g z)
    rw [show g (conj z) = conj (g z) from hg.conj z, map_mul, map_sub, conj_ofReal]
  have h1 : (iteratedDeriv 1 f x).re = (g x).re + (x - r) * (_root_.deriv g x).re := by
    rw [iteratedDeriv_one, hder]
    simp
  have h2 : (iteratedDeriv 2 f x).re =
      2 * (_root_.deriv g x).re + (x - r) * (_root_.deriv (_root_.deriv g) x).re := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hder2]
    simp
  change laguerreCoefficient f x 1 = _
  rw [laguerreCoefficient_one hfd hfc, h1, h2,
    laguerreCoefficient_one hg.differentiable hg.conj]
  simp only [f, mul_re, sub_re, ofReal_re, sub_im, ofReal_im, sub_self, zero_mul,
    sub_zero, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

/-- Equality in the first Laguerre inequality at a nonzero value forces
an LP function to be zero-free. -/
theorem IsLaguerrePolya.zero_free_of_laguerre_one_eq_zero {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {x : ℝ} (hfx : f x ≠ 0)
    (heq : laguerreCoefficient f x 1 = 0) : ∀ z, f z ≠ 0 := by
  intro z hz
  have hfn : f ≠ 0 := fun h => hfx (by simp [h])
  have him := hf.im_eq_zero_of_eq_zero hfn hz
  have hreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  have hr : f (z.re : ℂ) = 0 := by rwa [hreal]
  let g := dslope f (z.re : ℂ)
  have hg : IsLaguerrePolya g := hf.dslope_of_eq_zero hr
  have hfactor (w : ℂ) : f w = (w - z.re) * g w := by
    simpa only [smul_eq_mul] using (sub_smul_dslope_of_zero hr w).symm
  have hgx : g x ≠ 0 := by
    intro hzero
    exact hfx (by rw [hfactor, hzero, mul_zero])
  have hgre : (g x).re ≠ 0 := by
    intro hzero
    have hc : ((g x).re : ℂ) = g x := by
      apply conj_eq_iff_re.mp
      simpa using (hg.conj (x : ℂ)).symm
    exact hgx (by rw [← hc, hzero, ofReal_zero])
  rw [show f = (fun w => (w - z.re) * g w) from funext hfactor,
    laguerreCoefficient_one_linear_mul hg] at heq
  have hnonneg := mul_nonneg (sq_nonneg (x - z.re)) (hg.laguerreCoefficient_nonneg x 1)
  have hpos := sq_pos_of_ne_zero hgre
  linarith

/-- The first Laguerre coefficient of a real quadratic exponential is the
negative doubled quadratic parameter times the square of its value. -/
theorem laguerreCoefficient_one_exp_quadratic (c a s x : ℝ) :
    laguerreCoefficient (fun z => (c : ℂ) * exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) x 1 =
      -2 * s * (((c : ℂ) * exp ((a : ℂ) * x + (s : ℂ) * (x : ℂ) ^ 2)).re) ^ 2 := by
  let f := fun z : ℂ => (c : ℂ) * exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)
  have hfd : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hfc : ∀ z, f (conj z) = conj (f z) := by
    intro z
    simp only [f, map_mul, map_add, map_pow, conj_ofReal, ← exp_conj]
  have he : (a : ℂ) + 2 * (s : ℂ) * (x : ℂ) = ((a + 2 * s * x : ℝ) : ℂ) := by
    push_cast
    ring
  have hraw (n : ℕ) : iteratedDeriv n f x =
      f x * ((hermiteHomogeneous (a + 2 * s * x) s n : ℝ) : ℂ) := by
    dsimp [f]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_exp_quadratic, he]
    have hmap : ((hermiteHomogeneous (a + 2 * s * x) s n : ℝ) : ℂ) =
        hermiteHomogeneous ((a + 2 * s * x : ℝ) : ℂ) (s : ℂ) n :=
      map_hermiteHomogeneous ofRealHom (a + 2 * s * x) s n
    rw [hmap]
    ring
  have hre (n : ℕ) : (iteratedDeriv n f x).re =
      (f x).re * hermiteHomogeneous (a + 2 * s * x) s n := by
    simpa using congrArg Complex.re (hraw n)
  change laguerreCoefficient f x 1 = -2 * s * (f x).re ^ 2
  rw [laguerreCoefficient_one hfd hfc, hre 1, hre 2]
  norm_num [hermiteHomogeneous_add_two]
  ring

/-- Equality in the first Laguerre form away from a zero characterizes the
ordinary exponential exception among LP functions. -/
theorem IsLaguerrePolya.eq_exp_of_laguerre_one_eq_zero {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) {x : ℝ} (hfx : f x ≠ 0)
    (heq : laguerreCoefficient f x 1 = 0) :
    ∃ a : ℝ, ∀ z, f z = f 0 * exp ((a : ℂ) * z) := by
  obtain ⟨a, b, hb, hfactor⟩ := hf.exists_exp_quadratic_of_forall_ne_zero
    (hf.zero_free_of_laguerre_one_eq_zero hfx heq)
  have hf0real : ((f 0).re : ℂ) = f 0 := by
    simpa only [iteratedDeriv_zero] using ofReal_re_iteratedDeriv_zero hf.conj 0
  have hfre : (f x).re ≠ 0 := by
    intro hz
    have hreal : ((f x).re : ℂ) = f x := by
      apply conj_eq_iff_re.mp
      simpa using (hf.conj (x : ℂ)).symm
    exact hfx (by rw [← hreal, hz, ofReal_zero])
  have hexfun : f = fun z => ((f 0).re : ℂ) *
      exp ((a : ℂ) * z + ((-b / 2 : ℝ) : ℂ) * z ^ 2) := by
    funext z
    rw [hfactor, hf0real]
    congr 2
    push_cast
    ring
  have hl : laguerreCoefficient f x 1 = b * (f x).re ^ 2 := by
    conv_lhs => rw [hexfun, laguerreCoefficient_one_exp_quadratic]
    have hx := congrFun hexfun (x : ℂ)
    rw [← hx]
    ring
  have hb0 : b = 0 := by
    rw [hl] at heq
    exact (mul_eq_zero.mp heq).resolve_right (pow_ne_zero _ hfre)
  refine ⟨a, fun z => ?_⟩
  simpa [hb0] using hfactor z

/-- A nonexponential LP function has strictly positive first Laguerre
coefficient wherever its value is nonzero. -/
theorem IsLaguerrePolya.laguerre_one_pos_of_ne_exp {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f)
    (hne : ∀ a : ℝ, f ≠ fun z => f 0 * exp ((a : ℂ) * z))
    {x : ℝ} (hfx : f x ≠ 0) : 0 < laguerreCoefficient f x 1 := by
  apply lt_of_le_of_ne (hf.laguerreCoefficient_nonneg x 1)
  intro heq
  obtain ⟨a, ha⟩ := hf.eq_exp_of_laguerre_one_eq_zero hfx heq.symm
  exact hne a (funext ha)

/-- Equality in the first Laguerre inequality occurs exactly at a multiple
zero, or for an ordinary real exponential. This includes the zero function. -/
theorem IsLaguerrePolya.laguerre_one_eq_zero_iff {f : ℂ → ℂ}
    (hf : IsLaguerrePolya f) (x : ℝ) :
    laguerreCoefficient f x 1 = 0 ↔
      (f x = 0 ∧ _root_.deriv f x = 0) ∨ ∃ a : ℝ, ∀ z, f z = f 0 * exp ((a : ℂ) * z) := by
  constructor
  · intro heq
    by_cases hfx : f x = 0
    · left
      refine ⟨hfx, ?_⟩
      rw [laguerreCoefficient_one hf.differentiable hf.conj, hfx] at heq
      have hre : (_root_.deriv f x).re = 0 := by simpa using heq
      have hc : ((_root_.deriv f x).re : ℂ) = _root_.deriv f x := by
        apply conj_eq_iff_re.mp
        simpa using (hf.deriv.conj (x : ℂ)).symm
      rw [← hc, hre, ofReal_zero]
    · exact Or.inr (hf.eq_exp_of_laguerre_one_eq_zero hfx heq)
  · rintro (⟨hfx, hdf⟩ | ⟨a, ha⟩)
    · rw [laguerreCoefficient_one hf.differentiable hf.conj]
      simp [hfx, hdf]
    · have hc : ((f 0).re : ℂ) = f 0 := by
        simpa only [iteratedDeriv_zero] using ofReal_re_iteratedDeriv_zero hf.conj 0
      have heq : f = fun z => ((f 0).re : ℂ) *
          exp ((a : ℂ) * z + ((0 : ℝ) : ℂ) * z ^ 2) := by
        funext z
        simpa only [hc, ofReal_zero, zero_mul, add_zero] using ha z
      rw [heq, laguerreCoefficient_one_exp_quadratic]
      simp

end RealRooted
