module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.IteratedDerivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GeneralizedInequality
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.LaguerreInequalities.DerivativeFormula
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Analytic.Order

/-!
# Simple zeros along Laguerre--Pólya backward heat flows

A local parameter family of LP functions satisfying the backward heat equation
for all spatial Taylor derivatives has only simple zeros at every nonzero
interior time slice. The proof is the local mechanism in Craven–Csordas (1994),
Theorem 3.10: a double zero makes the first Laguerre form a local minimum, but
its time derivative is the square of the second spatial derivative. Iteration
and analyticity exclude every finite or infinite multiplicity above one.

The statements assume a flow and its parameter derivatives explicitly. They
do not assert convergence of an infinite heat-operator series on entire inputs.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- At a double zero, a nonnegative Laguerre form along a backward heat jet
forces the second jet to vanish. -/
private theorem heat_jet_zero_of_local_nonneg {A B C : ℝ → ℝ} {t b c : ℝ}
    (hA : HasDerivAt A (-C t) t) (hB : HasDerivAt B b t) (hC : HasDerivAt C c t)
    (hn : ∀ᶠ s in 𝓝 t, 0 ≤ B s ^ 2 - A s * C s) (h0 : A t = 0) (h1 : B t = 0) :
    C t = 0 := by
  have hm : IsLocalMin (fun s => B s ^ 2 - A s * C s) t := by
    filter_upwards [hn] with s hs
    simpa only [h0, h1, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] using hs
  have hd := (hB.pow 2).sub (hA.mul hC)
  have heq := hm.hasDerivAt_eq_zero hd
  simp only [h0, h1, zero_pow (by decide : 2 - 1 ≠ 0), mul_zero, zero_mul] at heq
  nlinarith [sq_nonneg (C t)]

/-- Every real zero in a nonzero interior slice of a local backward heat flow
of LP functions is simple. The heat equation is assumed for every spatial jet. -/
theorem deriv_ne_zero_of_laguerrePolya_heat_flow {u : ℝ → ℂ → ℂ} {t x : ℝ}
    (hLP : ∀ᶠ s in 𝓝 t, IsLaguerrePolya (u s)) (hne : ∃ z, u t z ≠ 0)
    (hheat : ∀ n, HasDerivAt (fun s => (iteratedDeriv n (u s) (x : ℂ)).re)
      (-(iteratedDeriv (n + 2) (u t) (x : ℂ)).re) t)
    (hz : u t x = 0) : _root_.deriv (u t) x ≠ 0 := by
  intro hd
  have hf : IsLaguerrePolya (u t) := hLP.self_of_nhds
  have hstep (n : ℕ) (h0 : (iteratedDeriv n (u t) (x : ℂ)).re = 0)
      (h1 : (iteratedDeriv (n + 1) (u t) (x : ℂ)).re = 0) :
      (iteratedDeriv (n + 2) (u t) (x : ℂ)).re = 0 := by
    apply heat_jet_zero_of_local_nonneg (hheat n) (hheat (n + 1)) (hheat (n + 2)) _ h0 h1
    filter_upwards [hLP] with s hs
    have hds := hs.iteratedDeriv n
    have h := hds.laguerreCoefficient_nonneg x 1
    rw [laguerreCoefficient_one hds.differentiable hds.conj] at h
    simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero,
      Nat.add_assoc] using h
  have hall_re : ∀ n, (iteratedDeriv n (u t) (x : ℂ)).re = 0 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp only [iteratedDeriv_zero, hz, zero_re]
    | one => simp only [iteratedDeriv_one, hd, zero_re]
    | more n hn hn1 => exact hstep n hn hn1
  have hall : ∀ n, iteratedDeriv n (u t) (x : ℂ) = 0 := by
    intro n
    have hr : ((iteratedDeriv n (u t) (x : ℂ)).re : ℂ) =
        iteratedDeriv n (u t) (x : ℂ) := by
      apply conj_eq_iff_re.mp
      simpa using (iteratedDeriv_conj hf.conj n (x : ℂ)).symm
    rw [← hr, hall_re n, ofReal_zero]
  have htop : analyticOrderAt (u t) (x : ℂ) = ⊤ := by
    apply ENat.eq_top_iff_forall_ge.mpr
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (hf.differentiable.analyticAt _)).mpr (fun j _ => hall j)
  obtain ⟨z, hz⟩ := hne
  have hfinite := hf.analyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ z) (Set.mem_univ (x : ℂ))
    (by simp [analyticOrderAt_eq_zero.mpr (.inr hz)])
  exact hfinite htop

/-- All complex zeros in a nonzero LP backward heat slice are simple.
Their reality follows from LP membership, so the heat equation is needed
only at real spatial points. -/
theorem deriv_ne_zero_of_laguerrePolya_heat_flow_complex {u : ℝ → ℂ → ℂ} {t : ℝ}
    (hLP : ∀ᶠ s in 𝓝 t, IsLaguerrePolya (u s)) (hne : ∃ z, u t z ≠ 0)
    (hheat : ∀ x : ℝ, ∀ n,
      HasDerivAt (fun s => (iteratedDeriv n (u s) (x : ℂ)).re)
        (-(iteratedDeriv (n + 2) (u t) (x : ℂ)).re) t)
    {z : ℂ} (hz : u t z = 0) : _root_.deriv (u t) z ≠ 0 := by
  have hf : IsLaguerrePolya (u t) := hLP.self_of_nhds
  have hf0 : u t ≠ 0 := by
    intro heq
    obtain ⟨w, hw⟩ := hne
    exact hw (congrFun heq w)
  have him := hf.im_eq_zero_of_eq_zero hf0 hz
  have heq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  rw [← heq] at hz ⊢
  exact deriv_ne_zero_of_laguerrePolya_heat_flow hLP hne (hheat z.re) hz

end RealRooted
