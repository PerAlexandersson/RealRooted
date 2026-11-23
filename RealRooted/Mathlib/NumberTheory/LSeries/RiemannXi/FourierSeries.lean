/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.FourierSummand
import Mathlib.Analysis.Calculus.SmoothSeries
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.FourierMajorant

/-!
# The xi Fourier kernel and its actual derivatives

The all-natural-index sum includes a zero summand at index zero, so it equals
the positive-index Fourier series. Absolute local derivative majorants justify
differentiation to every order on the whole real line.
-/

public section

open Real Set
open scoped ContDiff

/-- The Fourier kernel in the even integral representation of the Riemann xi function. -/
@[expose] noncomputable def riemannXiFourierKernel (t : ℝ) : ℝ :=
  ∑' n : ℕ, riemannXiFourierTerm 0 n t

/-- The artificial zeroth lattice term vanishes at every derivative order. -/
@[simp] theorem riemannXiFourierTerm_zero_index (j : ℕ) (t : ℝ) :
    riemannXiFourierTerm j 0 t = 0 := by simp [riemannXiFourierTerm]

/-- Termwise differentiation of every derivative series is valid at every real point. -/
theorem hasDerivAt_tsum_riemannXiFourierTerm (j : ℕ) (t : ℝ) :
    HasDerivAt (fun x => ∑' n : ℕ, riemannXiFourierTerm j n x)
      (∑' n : ℕ, riemannXiFourierTerm (j + 1) n t) t := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_summable_bound_riemannXiFourierTerm (j + 1) (t - 1) (t + 1)
  have ht : t ∈ Ioo (t - 1) (t + 1) := by constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected hM isOpen_Ioo isPreconnected_Ioo
    (fun n x _ => hasDerivAt_riemannXiFourierTerm j n x)
    (fun n x hx => hbound n x ⟨hx.1.le, hx.2.le⟩) ht
    (summable_riemannXiFourierTerm j t) ht

/-- The polynomial summands give the actual iterated derivatives of the full Fourier kernel. -/
theorem iteratedDeriv_riemannXiFourierKernel (j : ℕ) :
    iteratedDeriv j riemannXiFourierKernel =
      fun t => ∑' n : ℕ, riemannXiFourierTerm j n t := by
  induction j with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun t => (hasDerivAt_tsum_riemannXiFourierTerm j t).deriv

/-- Each iterated derivative of the Fourier kernel is continuous on the real line. -/
theorem continuous_iteratedDeriv_riemannXiFourierKernel (j : ℕ) :
    Continuous (iteratedDeriv j riemannXiFourierKernel) := by
  rw [iteratedDeriv_riemannXiFourierKernel]
  exact continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_tsum_riemannXiFourierTerm j t).continuousAt

/-- The Fourier kernel is smooth to every finite order on the whole real line. -/
theorem contDiff_riemannXiFourierKernel : ContDiff ℝ ∞ riemannXiFourierKernel := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j _
  rw [iteratedDeriv_riemannXiFourierKernel]
  exact fun t => (hasDerivAt_tsum_riemannXiFourierTerm j t).differentiableAt
