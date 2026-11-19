module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact dominant-pair expansions

The domain is an arbitrary set; the phase theorem will require it to be order connected.
This includes bounded open intervals and either open ray without special endpoint data.
The expansion starts at `first`, allowing a polynomial part in a rational generating function.
An instance supplies the exact expansion, rather than assuming its real-rootedness conclusion.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

/-- Exact conjugate-pair expansion. The eigenvalue and amplitude are continuous on `J`,
the eigenvalue lies in the upper half-plane, and the amplitude never vanishes.
The real remainder is deliberately separate from its domination certificates. -/
structure PairExpansion (P : ℕ → Polynomial ℝ) (J : Set ℝ) where
  /-- First index after the polynomial part of the generating function. -/
  first : ℕ
  /-- Upper-half-plane eigenvalue. -/
  lam : ℝ → ℂ
  /-- Coefficient of the dominant eigenvalue. -/
  amplitude : ℝ → ℂ
  /-- Exact real remainder. -/
  rest : ℕ → ℝ → ℝ
  /-- Continuity of the chosen eigenvalue branch. -/
  continuousOn_lam : ContinuousOn lam J
  /-- Continuity of the amplitude. -/
  continuousOn_amplitude : ContinuousOn amplitude J
  /-- The branch stays in the open upper half-plane. -/
  im_pos : ∀ t ∈ J, 0 < (lam t).im
  /-- The dominant amplitude has no zeros. -/
  amplitude_ne_zero : ∀ t ∈ J, amplitude t ≠ 0
  /-- Exact expansion after the polynomial part. -/
  expand : ∀ n, first ≤ n → ∀ t ∈ J,
    (P n).eval t = 2 * (amplitude t * lam t ^ n).re + rest n t

namespace PairExpansion

variable {P : ℕ → Polynomial ℝ} {J : Set ℝ} (h : PairExpansion P J)

/-- Strict domination of the exact remainder at one index and point. -/
def Dominates (n : ℕ) (t : ℝ) : Prop :=
  |h.rest n t| < 2 * ‖h.amplitude t‖ * ‖h.lam t‖ ^ n

/-- Domination on `S` for every index at least `N`. The phase theorem separately checks
that the index is after `first` and that the sample points belong to `J`. -/
def Dom (S : Set ℝ) (N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ t ∈ S, h.Dominates n t

/-- The upper-half-plane branch is nonzero. -/
theorem lam_ne_zero {t : ℝ} (ht : t ∈ J) : h.lam t ≠ 0 := by
  intro heq
  have := h.im_pos t ht
  simp [heq] at this

/-- The dominant oscillation has positive modulus. -/
theorem norm_amplitude_mul_pow_pos {t : ℝ} (ht : t ∈ J) (n : ℕ) :
    0 < ‖h.amplitude t‖ * ‖h.lam t‖ ^ n := by
  exact mul_pos (norm_pos_iff.mpr (h.amplitude_ne_zero t ht))
    (pow_pos (norm_pos_iff.mpr (h.lam_ne_zero ht)) n)

/-- A domination certificate remains valid after increasing the cutoff. -/
theorem Dom.mono_index {S : Set ℝ} {N M : ℕ} (hd : h.Dom S N) (hNM : N ≤ M) :
    h.Dom S M := by
  intro n hn t ht
  exact hd n (hNM.trans hn) t ht

/-- Restrict a domination certificate to a smaller set. -/
theorem Dom.mono_set {S T : Set ℝ} {N : ℕ} (hd : h.Dom S N) (hTS : T ⊆ S) :
    h.Dom T N := by
  intro n hn t ht
  exact hd n hn t (hTS ht)

/-- Certificates on two regions combine at the larger cutoff. -/
theorem Dom.union {S T : Set ℝ} {N M : ℕ} (hS : h.Dom S N) (hT : h.Dom T M) :
    h.Dom (S ∪ T) (max N M) := by
  intro n hn t ht
  rcases ht with ht | ht
  · exact hS n ((le_max_left N M).trans hn) t ht
  · exact hT n ((le_max_right N M).trans hn) t ht

/-- With no remainder, every index is dominated. This is the order-two supplier. -/
theorem dom_of_rest_eq_zero {S : Set ℝ} (hS : S ⊆ J)
    (hr : ∀ n t, t ∈ S → h.rest n t = 0) : h.Dom S 0 := by
  intro n _ t ht
  unfold Dominates
  rw [hr n t ht, abs_zero]
  have := h.norm_amplitude_mul_pow_pos (hS ht) n
  linarith

end PairExpansion
end RealRooted.EffectiveBKW
