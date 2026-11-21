/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Toeplitz.SchurSign
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.Ring

/-!
# Finite-degree transfer from rectangular Schur evaluations

We formalize the sign-change step of Proposition 3 of the unpublished manuscript
*Real limiting spectra for balanced five-diagonal Toeplitz matrices* (2026-10-29),
tracked in RealRooted issue #2157. We use the existing interval root-count theorem.
The Toeplitz--Schur identity and analytic construction of the grid remain separate
inputs: this module does not assert the real-limit implication.
-/

public section

open Polynomial

namespace RealRooted.Toeplitz

/-- Schur grid evaluations with neighboring outer parameters and scale factors of
matching signs force all roots of a degree-`n` real polynomial to be simple and real.
Every root lies strictly between the outermost sample points.

For Toeplitz sections the evaluation identity is the dual Jacobi--Trudi correspondence;
it is retained as an algebraic input here, rather than assuming any root conclusion.
Continuity and nonvanishing of the outer parameter and radius give the two product
conditions in a root parametrization. -/
theorem splits_of_schurGrid {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0) (hdegree : p.natDegree ≤ n)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (a c scale : Fin (n + 1) → ℝ)
    (ha : ∀ i, |a i| < 1) (hc : ∀ i, 1 < |c i|)
    (hcc : ∀ i : Fin n, 0 < c i.castSucc * c i.succ)
    (hscale : ∀ i : Fin n, 0 < scale i.castSucc * scale i.succ)
    (heval : ∀ i : Fin (n + 1), ((p.eval (x i) : ℝ) : ℂ) =
      (scale i : ℂ) * rectangularSchurQuotient n (a i) (c i)
        (Complex.exp (((((i.val + 1 : ℕ) : ℝ) * Real.pi / (n + 2) : ℝ) : ℂ) * Complex.I))
        (Complex.exp (((-(((i.val + 1 : ℕ) : ℝ) * Real.pi / (n + 2)) : ℝ) : ℂ) *
          Complex.I))) :
    p.natDegree = n ∧ p.Splits ∧ p.roots.Nodup ∧
      ∀ z ∈ p.roots, x 0 < z ∧ z < x (Fin.last n) := by
  let q (i : Fin (n + 1)) : ℝ :=
    (rectangularSchurQuotient n (a i) (c i)
      (Complex.exp (((((i.val + 1 : ℕ) : ℝ) * Real.pi / (n + 2) : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((-(((i.val + 1 : ℕ) : ℝ) * Real.pi / (n + 2)) : ℝ) : ℂ) *
        Complex.I))).re
  have hs (i : Fin (n + 1)) :
      0 < (-1 : ℝ) ^ (i.val + 2) * c i ^ (n + 2) * q i :=
    rectangularSchurQuotient_grid_signed_pos n (i.val + 1) (a i) (c i)
      (ha i) (hc i) (by lia) (by lia)
  have he (i : Fin (n + 1)) : p.eval (x i) = scale i * q i := by
    have h := congrArg Complex.re (heval i)
    simpa [q, Complex.mul_re] using h
  apply Polynomial.splits_nodup_roots_of_strict_sign_changes hp hdegree x hx
  intro i
  let ε : ℝ := (-1) ^ (i.val + 2)
  have hε : ε ^ 2 = 1 := by
    dsimp [ε]
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  have h1 : 0 < ε * c i.castSucc ^ (n + 2) * q i.castSucc := hs i.castSucc
  have h2 : 0 < -ε * c i.succ ^ (n + 2) * q i.succ := by
    simpa [ε, pow_succ, mul_assoc] using hs i.succ
  have hprod := mul_pos h1 h2
  have hid :
      (ε * c i.castSucc ^ (n + 2) * q i.castSucc) *
        (-ε * c i.succ ^ (n + 2) * q i.succ) =
      -(c i.castSucc * c i.succ) ^ (n + 2) * (q i.castSucc * q i.succ) := by
    calc
      _ = -ε ^ 2 * (c i.castSucc * c i.succ) ^ (n + 2) *
          (q i.castSucc * q i.succ) := by rw [mul_pow]; ring
      _ = _ := by rw [hε]; ring
  rw [hid] at hprod
  have hC : 0 < (c i.castSucc * c i.succ) ^ (n + 2) := pow_pos (hcc i) _
  have hq : q i.castSucc * q i.succ < 0 := by nlinarith
  rw [he, he]
  have ht := mul_neg_of_pos_of_neg (hscale i) hq
  convert ht using 1
  ring

/-- A continuous separated outer root and a monotone spectral parameter turn the
Schur formula into simple real roots in every degree. The formula is an explicit
algebraic input, representing the still separate Toeplitz--Schur correspondence;
no real-rootedness or root-count conclusion is assumed. The radius and inner root
need only satisfy their pointwise bounds. -/
theorem splits_of_schurParametrization {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0) (hdegree : p.natDegree ≤ n)
    (x a c r : ℝ → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hx : StrictMonoOn x (Set.Ioo 0 Real.pi))
    (hccont : ContinuousOn c (Set.Ioo 0 Real.pi))
    (ha : ∀ θ ∈ Set.Ioo 0 Real.pi, |a θ| < 1)
    (hc : ∀ θ ∈ Set.Ioo 0 Real.pi, 1 < |c θ|)
    (hr : ∀ θ ∈ Set.Ioo 0 Real.pi, 0 < r θ)
    (heval : ∀ θ ∈ Set.Ioo 0 Real.pi, ((p.eval (x θ) : ℝ) : ℂ) =
      ((κ * r θ ^ (2 * n) : ℝ) : ℂ) *
        rectangularSchurQuotient n (a θ) (c θ)
          (Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.exp ((-θ : ℝ) * Complex.I))) :
    p.natDegree = n ∧ p.Splits ∧ p.roots.Nodup ∧
      ∀ z ∈ p.roots, x (Real.pi / (n + 2)) < z ∧
        z < x (((n : ℝ) + 1) * Real.pi / (n + 2)) := by
  let θ (i : Fin (n + 1)) : ℝ := (i.val + 1 : ℕ) * Real.pi / (n + 2)
  have hθ (i : Fin (n + 1)) : θ i ∈ Set.Ioo 0 Real.pi := by
    have hd : 0 < (n : ℝ) + 2 := by positivity
    constructor
    · dsimp [θ]
      positivity
    · dsimp [θ]
      rw [div_lt_iff₀ hd]
      have hi : ((i.val + 1 : ℕ) : ℝ) < (n : ℝ) + 2 := by
        exact_mod_cast (show i.val + 1 < n + 2 by lia)
      simpa only [mul_comm Real.pi] using mul_lt_mul_of_pos_right hi Real.pi_pos
  have hθmono : StrictMono θ := by
    intro i j hij
    dsimp [θ]
    apply div_lt_div_of_pos_right _ (by positivity : 0 < (n : ℝ) + 2)
    apply mul_lt_mul_of_pos_right _ Real.pi_pos
    exact_mod_cast (show i.val + 1 < j.val + 1 by exact Nat.add_lt_add_right hij 1)
  have hcprod (u v : ℝ) (hu : u ∈ Set.Ioo 0 Real.pi) (hv : v ∈ Set.Ioo 0 Real.pi) :
      0 < c u * c v := by
    have hnz (t : ℝ) (ht : t ∈ Set.Ioo 0 Real.pi) : c t ≠ 0 := by
      intro h
      have := hc t ht
      norm_num [h] at this
    by_contra h
    have hm : c u * c v < 0 := lt_of_le_of_ne (le_of_not_gt h)
      (mul_ne_zero (hnz u hu) (hnz v hv))
    rcases mul_neg_iff.mp hm with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · obtain ⟨t, ht, he⟩ := isPreconnected_Ioo.intermediate_value hv hu hccont
        (show (0 : ℝ) ∈ Set.Icc (c v) (c u) from ⟨hv'.le, hu'.le⟩)
      exact hnz t ht he
    · obtain ⟨t, ht, he⟩ := isPreconnected_Ioo.intermediate_value hu hv hccont
        (show (0 : ℝ) ∈ Set.Icc (c u) (c v) from ⟨hu'.le, hv'.le⟩)
      exact hnz t ht he
  have h := splits_of_schurGrid hp hdegree (fun i => x (θ i))
    (fun i j hij => hx (hθ i) (hθ j) (hθmono hij))
    (fun i => a (θ i)) (fun i => c (θ i)) (fun i => κ * r (θ i) ^ (2 * n))
    (fun i => ha _ (hθ i)) (fun i => hc _ (hθ i))
    (fun i => hcprod _ _ (hθ i.castSucc) (hθ i.succ))
    (fun i => by
      have hpowers := mul_pos (pow_pos (hr _ (hθ i.castSucc)) (2 * n))
        (pow_pos (hr _ (hθ i.succ)) (2 * n))
      have ht := mul_pos (mul_self_pos.mpr hκ) hpowers
      convert ht using 1
      ring)
    (fun i => heval _ (hθ i))
  simpa [θ] using h

/-- The decreasing-parameter version of `splits_of_schurParametrization`, obtained
by reflecting the spectral variable. The algebraic input remains the same Schur
formula, and the bounding grid points occur in the opposite order. -/
theorem splits_of_schurParametrization_antitone {p : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0) (hdegree : p.natDegree ≤ n)
    (x a c r : ℝ → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hx : StrictAntiOn x (Set.Ioo 0 Real.pi))
    (hccont : ContinuousOn c (Set.Ioo 0 Real.pi))
    (ha : ∀ θ ∈ Set.Ioo 0 Real.pi, |a θ| < 1)
    (hc : ∀ θ ∈ Set.Ioo 0 Real.pi, 1 < |c θ|)
    (hr : ∀ θ ∈ Set.Ioo 0 Real.pi, 0 < r θ)
    (heval : ∀ θ ∈ Set.Ioo 0 Real.pi, ((p.eval (x θ) : ℝ) : ℂ) =
      ((κ * r θ ^ (2 * n) : ℝ) : ℂ) *
        rectangularSchurQuotient n (a θ) (c θ)
          (Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.exp ((-θ : ℝ) * Complex.I))) :
    p.natDegree = n ∧ p.Splits ∧ p.roots.Nodup ∧
      ∀ z ∈ p.roots, x (((n : ℝ) + 1) * Real.pi / (n + 2)) < z ∧
        z < x (Real.pi / (n + 2)) := by
  have hp' : p.comp (-X) ≠ 0 := comp_neg_X_eq_zero_iff.not.mpr hp
  have hd' : (p.comp (-X)).natDegree ≤ n := by simpa [natDegree_comp] using hdegree
  have hx' : StrictMonoOn (fun t => -x t) (Set.Ioo 0 Real.pi) := by
    intro u hu v hv huv
    exact neg_lt_neg (hx hu hv huv)
  have he' (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
      (((p.comp (-X)).eval (-x θ) : ℝ) : ℂ) =
      ((κ * r θ ^ (2 * n) : ℝ) : ℂ) *
        rectangularSchurQuotient n (a θ) (c θ)
          (Complex.exp ((θ : ℂ) * Complex.I))
          (Complex.exp ((-θ : ℝ) * Complex.I)) := by
    simpa using heval θ hθ
  obtain ⟨hd, hs, hn, hb⟩ := splits_of_schurParametrization hp' hd'
    (fun t => -x t) a c r κ hκ hx' hccont ha hc hr he'
  refine ⟨by simpa [natDegree_comp] using hd, ?_, ?_, ?_⟩
  · simpa [comp_neg_X_comp_neg_X] using hs.comp_neg_X
  · rw [roots_comp_neg_X] at hn
    exact hn.of_map
  · intro z hz
    have hz' : -z ∈ (p.comp (-X)).roots := by
      rw [roots_comp_neg_X]
      exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
    obtain ⟨hl, hu⟩ := hb (-z) hz'
    constructor <;> linarith

end RealRooted.Toeplitz
