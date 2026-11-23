/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

import RealRooted.Interlacing.RootPerturbation
public import RealRooted.SimpleRoots
public import RealRooted.Basic.Coefficients
import RealRooted.Wronskian.Forward
import RealRooted.Bezoutian.WronskianConverse
import RealRooted.ObreschkoffConverse.Forward
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Simple pencils from strict interlacing

A coprime adjacent-degree pair has a strictly signed Wronskian. Adding any
multiple of the lower polynomial preserves that Wronskian and therefore excludes
multiple roots of every pencil member. Coefficient perturbations yield uniform
pencil conclusions for all real parameters at once.
-/

public section

open Polynomial Filter Topology

namespace RealRooted

/-- A nonzero scalar preserves simple real-rootedness. -/
theorem IsSimpleRealRooted.C_mul {p : ℝ[X]} (hp : IsSimpleRealRooted p)
    {c : ℝ} (hc : c ≠ 0) : IsSimpleRealRooted (C c * p) :=
  ⟨mul_ne_zero (C_ne_zero.mpr hc) hp.1, hp.2.1.C_mul c, hp.2.2.C_mul hc⟩

/-- Every right pencil member of a genuinely strict adjacent-degree pair is
simple and real-rooted. The lower polynomial may be constant. -/
theorem StrictInterl.isSimpleRealRooted_add_C_mul {p q : ℝ[X]}
    (h : StrictInterl p q) (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x) (c : ℝ) :
    IsSimpleRealRooted (q + C c * p) := by
  have hsimple := h.hasSimpleRoots_of_no_common_root fun x hx => hno x hx.1 hx.2
  have hW := wronskian_pos_of_strictInterl_succ hq hp hdeg h
    hsimple.2.roots_nodup hsimple.1.roots_nodup (fun x hxq hxp => hno x hxp hxq)
  have hsmall : (C c * p).natDegree < q.natDegree := by
    have hle := natDegree_C_mul_le c p
    lia
  have hdegree : (q + C c * p).natDegree = q.natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hsmall
  have hne : q + C c * p ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hdegree
    lia
  have hsplit : (q + C c * p).Splits := by
    simpa only [C_1, one_mul, add_comm] using (allComboRealRooted_of_strictInterl h) c 1
  have hW' (x : ℝ) :
      0 < (q + C c * p).derivative.eval x * p.eval x -
        (q + C c * p).eval x * p.derivative.eval x := by
    convert hW x using 1
    simp only [derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C]
    ring
  exact ⟨hne, hsplit,
    HasSimpleRoots.of_roots_nodup hne (Polynomial.roots_nodup_of_wronskian_pos hW').2⟩

/-- Every nontrivial real linear combination of a genuinely strict adjacent-degree
pair has simple real roots, including the constant endpoint in degree zero. -/
theorem StrictInterl.isSimpleRealRooted_C_mul_add_C_mul {p q : ℝ[X]}
    (h : StrictInterl p q) (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x)
    (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    IsSimpleRealRooted (C a * p + C b * q) := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (fun h => h hb)
    have hsimple := h.hasSimpleRoots_of_no_common_root fun x hx => hno x hx.1 hx.2
    simpa only [hb, C_0, zero_mul, add_zero] using
      (show IsSimpleRealRooted p from ⟨h.1.1, h.1.2, hsimple.1⟩).C_mul ha
  · have hf := (h.isSimpleRealRooted_add_C_mul hp hq hdeg hno (a / b)).C_mul hb
    have heq : C b * (q + C (a / b) * p) = C a * p + C b * q := by
      rw [mul_add, ← mul_assoc, ← C_mul]
      have hscalar : b * (a / b) = a := by
        rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hb, mul_one]
      rw [hscalar, add_comm]
    rwa [heq] at hf

/-- Independent coefficient perturbations of a genuinely strict monic reference
pair eventually yield simple pencils for every nontrivial real parameter pair. -/
theorem eventually_isSimpleRealRooted_pencil_of_coeff_tendsto
    {ι : Type*} {l : Filter ι} {P Q : ι → ℝ[X]} {p q : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : IsMonicOfDegree q (n + 1))
    (h : StrictInterl p q) (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x)
    (hPdeg : ∀ᶠ t in l, (P t).natDegree ≤ n)
    (hQdeg : ∀ᶠ t in l, (Q t).natDegree ≤ n + 1)
    (hPc : ∀ k ≤ n, Tendsto (fun t => (P t).coeff k) l (𝓝 (p.coeff k)))
    (hQc : ∀ k ≤ n + 1, Tendsto (fun t => (Q t).coeff k) l (𝓝 (q.coeff k))) :
    ∀ᶠ t in l, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      IsSimpleRealRooted (C a * P t + C b * Q t) := by
  have hinter := eventually_interlaces_of_coeff_tendsto hp hq h hno hPdeg hQdeg hPc hQc
  have hpcoeff : p.coeff n = 1 := by rw [← hp.natDegree_eq, hp.monic.coeff_natDegree]
  have hqcoeff : q.coeff (n + 1) = 1 := by rw [← hq.natDegree_eq, hq.monic.coeff_natDegree]
  have hPpos : ∀ᶠ t in l, 0 < (P t).coeff n := by
    apply tendsto_const_nhds.eventually_lt (hPc n le_rfl)
    rw [hpcoeff]
    exact zero_lt_one
  have hQpos : ∀ᶠ t in l, 0 < (Q t).coeff (n + 1) := by
    apply tendsto_const_nhds.eventually_lt (hQc (n + 1) le_rfl)
    rw [hqcoeff]
    exact zero_lt_one
  filter_upwards [hinter, hPpos, hQpos] with t ht hp' hq'
  have hPle : HasPosLeadingCoeff (P t) := by
    change 0 < (P t).leadingCoeff
    rw [leadingCoeff, ht.1]
    exact hp'
  have hQle : HasPosLeadingCoeff (Q t) := by
    change 0 < (Q t).leadingCoeff
    rw [leadingCoeff, ht.2.1]
    exact hq'
  exact ht.2.2.1.toStrictInterl.isSimpleRealRooted_C_mul_add_C_mul hPle hQle
    (by rw [ht.1, ht.2.1]) ht.2.2.2

end RealRooted
