import RealRooted.Interlacing.NegativeRoots
import RealRooted.Interlacing.OuterDifference
import RealRooted.Interlacing.ResidueCriterion
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.MaWang.StrictStep

/-!
# Residue-controlled Euler steps

This file packages a strict Ma--Wang step whose derivative-sign auxiliary is
obtained from the positive-point residue criterion. An additional interlacing
tail with nonnegative weight preserves the strict sign at every old root.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- An Euler derivative step with a residue-controlled predecessor and an
additional interlacing tail. -/
def residueEulerStep (a b : ℝ) (f h r : ℝ[X]) : ℝ[X] :=
  X * (1 - X) * f.derivative +
    (1 + C ((f.natDegree : ℝ) + 1) * X) * f -
      C a * X * h + C b * X * r

/-- The Euler step separates into its old row, residue auxiliary, and
interlacing tail. -/
theorem residueEulerStep_eq (a b : ℝ) (f h r : ℝ[X]) :
    residueEulerStep a b f h r =
      (1 + X) * f + X * residueAuxiliary 1 a f h + C b * X * r := by
  simp [residueEulerStep, residueAuxiliary]
  ring

/-- The residue-controlled Euler step raises degree exactly once and preserves
the leading coefficient. -/
theorem natDegree_and_leadingCoeff_residueEulerStep
    {f h r : ℝ[X]} (hf : f ≠ 0)
    (hhdeg : h.natDegree < f.natDegree)
    (hrdeg : r.natDegree < f.natDegree) (a b : ℝ) :
    (residueEulerStep a b f h r).natDegree = f.natDegree + 1 ∧
      (residueEulerStep a b f h r).leadingCoeff = f.leadingCoeff := by
  let tail : ℝ[X] := -C a * X * h + C b * X * r
  have hhX : (X * h).natDegree ≤ f.natDegree := by
    calc
      (X * h).natDegree ≤ X.natDegree + h.natDegree := natDegree_mul_le
      _ ≤ f.natDegree := by simp only [natDegree_X]; lia
  have hrX : (X * r).natDegree ≤ f.natDegree := by
    calc
      (X * r).natDegree ≤ X.natDegree + r.natDegree := natDegree_mul_le
      _ ≤ f.natDegree := by simp only [natDegree_X]; lia
  have hleft : (-C a * X * h).natDegree ≤ f.natDegree := by
    simpa [mul_assoc] using (natDegree_C_mul_le (-a) (X * h)).trans hhX
  have hright : (C b * X * r).natDegree ≤ f.natDegree := by
    simpa [mul_assoc] using (natDegree_C_mul_le b (X * r)).trans hrX
  have htail : tail.natDegree ≤ f.natDegree := by
    exact (natDegree_add_le _ _).trans (max_le hleft hright)
  have htop :
      ((-1 : ℝ) * (f.natDegree : ℝ) + ((f.natDegree : ℝ) + 1)) *
          f.leadingCoeff ≠ 0 := by
    simpa using leadingCoeff_ne_zero.mpr hf
  have hdegree :=
    Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
      f tail 1 (-1) 1 ((f.natDegree : ℝ) + 1) htail htop
  have hform :
      residueEulerStep a b f h r =
        (C 1 * X + C (-1) * X ^ 2) * f.derivative +
          (C 1 + C ((f.natDegree : ℝ) + 1) * X) * f + tail := by
    simp [residueEulerStep, tail]
    ring
  rw [hform]
  refine ⟨hdegree.1, hdegree.2.trans ?_⟩
  ring

/-- A monic input gives a monic residue-controlled Euler step. -/
theorem monic_residueEulerStep
    {f h r : ℝ[X]} (hf : f.Monic)
    (hhdeg : h.natDegree < f.natDegree)
    (hrdeg : r.natDegree < f.natDegree) (a b : ℝ) :
    (residueEulerStep a b f h r).Monic := by
  rw [Monic.def,
    (natDegree_and_leadingCoeff_residueEulerStep hf.ne_zero hhdeg hrdeg a b).2,
    hf.leadingCoeff]

/-- A positive-point residue gap, together with a nonnegative interlacing
tail, gives a strict proper-position successor with simple negative roots. -/
theorem residueEulerStep_strict_package
    {f h r : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hfdeg : 1 ≤ f.natDegree)
    (hf_simple : HasSimpleRoots f)
    (hf_neg : ∀ x, f.IsRoot x → x < 0)
    (hhf : StrictInterl h f) (hh_pos : HasPosLeadingCoeff h)
    (hhdeg : h.degree < f.natDegree)
    (hrf : Interlaces r f) (hr_pos : HasPosLeadingCoeff r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgap : a * h.eval 1 < f.eval 1) :
    Interlaces (residueAuxiliary 1 a f h) f ∧
      StrictInterl f (residueEulerStep a b f h r) ∧
      (∀ x, f.IsRoot x → ¬ (residueEulerStep a b f h r).IsRoot x) ∧
      HasSimpleRoots (residueEulerStep a b f h r) ∧
      ∀ x, (residueEulerStep a b f h r).IsRoot x → x < 0 := by
  have hhNat : h.natDegree < f.natDegree := by
    rw [degree_eq_natDegree hh_pos.ne_zero] at hhdeg
    exact_mod_cast hhdeg
  have hrNat : r.natDegree < f.natDegree := by
    have hrsucc := hrf.2.2.1
    lia
  have hdegree := natDegree_and_leadingCoeff_residueEulerStep
    hf_pos.ne_zero hhNat hrNat a b
  have hstep_pos : HasPosLeadingCoeff (residueEulerStep a b f h r) := by
    unfold HasPosLeadingCoeff
    rw [hdegree.2]
    exact hf_pos
  have hroots_lt_one : ∀ x ∈ f.roots, x < (1 : ℝ) := by
    intro x hx
    have hxroot : f.IsRoot x := (mem_roots hf_pos.ne_zero).mp hx
    linarith [hf_neg x hxroot]
  have haux_interlaces : Interlaces (residueAuxiliary 1 a f h) f :=
    residueAuxiliary_interlaces hhf hf_pos hh_pos
      hfdeg hhdeg hf_simple ha hroots_lt_one hgap
  have haux_sign : ∀ x, f.IsRoot x →
      0 < (residueAuxiliary 1 a f h).eval x * f.derivative.eval x := by
    intro x hx
    exact residueAuxiliary_eval_mul_derivative_pos
      hhf hf_pos hh_pos hfdeg hhdeg hf_simple
        ha hroots_lt_one hgap hx
  let tail : ℝ[X] := C b * X * r
  have hrec :
      residueEulerStep a b f h r =
        (1 + X) * f + X * residueAuxiliary 1 a f h + tail := by
    simpa only [tail] using residueEulerStep_eq a b f h r
  have hX_neg : ∀ x, f.IsRoot x → X.eval x < 0 := by
    intro x hx
    simpa using hf_neg x hx
  have htail_nonpos : ∀ x, f.IsRoot x →
      tail.eval x * f.derivative.eval x ≤ 0 := by
    intro x hx
    have hx_neg := hf_neg x hx
    have htail_sign :
        0 ≤ r.eval x * f.derivative.eval x :=
      eval_mul_derivative_nonneg_of_prec_right_root
        hrf.toStrictInterl hr_pos hf_pos hx
    have hweighted :
        b * x * (r.eval x * f.derivative.eval x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hb hx_neg.le) htail_sign
    have heval :
        tail.eval x * f.derivative.eval x =
          b * x * (r.eval x * f.derivative.eval x) := by
      simp only [tail, eval_mul, eval_C, eval_X]
      ring
    rw [heval]
    exact hweighted
  have hstep := prec_and_hasSimpleRoots_of_auxiliary_sign_succ_add_tail
    hhf.2.1.2 hf_pos hstep_pos hfdeg hdegree.1 hrec haux_sign hX_neg
      htail_nonpos
  have hprec : StrictInterl f (residueEulerStep a b f h r) := hstep.1
  have hsimple : HasSimpleRoots (residueEulerStep a b f h r) := hstep.2
  have hno : ∀ x, f.IsRoot x →
      ¬ (residueEulerStep a b f h r).IsRoot x :=
    noCommonRoot_of_auxiliary_sign_add_tail
      hrec haux_sign hX_neg htail_nonpos
  have hf_zero : 0 < f.eval 0 := by
    apply eval_pos_of_all_roots_lt hf_pos.ne_zero hhf.2.1.2 hf_pos
    intro x hx
    exact hf_neg x ((mem_roots hf_pos.ne_zero).mp hx)
  have hstep_zero : (residueEulerStep a b f h r).eval 0 = f.eval 0 := by
    simp [residueEulerStep]
  have hstep_neg : ∀ x, (residueEulerStep a b f h r).IsRoot x → x < 0 := by
    apply roots_neg_of_interlaces_of_eval_zero_pos
      (hprec.toInterlaces (by lia)) hstep_pos
    · rwa [hstep_zero]
    · exact hf_neg
  exact ⟨haux_interlaces, hprec, hno, hsimple, hstep_neg⟩

end RealRooted
