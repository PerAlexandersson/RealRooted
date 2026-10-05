import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ParameterFamily
import RealRooted.CriticalValueContinuation

/-!
# Calculus for a weighted A144438 contact

We construct a differentiable branch through a simple output root while one
input-root parameter varies.  At a zero companion residue, we compute the
derivative of that residue along the branch.
-/

open Filter Polynomial Topology
open scoped ContDiff

noncomputable section

namespace RealRooted.Applications.OEIS

@[simp]
theorem weightedDecoParameterImageAt_self {I : Type*} [DecidableEq I]
    (w : ℝ) {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) :
    weightedDecoParameterImageAt w s a j (a j) =
      weightedDecoParameterImage w s a := by
  unfold weightedDecoParameterImageAt weightedDecoParameterImage
  rw [weightedDecoParameterInputAt_self hj]

@[simp]
theorem weightedDecoParameterCompanionAt_self {I : Type*} [DecidableEq I]
    (w : ℝ) {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) :
    weightedDecoParameterCompanionAt w s a j (a j) =
      weightedDecoParameterCompanion w s a := by
  unfold weightedDecoParameterCompanionAt weightedDecoParameterCompanion
  rw [weightedDecoParameterInputAt_self hj]

theorem weightedDecoParameterCompanionAt_eq_add {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) (b : ℝ) :
    weightedDecoParameterCompanionAt w s a j b =
      weightedDecoParameterCompanionAt w s a j 0 +
        C b * weightedDecoParameterCompanion w (s.erase j) a := by
  have h := weightedDecoParameterCompanionAt_sub w s a j b 0
  simpa [add_comm] using (sub_eq_iff_eq_add.mp h)

theorem contDiff_weightedDecoParameterImageAt_eval_prod
    {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterImageAt w s a j z.1).eval z.2) := by
  rw [show (fun z : ℝ × ℝ =>
      (weightedDecoParameterImageAt w s a j z.1).eval z.2) =
      fun z => (1 + z.2 + z.1) *
          (weightedDecoParameterImage w (s.erase j) a).eval z.2 +
        z.2 * (weightedDecoParameterCompanion w (s.erase j) a).eval z.2 by
    funext z
    rw [weightedDecoParameterImageAt_insertion]
    simp only [eval_add, eval_mul, eval_one, eval_X, eval_C]
    ]
  have hP : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterImage w (s.erase j) a).eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  have hH : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanion w (s.erase j) a).eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  exact (((contDiff_const.add contDiff_snd).add contDiff_fst).mul hP).add
    (contDiff_snd.mul hH)

theorem contDiff_weightedDecoParameterImageAt_derivative_eval_prod
    {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterImageAt w s a j z.1).derivative.eval z.2) := by
  rw [show (fun z : ℝ × ℝ =>
      (weightedDecoParameterImageAt w s a j z.1).derivative.eval z.2) =
      fun z =>
        (weightedDecoParameterImage w (s.erase j) a).eval z.2 +
          (1 + z.2 + z.1) *
            (weightedDecoParameterImage w (s.erase j) a).derivative.eval z.2 +
          (weightedDecoParameterCompanion w (s.erase j) a).eval z.2 +
          z.2 *
            (weightedDecoParameterCompanion w (s.erase j) a).derivative.eval z.2 by
    funext z
    rw [weightedDecoParameterImageAt_insertion]
    simp only [derivative_add, derivative_mul, derivative_one,
      derivative_X, derivative_C, zero_add, eval_add, eval_mul, eval_one,
      eval_X, eval_C, eval_zero]
    ring]
  have hP : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterImage w (s.erase j) a).eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  have hP' : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterImage w (s.erase j) a).derivative.eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  have hH : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanion w (s.erase j) a).eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  have hH' : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanion w (s.erase j) a).derivative.eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  have hfactor : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (1 : ℝ) + z.2 + z.1) :=
    (contDiff_const.add contDiff_snd).add contDiff_fst
  exact ((hP.add (hfactor.mul hP')).add hH).add (contDiff_snd.mul hH')

theorem contDiff_weightedDecoParameterCompanionAt_eval_prod
    {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanionAt w s a j z.1).eval z.2) := by
  rw [show (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanionAt w s a j z.1).eval z.2) =
      fun z =>
        (weightedDecoParameterCompanionAt w s a j 0).eval z.2 +
          z.1 *
            (weightedDecoParameterCompanion w (s.erase j) a).eval z.2 by
    funext z
    rw [weightedDecoParameterCompanionAt_eq_add]
    simp only [eval_add, eval_mul, eval_C]
    ]
  have h0 : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanionAt w s a j 0).eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  have hH : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      (weightedDecoParameterCompanion w (s.erase j) a).eval z.2) :=
    (Polynomial.contDiff_aeval _ ∞).comp contDiff_snd
  exact h0.add (contDiff_fst.mul hH)

/-- A simple root of a coordinate family admits a differentiable local root
branch with the usual implicit derivative. -/
theorem exists_hasDerivAt_weightedDecoParameterImageAt_root
    {I : Type*} [DecidableEq I]
    {w : ℝ} {s : Finset I} {a : I → ℝ} {j : I} {b r : ℝ}
    (hr : (weightedDecoParameterImageAt w s a j b).IsRoot r)
    (hregular :
      (weightedDecoParameterImageAt w s a j b).derivative.eval r ≠ 0) :
    ∃ ρ : ℝ → ℝ,
      HasDerivAt ρ
        (-((weightedDecoParameterImage w (s.erase j) a).eval r) /
          (weightedDecoParameterImageAt w s a j b).derivative.eval r) b ∧
      ρ b = r ∧
      ∀ᶠ c in 𝓝 b,
        (weightedDecoParameterImageAt w s a j c).IsRoot (ρ c) := by
  let p : ℝ → ℝ[X] := fun c => weightedDecoParameterImageAt w s a j c
  have hsmooth : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => (p z.1).eval z.2) (b, r) :=
    (contDiff_weightedDecoParameterImageAt_eval_prod w s a j).contDiffAt.of_le
      (by norm_num)
  obtain ⟨ρ, hρsmooth, hρbase, hρroot⟩ :=
    RealRooted.exists_contDiffAt_polynomial_root p hsmooth hr hregular
  let v := deriv ρ b
  have hρderiv : HasDerivAt ρ v b :=
    hρsmooth.differentiableAt (by norm_num) |>.hasDerivAt
  let P := weightedDecoParameterImage w (s.erase j) a
  let H := weightedDecoParameterCompanion w (s.erase j) a
  have hPcomp : HasDerivAt (fun c => P.eval (ρ c))
      (P.derivative.eval r * v) b := by
    have h := (P.hasDerivAt (ρ b)).comp b hρderiv
    rw [hρbase] at h
    change HasDerivAt ((fun x => P.eval x) ∘ ρ)
      (P.derivative.eval r * v) b
    exact h
  have hHcomp : HasDerivAt (fun c => H.eval (ρ c))
      (H.derivative.eval r * v) b := by
    have h := (H.hasDerivAt (ρ b)).comp b hρderiv
    rw [hρbase] at h
    change HasDerivAt ((fun x => H.eval x) ∘ ρ)
      (H.derivative.eval r * v) b
    exact h
  have hpAlong : HasDerivAt (fun c => (p c).eval (ρ c))
      (P.eval r + (p b).derivative.eval r * v) b := by
    have hpderivative : (p b).derivative.eval r =
        P.eval r + (1 + r + b) * P.derivative.eval r + H.eval r +
          r * H.derivative.eval r := by
      dsimp only [p, P, H]
      rw [weightedDecoParameterImageAt_insertion]
      simp only [derivative_add, derivative_mul, derivative_one,
        derivative_X, derivative_C, zero_add, eval_add, eval_mul, eval_one,
        eval_X, eval_C, eval_zero]
      ring
    rw [show (fun c => (p c).eval (ρ c)) =
        fun c => (1 + ρ c + c) * P.eval (ρ c) + ρ c * H.eval (ρ c) by
      funext c
      dsimp only [p, P, H]
      rw [weightedDecoParameterImageAt_insertion]
      simp only [eval_add, eval_mul, eval_one, eval_X, eval_C]]
    convert (((((hasDerivAt_const b (1 : ℝ)).add hρderiv).add
      (hasDerivAt_id b)).mul hPcomp).add (hρderiv.mul hHcomp)) using 1
    · ext c
      rfl
    · rw [hρbase, hpderivative]
      simp only [Pi.add_apply, id_eq]
      rw [hρbase]
      ring
  have hpZero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 b :=
    hasDerivAt_const b 0
  have hrootEq : (fun c => (p c).eval (ρ c)) =ᶠ[𝓝 b] fun _ => 0 := by
    filter_upwards [hρroot] with c hc
    simpa only [Polynomial.IsRoot.def] using hc
  have hvelocity : v = -P.eval r / (p b).derivative.eval r := by
    have hderivZero := hpAlong.unique (hpZero.congr_of_eventuallyEq hrootEq)
    rw [eq_div_iff hregular]
    nlinarith
  refine ⟨ρ, ?_, hρbase, hρroot⟩
  simpa only [p, P] using hρderiv.congr_deriv hvelocity

/-- At a zero companion residue, varying one input-root parameter gives the
quotient-rule derivative used in the first-contact argument. -/
theorem exists_hasDerivAt_weightedDecoParameterResidueAt_contact
    {I : Type*} [DecidableEq I]
    {w : ℝ} {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) {r : ℝ}
    (hr : (weightedDecoParameterImage w s a).IsRoot r)
    (hsimple : HasSimpleRoots (weightedDecoParameterImage w s a))
    (hcontact : (weightedDecoParameterCompanion w s a).eval r = 0) :
    ∃ ρ : ℝ → ℝ,
      ρ (a j) = r ∧
      (∀ᶠ c in 𝓝 (a j),
        (weightedDecoParameterImageAt w s a j c).IsRoot (ρ c)) ∧
      HasDerivAt
        (fun c =>
          (weightedDecoParameterCompanionAt w s a j c).eval (ρ c) /
            (weightedDecoParameterImageAt w s a j c).derivative.eval (ρ c))
        (((weightedDecoParameterCompanion w (s.erase j) a).eval r *
              (weightedDecoParameterImage w s a).derivative.eval r -
            (weightedDecoParameterCompanion w s a).derivative.eval r *
              (weightedDecoParameterImage w (s.erase j) a).eval r) /
          (weightedDecoParameterImage w s a).derivative.eval r ^ 2)
        (a j) := by
  let p := weightedDecoParameterImage w s a
  let h := weightedDecoParameterCompanion w s a
  let P := weightedDecoParameterImage w (s.erase j) a
  let H := weightedDecoParameterCompanion w (s.erase j) a
  let b := a j
  let d := p.derivative.eval r
  have hd : d ≠ 0 := hsimple.eval_derivative_ne_zero hr
  have hrAt : (weightedDecoParameterImageAt w s a j b).IsRoot r := by
    dsimp only [b]
    rw [weightedDecoParameterImageAt_self w hj]
    exact hr
  have hdAt :
      (weightedDecoParameterImageAt w s a j b).derivative.eval r ≠ 0 := by
    dsimp only [b]
    rw [weightedDecoParameterImageAt_self w hj]
    exact hd
  obtain ⟨ρ, hρderiv, hρbase, hρroot⟩ :=
    exists_hasDerivAt_weightedDecoParameterImageAt_root hrAt hdAt
  have hvelocity : deriv ρ b = -P.eval r / d := by
    rw [hρderiv.deriv]
    dsimp only [P, d, p, b]
    rw [weightedDecoParameterImageAt_self w hj]
  let h0 := weightedDecoParameterCompanionAt w s a j 0
  have hh0comp : HasDerivAt (fun c => h0.eval (ρ c))
      (h0.derivative.eval r * deriv ρ b) b := by
    have hρ := hρderiv
    have hcomp := (h0.hasDerivAt (ρ b)).comp b hρ
    rw [hρbase] at hcomp
    change HasDerivAt ((fun x => h0.eval x) ∘ ρ)
      (h0.derivative.eval r * deriv ρ b) b
    convert hcomp using 1
    rw [hρderiv.deriv]
  have hHcomp : HasDerivAt (fun c => H.eval (ρ c))
      (H.derivative.eval r * deriv ρ b) b := by
    have hρ := hρderiv
    have hcomp := (H.hasDerivAt (ρ b)).comp b hρ
    rw [hρbase] at hcomp
    change HasDerivAt ((fun x => H.eval x) ∘ ρ)
      (H.derivative.eval r * deriv ρ b) b
    convert hcomp using 1
    rw [hρderiv.deriv]
  have hhAlong : HasDerivAt
      (fun c =>
        (weightedDecoParameterCompanionAt w s a j c).eval (ρ c))
      (H.eval r + h.derivative.eval r * deriv ρ b) b := by
    have hhderivative : h.derivative.eval r =
        h0.derivative.eval r + b * H.derivative.eval r := by
      have heq := weightedDecoParameterCompanionAt_eq_add w s a j b
      rw [show weightedDecoParameterCompanionAt w s a j b = h by
        dsimp only [b, h]
        rw [weightedDecoParameterCompanionAt_self w hj]] at heq
      have heq' := congrArg (fun q : ℝ[X] => q.derivative.eval r) heq
      simpa only [derivative_add, derivative_mul, derivative_C, eval_add,
        eval_mul, eval_C, eval_zero, zero_mul, zero_add] using heq'
    rw [show (fun c =>
        (weightedDecoParameterCompanionAt w s a j c).eval (ρ c)) =
        fun c => h0.eval (ρ c) + c * H.eval (ρ c) by
      funext c
      rw [weightedDecoParameterCompanionAt_eq_add]
      simp only [eval_add, eval_mul, eval_C]
      dsimp only [h0, H]]
    convert hh0comp.add ((hasDerivAt_id b).mul hHcomp) using 1
    · ext c
      rfl
    · rw [hρbase, hhderivative]
      simp only [id_eq]
      ring
  have hdenDiff : DifferentiableAt ℝ
      (fun c =>
        (weightedDecoParameterImageAt w s a j c).derivative.eval (ρ c)) b := by
    have houter : DifferentiableAt ℝ
        (fun z : ℝ × ℝ =>
          (weightedDecoParameterImageAt w s a j z.1).derivative.eval z.2)
        (b, ρ b) :=
      ((contDiff_weightedDecoParameterImageAt_derivative_eval_prod w s a j)
        |>.differentiable (by norm_num)).differentiableAt
    exact houter.comp b (differentiableAt_id.prodMk hρderiv.differentiableAt)
  have hdenAt :
      (weightedDecoParameterImageAt w s a j b).derivative.eval (ρ b) = d := by
    rw [hρbase]
    dsimp only [b, d, p]
    rw [weightedDecoParameterImageAt_self w hj]
  have hnumAt :
      (weightedDecoParameterCompanionAt w s a j b).eval (ρ b) = 0 := by
    rw [hρbase]
    dsimp only [b, h]
    rw [weightedDecoParameterCompanionAt_self w hj]
    exact hcontact
  have hquot := hhAlong.div hdenDiff.hasDerivAt (by simpa [hdenAt] using hd)
  refine ⟨ρ, hρbase, hρroot, ?_⟩
  have halgebra (q : ℝ) :
      ((H.eval r + h.derivative.eval r * (-P.eval r / d)) * d - 0 * q) /
          d ^ 2 =
        (H.eval r * d - h.derivative.eval r * P.eval r) / d ^ 2 := by
    field_simp [hd]
    ring
  convert hquot using 1
  rw [hnumAt, hdenAt, hvelocity]
  dsimp only [p, h, P, H, b, d]
  exact (halgebra _).symm

/-- Factorized form of the coordinate residue derivative at a negative
contact root. -/
theorem exists_hasDerivAt_weightedDecoParameterResidueAt_contact_factor
    {I : Type*} [DecidableEq I]
    {w : ℝ} {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) {r : ℝ}
    (hr : (weightedDecoParameterImage w s a).IsRoot r)
    (hrneg : r < 0)
    (hsimple : HasSimpleRoots (weightedDecoParameterImage w s a))
    (hcontact : (weightedDecoParameterCompanion w s a).eval r = 0) :
    ∃ ρ : ℝ → ℝ,
      ρ (a j) = r ∧
      (∀ᶠ c in 𝓝 (a j),
        (weightedDecoParameterImageAt w s a j c).IsRoot (ρ c)) ∧
      HasDerivAt
        (fun c =>
          (weightedDecoParameterCompanionAt w s a j c).eval (ρ c) /
            (weightedDecoParameterImageAt w s a j c).derivative.eval (ρ c))
        (((weightedDecoParameterImage w (s.erase j) a).eval r /
              (weightedDecoParameterImage w s a).derivative.eval r) *
          (-(1 + r + a j) / r -
            (weightedDecoParameterCompanion w s a).derivative.eval r /
              (weightedDecoParameterImage w s a).derivative.eval r))
        (a j) := by
  let p := weightedDecoParameterImage w s a
  let h := weightedDecoParameterCompanion w s a
  let P := weightedDecoParameterImage w (s.erase j) a
  let H := weightedDecoParameterCompanion w (s.erase j) a
  let d := p.derivative.eval r
  have hd : d ≠ 0 := hsimple.eval_derivative_ne_zero hr
  have hrec : p = (1 + X + C (a j)) * P + X * H := by
    calc
      p = weightedDecoParameterImageAt w s a j (a j) := by
        symm
        exact weightedDecoParameterImageAt_self w hj
      _ = (1 + X + C (a j)) * P + X * H := by
        exact weightedDecoParameterImageAt_insertion w s a j (a j)
  have hinsertion : (1 + r + a j) * P.eval r + r * H.eval r = 0 := by
    have heval := congrArg (fun q : ℝ[X] => q.eval r) hrec
    have hrzero : p.eval r = 0 := by
      dsimp only [p]
      exact hr
    rw [hrzero] at heval
    simpa only [eval_add, eval_mul, eval_one, eval_X, eval_C] using heval.symm
  have hfactor := weightedDeco_contact_residue_derivative
    (hderivative := h.derivative.eval r) hrneg.ne hd hinsertion
  obtain ⟨ρ, hρbase, hρroot, hρderiv⟩ :=
    exists_hasDerivAt_weightedDecoParameterResidueAt_contact hj hr hsimple hcontact
  refine ⟨ρ, hρbase, hρroot, ?_⟩
  apply hρderiv.congr_deriv
  exact hfactor

end RealRooted.Applications.OEIS
