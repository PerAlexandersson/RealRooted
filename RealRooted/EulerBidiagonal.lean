import RealRooted.DerivativeRecurrence.Interlacing
import RealRooted.Interlacing.Residue
import RealRooted.MaWang.Strong
import RealRooted.MaWang.Weak.Endpoint
import RealRooted.EulerOperator.Darboux.NegativeRoots
import RealRooted.Wronskian.Algebra
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Wronskian.Forward
import RealRooted.ObreschkoffConverse.Regularization
import RealRooted.Interlacing.PencilPreserver
import RealRooted.QuadraticRoot

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-!
# Interlacing for the bidiagonal Euler step `X + (θ + a)(θ + b)`

For `a, b ≥ 0` with `a * b > 0`, the operator `T = X + (θ + a)(θ + b)` (coefficientwise
`(T p)_k = (k + a)(k + b) p_k + p_(k-1)`) has the following properties.
* `isNegativeSimple_step`: `T` maps polynomials with simple negative roots to such polynomials,
  raising the degree by one; `strictInterl_comparison_step` compares `T q` with
  `(θ + c/2) q`, `c = a + b + 1`.
* `splits_step_X_sub_C_mul`: `T ((X − ρ) q)` has simple real roots for every real `ρ`.
* `strictInterl_step_of_strictInterl`: `T` preserves strict interlacing (without common roots)
  of pairs with simple negative roots, via the Obreschkoff pencil
  (`strictInterl_map_of_negative_simple_pencil`).
* `strictInterl_rows`: the rows `P (n+1) = T (P n)`, `P 0 = 1`, strictly interlace.

The key step is the identity
`q(σ) · (T q)(σ) = σ² (q q'' − q'²)(σ) + (ab − c²/4 + σ) q(σ)²` at the zeros `σ` of
`2 X q' + c q`, combined with Laguerre's inequality `q q'' − q'² < 0`.  The rows include the
central factorial numbers (A036969, `a = b = 1`) and the Legendre–Stirling numbers (A071951,
`a = 1, b = 2`); real-rootedness of these rows is classical (Andrews–Gawronski–Littlejohn,
Andrews–Egge–Gawronski–Littlejohn, Mongelli), but interlacing of consecutive rows appears to be
new.  The argument was found in this project (see issue #1324).
-/

/-- The operator `T = X + (theta + a) (theta + b)`. -/
def step (a b : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * p + (theta (theta p) + C (a + b) * theta p + C (a * b) * p)

/-- The half-Euler comparison polynomial `u = (theta + c / 2) p`. -/
def comparison (c : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * p.derivative + C (c / 2) * p

private theorem coeff_comparison (c : ℝ) (p : ℝ[X]) (k : ℕ) :
    (comparison c p).coeff k = ((k : ℝ) + c / 2) * p.coeff k := by
  simp only [comparison, coeff_add, coeff_X_mul_derivative, coeff_C_mul]
  ring

/-- The Euler bidiagonal step as an `ℝ`-linear map. -/
def stepLinearMap (a b : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  { toFun := step a b
    map_add' := by
      intro p q
      simp only [step, theta_add, mul_add]
      ring
    map_smul' := by
      intro r p
      simp only [step, smul_eq_C_mul, RingHom.id_apply, theta_C_mul]
      ring }

/-- Applying the linear-map packaging gives the original polynomial operator. -/
@[simp] theorem stepLinearMap_apply (a b : ℝ) (p : ℝ[X]) :
    stepLinearMap a b p = step a b p :=
  rfl

/-- Coefficients of the bidiagonal Euler step. -/
@[simp] theorem coeff_step (a b : ℝ) (p : ℝ[X]) (k : ℕ) :
    (step a b p).coeff k =
      ((k : ℝ) + a) * ((k : ℝ) + b) * p.coeff k +
        if k = 0 then 0 else p.coeff (k - 1) := by
  cases k with
  | zero =>
      simp [step]
  | succ k =>
      simp only [step, coeff_add, coeff_X_mul, coeff_C_mul, coeff_theta,
        Nat.cast_add, Nat.cast_one]
      rw [ite_eq_right (Nat.add_one_ne_zero k)]
      simp only [Nat.add_sub_cancel]
      ring

/-- Differential form of the bidiagonal Euler step. -/
theorem step_eq_second_derivative (a b : ℝ) (p : ℝ[X]) :
    step a b p =
      X ^ 2 * p.derivative.derivative + C (a + b + 1) * X * p.derivative +
        (C (a * b) + X) * p := by
  simp only [step, theta, derivative_mul, derivative_X, add_mul, one_mul]
  simp only [map_add, map_one]
  ring

/-- The operator intertwines multiplication by `X` with a shifted parameter pair. -/
theorem step_X_mul (a b : ℝ) (p : ℝ[X]) :
    step a b (X * p) = X * step (a + 1) (b + 1) p := by
  rw [step_eq_second_derivative, step_eq_second_derivative]
  simp only [derivative_mul, derivative_X, one_mul, add_mul, map_add, map_one,
    map_mul]
  ring

/-- The parameter-shifted step differs from the original by the Euler term. -/
theorem step_shift_sub (a b : ℝ) (p : ℝ[X]) :
    step (a + 1) (b + 1) p - step a b p =
      C 2 * theta p + C (a + b + 1) * p := by
  ext k
  simp only [step, coeff_sub, coeff_add, coeff_C_mul, coeff_theta]
  ring

private theorem u_natDegree_and_leadingCoeff
    (c : ℝ) (p : ℝ[X]) (d : ℕ) (hd : p.natDegree = d)
    (htop : (c / 2 + (d : ℝ)) * p.leadingCoeff ≠ 0) :
    (comparison c p).natDegree = d ∧
      (comparison c p).leadingCoeff = (c / 2 + (d : ℝ)) * p.leadingCoeff := by
  have htop' : (c / 2 + (p.natDegree : ℝ)) * p.leadingCoeff ≠ 0 := by
    simpa [hd, add_comm] using htop
  have h := Polynomial.natDegree_and_leadingCoeff_C_mul_add_affine_mul_derivative
    p (c / 2) 0 1 (by simpa using htop')
  rw [hd] at h
  have hu_eq : comparison c p = C (c / 2) * p + (C 0 + C 1 * X) * p.derivative := by
    simp only [comparison, map_zero, map_one]
    ring
  dsimp only at h
  rw [hu_eq]
  simpa using h

private theorem step_natDegree_and_leadingCoeff
    (a b : ℝ) (p : ℝ[X]) (d : ℕ) (hd : p.natDegree = d)
    (hpos : HasPosLeadingCoeff p) :
    (step a b p).natDegree = d + 1 ∧
      (step a b p).leadingCoeff = p.leadingCoeff := by
  let F := step a b p
  have htop : F.coeff (d + 1) = p.leadingCoeff := by
    rw [coeff_step]
    have hzero : p.coeff (d + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd]
      lia
    rw [ite_eq_right (Nat.add_one_ne_zero d), Nat.add_sub_cancel, hzero]
    simp only [mul_zero, zero_add, leadingCoeff, hd]
  have hle : F.natDegree ≤ d + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_step]
    have hpk : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hd]; lia)
    have hpkm : p.coeff (k - 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd]
      lia
    simp only [hpk, hpkm, mul_zero, zero_add]
    rw [ite_eq_right (by lia)]
  have hdeg : F.natDegree = d + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by
      intro hzero
      have hp : p.leadingCoeff = 0 := by rw [← htop, hzero]
      have hpos' : 0 < p.leadingCoeff := hpos
      rw [hp] at hpos'
      linarith)
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg]
  exact htop

/-- Root-local evaluation identity at a zero of `2 X p' + c p`. -/
theorem eval_mul_step_of_two_mul_eval_X_mul_derivative_add_eq_zero
    (a b c σ : ℝ) (p : ℝ[X]) (hc : c = a + b + 1)
    (hσ : 2 * σ * p.derivative.eval σ + c * p.eval σ = 0) :
    p.eval σ * (step a b p).eval σ =
      σ ^ 2 *
          (p.eval σ * p.derivative.derivative.eval σ - p.derivative.eval σ ^ 2) +
        (a * b - c ^ 2 / 4 + σ) * p.eval σ ^ 2 := by
  subst c
  simp only [step, eval_add, eval_mul, eval_C, eval_X, theta, derivative_mul,
    derivative_X]
  simp only [eval_one]
  have hsquare := congrArg (fun x : ℝ => x ^ 2) hσ
  ring_nf at hsquare ⊢
  nlinarith

/-- The strict parameter inequality used in the sign argument for real-rootedness. -/
private theorem param_gap_neg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b - (a + b + 1) ^ 2 / 4 < 0 := by
  nlinarith [sq_nonneg (a - b)]

/-- The bidiagonal step has simple negative roots and is right of
the half-Euler comparison polynomial. -/
private theorem step_simpleNegRooted_and_strictInterl {a b c : ℝ} {d : ℕ} (q : ℝ[X])
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b) (hc : c = a + b + 1)
    (hq : SimpleNegRooted q d) (hd : 1 ≤ d) :
    SimpleNegRooted (step a b q) (d + 1) ∧
      StrictInterl (comparison c q) (step a b q) := by
  have hcpos : 0 < c := by
    rw [hc]
    nlinarith
  have hfac_u : 0 < c / 2 + (d : ℝ) := by
    have hd' : 0 < (d : ℝ) := by positivity
    nlinarith
  have hu_data := u_natDegree_and_leadingCoeff c q d hq.natDegree_eq
    (mul_ne_zero (ne_of_gt hfac_u) (ne_of_gt hq.pos))
  have hu_pos : HasPosLeadingCoeff (comparison c q) := by
    rw [HasPosLeadingCoeff, hu_data.2]
    exact mul_pos hfac_u hq.pos
  have hu_nonneg : HasNonnegCoeffs (comparison c q) := by
    intro k
    rw [coeff_comparison]
    have hk : 0 ≤ (k : ℝ) := by positivity
    exact mul_nonneg (by nlinarith) (hq.nonneg k)
  have hu_zero : 0 < (comparison c q).coeff 0 := by
    rw [coeff_comparison]
    simp only [Nat.cast_zero, zero_add]
    exact mul_pos (by nlinarith) hq.coeff_zero_pos
  have hdq : 1 ≤ q.natDegree := by
    rw [hq.natDegree_eq]
    exact hd
  have hq_der : Interlaces q.derivative q :=
    derivative_interlaces_of_pos hq.splits hq.pos hdq
  have hq_der_pos : HasPosLeadingCoeff q.derivative :=
    HasPosLeadingCoeff.derivative hq.pos (by rw [hq.natDegree_eq]; lia)
  have hstrict_qu : StrictInterl q (comparison c q) := by
    have hdeg_u : (comparison c q).natDegree = q.natDegree := by
      rw [hu_data.1, hq.natDegree_eq]
    have hu_expr_pos : HasPosLeadingCoeff
        (C (c / 2) * q + X * q.derivative) := by
      simpa [comparison, add_comm] using hu_pos
    have hu_expr_deg :
        (C (c / 2) * q + X * q.derivative).natDegree = q.natDegree := by
      simpa [comparison, add_comm] using hdeg_u
    have h := strictInterl_of_interlaces_evalCoeff_nonpos
      (f := q) (g := q.derivative) (a := C (c / 2)) (b := X)
      hq_der hq_der_pos hu_expr_pos hu_expr_deg.ge
      (hu_expr_deg.le.trans (Nat.le_succ _))
      (by
        intro r hr
        simp only [eval_X]
        exact (hq.isRoot_neg hr).le)
    simpa [comparison, add_comm] using h
  have hno_qu : ∀ r : ℝ, ¬ (q.IsRoot r ∧ (comparison c q).IsRoot r) := by
    intro r hr
    have hqr := hq.simple.eval_derivative_ne_zero hr.1
    have hu_eval : (comparison c q).eval r = r * q.derivative.eval r := by
      rw [comparison]
      simp only [eval_add, eval_mul, eval_X, eval_C]
      rw [hr.1.eq_zero]
      ring
    rw [hr.2.eq_zero] at hu_eval
    exact mul_ne_zero (ne_of_lt (hq.isRoot_neg hr.1)) hqr hu_eval.symm
  have hu_simple : HasSimpleRoots (comparison c q) :=
    hstrict_qu.hasSimpleRoots_of_no_common_root hno_qu |>.2
  have hroot_sign : ∀ s : ℝ, (comparison c q).IsRoot s →
      (step a b q).eval s * (comparison c q).derivative.eval s < 0 := by
    intro s hs
    have hs_mem : s ∈ (comparison c q).roots := (mem_roots hu_simple.ne_zero).mpr hs
    have hs_nonpos := roots_nonpos_of_hasNonnegCoeffs hu_nonneg s hs_mem
    have hs_ne : s ≠ 0 := by
      intro hs0
      subst s
      have hzero := hs.eq_zero
      have hzero_pos : 0 < (comparison c q).eval 0 := by
        simpa [coeff_zero_eq_eval_zero] using hu_zero
      linarith
    have hs_neg : s < 0 := lt_of_le_of_ne hs_nonpos hs_ne
    have hq_ne : q.eval s ≠ 0 := by
      intro hzero
      have hq_root : q.IsRoot s := by
        simpa [Polynomial.IsRoot.def] using hzero
      exact hno_qu s ⟨hq_root, hs⟩
    have hrel : 2 * s * q.derivative.eval s + c * q.eval s = 0 := by
      have hzero := hs.eq_zero
      rw [comparison] at hzero
      simp only [eval_add, eval_mul, eval_X, eval_C] at hzero
      nlinarith
    have hidentity :=
      eval_mul_step_of_two_mul_eval_X_mul_derivative_add_eq_zero a b c s q hc hrel
    have hlag := laguerre_form_nonneg hq.splits s
    have hfirst : s ^ 2 *
        (q.eval s * q.derivative.derivative.eval s - q.derivative.eval s ^ 2) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s)
      linarith
    have hgap : a * b - c ^ 2 / 4 + s < 0 := by
      have hparam := param_gap_neg (a := a) (b := b) (by assumption) (by assumption)
      rw [← hc] at hparam
      linarith
    have hsecond : (a * b - c ^ 2 / 4 + s) * q.eval s ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hgap (sq_pos_of_ne_zero hq_ne)
    have hqF : q.eval s * (step a b q).eval s < 0 := by
      rw [hidentity]
      nlinarith
    have hres : 0 < q.eval s * (comparison c q).derivative.eval s := by
      apply residue_sign_pos hstrict_qu hu_pos hq.pos hu_simple.roots_nodup
        hq.simple.roots_nodup s hs_mem
      intro hsmem
      exact hq_ne ((mem_roots hq.pos.ne_zero).mp hsmem).eq_zero
    rcases lt_or_gt_of_ne hq_ne with hq_neg | hq_pos
    · have hF_pos : 0 < (step a b q).eval s := by nlinarith
      have hu_der_neg : (comparison c q).derivative.eval s < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hF_pos hu_der_neg
    · have hF_neg : (step a b q).eval s < 0 := by nlinarith
      have hu_der_pos : 0 < (comparison c q).derivative.eval s := by nlinarith
      exact mul_neg_of_neg_of_pos hF_neg hu_der_pos
  have hU_der : Interlaces (comparison c q).derivative (comparison c q) :=
    derivative_interlaces_of_pos hstrict_qu.2.1.2 hu_pos (by rw [hu_data.1]; lia)
  have hF_data := step_natDegree_and_leadingCoeff a b q d hq.natDegree_eq hq.pos
  have hF_pos : HasPosLeadingCoeff (step a b q) := by
    rw [HasPosLeadingCoeff, hF_data.2]
    exact hq.pos
  have hUF : StrictInterl (comparison c q) (step a b q) :=
    strictInterl_of_interlaces_eval_mul_neg_succ hU_der
      (HasPosLeadingCoeff.derivative hu_pos (by rw [hu_data.1]; lia)) hF_pos
      (by rw [hF_data.1, hu_data.1]) hroot_sign
  have hno_UF : ∀ r : ℝ, ¬ ((comparison c q).IsRoot r ∧ (step a b q).IsRoot r) := by
    intro r hr
    have hsign := hroot_sign r hr.1
    rw [hr.2.eq_zero] at hsign
    linarith
  have hF_simple : HasSimpleRoots (step a b q) :=
    hUF.hasSimpleRoots_of_no_common_root hno_UF |>.2
  have hF_nonneg : HasNonnegCoeffs (step a b q) := by
    intro k
    rw [coeff_step]
    by_cases hk : k = 0
    · simp only [hk, ite_true, Nat.cast_zero, zero_add, add_zero]
      simpa using le_of_lt (mul_pos hab hq.coeff_zero_pos)
    · rw [ite_eq_right hk]
      have hka : 0 ≤ (k : ℝ) + a := by positivity
      have hkb : 0 ≤ (k : ℝ) + b := by positivity
      exact add_nonneg (mul_nonneg (mul_nonneg hka hkb) (hq.nonneg k))
        (hq.nonneg (k - 1))
  have hF_zero : 0 < (step a b q).coeff 0 := by
    rw [coeff_step]
    simp only [Nat.cast_zero, zero_add, ite_true, zero_add]
    nlinarith [mul_pos hab hq.coeff_zero_pos]
  have hF_neg : ∀ r ∈ (step a b q).roots, r < 0 := by
    intro r hr
    have hr_nonpos := roots_nonpos_of_hasNonnegCoeffs hF_nonneg r hr
    have hr_ne : r ≠ 0 := by
      intro hr0
      subst r
      have hroot := (mem_roots hF_pos.ne_zero).mp hr
      have hzero := hroot.eq_zero
      have hzero_pos : 0 < (step a b q).eval 0 := by
        simpa [coeff_zero_eq_eval_zero] using hF_zero
      linarith
    exact lt_of_le_of_ne hr_nonpos hr_ne
  refine ⟨⟨hF_data.1, hF_pos, hF_nonneg, hF_zero, hUF.2.1.2, hF_simple⟩, hUF⟩

/- The step is linear on the pencil generated by `X * p` and `p`. -/
theorem step_sub (a b ρ : ℝ) (p : ℝ[X]) :
    step a b ((X - C ρ) * p) = step a b (X * p) - C ρ * step a b p := by
  rw [sub_mul]
  have h := (stepLinearMap a b).map_sub (X * p) (ρ • p)
  rw [(stepLinearMap a b).map_smul] at h
  simpa [stepLinearMap, smul_eq_C_mul] using h

/-- Corollary B: every affine shift of the input gives a simple real-rooted step. -/
private theorem splits_step_X_sub_C_mul_of_simpleNegRooted {a b c : ℝ} {d : ℕ} (q : ℝ[X])
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b) (hc : c = a + b + 1)
    (hq : SimpleNegRooted q d) (hd : 1 ≤ d) :
    ∀ ρ : ℝ, (step a b ((X - C ρ) * q)).Splits ∧
      HasSimpleRoots (step a b ((X - C ρ) * q)) := by
  have hA := step_simpleNegRooted_and_strictInterl q ha hb hab hc hq hd
  have hF_pos : HasPosLeadingCoeff (step a b q) := hA.1.pos
  have hF_nonneg : HasNonnegCoeffs (step a b q) := hA.1.nonneg
  have hF_ne : step a b q ≠ 0 := hF_pos.ne_zero
  have hcpos : 0 < c := by
    rw [hc]
    nlinarith
  have hU_nonneg : HasNonnegCoeffs (comparison c q) := by
    intro k
    rw [coeff_comparison]
    exact mul_nonneg (by positivity) (hq.nonneg k)
  have hU_top : (c / 2 + (d : ℝ)) * q.leadingCoeff ≠ 0 := by
    exact mul_ne_zero (ne_of_gt (by nlinarith))
      (leadingCoeff_ne_zero.mpr hq.pos.ne_zero)
  have hU_data := u_natDegree_and_leadingCoeff c q d hq.natDegree_eq hU_top
  have hU_pos : HasPosLeadingCoeff (comparison c q) := by
    rw [HasPosLeadingCoeff, hU_data.2]
    exact mul_pos (by nlinarith) hq.pos
  have hU_ne : comparison c q ≠ 0 := hU_pos.ne_zero
  have hU_zero : 0 < (comparison c q).coeff 0 := by
    rw [coeff_comparison]
    simp only [Nat.cast_zero, zero_add]
    exact mul_pos (by nlinarith) hq.coeff_zero_pos
  have hno_qu : ∀ r : ℝ, ¬ (q.IsRoot r ∧ (comparison c q).IsRoot r) := by
    intro r hr
    have hqr := hq.simple.eval_derivative_ne_zero hr.1
    have hu_eval : (comparison c q).eval r = r * q.derivative.eval r := by
      rw [comparison]
      simp only [eval_add, eval_mul, eval_X, eval_C]
      rw [hr.1.eq_zero]
      ring
    rw [hr.2.eq_zero] at hu_eval
    exact mul_ne_zero (ne_of_lt (hq.isRoot_neg hr.1)) hqr hu_eval.symm
  have hno_UF : ∀ r : ℝ, ¬ ((comparison c q).IsRoot r ∧ (step a b q).IsRoot r) := by
    intro s hs
    have hs_mem : s ∈ (comparison c q).roots := (mem_roots hU_ne).mpr hs.1
    have hs_nonpos := roots_nonpos_of_hasNonnegCoeffs hU_nonneg s hs_mem
    have hs_ne : s ≠ 0 := by
      intro hs0
      subst s
      have hzero := hs.1.eq_zero
      have hzero_pos : 0 < (comparison c q).eval 0 := by
        simpa [coeff_zero_eq_eval_zero] using hU_zero
      linarith
    have hs_neg : s < 0 := lt_of_le_of_ne hs_nonpos hs_ne
    have hq_ne : q.eval s ≠ 0 := by
      intro hzero
      have hq_root : q.IsRoot s := by
        simpa [Polynomial.IsRoot.def] using hzero
      exact hno_qu s ⟨hq_root, hs.1⟩
    have hrel : 2 * s * q.derivative.eval s + c * q.eval s = 0 := by
      have hzero := hs.1.eq_zero
      rw [comparison] at hzero
      simp only [eval_add, eval_mul, eval_X, eval_C] at hzero
      nlinarith
    have hidentity :=
      eval_mul_step_of_two_mul_eval_X_mul_derivative_add_eq_zero a b c s q hc hrel
    have hlag := laguerre_form_nonneg hq.splits s
    have hfirst : s ^ 2 *
        (q.eval s * q.derivative.derivative.eval s - q.derivative.eval s ^ 2) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s)
      linarith
    have hgap : a * b - c ^ 2 / 4 + s < 0 := by
      have hparam := param_gap_neg (a := a) (b := b) ha hb
      rw [← hc] at hparam
      linarith
    have hsecond : (a * b - c ^ 2 / 4 + s) * q.eval s ^ 2 < 0 :=
      mul_neg_of_neg_of_pos hgap (sq_pos_of_ne_zero hq_ne)
    have hqF : q.eval s * (step a b q).eval s < 0 := by
      rw [hidentity]
      nlinarith
    rw [hs.2.eq_zero] at hqF
    linarith
  have hXF : StrictInterl (step a b q) (X * step a b q) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg
      (StrictInterl.refl hF_ne hA.1.splits) hF_nonneg hF_nonneg
  have hXU : StrictInterl (step a b q) (X * comparison c q) :=
    strictInterl_mul_X_of_strictInterl_of_nonneg hA.2 hU_nonneg hF_nonneg
  have hXF_pos : HasPosLeadingCoeff (X * step a b q) :=
    hF_nonneg.X_mul.pos_leadingCoeff hXF.2.1.1
  have hXU_pos : HasPosLeadingCoeff (X * comparison c q) :=
    hU_nonneg.X_mul.pos_leadingCoeff (mul_ne_zero X_ne_zero hU_ne)
  have hcone : StrictInterl (step a b q)
      (weightedSum [(1, X * step a b q), (2, X * comparison c q)]) := by
    apply StrictInterl.weightedSum_left_of_common_left_signed
      [(1, X * step a b q), (2, X * comparison c q)] (step a b q)
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · norm_num
      · rcases hp with hp | hp
        · rw [hp]
          norm_num
        · simp at hp
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hXF
      · rcases hp with hp | hp
        · rw [hp]
          exact hXU
        · simp at hp
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hXF_pos
      · rcases hp with hp | hp
        · rw [hp]
          exact hXU_pos
        · simp at hp
    · exact ⟨(1, X * step a b q), by simp, by norm_num⟩
  have hshift : step (a + 1) (b + 1) q = step a b q + C 2 * comparison c q := by
    have hs := step_shift_sub a b q
    calc
      step (a + 1) (b + 1) q =
          (C 2 * theta q + C (a + b + 1) * q) + step a b q :=
        sub_eq_iff_eq_add.mp hs
      _ = step a b q + C 2 * comparison c q := by
        simp only [comparison, theta]
        rw [hc]
        have hC : C (a + b + 1) = C 2 * C ((a + b + 1) / 2) := by
          rw [← C_mul]
          congr 1
          ring
        rw [hC]
        ring
  have hstepX : step a b (X * q) =
      weightedSum [(1, X * step a b q), (2, X * comparison c q)] := by
    rw [step_X_mul, hshift]
    simp only [weightedSum_cons, weightedSum_nil, C_1, one_mul]
    simp only [add_zero]
    ring
  have hFG : StrictInterl (step a b q) (step a b (X * q)) := by
    rw [hstepX]
    exact hcone
  have hXq_deg : (X * q).natDegree = d + 1 := by
    rw [natDegree_mul X_ne_zero hq.pos.ne_zero, natDegree_X, hq.natDegree_eq]
    lia
  have hXq_pos : HasPosLeadingCoeff (X * q) := hq.pos.X_mul
  have hG_data := step_natDegree_and_leadingCoeff a b (X * q) (d + 1) hXq_deg hXq_pos
  have hG_pos : HasPosLeadingCoeff (step a b (X * q)) := by
    rw [HasPosLeadingCoeff, hG_data.2]
    exact hXq_pos
  have hno_FG : ∀ r : ℝ, ¬ ((step a b q).IsRoot r ∧
      (step a b (X * q)).IsRoot r) := by
    intro r hr
    have hr_ne : r ≠ 0 := by
      intro hr0
      subst r
      have hroot := hr.1.eq_zero
      have hzero_pos : 0 < (step a b q).eval 0 := by
        simpa [coeff_zero_eq_eval_zero] using hA.1.coeff_zero_pos
      linarith
    have hroot_sum := hr.2.eq_zero
    rw [hstepX] at hroot_sum
    simp only [weightedSum_cons, weightedSum_nil] at hroot_sum
    simp only [eval_add, eval_mul, eval_C, eval_X, C_1, one_mul, add_zero] at hroot_sum
    rw [hr.1.eq_zero] at hroot_sum
    have hU_root : (comparison c q).IsRoot r := by
      have hmul : r * (comparison c q).eval r = 0 := by
        nlinarith [hroot_sum]
      have hzero : (comparison c q).eval r = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hr_ne
      simpa [Polynomial.IsRoot.def] using hzero
    exact hno_UF r ⟨hU_root, hr.1⟩
  have hFG_simple := hFG.hasSimpleRoots_of_no_common_root hno_FG
  have hWne : ∀ t : ℝ,
      (ObreschkoffConverseInternal.wronskianPoly
        (step a b q) (step a b (X * q))).eval t ≠ 0 := by
    intro t hz
    have hw := wronskian_pos_of_strictInterl_succ hG_pos hF_pos
      (by rw [hG_data.1, hA.1.natDegree_eq]) hFG
      hFG_simple.2.roots_nodup hFG_simple.1.roots_nodup (by
        intro r hGr hFr
        exact hno_FG r ⟨hFr, hGr⟩) t
    simp only [ObreschkoffConverseInternal.wronskianPoly, eval_sub, eval_mul] at hz
    nlinarith
  have hall := allComboRealRooted_of_strictInterl hFG
  intro ρ
  have hcombo :=
    ObreschkoffConverseInternal.combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
      hall hWne (-ρ) 1
  have htarget_ne : step a b ((X - C ρ) * q) ≠ 0 := by
    intro hz
    have hcoeff := congrArg (fun p : ℝ[X] => p.coeff (d + 2)) hz
    rw [step_sub] at hcoeff
    have hFcoeff : (step a b q).coeff (d + 2) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hA.1.natDegree_eq]; lia)
    have hGcoeff : (step a b (X * q)).coeff (d + 2) =
        (step a b (X * q)).leadingCoeff := by
      rw [← hG_data.1, coeff_natDegree]
    have hcoeff' : (step a b (X * q)).coeff (d + 2) -
        ρ * (step a b q).coeff (d + 2) = 0 := by
      simpa using hcoeff
    rw [hFcoeff, mul_zero, sub_zero, hGcoeff] at hcoeff'
    exact (leadingCoeff_ne_zero.mpr hG_pos.ne_zero) hcoeff'
  have htarget : step a b ((X - C ρ) * q) =
      C (-ρ) * step a b q + C 1 * step a b (X * q) := by
    rw [step_sub]
    simp only [C_1, one_mul, C_neg, neg_mul]
    ring
  rcases hcombo with hz | ⟨⟨hne, hsplits⟩, hsimple⟩
  · exact False.elim (htarget_ne (by rw [htarget, hz]))
  · exact ⟨by rw [htarget]; exact hsplits, by rw [htarget]; exact hsimple⟩

end RealRooted.EulerBidiagonal

namespace RealRooted

private theorem IsNegativeSimple.toSimpleNegRooted {p : ℝ[X]}
    (hp : IsNegativeSimple p) (d : ℕ) (hd : p.natDegree = d) :
    SimpleNegRooted p d := by
  have hnonneg : HasNonnegCoeffs p :=
    ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hp.2.1).2
      ⟨hp.2.2.2.1, fun r hr => (hp.2.2.2.2 r hr).le⟩).1
  have hzero : 0 < p.coeff 0 := by
    apply lt_of_le_of_ne (hnonneg 0)
    intro hz
    have hroot : p.IsRoot 0 := by
      rw [Polynomial.IsRoot.def]
      simpa [coeff_zero_eq_eval_zero] using hz.symm
    have hmem : (0 : ℝ) ∈ p.roots := (mem_roots hp.1).mpr hroot
    exact lt_irrefl 0 (hp.2.2.2.2 0 hmem)
  exact ⟨hd, hp.2.2.2.1, hnonneg, hzero, hp.2.1, hp.2.2.1⟩

private theorem isNegativeSimple_of_simpleNegRooted {p : ℝ[X]} {d : ℕ}
    (hp : SimpleNegRooted p d) : IsNegativeSimple p := by
  refine ⟨hp.pos.ne_zero, hp.splits, hp.simple, hp.pos, ?_⟩
  intro r hr
  exact hp.isRoot_neg ((mem_roots hp.pos.ne_zero).mp hr)

namespace EulerBidiagonal

/-- The Euler step preserves negative-simple polynomials of positive degree. -/
theorem isNegativeSimple_step {a b : ℝ} {d : ℕ} (q : ℝ[X])
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b)
    (hq : IsNegativeSimple q) (hd : 1 ≤ d) (hqd : q.natDegree = d) :
    IsNegativeSimple (step a b q) ∧ (step a b q).natDegree = d + 1 := by
  have hq' := hq.toSimpleNegRooted d hqd
  have h := step_simpleNegRooted_and_strictInterl q ha hb hab rfl hq' hd
  exact ⟨isNegativeSimple_of_simpleNegRooted h.1, h.1.natDegree_eq⟩

/-- The comparison polynomial strictly interlaces the Euler step. -/
theorem strictInterl_comparison_step {a b : ℝ} {d : ℕ} (q : ℝ[X])
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b)
    (hq : IsNegativeSimple q) (hd : 1 ≤ d) (hqd : q.natDegree = d) :
    StrictInterl (comparison (a + b + 1) q) (step a b q) :=
  (step_simpleNegRooted_and_strictInterl q ha hb hab rfl (hq.toSimpleNegRooted d hqd) hd).2

/-- Affine shifts of a positive-degree negative-simple input have simple real roots. -/
theorem splits_step_X_sub_C_mul {a b : ℝ} {d : ℕ} (q : ℝ[X])
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b)
    (hq : IsNegativeSimple q) (hd : 1 ≤ d) (hqd : q.natDegree = d) :
    ∀ ρ : ℝ, (step a b ((X - C ρ) * q)).Splits ∧
      HasSimpleRoots (step a b ((X - C ρ) * q)) := by
  exact splits_step_X_sub_C_mul_of_simpleNegRooted q ha hb hab rfl (hq.toSimpleNegRooted d hqd) hd

private theorem isNegativeSimple_step_of_natDegree_zero {a b : ℝ}
    (hab : 0 < a * b) {q : ℝ[X]}
    (hq : IsNegativeSimple q) (hqd : q.natDegree = 0) :
    IsNegativeSimple (step a b q) ∧ (step a b q).natDegree = 1 := by
  have hq' := hq.toSimpleNegRooted 0 hqd
  have hconst : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hqd
  have hc : 0 < q.coeff 0 := hq'.coeff_zero_pos
  have hbase : SimpleNegRooted (X + C (a * b)) 1 := by
    refine ⟨Polynomial.natDegree_X_add_C _, hasPosLeadingCoeff_X_add_C _, ?_, ?_, ?_, ?_⟩
    · intro k
      simp only [coeff_add, coeff_X, coeff_C]
      split <;> positivity
    · simp only [coeff_add, coeff_X, coeff_C]
      norm_num [hab]
    · simpa [sub_eq_add_neg] using (isRealRooted_X_sub_C (-a * b : ℝ)).2
    · have hne : X + C (a * b) ≠ 0 := by
        intro hzero
        have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 1) hzero
        norm_num at hcoeff
      exact hasSimpleRoots_of_natDegree_le_one hne
        (by
          exact (Polynomial.natDegree_X_add_C (a * b)).le)
  have hscaled := hbase.C_mul hc
  have hstep : step a b q = C (q.coeff 0) * (X + C (a * b)) := by
    rw [hconst]
    simp only [step, theta, derivative_C, map_zero, mul_zero, add_zero,
      coeff_C, ite_true]
    ring
  rw [hstep]
  exact ⟨isNegativeSimple_of_simpleNegRooted hscaled, by
    simpa using hscaled.natDegree_eq⟩

/-- The Euler step satisfies H1, including positive constants. -/
theorem mapsNegativeSimpleBySucc_step {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) :
    MapsNegativeSimpleBySucc (stepLinearMap a b) := by
  intro q hq
  by_cases hqd : q.natDegree = 0
  · have h := isNegativeSimple_step_of_natDegree_zero hab hq hqd
    rw [hqd]
    simpa only [stepLinearMap_apply] using h
  · have hd : 1 ≤ q.natDegree := Nat.one_le_iff_ne_zero.mpr hqd
    have h := isNegativeSimple_step q ha hb hab hq hd rfl
    simpa only [stepLinearMap_apply] using h

/-- The Euler step sends an affine negative-simple input to simple real roots. -/
theorem mapsAffineNegativeSimple_step {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) :
    MapsAffineNegativeSimple (stepLinearMap a b) := by
  intro q ρ hq
  by_cases hqd : q.natDegree = 0
  · have hq' := hq.toSimpleNegRooted 0 hqd
    have hq0 : 0 < q.coeff 0 := hq'.coeff_zero_pos
    have hconst : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hqd
    let B : ℝ := (1 + a) * (1 + b) - ρ
    let Q : ℝ[X] := X ^ 2 + C B * X + C (-a * b * ρ)
    have hQ : step a b (X - C ρ) = Q := by
      dsimp [Q, B]
      simp only [step, theta, derivative_X, derivative_C,
        mul_zero, sub_zero, add_zero, one_mul, derivative_mul, derivative_one, map_sub,
        map_mul, map_add, map_neg, map_one]
      ring
    have hdisc : 0 < discrim 1 B (-a * b * ρ) := by
      dsimp [B]
      rw [discrim]
      nlinarith [sq_nonneg (ρ + 2 * a * b - (1 + a) * (1 + b))]
    have hQs : Q.Splits := by
      simpa only [Q, C_1, one_mul] using
        (quadraticPoly_splits_of_discrim_nonneg (a := (1 : ℝ)) (b := B)
          (c := -a * b * ρ) one_ne_zero hdisc.le)
    have hQne : Q ≠ 0 := by
      intro hzero
      have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 2) hzero
      simp [Q] at hcoeff
    have hQsimple : HasSimpleRoots Q := by
      apply HasSimpleRoots.of_roots_nodup hQne
      dsimp [Q]
      have hroots := roots_quadratic_posLead (b := B) (c := -a * b * ρ)
        (by norm_num) hdisc.le
      simp only [C_1, one_mul] at hroots
      rw [hroots]
      have hsqrt : 0 < Real.sqrt (discrim 1 B (-a * b * ρ)) := by
        positivity
      simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton]
      constructor
      · intro heq
        have hsqrt' : 0 < Real.sqrt (B ^ 2 - 4 * 1 * (-a * b * ρ)) := by
          simpa only [discrim] using hsqrt
        have heq' := (div_eq_div_iff (by norm_num) (by norm_num)).mp heq
        nlinarith
      · simp
    have hstep : step a b ((X - C ρ) * q) = C (q.coeff 0) * Q := by
      rw [hconst]
      simp only [coeff_C, ite_true]
      calc
        step a b ((X - C ρ) * C (q.coeff 0)) =
            step a b (C (q.coeff 0) * (X - C ρ)) := by
              congr 1
              ring
        _ = C (q.coeff 0) * step a b (X - C ρ) := by
          change (stepLinearMap a b) (C (q.coeff 0) * (X - C ρ)) = _
          rw [← smul_eq_C_mul, (stepLinearMap a b).map_smul]
          simp only [stepLinearMap_apply, smul_eq_C_mul]
        _ = C (q.coeff 0) * Q := by rw [hQ]
    rw [stepLinearMap_apply, hstep]
    have hrr := isRealRooted_C_mul hQne hQs (ne_of_gt hq0)
    have hs : HasSimpleRoots (C (q.coeff 0) * Q) := by
      apply HasSimpleRoots.of_roots_nodup hrr.1
      rw [Polynomial.roots_C_mul _ (ne_of_gt hq0)]
      exact hQsimple.roots_nodup
    exact ⟨hrr.1, hrr.2, hs⟩
  · have hd : 1 ≤ q.natDegree := Nat.one_le_iff_ne_zero.mpr hqd
    have hq' := hq.toSimpleNegRooted q.natDegree rfl
    have h := splits_step_X_sub_C_mul q ha hb hab hq hd rfl ρ
    have hstep_ne := h.2.ne_zero
    exact ⟨hstep_ne, h.1, h.2⟩

/-- The Euler step preserves strict successor-degree interlacing. -/
theorem strictInterl_step_of_strictInterl {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcop : ∀ r, ¬ (f.IsRoot r ∧ g.IsRoot r))
    (hf : IsNegativeSimple f) (hg : IsNegativeSimple g) :
    StrictInterl (step a b f) (step a b g) ∧
      ∀ r, ¬ ((step a b f).IsRoot r ∧ (step a b g).IsRoot r) := by
  exact strictInterl_map_of_negative_simple_pencil hfg hdeg hcop hf hg
    (mapsNegativeSimpleBySucc_step ha hb hab)
    (mapsAffineNegativeSimple_step ha hb hab)

/-! The rows of the Euler bidiagonal recurrence. -/
def rows (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => step a b (rows a b n)

private theorem isNegativeSimple_one : IsNegativeSimple (1 : ℝ[X]) := by
  refine ⟨by norm_num, Splits.one, ?_, hasPosLeadingCoeff_one, ?_⟩
  · exact fun r hr => absurd hr (by simp)
  · intro r hr
    exact absurd hr (by simp)

private theorem isNegativeSimple_X_add_C {c : ℝ} (hc : 0 < c) :
    IsNegativeSimple (X + C c) := by
  refine ⟨X_add_C_ne_zero c, ?_, ?_, hasPosLeadingCoeff_X_add_C c, ?_⟩
  · have h := (isRealRooted_X_sub_C (-c : ℝ)).2
    have heq : X + C c = X - C (-c) := by simp
    rw [heq]
    exact h
  · exact hasSimpleRoots_of_natDegree_le_one (X_add_C_ne_zero c) (by simp)
  · intro r hr
    rw [roots_X_add_C] at hr
    have hroot : r = -c := by simpa using hr
    rw [hroot]
    exact neg_lt_zero.mpr hc

/-- Consecutive Euler rows strictly interlace and have no common roots. -/
theorem strictInterl_rows {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) :
    ∀ n, StrictInterl (rows a b n) (rows a b (n + 1)) ∧
      ∀ r, ¬ ((rows a b n).IsRoot r ∧ (rows a b (n + 1)).IsRoot r) := by
  have hP1 : IsNegativeSimple (rows a b 1) := by
    change IsNegativeSimple (step a b 1)
    have h := isNegativeSimple_step_of_natDegree_zero hab isNegativeSimple_one (by simp)
    simpa using h.1
  have hP1_eq : rows a b 1 = X + C (a * b) := by
    simp only [rows, step, theta, derivative_one, map_zero, mul_zero, add_zero]
    simp only [mul_one, zero_add]
  have hbase : StrictInterl (rows a b 0) (rows a b 1) := by
    rw [hP1_eq]
    simpa [rows] using
      (interlaces_one_linear (p := X + C (a * b))
        (Polynomial.natDegree_X_add_C (a * b))).toStrictInterl
  have hbase_cop : ∀ r, ¬ ((rows a b 0).IsRoot r ∧ (rows a b 1).IsRoot r) := by
    intro r hr
    have hzero : (1 : ℝ[X]).eval r = 0 := by
      simpa [rows, Polynomial.IsRoot.def] using hr.1
    norm_num at hzero
  have hrec : ∀ n, rows a b (n + 1) = stepLinearMap a b (rows a b n) := by
    intro n
    simp only [rows, stepLinearMap_apply]
  exact strictInterl_iterate_of_negative_simple hrec isNegativeSimple_one
    (by simpa [hP1_eq] using hP1) hbase hbase_cop
    (mapsNegativeSimpleBySucc_step ha hb hab)
    (mapsAffineNegativeSimple_step ha hb hab)

/-- Every Euler row has exactly its index as its degree and is negative-simple. -/
theorem isNegativeSimple_rows {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a * b) :
    ∀ n, IsNegativeSimple (rows a b n) ∧ (rows a b n).natDegree = n := by
  have hrec : ∀ n, rows a b (n + 1) = stepLinearMap a b (rows a b n) := by
    intro n
    simp only [rows, stepLinearMap_apply]
  intro n
  induction n with
  | zero =>
      exact ⟨isNegativeSimple_one, by simp [rows]⟩
  | succ n ih =>
      have hs := mapsNegativeSimpleBySucc_step ha hb hab ih.1
      have hnext : IsNegativeSimple (rows a b (n + 1)) := by
        rw [hrec n]
        exact hs.1
      have hnextdeg : (rows a b (n + 1)).natDegree = n + 1 := by
        calc
          (rows a b (n + 1)).natDegree =
              (stepLinearMap a b (rows a b n)).natDegree := by rw [hrec n]
          _ = (rows a b n).natDegree + 1 := hs.2
          _ = n + 1 := by rw [ih.2]
      exact ⟨hnext, hnextdeg⟩

end EulerBidiagonal
end RealRooted
