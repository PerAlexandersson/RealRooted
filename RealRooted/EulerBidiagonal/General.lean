import RealRooted.EulerBidiagonal
import RealRooted.RootCounting.SignChanges

/-!
# The general Euler step `κ(θ + a)(θ + b) + X(u + vθ)`

For `κ, a, b > 0`, the operator
`generalStep κ a b u v = κ(θ + a)(θ + b) + X·(u + vθ)` (coefficientwise
`(T p)_(k+1) = κ(k+1+a)(k+1+b) p_(k+1) + (u + vk) p_k`) generalizes the bidiagonal Euler step
`X + (θ + a)(θ + b)` of `RealRooted.EulerBidiagonal`.

`isNegativeSimple_generalStep_of_pos` and `isNegativeSimple_generalStep_zero`: if `q` has positive
leading coefficient and simple negative roots, `u + vk > 0` on the degrees `k ≤ deg q`, and the
comparison defect `comparisonDefect κ a b u v σ` is negative for `σ ≤ 0` (implied by
`2u ≥ (a + b + 1)v`, `comparisonDefect_neg_of_two_mul_u_ge`), then so does `generalStep q`, of
one higher degree.  The proof evaluates the identity
`q(σ)(T q)(σ) = κσ²(q q'' − q'²)(σ) + comparisonDefect(σ) q(σ)²` at the zeros `σ` of the comparison
polynomial `generalComparison q = 2κXq' + (κ(a+b+1) + vX) q` and counts sign changes.  This step
covers the OEIS rows A156289, A166960, A166961, A166962 and A166972 (#1074).
-/


open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-! The general five-parameter Euler step used in the generalized argument. -/

/-- The operator `κ(θ+a)(θ+b) + X(u+vθ)`. -/
def generalStep (κ a b u v : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C κ * (theta (theta p) + C (a + b) * theta p + C (a * b) * p) +
    X * (C u * p + C v * theta p)

/-- The general Euler step as an `ℝ`-linear map. -/
def generalStepLinearMap (κ a b u v : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  { toFun := generalStep κ a b u v
    map_add' := by
      intro p q
      simp only [generalStep, theta_add, mul_add]
      ring
    map_smul' := by
      intro r p
      simp only [generalStep, smul_eq_C_mul, RingHom.id_apply, theta_C_mul]
      ring }

@[simp]
theorem generalStepLinearMap_apply (κ a b u v : ℝ) (p : ℝ[X]) :
    generalStepLinearMap κ a b u v p = generalStep κ a b u v p :=
  rfl

/-- Coefficients of the general Euler step. -/
@[simp]
theorem coeff_generalStep (κ a b u v : ℝ) (p : ℝ[X]) (k : ℕ) :
    (generalStep κ a b u v p).coeff (k + 1) =
      κ * ((k + 1 : ℕ) + a) * ((k + 1 : ℕ) + b) * p.coeff (k + 1) +
        (u + v * k) * p.coeff k := by
  simp only [generalStep, coeff_add, coeff_C_mul, coeff_X_mul, coeff_theta,
    Nat.cast_add, Nat.cast_one]
  ring

/-- The constant coefficient of the general Euler step. -/
@[simp]
theorem coeff_zero_generalStep (κ a b u v : ℝ) (p : ℝ[X]) :
    (generalStep κ a b u v p).coeff 0 = κ * a * b * p.coeff 0 := by
  simp only [generalStep, coeff_add, coeff_C_mul, coeff_X_mul_zero, coeff_theta,
    Nat.cast_zero, zero_mul, zero_add, add_zero]
  ring

/-- The unit Euler step is the previously formalized bidiagonal step. -/
theorem generalStep_one_one_zero (a b : ℝ) (p : ℝ[X]) :
    generalStep 1 a b 1 0 p = step a b p := by
  simp only [generalStep, step, C_1, one_mul, zero_mul, C_0, add_zero,
    C_mul]
  ring

/-- The comparison polynomial occurring in the general Euler argument. -/
def generalComparison (κ a b v : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C κ * C 2 * theta p +
    (C κ * (C (a + b) + C 1) + C v * X) * p

/-- The quadratic sign expression in the root-local identity. -/
def comparisonDefect (κ a b u v σ : ℝ) : ℝ :=
  κ * (a * b - (a + b + 1) ^ 2 / 4) +
    (u - (a + b + 1) * v / 2) * σ - v ^ 2 / (4 * κ) * σ ^ 2

/-- Differential form of the general Euler step. -/
theorem generalStep_eq_second_derivative (κ a b u v : ℝ) (p : ℝ[X]) :
    generalStep κ a b u v p =
      C κ * X ^ 2 * p.derivative.derivative +
        X * (C (κ * (a + b + 1)) + C v * X) * p.derivative +
        (C (κ * (a * b)) + C u * X) * p := by
  simp only [generalStep, theta, derivative_mul, derivative_X, add_mul, one_mul,
    map_add, map_one, C_mul]
  ring

/-- First algebraic identity for the general Euler step. -/
theorem generalStep_eval_form (κ a b u v : ℝ) (p : ℝ[X]) :
    generalStep κ a b u v p =
      C κ * X ^ 2 * p.derivative.derivative +
        X * (C (κ * (a + b + 1)) + C v * X) * p.derivative +
        (C (κ * (a * b)) + C u * X) * p := by
  exact generalStep_eq_second_derivative κ a b u v p

/-- Intertwining identity with multiplication by `X`. -/
theorem generalStep_X_mul (κ a b u v : ℝ) (p : ℝ[X]) :
    generalStep κ a b u v (X * p) =
      X * generalStep κ a b u v p + X * generalComparison κ a b v p := by
  rw [generalStep_eq_second_derivative, generalStep_eq_second_derivative]
  simp only [derivative_mul, derivative_X, one_mul, add_mul, map_add, map_one,
    generalComparison, theta, C_mul, C_ofNat]
  ring

/-- The affine-factor version of the intertwining identity. -/
theorem generalStep_sub (κ a b u v ρ : ℝ) (p : ℝ[X]) :
    generalStep κ a b u v ((X - C ρ) * p) =
      (X - C ρ) * generalStep κ a b u v p + X * generalComparison κ a b v p := by
  rw [sub_mul]
  calc
    generalStep κ a b u v (X * p - C ρ * p) =
        generalStep κ a b u v (X * p) - C ρ * generalStep κ a b u v p := by
      have h := (generalStepLinearMap κ a b u v).map_sub (X * p) (ρ • p)
      rw [(generalStepLinearMap κ a b u v).map_smul] at h
      simpa only [generalStepLinearMap_apply, smul_eq_C_mul] using h
    _ = (X - C ρ) * generalStep κ a b u v p + X * generalComparison κ a b v p := by
      rw [generalStep_X_mul]
      ring

/-- Root-local quadratic identity (I4). -/
theorem eval_mul_generalStep_of_generalComparison_eval_eq_zero
    (κ a b u v σ : ℝ) (p : ℝ[X]) (hκ : κ ≠ 0)
    (hσ : (generalComparison κ a b v p).eval σ = 0) :
    p.eval σ * (generalStep κ a b u v p).eval σ =
      κ * σ ^ 2 *
          (p.eval σ * p.derivative.derivative.eval σ - p.derivative.eval σ ^ 2) +
        comparisonDefect κ a b u v σ * p.eval σ ^ 2 := by
  rw [generalComparison] at hσ
  simp only [eval_add, eval_mul, eval_C, eval_X, theta, eval_one, map_add,
    map_one] at hσ ⊢
  have hident :
      4 * κ * (p.eval σ * (generalStep κ a b u v p).eval σ -
        κ * σ ^ 2 *
          (p.eval σ * p.derivative.derivative.eval σ - p.derivative.eval σ ^ 2) -
        comparisonDefect κ a b u v σ * p.eval σ ^ 2) =
        (2 * κ * (σ * p.derivative.eval σ) +
          (κ * (a + b + 1) + v * σ) * p.eval σ) ^ 2 := by
    dsimp [comparisonDefect]
    simp only [generalStep, eval_add, eval_mul, eval_C, eval_X, theta,
      derivative_mul, derivative_X, eval_one, map_add, C_mul] at ⊢
    field_simp [hκ]
    ring
  have hzero :
      4 * κ * (p.eval σ * (generalStep κ a b u v p).eval σ -
        κ * σ ^ 2 *
          (p.eval σ * p.derivative.derivative.eval σ - p.derivative.eval σ ^ 2) -
        comparisonDefect κ a b u v σ * p.eval σ ^ 2) = 0 := by
    have hσ' : 2 * κ * (σ * p.derivative.eval σ) +
        (κ * (a + b + 1) + v * σ) * p.eval σ = 0 := by
      nlinarith [hσ]
    rw [hident, hσ']
    ring
  have hfour : 4 * κ ≠ 0 := mul_ne_zero (by norm_num) hκ
  have hdiff := (mul_eq_zero.mp hzero).resolve_left hfour
  linarith

/-- The parameter inequality implies the quadratic condition on all nonpositive inputs. -/
theorem comparisonDefect_neg_of_two_mul_u_ge (κ a b u v : ℝ) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hu : 2 * u ≥ (a + b + 1) * v) :
    ∀ σ ≤ 0, comparisonDefect κ a b u v σ < 0 := by
  intro σ hσ
  have hconst : a * b - (a + b + 1) ^ 2 / 4 < 0 := by
    nlinarith [sq_nonneg (a - b)]
  have hlin : 0 ≤ u - (a + b + 1) * v / 2 := by
    linarith
  have hquad : 0 ≤ v ^ 2 / (4 * κ) * σ ^ 2 := by
    positivity
  have hconst' : κ * (a * b - (a + b + 1) ^ 2 / 4) < 0 :=
    mul_neg_of_pos_of_neg hκ hconst
  dsimp [comparisonDefect]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hlin hσ]

/-- The negative-simple general-step conclusion under a reusable map certificate. -/
private theorem isNegativeSimple_generalStep_of_map_certificate
    (κ a b u v : ℝ) (q : ℝ[X])
    (hmap : MapsNegativeSimpleBySucc (generalStepLinearMap κ a b u v))
    (hq : IsNegativeSimple q) :
    IsNegativeSimple (generalStep κ a b u v q) ∧
      (generalStep κ a b u v q).natDegree = q.natDegree + 1 := by
  simpa only [generalStepLinearMap_apply] using hmap hq

end RealRooted.EulerBidiagonal




open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

private lemma derivative_eval_mul_neg_of_adjacent_roots
    {q : ℝ[X]} {rs pre rest : List ℝ} {r₁ r₂ : ℝ}
    (hq : IsNegativeSimple q)
    (hrs_sorted : rs.Pairwise (· < ·))
    (hrs_eq : (↑rs : Multiset ℝ) = q.roots)
    (hdecomp : rs = pre ++ r₁ :: r₂ :: rest) :
    q.derivative.eval r₁ * q.derivative.eval r₂ < 0 := by
  have hqne : q ≠ 0 := hq.1
  have hroot₁ : q.IsRoot r₁ := by
    apply isRoot_of_mem_roots
    rw [← hrs_eq]
    simp [hdecomp]
  have hroot₂ : q.IsRoot r₂ := by
    apply isRoot_of_mem_roots
    rw [← hrs_eq]
    simp [hdecomp]
  have hcount₁ : q.roots.count r₁ = 1 :=
    hq.2.2.1.roots_count_eq_one hroot₁
  have hcount₂ : q.roots.count r₂ = 1 :=
    hq.2.2.1.roots_count_eq_one hroot₂
  have hder₁ := deriv_at_root_sign hq.2.1 hq.2.2.2.1 r₁
    ((mem_roots hqne).mpr hroot₁) hcount₁
  have hder₂ := deriv_at_root_sign hq.2.1 hq.2.2.2.1 r₂
    ((mem_roots hqne).mpr hroot₂) hcount₂
  have hcount_rel : q.roots.countP (fun r => r₁ < r) =
      q.roots.countP (fun r => r₂ < r) + 1 := by
    have hs := hrs_sorted
    rw [hdecomp] at hs
    have hpre : ∀ x ∈ pre, x < r₁ := by
      intro x hx
      exact (List.pairwise_append.mp hs).2.2 x hx r₁ (by simp)
    have htail : ∀ x ∈ rest, r₂ < x := by
      intro x hx
      exact (List.pairwise_cons.mp
        (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2).1 x hx
    have hpre₁ : ∀ x ∈ pre, ¬ r₁ < x := by
      intro x hx h
      linarith [hpre x hx]
    have hpre₂ : ∀ x ∈ pre, ¬ r₂ < x := by
      intro x hx h
      have hxr₂ : x < r₂ := (hpre x hx).trans
        ((List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 r₂ (by simp))
      linarith
    have hr₁₂ : r₁ < r₂ :=
      (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 r₂ (by simp)
    have hpre₁_zero : List.countP (fun x => decide (r₁ < x)) pre = 0 :=
      List.countP_eq_zero.mpr (by
        intro x hx
        simp [hpre₁ x hx])
    have hpre₂_zero : List.countP (fun x => decide (r₂ < x)) pre = 0 :=
      List.countP_eq_zero.mpr (by
        intro x hx
        simp [hpre₂ x hx])
    have htail₁ : ∀ x ∈ r₂ :: rest, r₁ < x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hr₁₂
      · exact hr₁₂.trans (htail x hx)
    have hlist :
        List.countP (fun x => decide (r₁ < x)) (pre ++ r₁ :: r₂ :: rest) =
          List.countP (fun x => decide (r₂ < x)) (pre ++ r₁ :: r₂ :: rest) + 1 := by
      rw [List.countP_append, List.countP_append]
      rw [hpre₁_zero, hpre₂_zero]
      have hrest₁ :
          List.countP (fun x => decide (r₁ < x)) rest = rest.length :=
        List.countP_eq_length.mpr (by
          intro x hx
          simp [htail₁ x (by simp [hx])])
      have hrest₂ :
          List.countP (fun x => decide (r₂ < x)) rest = rest.length :=
        List.countP_eq_length.mpr (by
          intro x hx
          simp [htail x hx])
      have htail₁_count :
          List.countP (fun x => decide (r₁ < x)) (r₂ :: rest) = rest.length + 1 := by
        simp [hr₁₂, hrest₁]
      have htail₂_count :
          List.countP (fun x => decide (r₂ < x)) (r₁ :: r₂ :: rest) = rest.length := by
        have hnot : ¬r₂ < r₁ := not_lt.mpr (le_of_lt hr₁₂)
        simp [hnot, hrest₂]
      have htail₁_all :
          List.countP (fun x => decide (r₁ < x)) (r₁ :: r₂ :: rest) = rest.length + 1 := by
        simp [hr₁₂, hrest₁]
      rw [htail₁_all, htail₂_count]
      simp
    have hroots :
        (↑(pre ++ r₁ :: r₂ :: rest) : Multiset ℝ) = q.roots := by
      rw [← hdecomp, hrs_eq]
    rw [← hroots]
    simpa using hlist
  have hparity : (-1 : ℝ) ^ q.roots.countP (fun r => r₁ < r) =
      -(-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r) := by
    rw [hcount_rel, pow_succ]
    ring
  have hprod : 0 <
      (q.derivative.eval r₁ * (-1 : ℝ) ^ q.roots.countP (fun r => r₁ < r)) *
        (q.derivative.eval r₂ * (-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r)) :=
    mul_pos hder₁ hder₂
  rw [hparity] at hprod
  have heven :
      (-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r) *
          (-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r) = 1 := by
    rw [← pow_add]
    simp
  have hprod' : 0 <
      -(q.derivative.eval r₁ * q.derivative.eval r₂) := by
    calc
      0 < (q.derivative.eval r₁ * -(-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r)) *
          (q.derivative.eval r₂ * (-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r)) := hprod
      _ = -(q.derivative.eval r₁ * q.derivative.eval r₂) := by
        calc
          _ = -(q.derivative.eval r₁ * q.derivative.eval r₂) *
              ((-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r) *
                (-1 : ℝ) ^ q.roots.countP (fun r => r₂ < r)) := by ring
          _ = _ := by rw [heven]; ring
  linarith

/-- The comparison polynomial has opposite signs at consecutive simple negative
roots of the input polynomial. -/
theorem generalComparison_eval_mul_neg_of_adjacent_roots
    (κ a b v : ℝ) (q : ℝ[X]) (rs pre rest : List ℝ) (r₁ r₂ : ℝ)
    (hκ : 0 < κ) (hq : IsNegativeSimple q)
    (hrs_sorted : rs.Pairwise (· < ·))
    (hrs_eq : (↑rs : Multiset ℝ) = q.roots)
    (hdecomp : rs = pre ++ r₁ :: r₂ :: rest) :
    (generalComparison κ a b v q).eval r₁ * (generalComparison κ a b v q).eval r₂ < 0 := by
  have hroot₁ : q.IsRoot r₁ := by
    apply isRoot_of_mem_roots
    rw [← hrs_eq]
    simp [hdecomp]
  have hroot₂ : q.IsRoot r₂ := by
    apply isRoot_of_mem_roots
    rw [← hrs_eq]
    simp [hdecomp]
  have hneg₁ : r₁ < 0 := by
    apply hq.2.2.2.2 r₁
    rw [← hrs_eq]
    simp [hdecomp]
  have hneg₂ : r₂ < 0 := by
    apply hq.2.2.2.2 r₂
    rw [← hrs_eq]
    simp [hdecomp]
  have hder := derivative_eval_mul_neg_of_adjacent_roots hq hrs_sorted hrs_eq hdecomp
  have heval₁ : (generalComparison κ a b v q).eval r₁ =
      2 * κ * r₁ * q.derivative.eval r₁ := by
    rw [generalComparison]
    simp only [eval_add, eval_mul, eval_C, eval_X, theta, hroot₁.eq_zero]
    ring
  have heval₂ : (generalComparison κ a b v q).eval r₂ =
      2 * κ * r₂ * q.derivative.eval r₂ := by
    rw [generalComparison]
    simp only [eval_add, eval_mul, eval_C, eval_X, theta, hroot₂.eq_zero]
    ring
  have hfac : 0 < (2 * κ * r₁) * (2 * κ * r₂) := by
    have h2κ : 0 < 2 * κ := by linarith
    have hleft : 2 * κ * r₁ < 0 := mul_neg_of_pos_of_neg h2κ hneg₁
    have hright : 2 * κ * r₂ < 0 := mul_neg_of_pos_of_neg h2κ hneg₂
    exact mul_pos_of_neg_of_neg hleft hright
  calc
    (generalComparison κ a b v q).eval r₁ * (generalComparison κ a b v q).eval r₂ =
        ((2 * κ * r₁) * (2 * κ * r₂)) *
          (q.derivative.eval r₁ * q.derivative.eval r₂) := by
      rw [heval₁, heval₂]
      ring
    _ < 0 := mul_neg_of_pos_of_neg hfac hder

/-- The comparison polynomial is negative at the rightmost input root. -/
theorem generalComparison_eval_neg_at_last_root
    (κ a b v : ℝ) (q : ℝ[X]) (rs : List ℝ) (r : ℝ)
    (hκ : 0 < κ) (hq : IsNegativeSimple q)
    (_hrs_sorted : rs.Pairwise (· < ·))
    (hrs_eq : (↑rs : Multiset ℝ) = q.roots)
    (hr_mem : r ∈ rs) (hr_last : ∀ x ∈ rs, x ≤ r) (hr_neg : r < 0) :
    (generalComparison κ a b v q).eval r < 0 := by
  have hqne : q ≠ 0 := hq.1
  have hroot : q.IsRoot r := by
    apply isRoot_of_mem_roots
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr hr_mem
  have hcount : q.roots.countP (fun x => r < x) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro x hx hxr
    have hxrs : x ∈ rs := by
      apply Multiset.mem_coe.mp
      rw [hrs_eq]
      exact hx
    linarith [hr_last x hxrs]
  have hder := deriv_at_root_sign hq.2.1 hq.2.2.2.1 r
    ((mem_roots hqne).mpr hroot) (hq.2.2.1.roots_count_eq_one hroot)
  have hder_pos : 0 < q.derivative.eval r := by
    simpa [hcount] using hder
  have heval : (generalComparison κ a b v q).eval r = 2 * κ * r * q.derivative.eval r := by
    rw [generalComparison]
    simp only [eval_add, eval_mul, eval_C, eval_X, theta, hroot.eq_zero]
    ring
  rw [heval]
  have h2κ : 0 < 2 * κ := by linarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h2κ hr_neg) hder_pos

/-- The comparison polynomial is positive at zero for a negative-simple input. -/
theorem generalComparison_eval_zero_pos
    (κ a b v : ℝ) (q : ℝ[X]) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hq : IsNegativeSimple q) :
    0 < (generalComparison κ a b v q).eval 0 := by
  have hqne : q ≠ 0 := hq.1
  have hq0root : ¬q.IsRoot 0 := by
    intro hroot
    have hmem : (0 : ℝ) ∈ q.roots := (mem_roots hqne).mpr hroot
    exact (not_lt_of_ge (le_refl 0)) (hq.2.2.2.2 0 hmem)
  have hq0mem : (0 : ℝ) ∉ q.roots := by
    intro hmem
    exact hq0root ((mem_roots hqne).mp hmem)
  have hcount : q.roots.countP (fun x => 0 < x) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro x hx hpos
    exact (not_lt_of_ge (hq.2.2.2.2 x hx).le) hpos
  have hq0 : 0 < q.eval 0 := by
    have hs := eval_sign hq.2.1 hq.2.2.2.1 0 hq0mem
    simpa [hcount] using hs
  rw [generalComparison]
  simp only [eval_add, eval_mul, eval_C, eval_X, theta]
  have hc : 0 < a + b + 1 := by linarith
  nlinarith [mul_pos (mul_pos hκ hc) hq0]

/-- Inner comparison roots obtained from the strict sign changes at input roots. -/
theorem exists_inner_comparison_roots
    (κ a b v : ℝ) (q : ℝ[X]) (rs : List ℝ)
    (hκ : 0 < κ) (hq : IsNegativeSimple q)
    (hrs_sorted : rs.Pairwise (· < ·))
    (hrs_eq : (↑rs : Multiset ℝ) = q.roots) :
    ∃ ss : List ℝ, ss.length = rs.length - 1 ∧
      ListInterlaces ss rs ∧
      (∀ s ∈ ss, (generalComparison κ a b v q).IsRoot s) ∧ ss.Pairwise (· < ·) := by
  obtain ⟨ss, hlen, hint, hroots, hss_sorted⟩ :=
    MaWangInternal.exists_roots_strictly_interlacing_of_consecutive_signs
      (F := generalComparison κ a b v q) (hrs_sorted.imp le_of_lt) (by
        intro pre r₁ r₂ rest hdecomp
        exact generalComparison_eval_mul_neg_of_adjacent_roots κ a b v q rs pre rest r₁ r₂
          hκ hq hrs_sorted hrs_eq hdecomp)
  exact ⟨ss, hlen, hint, hroots, hss_sorted⟩

/-- The sign identity forces opposite signs for the step and input at every
negative comparison root. -/
theorem generalStep_eval_mul_neg_of_generalComparison_root
    (κ a b u v : ℝ) (q : ℝ[X]) (σ : ℝ)
    (hκ : 0 < κ) (hq : IsNegativeSimple q)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0)
    (hσroot : (generalComparison κ a b v q).IsRoot σ) (hσneg : σ < 0) :
    q.eval σ * (generalStep κ a b u v q).eval σ < 0 := by
  have hqne : q ≠ 0 := hq.1
  have hqeval : q.eval σ ≠ 0 := by
    intro hzero
    have hqroot : q.IsRoot σ := by
      simpa [Polynomial.IsRoot.def] using hzero
    have hderne : q.derivative.eval σ ≠ 0 :=
      hq.2.2.1.eval_derivative_ne_zero hqroot
    have hgeval := hσroot.eq_zero
    rw [generalComparison] at hgeval
    simp only [eval_add, eval_mul, eval_C, eval_X, theta, hzero] at hgeval
    have hmul : κ * σ * q.derivative.eval σ = 0 := by
      nlinarith [hgeval]
    exact hderne ((mul_eq_zero.mp hmul).resolve_left
      (mul_ne_zero (ne_of_gt hκ) (ne_of_lt hσneg)))
  have hlag := laguerre_form_nonneg hq.2.1 σ
  have hfirst : κ * σ ^ 2 *
      (q.eval σ * q.derivative.derivative.eval σ - q.derivative.eval σ ^ 2) ≤ 0 := by
    have hnonneg : 0 ≤ κ * σ ^ 2 := mul_nonneg (le_of_lt hκ) (sq_nonneg σ)
    have hinner : q.eval σ * q.derivative.derivative.eval σ -
        q.derivative.eval σ ^ 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hnonneg hinner
  have hsecond : comparisonDefect κ a b u v σ * q.eval σ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (hQ σ hσneg.le) (sq_pos_of_ne_zero hqeval)
  have hprod := eval_mul_generalStep_of_generalComparison_eval_eq_zero κ a b u v σ q
    (ne_of_gt hκ) hσroot.eq_zero
  rw [hprod]
  nlinarith

end RealRooted.EulerBidiagonal




open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-! The endpoint part of the comparison-root argument, together with the
degree data needed by the sign-change theorem.  The hypotheses are kept
explicit so that the eventual theorem can be assembled without hiding any
of the root-order guards. -/

theorem exists_last_comparison_root
    (κ a b v : ℝ) (q : ℝ[X]) (r : ℝ)
    (_hκ : 0 < κ) (_hq : IsNegativeSimple q)
    (_hrs_eq : r ∈ q.roots) (_hr_last : ∀ x ∈ q.roots, x ≤ r)
    (hr_neg : r < 0) (hzero : 0 < (generalComparison κ a b v q).eval 0)
    (hneg : (generalComparison κ a b v q).eval r < 0) :
    ∃ σ, r < σ ∧ σ < 0 ∧ (generalComparison κ a b v q).IsRoot σ := by
  obtain ⟨σ, hleft, hright, hroot⟩ :=
    MaWangInternal.exists_isRoot_between_of_eval_mul_neg
      (p := generalComparison κ a b v q) (a := r) (b := 0) (by linarith)
      (mul_neg_of_neg_of_pos hneg hzero)
  exact ⟨σ, hleft, hright, hroot⟩

private lemma listInterlaces_append_endpoint
    {ss rs : List ℝ} {σ : ℝ}
    (hint : ListInterlaces ss rs)
    (hrs_ne : rs ≠ []) (hrs : ∀ x ∈ rs, x ≤ σ) (hσ : σ ≤ 0) :
    ListInterlaces (ss ++ [σ]) (rs ++ [0]) := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil => exact False.elim (hrs_ne rfl)
      | cons r rs =>
          cases rs with
          | nil =>
              simpa [ListInterlaces] using
                (And.intro (hrs r (by simp)) hσ)
          | cons r₂ rs => simp [ListInterlaces] at hint
  | cons s ss ih =>
      cases rs with
      | nil => simp [ListInterlaces] at hint
      | cons r rs =>
          cases rs with
          | nil => simp [ListInterlaces] at hint
          | cons r₂ rs =>
              rcases hint with ⟨hsr₁, hsr₂, htail⟩
              refine ⟨hsr₁, hsr₂, ?_⟩
              apply ih htail (by simp)
              intro x hx
              exact hrs x (by simp [hx])

theorem exists_comparison_roots_with_last
    (κ a b v : ℝ) (q : ℝ[X]) (rs : List ℝ) (r : ℝ)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hq : IsNegativeSimple q)
    (hrs_sorted : rs.Pairwise (· < ·))
    (hrs_eq : (↑rs : Multiset ℝ) = q.roots)
    (hr_mem : r ∈ rs) (hr_last : ∀ x ∈ rs, x ≤ r) (hr_neg : r < 0) :
    ∃ ss σ, ss.length = rs.length - 1 ∧
      ListInterlaces (ss ++ [σ]) (rs ++ [0]) ∧
      (∀ s ∈ ss ++ [σ], (generalComparison κ a b v q).IsRoot s) ∧
      (ss ++ [σ]).Pairwise (· < ·) := by
  obtain ⟨ss, hlen, hint, hroots, hss⟩ :=
    exists_inner_comparison_roots κ a b v q rs hκ hq hrs_sorted hrs_eq
  have hr_mem_roots : r ∈ q.roots := by
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr hr_mem
  have hneg := generalComparison_eval_neg_at_last_root κ a b v q rs r hκ hq
    hrs_sorted hrs_eq hr_mem hr_last hr_neg
  have hzero := generalComparison_eval_zero_pos κ a b v q hκ ha hb hq
  obtain ⟨σ, hrσ, hσ0, hσroot⟩ := exists_last_comparison_root κ a b v q r
    hκ hq hr_mem_roots (by
      intro x hx
      have hx' : x ∈ (↑rs : Multiset ℝ) := by
        rw [hrs_eq]
        exact hx
      exact hr_last x (Multiset.mem_coe.mp hx'))
    hr_neg hzero hneg
  have hrsσ : ∀ x ∈ rs, x ≤ σ := by
    intro x hx
    exact (hr_last x hx).trans (le_of_lt hrσ)
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    subst rs
    simp at hr_mem
  have hint' := listInterlaces_append_endpoint hint hrs_ne hrsσ (le_of_lt hσ0)
  have hcross : ∀ s ∈ ss, s < σ := by
    intro s hs
    have hle : s ≤ r := listInterlaces_left_le_of_right_le hint
      (fun x hx => hr_last x hx) s hs
    exact hle.trans_lt hrσ
  have hpair : (ss ++ [σ]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hss, by simp, ?_⟩
    intro s hs t ht
    simp only [List.mem_singleton.mp ht]
    exact hcross s hs
  refine ⟨ss, σ, hlen, hint', ?_, hpair⟩
  intro s hs
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with hs | rfl
  · exact hroots s hs
  · exact hσroot

theorem generalStep_natDegree_and_leadingCoeff
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ)
    (hqdeg : q.natDegree = m) (hqpos : HasPosLeadingCoeff q)
    (hell : ∀ k ≤ m, 0 < u + v * k) :
    (generalStep κ a b u v q).natDegree = m + 1 ∧
      0 < (generalStep κ a b u v q).leadingCoeff := by
  let T := generalStep κ a b u v q
  have htop : T.coeff (m + 1) = (u + v * m) * q.leadingCoeff := by
    rw [coeff_generalStep]
    have hzero : q.coeff (m + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hqdeg]
      lia
    rw [hzero]
    simp only [mul_zero, zero_add, leadingCoeff, hqdeg]
  have hle : T.natDegree ≤ m + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    cases k with
    | zero =>
        rw [coeff_zero_generalStep]
        have hqzero : q.coeff 0 = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hqdeg]
          lia
        rw [hqzero]
        ring
    | succ k =>
        rw [coeff_generalStep]
        have hqk : q.coeff (k + 1) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hqdeg]
          lia
        have hqkm : q.coeff k = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hqdeg]
          lia
        rw [hqk, hqkm]
        ring
  have hdeg : T.natDegree = m + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by
      intro hz
      have hz' : (u + v * m) * q.leadingCoeff = 0 := by
        rw [← htop, hz]
      have hℓ : 0 < u + v * m := hell m le_rfl
      have hq' : 0 < q.leadingCoeff := hqpos
      nlinarith)
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg]
  rw [htop]
  exact mul_pos (hell m le_rfl) hqpos

theorem hasNonnegCoeffs_generalStep
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ)
    (hqdeg : q.natDegree = m) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hell : ∀ k ≤ m, 0 ≤ u + v * k)
    (hqcoeff : HasNonnegCoeffs q) :
    HasNonnegCoeffs (generalStep κ a b u v q) := by
  intro n
  cases n with
  | zero =>
      rw [coeff_zero_generalStep]
      exact mul_nonneg (mul_nonneg (mul_nonneg hκ ha) hb) (hqcoeff 0)
  | succ k =>
      rw [coeff_generalStep]
      by_cases hk : k ≤ m
      · apply add_nonneg
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg hκ (by positivity)) (by positivity))
            (hqcoeff (k + 1))
        · exact mul_nonneg (hell k hk) (hqcoeff k)
      · have hkm : m < k := lt_of_not_ge hk
        have hqk : q.coeff k = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hqdeg]
          exact hkm
        have hqk1 : q.coeff (k + 1) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [hqdeg]
          lia
        rw [hqk, hqk1]
        simp

theorem generalStep_sign_of_input_sign
    (κ a b u v : ℝ) (q : ℝ[X]) (σ : ℝ) (j : ℕ)
    (hprod : q.eval σ * (generalStep κ a b u v q).eval σ < 0)
    (hqsign : 0 < (-1 : ℝ) ^ j * q.eval σ) :
    0 < (-1 : ℝ) ^ (j + 1) *
      (generalStep κ a b u v q).eval σ := by
  have hpow : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← pow_add]
    simp
  have hqne : q.eval σ ≠ 0 := by
    intro hz
    rw [hz] at hqsign
    simp at hqsign
  have hTne : (generalStep κ a b u v q).eval σ ≠ 0 := by
    intro hz
    rw [hz] at hprod
    simp at hprod
  have hmul :
      ((-1 : ℝ) ^ j * q.eval σ) *
        ((-1 : ℝ) ^ j * (generalStep κ a b u v q).eval σ) < 0 := by
    calc
      _ = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) *
          (q.eval σ * (generalStep κ a b u v q).eval σ) := by ring
      _ = q.eval σ * (generalStep κ a b u v q).eval σ := by rw [hpow]; ring
      _ < 0 := hprod
  have hTsign : (-1 : ℝ) ^ j *
      (generalStep κ a b u v q).eval σ < 0 := by
    nlinarith
  rw [pow_succ]
  nlinarith

theorem hasSimpleRoots_of_sign_changes_with_left_endpoint
    {p : ℝ[X]} {d : ℕ} (hd : 0 < d) (hp : p ≠ 0)
    (hdegree : p.natDegree = d) (hlc : 0 < p.leadingCoeff)
    (r : Fin d → ℝ) (hr : ∀ i j, i < j → r i < r j)
    (hfirst : (-1 : ℝ) ^ d * p.eval (r ⟨0, hd⟩) < 0)
    (hsign : ∀ (k : ℕ) (hk : k + 1 < d),
      p.eval (r ⟨k, by lia⟩) * p.eval (r ⟨k + 1, hk⟩) < 0) :
    HasSimpleRoots p := by
  obtain ⟨R, hRlt, hRsign⟩ :=
    exists_left_endpoint_sign hdegree hlc (r ⟨0, hd⟩)
  let z : Fin (d + 1) → ℝ := Fin.cases R r
  have hz0 (i : Fin (d + 1)) (hi : i.1 = 0) : z i = R := by
    have : i = 0 := Fin.ext hi
    subst i
    simp [z]
  have hzpos (i : Fin (d + 1)) (hi : 0 < i.1) :
      z i = r ⟨i.1 - 1, by lia⟩ := by
    cases i using Fin.cases with
    | zero => simp at hi
    | succ k => simp [z]
  have hzsucc (i : Fin d) : z i.succ = r i := by simp [z]
  have hzorder : ∀ i j, i < j → z i < z j := by
    intro i j hij
    by_cases hi : i.1 = 0
    · rw [hz0 i hi, hzpos j (by lia)]
      by_cases hj : j.1 = 1
      · have heq : (⟨j.1 - 1, by lia⟩ : Fin d) = ⟨0, hd⟩ := by
          ext
          simp
          lia
        rwa [heq]
      · apply hRlt.trans
          (hr ⟨0, hd⟩ ⟨j.1 - 1, by lia⟩ (by simp; lia))
    · rw [hzpos i (Nat.pos_of_ne_zero hi), hzpos j (by lia)]
      apply hr
      simp
      lia
  have hzsign : ∀ (k : ℕ) (hk : k + 1 < d + 1),
      p.eval (z ⟨k, by lia⟩) * p.eval (z ⟨k + 1, hk⟩) < 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      have hnext : z (⟨0 + 1, hk⟩ : Fin (d + 1)) = r ⟨0, hd⟩ := by
        convert hzpos (⟨0 + 1, hk⟩ : Fin (d + 1)) (by lia) using 1
        simp
      rw [hz0 (⟨0, by lia⟩ : Fin (d + 1)) rfl,
        hnext]
      have hpow : (-1 : ℝ) ^ d * (-1 : ℝ) ^ d = 1 := by
        rw [← pow_add]
        simp
      have hprod := mul_pos hRsign (neg_pos.mpr hfirst)
      have heq :
          ((-1 : ℝ) ^ d * p.eval R) *
              (-((-1 : ℝ) ^ d * p.eval (r ⟨0, hd⟩))) =
            -(p.eval R * p.eval (r ⟨0, hd⟩)) := by
        calc
          _ = -(((-1 : ℝ) ^ d * (-1 : ℝ) ^ d) *
              (p.eval R * p.eval (r ⟨0, hd⟩))) := by ring
          _ = _ := by rw [hpow]; ring
      rw [heq] at hprod
      linarith
    · rw [hzpos ⟨k, by lia⟩ (Nat.pos_of_ne_zero hk0),
        hzpos ⟨k + 1, hk⟩ (by lia)]
      have hidx1 :
          (⟨↑(⟨k, by lia⟩ : Fin (d + 1)) - 1, by lia⟩ : Fin d) =
            ⟨k - 1, by lia⟩ := by
        ext
        rfl
      have hidx2 :
          (⟨↑(⟨k + 1, hk⟩ : Fin (d + 1)) - 1, by lia⟩ : Fin d) =
            ⟨k, by lia⟩ := by
        ext
        rfl
      rw [hidx1, hidx2]
      have hs := hsign (k - 1) (by lia)
      have hidx3 : (⟨k - 1 + 1, by lia⟩ : Fin d) = ⟨k, by lia⟩ := by
        ext
        lia
      rw [hidx3] at hs
      exact hs
  have hsplits := splits_of_sign_changes_with_left_endpoint
    hd hp hdegree hlc r hr hfirst hsign
  obtain ⟨us, hus_len, _, hus_roots, hus_strict⟩ :=
    MaWangInternal.exists_roots_strictly_interlacing_of_consecutive_signs
      (F := p) (List.pairwise_ofFn.2 (fun i j hij =>
        le_of_lt (hzorder i j hij))) (by
          intro pre r₁ r₂ rest hdecomp
          have hlength := congrArg List.length hdecomp
          simp only [List.length_ofFn, List.length_append, List.length_cons] at hlength
          have hi : pre.length < d + 1 := by lia
          let i : Fin d := ⟨pre.length, by lia⟩
          have hi₁ : pre.length < d + 1 := by lia
          have hi₂ : pre.length + 1 < d + 1 := by lia
          have hget₁ := congrArg (fun l : List ℝ => l[pre.length]?) hdecomp
          have hget₂ := congrArg (fun l : List ℝ => l[pre.length + 1]?) hdecomp
          simp only [List.getElem?_ofFn, hi₁] at hget₁
          simp only [List.getElem?_ofFn, hi₂] at hget₂
          simp at hget₁ hget₂
          have hs := hzsign pre.length (by lia)
          have hfin₁ : (⟨pre.length, hi₁⟩ : Fin (d + 1)) = i.castSucc := by
            ext
            rfl
          grind)
  have hus_nodup : us.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hus_strict.imp fun h => ne_of_lt h
  have hus_sub : (↑us : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hus_nodup)]
    intro x hx
    simp only [Multiset.mem_coe] at hx
    exact (mem_roots hp).mpr (hus_roots x hx)
  have hus_card : (↑us : Multiset ℝ).card = p.roots.card := by
    have hus_card' : (↑us : Multiset ℝ).card = d := by
      simpa [Multiset.coe_card] using hus_len
    have hp_card : p.roots.card = d := by
      rw [card_roots_of_splits hsplits, hdegree]
    apply le_antisymm
    · exact Multiset.card_le_card hus_sub
    · rw [hp_card, hus_card']
  have hroots_eq : (↑us : Multiset ℝ) = p.roots :=
    Multiset.eq_of_le_of_card_le hus_sub (le_of_eq hus_card.symm)
  have : p.roots.Nodup := by
    rw [← hroots_eq]
    exact Multiset.coe_nodup.mpr hus_nodup
  exact HasSimpleRoots.of_roots_nodup hp this

theorem isNegativeSimple_of_sign_changes_nonneg
    {p : ℝ[X]} {d : ℕ} (hd : 0 < d) (hp : p ≠ 0)
    (hdegree : p.natDegree = d) (hlc : 0 < p.leadingCoeff)
    (hnonneg : HasNonnegCoeffs p) (hp0 : 0 < p.eval 0)
    (r : Fin d → ℝ) (hr : ∀ i j, i < j → r i < r j)
    (hfirst : (-1 : ℝ) ^ d * p.eval (r ⟨0, hd⟩) < 0)
    (hsign : ∀ (k : ℕ) (hk : k + 1 < d),
      p.eval (r ⟨k, by lia⟩) * p.eval (r ⟨k + 1, hk⟩) < 0) :
    IsNegativeSimple p := by
  have hsplits := splits_of_sign_changes_with_left_endpoint
    hd hp hdegree hlc r hr hfirst hsign
  have hsimple := hasSimpleRoots_of_sign_changes_with_left_endpoint
    hd hp hdegree hlc r hr hfirst hsign
  have hstrict : ∀ x ∈ p.roots, x < 0 := by
    intro x hx
    have hx_nonpos := roots_nonpos_of_hasNonnegCoeffs hnonneg x hx
    have hxne : x ≠ 0 := by
      intro hxzero
      subst x
      have hroot := (mem_roots hp).mp hx
      rw [Polynomial.IsRoot.def] at hroot
      linarith
    exact lt_of_le_of_ne hx_nonpos hxne
  exact ⟨hp, hsplits, hsimple, hlc, hstrict⟩

private theorem isNegativeSimple_generalStep_of_certificate
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ)
    (hqdeg : q.natDegree = m) (hqpos : HasPosLeadingCoeff q)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k ≤ m, 0 < u + v * k)
    (hqcoeff : HasNonnegCoeffs q) (hq0 : 0 < q.eval 0)
    (hcert : ∃ r : Fin (m + 1) → ℝ,
      (∀ i j, i < j → r i < r j) ∧
      (-1 : ℝ) ^ (m + 1) *
          (generalStep κ a b u v q).eval (r ⟨0, by lia⟩) < 0 ∧
      (∀ k (hk : k + 1 < m + 1),
        (generalStep κ a b u v q).eval (r ⟨k, by lia⟩) *
            (generalStep κ a b u v q).eval (r ⟨k + 1, hk⟩) < 0)) :
    IsNegativeSimple (generalStep κ a b u v q) ∧
      (generalStep κ a b u v q).natDegree = m + 1 := by
  obtain ⟨r, hr, hfirst, hsign⟩ := hcert
  have hdeg_lc := generalStep_natDegree_and_leadingCoeff κ a b u v q m
    hqdeg hqpos hell
  have hTcoeff := hasNonnegCoeffs_generalStep κ a b u v q m hqdeg
    hκ.le ha.le hb.le (fun k hk => (hell k hk).le) hqcoeff
  have hq0c : 0 < q.coeff 0 := by
    simpa [coeff_zero_eq_eval_zero] using hq0
  have hT0 : 0 < (generalStep κ a b u v q).eval 0 := by
    calc
      0 < κ * a * b * q.coeff 0 :=
        mul_pos (mul_pos (mul_pos hκ ha) hb) hq0c
      _ = (generalStep κ a b u v q).coeff 0 := by
        rw [coeff_zero_generalStep]
      _ = (generalStep κ a b u v q).eval 0 := by
        simp [coeff_zero_eq_eval_zero]
  have hTne : generalStep κ a b u v q ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg_lc
    simp at hdeg_lc
  have hsimple := isNegativeSimple_of_sign_changes_nonneg
    (p := generalStep κ a b u v q) (d := m + 1) (by lia)
    hTne hdeg_lc.1 hdeg_lc.2 hTcoeff hT0 r hr hfirst hsign
  exact ⟨hsimple, hdeg_lc.1⟩

end RealRooted.EulerBidiagonal




open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

private theorem isNegativeSimple_C_mul_X_add_C
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    IsNegativeSimple (C c * (X + C β)) := by
  have hfne : X + C β ≠ 0 := X_add_C_ne_zero β
  have hfs : (X + C β).Splits := by
    have h := (isRealRooted_X_sub_C (-β : ℝ)).2
    have heq : X + C β = X - C (-β) := by
      simp [sub_eq_add_neg]
    rw [heq]
    exact h
  have hrr := isRealRooted_C_mul hfne hfs (ne_of_gt hc)
  have hsimple : HasSimpleRoots (C c * (X + C β)) := by
    apply HasSimpleRoots.of_roots_nodup hrr.1
    rw [Polynomial.roots_C_mul _ (ne_of_gt hc), roots_X_add_C]
    simp
  refine ⟨hrr.1, hrr.2, hsimple, ?_, ?_⟩
  · simpa [HasPosLeadingCoeff] using
      (mul_pos hc (hasPosLeadingCoeff_X_add_C β))
  · intro r hr
    rw [Polynomial.roots_C_mul _ (ne_of_gt hc), roots_X_add_C] at hr
    have hr' : r = -β := by simpa using hr
    rw [hr']
    linarith

theorem isNegativeSimple_generalStep_zero
    (κ a b u v : ℝ) (q : ℝ[X])
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hq : IsNegativeSimple q) (hqd : q.natDegree = 0) :
    IsNegativeSimple (generalStep κ a b u v q) ∧
      (generalStep κ a b u v q).natDegree = 1 := by
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hqd
  have hq0 : 0 < q.eval 0 := by
    have hq0mem : (0 : ℝ) ∉ q.roots := by
      intro hmem
      exact (not_lt_of_ge (le_refl 0)) (hq.2.2.2.2 0 hmem)
    have hcount : q.roots.countP (fun x => 0 < x) = 0 := by
      apply Multiset.countP_eq_zero.mpr
      intro x hx hpos
      exact (not_lt_of_ge (hq.2.2.2.2 x hx).le) hpos
    simpa [hcount] using (eval_sign hq.2.1 hq.2.2.2.1 0 hq0mem)
  have hq0c : 0 < q.coeff 0 := by
    simpa [coeff_zero_eq_eval_zero] using hq0
  have hform : generalStep κ a b u v q =
      C (q.coeff 0) * (C (κ * a * b) + C u * X) := by
    rw [hqC]
    simp only [generalStep, theta, derivative_C, map_zero, zero_add, C_mul,
      mul_zero, add_zero, mul_add, coeff_C, ite_true]
    ring
  have hfactor : C (κ * a * b) + C u * X =
      C u * (X + C (κ * a * b / u)) := by
    have hscalar : C u * C (κ * a * b / u) = C (κ * a * b) := by
      rw [← C_mul]
      congr 1
      field_simp [ne_of_gt hu]
    rw [mul_add, hscalar]
    ring
  have hsimple : IsNegativeSimple
      (C (q.coeff 0) * (C (κ * a * b) + C u * X)) := by
    have hc : 0 < q.coeff 0 * u := mul_pos hq0c hu
    have hscale : C (q.coeff 0) * C u = C (q.coeff 0 * u) := by
      rw [← C_mul]
    rw [hfactor]
    have heq : C (q.coeff 0) * (C u * (X + C (κ * a * b / u))) =
        C (q.coeff 0 * u) * (X + C (κ * a * b / u)) := by
      rw [← mul_assoc, hscale]
    rw [heq]
    exact isNegativeSimple_C_mul_X_add_C hc
      (div_pos (mul_pos (mul_pos hκ ha) hb) hu)
  have hdeg : (generalStep κ a b u v q).natDegree = 1 := by
    have := generalStep_natDegree_and_leadingCoeff κ a b u v q 0 hqd
      hq.2.2.2.1 (fun k hk => by
        have : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        simpa using hu)
    exact this.1
  have hsimpleT : IsNegativeSimple (generalStep κ a b u v q) := by
    rw [hform]
    exact hsimple
  exact ⟨hsimpleT, hdeg⟩

private lemma listInterlaces_head_le {ss rs' : List ℝ} {r : ℝ}
    (hint : ListInterlaces ss (r :: rs')) (hs : (r :: rs').Pairwise (· ≤ ·)) :
    ∀ x ∈ ss, r ≤ x := by
  induction ss generalizing r rs' with
  | nil => simp
  | cons s ss ih =>
      cases rs' with
      | nil => simp [ListInterlaces] at hint
      | cons r₂ rs'' =>
          rcases hint with ⟨h1, _, htail⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h1
          · have hr₂ := ih htail (List.Pairwise.of_cons hs) x hx
            exact (List.rel_of_pairwise_cons hs (by simp)).trans hr₂

private lemma countP_lt_getElem_of_listInterlaces {ss rs : List ℝ}
    (hint : ListInterlaces ss rs) (hrs : rs.Pairwise (· < ·))
    (hdisj : ∀ s ∈ ss, s ∉ rs) (hlen : ss.length + 1 = rs.length)
    (i : ℕ) (hi : i < ss.length) :
    rs.countP (fun r => decide (ss[i] < r)) = ss.length - i := by
  induction ss generalizing rs i with
  | nil => simp at hi
  | cons s ss ih =>
      rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs₂⟩⟩
      · simp at hlen
      · simp at hlen
      · obtain ⟨h1, h2, htail⟩ := hint
        have hr₂ : s ≠ r₂ := fun h => hdisj s (by simp) (by simp [h])
        have hr₁ : s ≠ r₁ := fun h => hdisj s (by simp) (by simp [h])
        have hlt₂ : s < r₂ := lt_of_le_of_ne h2 hr₂
        have hlen₂ : rs₂.length = ss.length := by
          simp only [List.length_cons] at hlen
          lia
        cases i with
        | zero =>
            have hall : rs₂.countP (fun r => decide (s < r)) = rs₂.length := by
              apply List.countP_eq_length.mpr
              intro x hx
              have := List.rel_of_pairwise_cons (List.Pairwise.of_cons hrs) hx
              simpa using hlt₂.trans this
            simp only [List.getElem_cons_zero, List.countP_cons, hall, hlen₂]
            have : ¬ s < r₁ := not_lt.mpr h1
            simp [this, hlt₂]
        | succ i' =>
            have hi' : i' < ss.length := by simpa using hi
            have hih := ih htail (List.Pairwise.of_cons hrs)
              (fun x hx => by
                intro hmem
                exact hdisj x (by simp [hx]) (by simp [hmem])) (by
                simp only [List.length_cons] at hlen ⊢
                lia) i' hi'
            have hx₂ := listInterlaces_head_le htail
              (List.Pairwise.imp (fun h => h.le) (List.Pairwise.of_cons hrs))
              ss[i'] (List.getElem_mem hi')
            have hr₁lt : r₁ < r₂ := List.rel_of_pairwise_cons hrs (by simp)
            have hn : ¬ ss[i'] < r₁ := not_lt.mpr (hr₁lt.le.trans hx₂)
            simp only [List.getElem_cons_succ, List.countP_cons, hih, List.length_cons]
            simp [hn]


/-- Unconditional general step: a negative-simple input of degree `m ≥ 1` is mapped to a
negative-simple polynomial of degree `m + 1`; the sign-change certificate is built from the
comparison roots of `generalComparison`. -/
theorem isNegativeSimple_generalStep_of_pos
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hm : 1 ≤ m)
    (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k ≤ m, 0 < u + v * k)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0)
    (hqcoeff : HasNonnegCoeffs q) :
    IsNegativeSimple (generalStep κ a b u v q) ∧
      (generalStep κ a b u v q).natDegree = m + 1 := by
  have hqne : q ≠ 0 := hq.1
  have hqsplits : q.Splits := hq.2.1
  have hqlc : 0 < q.leadingCoeff := hq.2.2.2.1
  have hq0mem : (0 : ℝ) ∉ q.roots := fun hmem => lt_irrefl _ (hq.2.2.2.2 0 hmem)
  have hq0 : 0 < q.eval 0 := by
    have hcount : q.roots.countP (fun x => 0 < x) = 0 := by
      apply Multiset.countP_eq_zero.mpr
      intro x hx hpos
      exact (not_lt_of_ge (hq.2.2.2.2 x hx).le) hpos
    simpa [hcount] using eval_sign hqsplits hqlc 0 hq0mem
  have hT0 : 0 < (generalStep κ a b u v q).eval 0 := by
    have hq0c : 0 < q.coeff 0 := by simpa [coeff_zero_eq_eval_zero] using hq0
    calc
      0 < κ * a * b * q.coeff 0 := mul_pos (mul_pos (mul_pos hκ ha) hb) hq0c
      _ = (generalStep κ a b u v q).coeff 0 := by rw [coeff_zero_generalStep]
      _ = (generalStep κ a b u v q).eval 0 := by simp [coeff_zero_eq_eval_zero]
  -- sorted roots
  set rs : List ℝ := q.roots.sort (· ≤ ·) with hrs_def
  have hrs_le : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
  have hrs_nodup : rs.Nodup := Multiset.coe_nodup.mp (by rw [hrs_eq]; exact hq.2.2.1.roots_nodup)
  have hrs_lt : rs.Pairwise (· < ·) :=
    (hrs_le.and hrs_nodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hrs_len : rs.length = m := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hqsplits, hqdeg]
  have hrs_ne : rs ≠ [] := by
    intro h
    rw [h] at hrs_len
    simp only [List.length_nil] at hrs_len
    lia
  have hrs_mem : ∀ x, x ∈ rs ↔ x ∈ q.roots := fun x => by
    rw [← hrs_eq]
    exact Multiset.mem_coe.symm
  have hrs_neg : ∀ x ∈ rs, x < 0 := fun x hx => hq.2.2.2.2 x ((hrs_mem x).mp hx)
  obtain ⟨ss, σ, hss_len, hint, hroots, hpair⟩ :=
    exists_comparison_roots_with_last κ a b v q rs (rs.getLast hrs_ne) hκ ha hb hq
      hrs_lt hrs_eq (List.getLast_mem hrs_ne)
      (fun x hx => List.Pairwise.rel_getLast hrs_le hx)
      (hrs_neg _ (List.getLast_mem hrs_ne))
  have hzero := generalComparison_eval_zero_pos κ a b v q hκ ha hb hq
  set A : List ℝ := ss ++ [σ] with hA
  have hA_len : A.length = m := by
    simp only [hA, List.length_append, List.length_singleton]
    lia
  have hA_le : ∀ x ∈ A, x ≤ 0 := by
    have := listInterlaces_left_le_of_right_le hint (c := 0) (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hrs_neg x hx).le
      · simp only [List.mem_singleton] at hx
        exact hx.le)
    exact this
  have hA_root : ∀ x ∈ A, (generalComparison κ a b v q).IsRoot x := hroots
  have hA_neg : ∀ x ∈ A, x < 0 := by
    intro x hx
    refine lt_of_le_of_ne (hA_le x hx) ?_
    intro h
    have := (hA_root x hx).eq_zero
    rw [h] at this
    linarith
  have hA_prod : ∀ x ∈ A, q.eval x * (generalStep κ a b u v q).eval x < 0 :=
    fun x hx => generalStep_eval_mul_neg_of_generalComparison_root κ a b u v q x hκ hq hQ
        (hA_root x hx)
      (hA_neg x hx)
  have hA_not : ∀ x ∈ A, x ∉ rs ++ [0] := by
    intro x hx hmem
    rcases List.mem_append.mp hmem with h | h
    · have hroot : q.eval x = 0 := (isRoot_of_mem_roots ((hrs_mem x).mp h)).eq_zero
      have := hA_prod x hx
      rw [hroot] at this
      simp at this
    · simp only [List.mem_singleton] at h
      exact lt_irrefl _ (h ▸ hA_neg x hx)
  have hrs0_lt : (rs ++ [0]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hrs_lt, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact hrs_neg x hx
  have hcount : ∀ (i : ℕ) (hi : i < m),
      q.roots.countP (fun r => A[i]'(by lia) < r) = m - i - 1 := by
    intro i hi
    have hc := countP_lt_getElem_of_listInterlaces hint hrs0_lt hA_not (by
      simp only [List.length_append, List.length_singleton, hA_len, hrs_len])
      i (by lia)
    rw [List.countP_append] at hc
    have h0 : [(0 : ℝ)].countP (fun r => decide (A[i]'(by lia) < r)) = 1 := by
      simp [hA_neg _ (List.getElem_mem _)]
    rw [h0, hA_len] at hc
    rw [← hrs_eq, Multiset.coe_countP]
    lia
  have hqsign : ∀ (i : ℕ) (hi : i < m),
      0 < (-1 : ℝ) ^ (m - i - 1) * q.eval (A[i]'(by lia)) := by
    intro i hi
    have hnot : A[i]'(by lia) ∉ q.roots := by
      rw [← hrs_eq]
      intro h
      exact hA_not _ (List.getElem_mem _) (List.mem_append_left _ (Multiset.mem_coe.mp h))
    have := eval_sign hqsplits hqlc _ hnot
    rw [hcount i hi] at this
    linarith
  set P : List ℝ := A ++ [0] with hP
  have hP_len : P.length = m + 1 := by
    simp only [hP, List.length_append, List.length_singleton, hA_len]
  have hP_lt : P.Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hpair, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact hA_neg x hx
  have hP_A : ∀ (i : ℕ) (hi : i < m), P[i]'(by lia) = A[i]'(by lia) := by
    intro i hi
    simp only [hP]
    exact List.getElem_append_left _
  have hP_m : P[m]'(by lia) = 0 := by
    simp only [hP]
    rw [List.getElem_append_right (by lia)]
    simp [hA_len]
  have hTsign : ∀ (i : ℕ) (hi : i < m + 1),
      0 < (-1 : ℝ) ^ (m - i) * (generalStep κ a b u v q).eval (P[i]'(by lia)) := by
    intro i hi
    rcases Nat.lt_or_ge i m with him | him
    · rw [hP_A i him]
      have := generalStep_sign_of_input_sign κ a b u v q (A[i]'(by lia)) (m - i - 1)
        (hA_prod _ (List.getElem_mem _)) (hqsign i him)
      have hmi : m - i - 1 + 1 = m - i := by lia
      rw [hmi] at this
      exact this
    · have him' : i = m := by lia
      subst him'
      rw [hP_m]
      simpa using hT0
  have hcert : ∃ r : Fin (m + 1) → ℝ,
      (∀ i j, i < j → r i < r j) ∧
      (-1 : ℝ) ^ (m + 1) *
          (generalStep κ a b u v q).eval (r ⟨0, by lia⟩) < 0 ∧
      (∀ k (hk : k + 1 < m + 1),
        (generalStep κ a b u v q).eval (r ⟨k, by lia⟩) *
            (generalStep κ a b u v q).eval (r ⟨k + 1, hk⟩) < 0) := by
    refine ⟨fun i => P[i.1]'(by rw [hP_len]; exact i.2), ?_, ?_, ?_⟩
    · intro i j hij
      exact List.pairwise_iff_getElem.mp hP_lt i.1 j.1 _ _ hij
    · have h0 := hTsign 0 (by lia)
      simp only [Nat.sub_zero] at h0
      rw [pow_succ]
      nlinarith
    · intro k hk
      have h1 := hTsign k (by lia)
      have h2 := hTsign (k + 1) hk
      have hmk : m - k = (m - (k + 1)) + 1 := by lia
      rw [hmk, pow_succ] at h1
      set e : ℝ := (-1 : ℝ) ^ (m - (k + 1)) with he
      have hee : e * e = 1 := by
        rw [he, ← pow_add]
        have : (-1 : ℝ) ^ ((m - (k + 1)) + (m - (k + 1))) =
            ((-1 : ℝ) ^ 2) ^ (m - (k + 1)) := by
          rw [← pow_mul]
          congr 1
          lia
        rw [this]
        simp
      set x := (generalStep κ a b u v q).eval (P[k]'(by lia))
      set y := (generalStep κ a b u v q).eval (P[k + 1]'(by lia))
      have hprod : 0 < (e * y) * (-(e * x)) := mul_pos h2 (by linarith)
      have : (e * y) * (-(e * x)) = -((e * e) * (x * y)) := by ring
      rw [this, hee] at hprod
      linarith
  exact isNegativeSimple_generalStep_of_certificate κ a b u v q m hqdeg hqlc hκ ha hb hell hqcoeff
      hq0 hcert


end RealRooted.EulerBidiagonal

