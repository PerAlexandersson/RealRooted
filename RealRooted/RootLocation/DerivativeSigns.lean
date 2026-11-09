module

public import RealRooted.RootLocation.Basic
public import RealRooted.Basic.Coefficients
import RealRooted.WagnerX.NonnegativeRoots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic

/-!
# Signs of derivatives outside the roots

If a real-rooted polynomial `q` has all its roots to the left of `x`, then the shifted polynomial
`q (X + x)` has only nonpositive roots, so its coefficients all have the sign of the leading
coefficient.  Since these coefficients are the Taylor coefficients `q ^ (k) (x) / k!`, every
derivative value `q ^ (k) (x)` has the sign of the leading coefficient.  Reflecting `X ↦ -X`
gives the corresponding statement to the left of all roots, where the sign alternates with `k`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- A polynomial rooted in `Iic 0` has coefficients with the sign of its leading coefficient. -/
private theorem leadingCoeff_mul_coeff_nonneg_of_isRealRootedIn_Iic {p : ℝ[X]}
    (hp : IsRealRootedIn (Iic 0) p) (k : ℕ) : 0 ≤ p.leadingCoeff * p.coeff k := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  have hmonic : (C p.leadingCoeff⁻¹ * p).leadingCoeff = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  have hroots : ∀ r ∈ (C p.leadingCoeff⁻¹ * p).roots, r ≤ 0 := fun r hr ↦
    (IsRealRootedIn.C_mul (inv_ne_zero hlc) hp).mem_of_mem_roots hr
  have hnn := (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos
    (hp.splits.C_mul _)).2 ⟨by rw [HasPosLeadingCoeff, hmonic]; exact one_pos, hroots⟩
  have hk := hnn.1 k
  rw [coeff_C_mul] at hk
  have : p.leadingCoeff * p.coeff k = p.leadingCoeff ^ 2 * (p.leadingCoeff⁻¹ * p.coeff k) := by
    field_simp
  rw [this]
  positivity

/-- **Signs of derivatives outside the root hull (general form).**  If `ε ≠ 0` and
`ε * (ρ - x) ≤ 0` for every root `ρ` of `q`, then `ε ^ (deg q + k) * lc q * q ^ (k) (x) ≥ 0`. -/
private theorem pow_mul_leadingCoeff_mul_eval_iterate_derivative_nonneg {q : ℝ[X]} {ε x : ℝ}
    (hε : ε ≠ 0) (hq : IsRealRootedIn {ρ | ε * (ρ - x) ≤ 0} q) (k : ℕ) :
    0 ≤ ε ^ (q.natDegree + k) * q.leadingCoeff * ((derivative^[k]) q).eval x := by
  have h1 : IsRealRootedIn (Iic 0) (q.comp (C ε * X + C x)) := by
    refine (hq.comp_C_mul_X_add_C x hε).mono fun y hy ↦ ?_
    simp only [mem_preimage, mem_ofPred_eq] at hy
    by_contra h
    have hy0 : 0 < y := lt_of_not_ge h
    nlinarith [mul_pos (sq_pos_of_ne_zero hε) hy0]
  have h2 := leadingCoeff_mul_coeff_nonneg_of_isRealRootedIn_Iic h1 k
  have hlin : (C ε * X + C x).natDegree = 1 := natDegree_linear hε
  have hlc : (q.comp (C ε * X + C x)).leadingCoeff = q.leadingCoeff * ε ^ q.natDegree := by
    rw [leadingCoeff_comp (by rw [hlin]; exact one_ne_zero), leadingCoeff_linear hε]
  have hcoeff : (q.comp (C ε * X + C x)).coeff k =
      (derivative^[k] q).eval x / k.factorial * ε ^ k := by
    have : q.comp (C ε * X + C x) = (taylor x q).comp (C ε * X) := by
      rw [taylor_apply, comp_assoc]
      simp
    have hd : (derivative^[k] q).eval x = k.factorial * (hasseDeriv k q).eval x := by
      rw [← factorial_smul_hasseDeriv]
      simp
    rw [this, comp_C_mul_X_coeff, taylor_coeff, hd]
    field_simp
  rw [hlc, hcoeff] at h2
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have : q.leadingCoeff * ε ^ q.natDegree * ((derivative^[k] q).eval x / k.factorial * ε ^ k) =
      (ε ^ (q.natDegree + k) * q.leadingCoeff * (derivative^[k] q).eval x) / k.factorial := by
    rw [pow_add]
    ring
  rw [this] at h2
  exact (div_nonneg_iff.mp h2).elim (fun h ↦ h.1) fun h ↦
    absurd h.2 (not_le.mpr hfac)

/-- **Derivatives to the right of the roots.**  If every root of `q` is at most `x`, then every
derivative of `q` at `x` has the sign of the leading coefficient of `q`. -/
theorem IsRealRootedIn.leadingCoeff_mul_eval_iterate_derivative_nonneg {q : ℝ[X]} {x : ℝ}
    (hq : IsRealRootedIn (Iic x) q) (k : ℕ) :
    0 ≤ q.leadingCoeff * ((derivative^[k]) q).eval x := by
  have := pow_mul_leadingCoeff_mul_eval_iterate_derivative_nonneg (ε := 1) (x := x)
    one_ne_zero (hq.mono fun ρ hρ ↦ by simpa using hρ) k
  simpa using this

/-- **Derivatives to the left of the roots.**  If every root of `q` is at least `x`, then the
`k`th derivative of `q` at `x` has the sign `(-1) ^ (deg q + k)` times that of the leading
coefficient of `q`. -/
theorem IsRealRootedIn.negOnePow_mul_eval_iterate_derivative_nonneg {q : ℝ[X]}
    {x : ℝ} (hq : IsRealRootedIn (Ici x) q) (k : ℕ) :
    0 ≤ (-1) ^ (q.natDegree + k) * q.leadingCoeff * ((derivative^[k]) q).eval x :=
  pow_mul_leadingCoeff_mul_eval_iterate_derivative_nonneg (ε := -1) (x := x) (by norm_num)
    (hq.mono fun ρ hρ ↦ by simp only [mem_Ici] at hρ; simp only [mem_ofPred_eq]; linarith) k

/-- A monic polynomial whose roots are all at most `x` is nonnegative at `x`. -/
theorem IsRealRootedIn.eval_nonneg_of_monic {q : ℝ[X]} {x : ℝ} (hq : IsRealRootedIn (Iic x) q)
    (hm : q.Monic) : 0 ≤ q.eval x := by
  simpa [hm.leadingCoeff] using hq.leadingCoeff_mul_eval_iterate_derivative_nonneg 0

end RealRooted
