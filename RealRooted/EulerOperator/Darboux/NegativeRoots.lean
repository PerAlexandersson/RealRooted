import RealRooted.EulerOperator.Darboux.Basic
import RealRooted.MaWang.DerivativeStep
import RealRooted.SimpleRoots

/-!
# Darboux operators on polynomials with simple negative roots

For `a > 0` the Darboux operator `D_{a,-b}(f) = x (1 - x) f' + (a + b x) f` raises the degree of
a polynomial of degree `d < b` with simple negative roots and nonnegative coefficients by one,
keeps all of these properties, and strictly interlaces with its input.  This is the common
first-order step behind the Jacobi–Stirling insertions (Ma–Wang, Lemma 2) and the multiset
Eulerian–Narayana factorization (Zhang–Zhao, Lemma 2.8).  The unit-interval counterpart is
`RealRooted.EulerOperator.Darboux.Interlacing`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The invariant `f` has degree `d`, positive leading coefficient, nonnegative coefficients,
positive constant term, and simple real roots; in particular all roots of `f` are negative. -/
structure SimpleNegRooted (f : ℝ[X]) (d : ℕ) : Prop where
  natDegree_eq : f.natDegree = d
  pos : HasPosLeadingCoeff f
  nonneg : HasNonnegCoeffs f
  coeff_zero_pos : 0 < f.coeff 0
  splits : f.Splits
  simple : HasSimpleRoots f

namespace SimpleNegRooted

variable {f : ℝ[X]} {d : ℕ}

theorem isRoot_neg (hf : SimpleNegRooted f d) {r : ℝ} (hr : f.IsRoot r) : r < 0 := by
  refine lt_of_le_of_ne (isRoot_nonpos_of_hasNonnegCoeffs hf.nonneg hf.pos.ne_zero hr) ?_
  rintro rfl
  have := hf.coeff_zero_pos
  rw [coeff_zero_eq_eval_zero, hr.eq_zero] at this
  exact lt_irrefl _ this

theorem of_eq {e : ℕ} (hf : SimpleNegRooted f d) (h : d = e) : SimpleNegRooted f e :=
  h ▸ hf

theorem one : SimpleNegRooted (1 : ℝ[X]) 0 :=
  ⟨by simp, by simp [HasPosLeadingCoeff], fun k => by rw [coeff_one]; split_ifs <;> norm_num,
    by simp, Splits.one, fun r hr => absurd hr (by simp)⟩

theorem C_mul (hf : SimpleNegRooted f d) {c : ℝ} (hc : 0 < c) :
    SimpleNegRooted (C c * f) d := by
  refine ⟨by rw [natDegree_C_mul hc.ne', hf.natDegree_eq], hasPosLeadingCoeff_C_mul hc hf.pos,
    fun k => by rw [coeff_C_mul]; exact mul_nonneg hc.le (hf.nonneg k),
    by rw [coeff_C_mul]; exact mul_pos hc hf.coeff_zero_pos, hf.splits.C_mul c, ?_⟩
  intro r hr
  rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc.ne') hf.pos.ne_zero),
    rootMultiplicity_C, zero_add]
  exact hf.simple r (by simpa [IsRoot, hc.ne'] using hr)

/-- **Darboux step.**  If `a > 0` and `deg f < b`, then
`D_{a,-b}(f) = x (1 - x) f' + (a + b x) f` keeps the invariant in degree `deg f + 1` and
strictly interlaces with `f`, with no common root. -/
theorem darbouxOperator (hf : SimpleNegRooted f d) {a b : ℝ} (ha : 0 < a) (hb : (d : ℝ) < b) :
    SimpleNegRooted (darbouxOperator a (-b) f) (d + 1) ∧
      StrictInterl f (darbouxOperator a (-b) f) ∧
      ∀ r, f.IsRoot r → ¬ (darbouxOperator a (-b) f).IsRoot r := by
  set F := RealRooted.darbouxOperator a (-b) f with hF
  have hcoeff_gt : ∀ k, d < k → f.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (hf.natDegree_eq ▸ hk)
  have hcoeff : ∀ k : ℕ,
      F.coeff (k + 1) = (k + 1 + a) * f.coeff (k + 1) + (b - k) * f.coeff k := by
    intro k
    rw [hF, coeff_darbouxOperator_succ]
    ring
  have hcoeff0 : F.coeff 0 = a * f.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, hF, darbouxOperator_eval_zero]
  have htop_pos : 0 < F.coeff (d + 1) := by
    rw [hcoeff, hcoeff_gt (d + 1) (by lia), mul_zero, zero_add]
    have := hf.pos
    rw [HasPosLeadingCoeff, leadingCoeff, hf.natDegree_eq] at this
    exact mul_pos (by linarith) this
  have hdeg : F.natDegree = d + 1 := by
    refine natDegree_eq_of_le_of_coeff_ne_zero
      ((natDegree_le_iff_coeff_eq_zero).mpr fun j hj => ?_) htop_pos.ne'
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
    rw [hcoeff, hcoeff_gt (k + 1) (by lia), hcoeff_gt k (by lia)]
    ring
  have hpos : HasPosLeadingCoeff F := by
    rw [HasPosLeadingCoeff, leadingCoeff, hdeg]
    exact htop_pos
  have hrec : F = (C a + C b * X) * f + X * (1 - X) * f.derivative := by
    rw [hF, RealRooted.darbouxOperator, map_neg]
    ring
  have hv : ∀ r, f.IsRoot r → (X * (1 - X) : ℝ[X]).eval r < 0 := by
    intro r hr
    have := hf.isRoot_neg hr
    simp only [eval_mul, eval_X, eval_sub, eval_one]
    nlinarith
  have hinterl : StrictInterl f F := by
    rw [hrec]
    exact MaWang.strictInterl_derivative_of_nonpos_of_splits hf.splits
      (by rw [← hrec, hdeg, hf.natDegree_eq]; lia) (by rw [← hrec, hdeg, hf.natDegree_eq])
      (hrec ▸ hpos) hf.pos fun r hr => (hv r hr).le
  have hno : ∀ r : ℝ, ¬ (f.IsRoot r ∧ F.IsRoot r) := by
    rintro r ⟨hr, hFr⟩
    have hval : F.eval r = (X * (1 - X) : ℝ[X]).eval r * f.derivative.eval r := by
      rw [hF, darbouxOperator_eval_isRoot _ _ hr]
      simp
    rw [hFr.eq_zero] at hval
    exact mul_ne_zero (hv r hr).ne (hf.simple.eval_derivative_ne_zero hr) hval.symm
  refine ⟨⟨hdeg, hpos, fun k => ?_, by rw [hcoeff0]; exact mul_pos ha hf.coeff_zero_pos,
    hinterl.2.1.2, (hinterl.hasSimpleRoots_of_no_common_root hno).2⟩, hinterl,
    fun r hr hFr => hno r ⟨hr, hFr⟩⟩
  rcases k with _ | k
  · rw [hcoeff0]
    exact mul_nonneg ha.le (hf.nonneg 0)
  rw [hcoeff]
  rcases le_or_gt k d with hk | hk
  · have : (k : ℝ) ≤ d := by exact_mod_cast hk
    have h1 := hf.nonneg (k + 1)
    have h2 := hf.nonneg k
    have : (0 : ℝ) ≤ b - k := by linarith
    positivity
  · rw [hcoeff_gt (k + 1) (by lia), hcoeff_gt k hk]
    ring_nf
    rfl

end SimpleNegRooted

end RealRooted
