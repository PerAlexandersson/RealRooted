module

public import RealRooted.EffectiveBKW.Certificate.IsolatedRoot
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Certified root branches

Cells certify opposite wall signs and a signed partial derivative. Overlapping
cells certify uniqueness on the vertical hull. A compact-graph argument proves
continuity, including at cell junctions.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open Polynomial BigDescents321.SmallCases Set

namespace IntPoly2

/-- Interpret the `y` polynomial after specializing `t`. -/
noncomputable def polynomial : IntPoly2 → ℝ → ℝ[X]
  | [], _ => 0
  | p :: f, t => C (p.eval t) + X * polynomial f t

/-- Polynomial specialization agrees with bivariate evaluation. -/
theorem eval_polynomial (f : IntPoly2) (t y : ℝ) :
    (f.polynomial t).eval y = f.eval t y := by
  induction f with
  | nil => simp [polynomial, eval]
  | cons p f ih => simp [polynomial, eval, ih]

/-- A vanishing specialized polynomial has zero coefficient lists. -/
private theorem all_eqCheck_nil_of_polynomial_eq_zero {f : IntPoly2}
    (h : ∀ t, polynomial f t = 0) : f.all (fun p => p.eqCheck []) = true := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    have hp : IntPoly.polynomial p = 0 := by
      apply Polynomial.funext
      intro t
      simp only [Polynomial.eval_zero]
      change p.eval t = 0
      have hc := congrArg (fun q : ℝ[X] => q.coeff 0) (h t)
      simpa only [polynomial, coeff_add, coeff_C_zero, coeff_X_mul_zero,
        add_zero, coeff_zero] using hc
    have hf : ∀ t, polynomial f t = 0 := by
      intro t
      have hp' : p.eval t = 0 := by
        rw [IntPoly.eval, hp, Polynomial.eval_zero]
      simpa only [polynomial, hp', C_0, zero_add, mul_eq_zero, X_ne_zero, false_or]
        using h t
    exact Bool.and_eq_true_iff.mpr ⟨IntPoly.eqCheck_of_polynomial_eq hp, ih hf⟩

/-- Bivariate polynomial equality is complete for the integer-list checker. -/
theorem eqCheck_of_forall_eval_eq {f g : IntPoly2}
    (he : ∀ t y, f.eval t y = g.eval t y) : f.eqCheck g = true := by
  have h : ∀ t, polynomial f t = polynomial g t := by
    intro t
    apply Polynomial.funext
    intro y
    simpa only [eval_polynomial] using he t y
  induction f generalizing g with
  | nil => exact all_eqCheck_nil_of_polynomial_eq_zero (fun t => (h t).symm)
  | cons p f ih =>
    cases g with
    | nil => exact all_eqCheck_nil_of_polynomial_eq_zero h
    | cons q g =>
      have hpq : IntPoly.polynomial p = IntPoly.polynomial q := by
        apply Polynomial.funext
        intro t
        change p.eval t = q.eval t
        have hc := congrArg (fun q : ℝ[X] => q.coeff 0) (h t)
        simpa only [polynomial, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero] using hc
      have hf : ∀ t, polynomial f t = polynomial g t := by
        intro t
        apply mul_left_cancel₀ (X_ne_zero : (X : ℝ[X]) ≠ 0)
        apply add_left_cancel (a := C (q.eval t))
        have hp' : p.eval t = q.eval t := congrArg (Polynomial.eval t) hpq
        simpa only [polynomial, hp'] using h t
      apply Bool.and_eq_true_iff.mpr
      refine ⟨IntPoly.eqCheck_of_polynomial_eq hpq, ih ?_ hf⟩
      intro t y
      simpa only [eval_polynomial] using congrArg (Polynomial.eval y) (hf t)

/-- Appending a zero coefficient row does not change bivariate evaluation. -/
private theorem eval_append_zero {p : IntPoly} (hp : p.all (· == 0) = true)
    (f : IntPoly2) (t y : ℝ) : (f ++ [p]).eval t y = f.eval t y := by
  have hz : p.eqCheck [] = true := by cases p <;> exact hp
  have hp0 : p.eval t = 0 := by
    simpa only [IntPoly.eval, IntPoly.polynomial, BigDescents321.SmallCases.ofList_nil,
      Polynomial.eval_zero] using congrArg (Polynomial.eval t) (IntPoly.eqCheck_sound hz)
  induction f with
  | nil => simpa only [List.nil_append, IntPoly2.eval, mul_zero, add_zero] using hp0
  | cons q f ih => simp only [List.cons_append, IntPoly2.eval, ih]

/-- Dropping zero rows before reversal preserves the represented polynomial. -/
private theorem eval_reverse_dropWhile (f : IntPoly2) (t y : ℝ) :
    IntPoly2.eval ((f.dropWhile (fun p ↦ p.all (· == 0))).reverse) t y =
      IntPoly2.eval f.reverse t y := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    by_cases hp : p.all (· == 0) = true
    · rw [List.dropWhile_cons_of_pos (p := fun p : IntPoly ↦ p.all (· == 0)) hp,
        List.reverse_cons, eval_append_zero hp, ih]
    · rw [List.dropWhile_cons_of_neg (p := fun p : IntPoly ↦ p.all (· == 0)) hp]

/-- Trimming zero rows leaves bivariate evaluation unchanged. -/
private theorem eval_trim (f : IntPoly2) (t y : ℝ) : f.trim.eval t y = f.eval t y := by
  simpa only [IntPoly2.trim, List.reverse_reverse] using
    eval_reverse_dropWhile f.reverse t y


/-- Homogeneous evaluation agrees with ordinary bivariate evaluation after division. -/
private theorem bernsteinEval_mul_eval (f : IntPoly2) (t x z : ℝ) (hz : z ≠ 0) :
    z * bernsteinEval (f.map (fun p ↦ p.eval t)) x z =
      z ^ f.length * f.eval t (x / z) := by
  induction f with
  | nil => simp [bernsteinEval, IntPoly2.eval]
  | cons p f ih =>
    simp only [List.map_cons, bernsteinEval, List.length_map, List.length_cons,
      IntPoly2.eval, pow_succ] at *
    calc
      _ = p.eval t * z ^ f.length * z + x *
          (z ^ f.length * IntPoly2.eval f t (x / z)) := by rw [← ih]; ring
      _ = _ := by field_simp


/-- The inverse linear substitution reconstructs homogeneous evaluation, after cancellation. -/
private theorem bernstein_reconstruction_eval (f coeffs : IntPoly2) (d l u : ℤ) (t y : ℝ)
    (hn : f.length ≠ 0) (hlen : coeffs.length = f.length)
    (hD : (0 : ℝ) < (d : ℝ) * (u - l)) (hz : (u : ℝ) - d * y ≠ 0)
    (hc : ∀ s : ℝ, coeffs.eval t s = bernsteinEval (f.map (fun p => p.eval t))
      (l + u * s) (d + d * s)) :
    ((d : ℝ) * (u - l)) ^ (f.length - 1) * f.eval t y =
      (bernsteinList [[-l], [d]] [[u], [-d]] coeffs).eval t y := by
  have hlin (a b : ℤ) (v : ℝ) : eval [[a], [b]] t v = a + v * b := by
    simp [eval, IntPoly.eval, IntPoly.polynomial, ofList_cons]
  let z : ℝ := u - d * y
  let s : ℝ := (-l + d * y) / z
  have hw : (d : ℝ) + d * s = (d : ℝ) * (u - l) / z := by
    dsimp [s, z]
    field_simp
    ring
  have hw0 : (d : ℝ) + d * s ≠ 0 := by rw [hw]; exact div_ne_zero hD.ne' hz
  have ha : ((l : ℝ) + u * s) / ((d : ℝ) + d * s) = y := by
    apply (div_eq_iff hw0).mpr
    dsimp [s, z]
    field_simp
    ring
  have he₁ := bernsteinEval_mul_eval coeffs t (-l + d * y) z hz
  have heval : (bernsteinList [[-l], [d]] [[u], [-d]] coeffs).eval t y =
      bernsteinEval (coeffs.map (fun p => p.eval t)) (-l + d * y) z := by
    simp only [eval_bernsteinList, hlin, Int.cast_neg, mul_neg, mul_comm,
      z, sub_eq_add_neg]
  rw [← heval, hlen] at he₁
  have he₂ := bernsteinEval_mul_eval f t (l + u * s) (d + d * s) hw0
  rw [ha, ← hc s] at he₂
  have hprod : ((d : ℝ) * (u - l)) * (bernsteinList [[-l], [d]] [[u], [-d]] coeffs).eval t y =
      ((d : ℝ) * (u - l)) ^ f.length * f.eval t y := by
    calc
      _ = (d + d * s) * (z * (bernsteinList [[-l], [d]] [[u], [-d]] coeffs).eval t y) := by
        rw [hw, div_mul_eq_mul_div, ← mul_assoc, mul_right_comm _ z,
          mul_div_cancel_right₀ _ hz]
      _ = (d + d * s) * (z ^ f.length * coeffs.eval t s) := by rw [he₁]
      _ = z ^ f.length * ((d + d * s) * coeffs.eval t s) := by ring
      _ = z ^ f.length * ((d + d * s) ^ f.length * f.eval t y) := by rw [he₂]
      _ = ((d : ℝ) * (u - l)) ^ f.length * f.eval t y := by
        rw [← mul_assoc, ← mul_pow, hw, mul_div_cancel₀ _ hz]
  have hpw : ((d : ℝ) * (u - l)) ^ f.length =
      ((d : ℝ) * (u - l)) * ((d : ℝ) * (u - l)) ^ (f.length - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  have he : ((d : ℝ) * (u - l)) ^ (f.length - 1) * f.eval t y =
      (bernsteinList [[-l], [d]] [[u], [-d]] coeffs).eval t y := by
    apply mul_left_cancel₀ hD.ne'
    rw [← mul_assoc, ← hpw]
    exact hprod.symm
  exact he

/-- The automatic Bernstein coefficients reconstruct the original polynomial when trimming
preserves the expected degree. -/
theorem bernsteinCoeffs_reconstruction {f : IntPoly2} {lo hi : QNum}
    (hlo : lo.valid = true) (hhi : hi.valid = true) (hlt : lo.lt hi = true)
    (hlen : (bernsteinCoeffs f lo hi).length = f.length) :
    let (d, l, u) := IntPoly.intervalData lo hi
    (smul ((d * (u - l)) ^ (f.length - 1)) f).eqCheck
      (bernsteinList [[-l], [d]] [[u], [-d]] (bernsteinCoeffs f lo hi)) = true := by
  by_cases hf : f = []
  · subst f
    rfl
  have hn : f.length ≠ 0 := fun h => hf (List.length_eq_zero_iff.mp h)
  let d : ℤ := lo.den * hi.den
  let l : ℤ := lo.num * hi.den
  let u : ℤ := hi.num * lo.den
  have hd : 0 < d := by
    exact mul_pos (Int.natCast_pos.mpr (of_decide_eq_true hlo))
      (Int.natCast_pos.mpr (of_decide_eq_true hhi))
  have hlu : l < u := of_decide_eq_true hlt
  have hD : (0 : ℝ) < (d : ℝ) * (u - l) := by exact_mod_cast mul_pos hd (sub_pos.mpr hlu)
  let coeffs := bernsteinCoeffs f lo hi
  let rhs := bernsteinList [[-l], [d]] [[u], [-d]] coeffs
  apply eqCheck_of_forall_eval_eq
  intro t y
  have hp : (smul ((d * (u - l)) ^ (f.length - 1)) f).polynomial t = rhs.polynomial t := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Iio_infinite ((u : ℝ) / d)).mono
    intro y hy
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd
    have hz : (u : ℝ) - d * y ≠ 0 := by
      apply ne_of_gt
      have := (lt_div_iff₀ hdr).mp hy
      linarith
    have hc (s : ℝ) : coeffs.eval t s = bernsteinEval (f.map (fun p => p.eval t))
        (l + u * s) (d + d * s) := by
      have hlin (a b : ℤ) (v : ℝ) : eval [[a], [b]] t v = a + v * b := by
        simp [eval, IntPoly.eval, IntPoly.polynomial, ofList_cons]
      simp only [coeffs, bernsteinCoeffs, IntPoly.intervalData, eval_trim, eval_homogenize, hlin]
      dsimp only [d, l, u]
      push_cast
      simp only [mul_comm]
    have he := bernstein_reconstruction_eval f coeffs d l u t y hn hlen hD hz hc
    simp only [mem_ofPred_eq, eval_polynomial]
    simpa only [eval_smul, Int.cast_pow, Int.cast_mul, Int.cast_sub] using he
  simpa only [eval_polynomial, rhs, d, l, u, IntPoly.intervalData] using
    congrArg (Polynomial.eval y) hp

/-- Assemble a box check by proving reconstruction symbolically and checking only coefficients. -/
theorem posOnBox_of_bernsteinCoeffs {f : IntPoly2} {tlo thi lo hi : QNum}
    (h : let cs := bernsteinCoeffs f lo hi
      (lo.valid && hi.valid && lo.lt hi && decide (cs.length = f.length) &&
        decide (cs ≠ []) && cs.all (fun p => p.posOn tlo thi)) = true) :
    f.posOnBox tlo thi lo hi = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hlt⟩, hlen⟩, hne⟩, hc⟩ := h
  have hd : (0 : ℤ) < (lo.den : ℤ) * hi.den :=
    mul_pos (Int.natCast_pos.mpr (of_decide_eq_true hlo))
      (Int.natCast_pos.mpr (of_decide_eq_true hhi))
  have hgap : lo.num * hi.den < hi.num * lo.den := of_decide_eq_true hlt
  dsimp only [posOnBox, PosCert.check, IntPoly.intervalData]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hlt⟩, decide_eq_true (pow_pos (mul_pos hd (sub_pos.mpr hgap)) _)⟩,
    decide_eq_true hne⟩, hc⟩, bernsteinCoeffs_reconstruction hlo hhi hlt hlen⟩


/-- Bivariate polynomial evaluation is continuous. -/
theorem continuous_eval (f : IntPoly2) :
    Continuous (fun v : ℝ × ℝ => f.eval v.1 v.2) := by
  induction f with
  | nil => exact continuous_const
  | cons p f ih =>
    exact (p.polynomial.continuous.comp continuous_fst).add (continuous_snd.mul ih)

/-- Partial derivative coefficient list, starting with exponent `n`. -/
def derivativeFrom : ℕ → IntPoly2 → IntPoly2
  | _, [] => []
  | n, p :: f => p.scale n :: derivativeFrom (n + 1) f

/-- Partial derivative with respect to `y`. -/
def derivativeY (f : IntPoly2) : IntPoly2 := derivativeFrom 1 f.tail

private theorem polynomial_derivativeFrom (f : IntPoly2) (n : ℕ) (t : ℝ) :
    (derivativeFrom n f).polynomial t =
      C (n : ℝ) * f.polynomial t + X * (f.polynomial t).derivative := by
  induction f generalizing n with
  | nil => simp [derivativeFrom, polynomial]
  | cons p f ih =>
    simp only [derivativeFrom, polynomial, IntPoly.eval_scale, Int.cast_natCast, ih,
      Nat.cast_add, Nat.cast_one, derivative_add, derivative_C, derivative_mul,
      derivative_X, zero_add, one_mul, C_mul, C_add, C_1]
    ring

/-- The executable partial derivative is the derivative of the specialized polynomial. -/
theorem polynomial_derivativeY (f : IntPoly2) (t : ℝ) :
    f.derivativeY.polynomial t = (f.polynomial t).derivative := by
  cases f with
  | nil => simp [derivativeY, derivativeFrom, polynomial]
  | cons p f =>
    simp [derivativeY, polynomial_derivativeFrom, polynomial, derivative_mul]

/-- Choose a Boolean sign for a bivariate polynomial. -/
def signed (neg : Bool) (f : IntPoly2) : IntPoly2 := smul (if neg then -1 else 1) f

/-- Evaluation commutes with signing. -/
theorem eval_signed (neg : Bool) (f : IntPoly2) (t y : ℝ) :
    (f.signed neg).eval t y = (if neg then -1 else 1 : ℝ) * f.eval t y := by
  cases neg <;> simp [signed, eval_smul]

/-- Substitute a rational `y`, clearing its denominator to the outer list length. -/
def specializeY (q : QNum) : IntPoly2 → IntPoly
  | [] => []
  | p :: f => addList (p.scale ((q.den : ℤ) ^ (f.length + 1)))
      ((specializeY q f).scale q.num)

/-- Real evaluation of rational specialization, with its positive integer scale. -/
theorem eval_specializeY (q : QNum) (f : IntPoly2) (hq : q.valid = true) (t : ℝ) :
    (specializeY q f).eval t = (q.den : ℝ) ^ f.length * f.eval t q.val := by
  have hd : (q.den : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (of_decide_eq_true hq : 0 < q.den))
  induction f with
  | nil => simp [specializeY, IntPoly.eval, IntPoly.polynomial, eval]
  | cons p f ih =>
    simp only [specializeY, IntPoly.eval_addList, IntPoly.eval_scale,
      ih, List.length_cons, eval, QNum.val, pow_succ]
    push_cast
    field_simp

/-- Integer evaluation of a bivariate polynomial at rational endpoints. -/
def evalScaled (f : IntPoly2) (t y : QNum) : ℤ :=
  (f.specializeY y).evalScaled t.num t.den

/-- Bivariate integer evaluation has an explicit positive denominator scale. -/
theorem evalScaled_eq (f : IntPoly2) (t y : QNum)
    (ht : t.valid = true) (hy : y.valid = true) :
    (f.evalScaled t y : ℝ) =
      (t.den : ℝ) ^ (f.specializeY y).length * (y.den : ℝ) ^ f.length *
        f.eval t.val y.val := by
  rw [evalScaled, IntPoly.evalScaled_eq _ _ ht, eval_specializeY _ _ hy]
  exact (mul_assoc _ _ _).symm

/-- A box derivative certificate gives strict monotonicity in the root coordinate. -/
theorem strictMonoOn_of_posOnBox_derivativeY {f : IntPoly2} {tlo thi lo hi : QNum}
    (h : f.derivativeY.posOnBox tlo thi lo hi = true) {t : ℝ}
    (ht : t ∈ Icc tlo.val thi.val) :
    StrictMonoOn (f.eval t) (Icc lo.val hi.val) := by
  have hm : StrictMonoOn (f.polynomial t).eval (Icc lo.val hi.val) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (f.polynomial t).continuous.continuousOn
    intro y hy
    rw [Polynomial.deriv, ← polynomial_derivativeY, eval_polynomial]
    exact posOnBox_sound h ht (interior_subset hy)
  simpa only [eval_polynomial] using hm

end IntPoly2

/-- A rational rectangle containing a root branch. -/
structure BranchCell where
  /-- Left parameter endpoint. -/
  tlo : QNum
  /-- Right parameter endpoint. -/
  thi : QNum
  /-- Lower vertical wall. -/
  lo : QNum
  /-- Upper vertical wall. -/
  hi : QNum
  deriving DecidableEq, Repr

/-- The closed parameter interval of a cell. -/
noncomputable def BranchCell.domain (c : BranchCell) : Set ℝ := Icc c.tlo.val c.thi.val

/-- The closed vertical strip of a cell. -/
noncomputable def BranchCell.strip (c : BranchCell) : Set ℝ := Icc c.lo.val c.hi.val

/-- Check the derivative orientation and the two strict wall signs. -/
def BranchCell.check (c : BranchCell) (f : IntPoly2) (neg : Bool) : Bool :=
  let g := f.signed neg
  c.tlo.valid && c.thi.valid && c.tlo.le c.thi &&
    c.lo.valid && c.hi.valid && c.lo.lt c.hi &&
    g.derivativeY.posOnBox c.tlo c.thi c.lo c.hi &&
    ((g.specializeY c.lo).signed true).posOn c.tlo c.thi &&
    (g.specializeY c.hi).posOn c.tlo c.thi

/-- Check cell walls numerically while using symbolic reconstruction for its derivative. -/
theorem BranchCell.check_of_bernsteinCoeffs {c : BranchCell} {f : IntPoly2} {neg : Bool}
    (h : let g := f.signed neg
      let cs := IntPoly2.bernsteinCoeffs g.derivativeY c.lo c.hi
      (c.tlo.valid && c.thi.valid && c.tlo.le c.thi &&
        (c.lo.valid && c.hi.valid && c.lo.lt c.hi &&
          decide (cs.length = g.derivativeY.length) && decide (cs ≠ []) &&
          cs.all (fun p => p.posOn c.tlo c.thi)) &&
        ((g.specializeY c.lo).signed true).posOn c.tlo c.thi &&
        (g.specializeY c.hi).posOn c.tlo c.thi) = true) :
    c.check f neg = true := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hlo, hhi⟩, hle⟩, hd⟩, hl⟩, hu⟩ := h
  have hb : (f.signed neg).derivativeY.posOnBox c.tlo c.thi c.lo c.hi = true :=
    IntPoly2.posOnBox_of_bernsteinCoeffs (by simpa only [Bool.and_eq_true] using hd)
  have he := hd
  simp only [check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hle⟩, he.1.1.1.1.1⟩, he.1.1.1.1.2⟩,
    he.1.1.1.2⟩, hb⟩, hl⟩, hu⟩

/-- A checked cell has one root at each parameter value, unique in its closed strip. -/
theorem BranchCell.check_sound {c : BranchCell} {f : IntPoly2} {neg : Bool}
    (h : c.check f neg = true) {t : ℝ} (ht : t ∈ c.domain) :
    ∃ y ∈ Ioo c.lo.val c.hi.val, f.eval t y = 0 ∧
      ∀ z ∈ c.strip, f.eval t z = 0 → z = y := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htlo, hthi⟩, htle⟩, hlo⟩, hhi⟩, hlt⟩, hd⟩, hl⟩, hu⟩ := h
  let g := f.signed neg
  have hl' := IntPoly.posOn_sound hl ht
  have hu' := IntPoly.posOn_sound hu ht
  rw [IntPoly.eval_signed, IntPoly2.eval_specializeY _ _ hlo] at hl'
  rw [IntPoly2.eval_specializeY _ _ hhi] at hu'
  have hdl : (0 : ℝ) < c.lo.den := by
    exact_mod_cast (of_decide_eq_true hlo : 0 < c.lo.den)
  have hdu : (0 : ℝ) < c.hi.den := by
    exact_mod_cast (of_decide_eq_true hhi : 0 < c.hi.den)
  have hgl : g.eval t c.lo.val < 0 := by
    change 0 < (-1 : ℝ) * ((c.lo.den : ℝ) ^ g.length * g.eval t c.lo.val) at hl'
    have hd'' := pow_pos hdl g.length
    nlinarith
  have hgu : 0 < g.eval t c.hi.val :=
    (mul_pos_iff_of_pos_left (pow_pos hdu g.length)).mp hu'
  have hab := (QNum.lt_sound hlo hhi hlt).le
  obtain ⟨y, hy, he⟩ := intermediate_value_Ioo hab
    (g.polynomial t).continuous.continuousOn
    (show (0 : ℝ) ∈ Ioo ((g.polynomial t).eval c.lo.val)
      ((g.polynomial t).eval c.hi.val) by simpa [IntPoly2.eval_polynomial] using ⟨hgl, hgu⟩)
  have he' : f.eval t y = 0 := by
    change (g.polynomial t).eval y = 0 at he
    rw [IntPoly2.eval_polynomial, IntPoly2.eval_signed] at he
    cases neg <;> simpa using he
  refine ⟨y, hy, he', ?_⟩
  intro z hz hzroot
  apply (IntPoly2.strictMonoOn_of_posOnBox_derivativeY hd ht).injOn hz ⟨hy.1.le, hy.2.le⟩
  simp [IntPoly2.eval_signed, hzroot, he']

/-- Valid rational coordinates extracted from a checked cell. -/
theorem BranchCell.valid_of_check {c : BranchCell} {f : IntPoly2} {neg : Bool}
    (h : c.check f neg = true) :
    c.tlo.valid = true ∧ c.thi.valid = true ∧ c.lo.valid = true ∧ c.hi.valid = true := by
  simp only [check, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2⟩

/-- Select the smaller rational endpoint without division. -/
def QNum.min (a b : QNum) : QNum := if a.le b then a else b

/-- Select the larger rational endpoint without division. -/
def QNum.max (a b : QNum) : QNum := if a.le b then b else a

/-- Real values of the rational minimum. -/
theorem QNum.val_min {a b : QNum} (ha : a.valid = true) (hb : b.valid = true) :
    (a.min b).val = Min.min a.val b.val := by
  by_cases h : a.le b = true
  · simp [QNum.min, h, min_eq_left (QNum.le_sound ha hb h)]
  · have hba : b.le a = true := by
      simp only [QNum.le, decide_eq_true_eq] at h ⊢
      lia
    simp [QNum.min, h, min_eq_right (QNum.le_sound hb ha hba)]

/-- Real values of the rational maximum. -/
theorem QNum.val_max {a b : QNum} (ha : a.valid = true) (hb : b.valid = true) :
    (a.max b).val = Max.max a.val b.val := by
  by_cases h : a.le b = true
  · simp [QNum.max, h, max_eq_right (QNum.le_sound ha hb h)]
  · have hba : b.le a = true := by
      simp only [QNum.le, decide_eq_true_eq] at h ⊢
      lia
    simp [QNum.max, h, max_eq_left (QNum.le_sound hb ha hba)]

/-- Check uniqueness on an overlap, including a one-point junction. -/
def BranchCell.compatible (c d : BranchCell) (f : IntPoly2) (neg : Bool) : Bool :=
  if c.thi.lt d.tlo || d.thi.lt c.tlo then true
  else (f.signed neg).derivativeY.posOnBox (c.tlo.max d.tlo) (c.thi.min d.thi)
    (c.lo.min d.lo) (c.hi.max d.hi)

/-- A checked cell already contains its self-overlap derivative certificate. -/
theorem BranchCell.compatible_self_of_check {c : BranchCell} {f : IntPoly2} {neg : Bool}
    (h : c.check f neg = true) : c.compatible c f neg = true := by
  simp only [BranchCell.check, Bool.and_eq_true] at h
  unfold BranchCell.compatible
  split
  · rfl
  · simpa only [QNum.max, QNum.min, ite_self] using h.1.1.2

/-- Swapping cells preserves compatibility when the four selected endpoints agree. -/
theorem BranchCell.compatible_of_endpoints_eq {c d : BranchCell} {f : IntPoly2} {neg : Bool}
    (he : (c.tlo.max d.tlo, c.thi.min d.thi, c.lo.min d.lo, c.hi.max d.hi) =
      (d.tlo.max c.tlo, d.thi.min c.thi, d.lo.min c.lo, d.hi.max c.hi))
    (h : d.compatible c f neg = true) : c.compatible d f neg = true := by
  simp only [Prod.mk.injEq] at he
  obtain ⟨h₁, h₂, h₃, h₄⟩ := he
  simpa only [BranchCell.compatible, h₁, h₂, h₃, h₄, Bool.or_comm] using h

/-- Reuse the self-overlap and one neighbor before checking the remaining row. -/
theorem BranchCell.compatible_all_of_check {cs : List BranchCell} {c d : BranchCell}
    {f : IntPoly2} {neg : Bool}
    (hc : c.check f neg = true) (hd : c.compatible d f neg = true)
    (h : cs.all (fun e ↦ if e = c ∨ e = d then true else c.compatible e f neg) = true) :
    cs.all (fun e ↦ c.compatible e f neg) = true := by
  apply List.all_eq_true.mpr
  intro e he
  by_cases hec : e = c
  · simpa only [hec] using compatible_self_of_check hc
  · by_cases hed : e = d
    · simpa only [hed] using hd
    · simpa only [ite_eq_right (not_or_intro hec hed)] using (List.all_eq_true.mp h e he)

/-- Overlap checks identify the two locally certified roots. -/
theorem BranchCell.compatible_sound {c d : BranchCell} {f : IntPoly2} {neg : Bool}
    (hc : c.check f neg = true) (hd : d.check f neg = true)
    (h : c.compatible d f neg = true) {t y z : ℝ}
    (hct : t ∈ c.domain) (hdt : t ∈ d.domain)
    (hy : y ∈ c.strip) (hz : z ∈ d.strip)
    (hey : f.eval t y = 0) (hez : f.eval t z = 0) : y = z := by
  obtain ⟨hcl, hcu, hcyl, hcyu⟩ := BranchCell.valid_of_check hc
  obtain ⟨hdl, hdu, hdyl, hdyu⟩ := BranchCell.valid_of_check hd
  unfold compatible at h
  split at h
  · rename_i hdisj
    rcases Bool.or_eq_true_iff.mp hdisj with hlt | hlt
    · have := QNum.lt_sound hcu hdl hlt
      exact (not_lt_of_ge (hdt.1.trans hct.2) this).elim
    · have := QNum.lt_sound hdu hcl hlt
      exact (not_lt_of_ge (hct.1.trans hdt.2) this).elim
  · have ht : t ∈ Icc (c.tlo.max d.tlo).val (c.thi.min d.thi).val := by
      rw [QNum.val_max hcl hdl, QNum.val_min hcu hdu]
      exact ⟨max_le hct.1 hdt.1, le_min hct.2 hdt.2⟩
    have hys : y ∈ Icc (c.lo.min d.lo).val (c.hi.max d.hi).val := by
      rw [QNum.val_min hcyl hdyl, QNum.val_max hcyu hdyu]
      exact ⟨(min_le_left _ _).trans hy.1, hy.2.trans (le_max_left _ _)⟩
    have hzs : z ∈ Icc (c.lo.min d.lo).val (c.hi.max d.hi).val := by
      rw [QNum.val_min hcyl hdyl, QNum.val_max hcyu hdyu]
      exact ⟨(min_le_right _ _).trans hz.1, hz.2.trans (le_max_right _ _)⟩
    apply (IntPoly2.strictMonoOn_of_posOnBox_derivativeY h ht).injOn hys hzs
    simp [IntPoly2.eval_signed, hey, hez]

/-- A finite, connected collection of rational root strips. -/
structure Branch where
  /-- The algebraic curve, in ascending `y` and then `t` order. -/
  curve : IntPoly2
  /-- Ordered parameter cells. -/
  cells : List BranchCell
  /-- Left endpoint of the full domain. -/
  lo : QNum
  /-- Right endpoint of the full domain. -/
  hi : QNum
  /-- Orientation of the partial derivative. -/
  neg : Bool := false
  deriving Repr

/-- Check exact adjacency of cells, with prescribed outer endpoints. -/
def Branch.covers (a b : QNum) : List BranchCell → Bool
  | [] => false
  | c :: cs => (a == c.tlo) && if cs.isEmpty then c.thi == b else covers c.thi b cs

/-- Adjacency certifies coverage by the closed parameter cells. -/
theorem Branch.covers_sound {cs : List BranchCell} {a b : QNum}
    (h : covers a b cs = true) {t : ℝ} (ht : t ∈ Icc a.val b.val) :
    ∃ c ∈ cs, t ∈ c.domain := by
  induction cs generalizing a with
  | nil => simp [covers] at h
  | cons c cs ih =>
    simp only [covers, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    cases cs with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, beq_iff_eq] at h
      exact ⟨c, by simp, by simpa [BranchCell.domain, h] using ht⟩
    | cons d cs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hle : t ≤ c.thi.val
      · exact ⟨c, by simp, ht.1, hle⟩
      · obtain ⟨e, he, hte⟩ := ih h ⟨(not_le.mp hle).le, ht.2⟩
        exact ⟨e, by simp [he], hte⟩

/-- Check the root cells, their domain coverage and every nonempty overlap.
For an ordered partition, overlap checks are exactly junction checks. -/
def Branch.check (b : Branch) : Bool :=
  b.lo.valid && b.hi.valid && b.lo.le b.hi && covers b.lo b.hi b.cells &&
    b.cells.all (fun c => c.check b.curve b.neg && b.lo.le c.tlo && c.thi.le b.hi) &&
    b.cells.all (fun c => b.cells.all (fun d => c.compatible d b.curve b.neg))

/-- The closed zero graph in a single cell. -/
noncomputable def BranchCell.graph (c : BranchCell) (f : IntPoly2) : Set (ℝ × ℝ) :=
  (c.domain ×ˢ c.strip) ∩ {v | f.eval v.1 v.2 = 0}

/-- Each cell contributes a compact zero graph. -/
theorem BranchCell.isCompact_graph (c : BranchCell) (f : IntPoly2) : IsCompact (c.graph f) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq f.continuous_eval continuous_const)

/-- Union of the finitely many cell zero graphs. -/
noncomputable def Branch.graph (b : Branch) : Set (ℝ × ℝ) :=
  ⋃ c ∈ b.cells, c.graph b.curve

/-- The full graph is compact, with no regularity assumption on its selected branch. -/
theorem Branch.isCompact_graph (b : Branch) : IsCompact b.graph :=
  b.cells.finite_toSet.isCompact_biUnion (fun c _ => c.isCompact_graph b.curve)

private theorem Branch.cell_check {b : Branch} (h : b.check = true)
    {c : BranchCell} (hc : c ∈ b.cells) : c.check b.curve b.neg = true := by
  simp only [Branch.check, Bool.and_eq_true] at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp h.1.2 c hc)).1).1

private theorem Branch.graph_domain {b : Branch} (h : b.check = true)
    {t y : ℝ} (hv : (t, y) ∈ b.graph) : t ∈ Icc b.lo.val b.hi.val := by
  obtain ⟨c, hc, ⟨ht, hy⟩, he⟩ := mem_iUnion₂.mp hv
  have hc' := BranchCell.valid_of_check (Branch.cell_check h hc)
  simp only [Branch.check, Bool.and_eq_true] at h
  have hh := List.all_eq_true.mp h.1.2 c hc
  simp only [Bool.and_eq_true] at hh
  exact ⟨(QNum.le_sound h.1.1.1.1.1 hc'.1 hh.1.2).trans ht.1,
    ht.2.trans (QNum.le_sound hc'.2.1 h.1.1.1.1.2 hh.2)⟩

private theorem Branch.exists_graph {b : Branch} (h : b.check = true)
    {t : ℝ} (ht : t ∈ Icc b.lo.val b.hi.val) : ∃ y, (t, y) ∈ b.graph := by
  have hcov : Branch.covers b.lo b.hi b.cells = true := by
    simp only [Branch.check, Bool.and_eq_true] at h
    exact h.1.1.2
  obtain ⟨c, hc, hct⟩ := Branch.covers_sound hcov ht
  obtain ⟨y, hy, he, hu⟩ := BranchCell.check_sound (Branch.cell_check h hc) hct
  exact ⟨y, mem_iUnion₂.mpr ⟨c, hc, ⟨hct, hy.1.le, hy.2.le⟩, he⟩⟩

private theorem Branch.graph_unique {b : Branch} (h : b.check = true)
    {t y z : ℝ} (hy : (t, y) ∈ b.graph) (hz : (t, z) ∈ b.graph) : y = z := by
  obtain ⟨c, hc, ⟨hct, hcy⟩, hey⟩ := mem_iUnion₂.mp hy
  obtain ⟨d, hd, ⟨hdt, hdz⟩, hez⟩ := mem_iUnion₂.mp hz
  have hcompat : c.compatible d b.curve b.neg = true := by
    simp only [Branch.check, Bool.and_eq_true] at h
    exact List.all_eq_true.mp (List.all_eq_true.mp h.2 c hc) d hd
  exact BranchCell.compatible_sound (Branch.cell_check h hc) (Branch.cell_check h hd)
    hcompat hct hdt hcy hdz hey hez

/-- The selected real root, extended by zero when there is no root in the certified graph. -/
noncomputable def Branch.y (b : Branch) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ y, (t, y) ∈ b.graph then h.choose else 0

private theorem Branch.y_mem {b : Branch} (h : b.check = true)
    {t : ℝ} (ht : t ∈ Icc b.lo.val b.hi.val) : (t, b.y t) ∈ b.graph := by
  classical
  have he := Branch.exists_graph h ht
  simp only [Branch.y, dite_eq_left he]
  exact he.choose_spec

private theorem continuousOn_of_compact_graph {s : Set ℝ} {y : ℝ → ℝ}
    (hg : IsCompact ((fun t => (t, y t)) '' s)) : ContinuousOn y s := by
  let g := (fun t => (t, y t)) '' s
  let : CompactSpace g := isCompact_iff_compactSpace.mp hg
  let proj : g → s := fun v => ⟨v.val.1, by
    obtain ⟨t, ht, he⟩ := v.property
    exact he ▸ ht⟩
  have hcont : Continuous proj :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hbij : Function.Bijective proj := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      obtain ⟨t, ht, he⟩ := v.property
      obtain ⟨u, hu, he'⟩ := w.property
      have htu : t = u := by
        have hv := congrArg Subtype.val hvw
        change v.val.1 = w.val.1 at hv
        rw [← he, ← he'] at hv
        exact hv
      rw [← he, ← he', htu]
    · intro t
      exact ⟨⟨(t, y t), mem_image_of_mem _ t.property⟩, rfl⟩
  let e := Equiv.ofBijective proj hbij
  have hc : Continuous e.symm := hcont.continuous_symm_of_equiv_compact_to_t2
  have hsnd : Continuous (fun t : s => ((e.symm t).val).2) :=
    continuous_snd.comp (continuous_subtype_val.comp hc)
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hsnd using 1
  funext t
  obtain ⟨u, hu, he⟩ := (e.symm t).property
  have hfst := congrArg Subtype.val (e.apply_symm_apply t)
  change (e.symm t).val.1 = t.val at hfst
  rw [← he] at hfst
  change u = t.val at hfst
  change y t.val = (e.symm t).val.2
  rw [← he]
  exact congrArg y hfst.symm

/-- A checked branch is continuous, lies on the curve, and stays inside every covering strip. -/
theorem Branch.check_sound {b : Branch} (h : b.check = true) :
    ContinuousOn b.y (Icc b.lo.val b.hi.val) ∧
      (∀ t ∈ Icc b.lo.val b.hi.val, b.curve.eval t (b.y t) = 0) ∧
      ∀ c ∈ b.cells, ∀ t ∈ c.domain, b.y t ∈ c.strip := by
  have hgraph : (fun t => (t, b.y t)) '' Icc b.lo.val b.hi.val = b.graph := by
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Branch.y_mem h ht
    · intro hv
      have ht := Branch.graph_domain h hv
      refine ⟨v.1, ht, ?_⟩
      exact Prod.ext rfl (Branch.graph_unique h (Branch.y_mem h ht) hv)
  have hcont : ContinuousOn b.y (Icc b.lo.val b.hi.val) :=
    continuousOn_of_compact_graph (hgraph ▸ b.isCompact_graph)
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, ⟨hct, hcy⟩, he⟩ := mem_iUnion₂.mp (Branch.y_mem h ht)
    exact he
  · intro c hc t ht
    obtain ⟨z, hz, he, hu⟩ := BranchCell.check_sound (Branch.cell_check h hc) ht
    have hzgraph : (t, z) ∈ b.graph :=
      mem_iUnion₂.mpr ⟨c, hc, ⟨ht, hz.1.le, hz.2.le⟩, he⟩
    have htd := Branch.graph_domain h hzgraph
    have hyz := Branch.graph_unique h (Branch.y_mem h htd) hzgraph
    exact hyz ▸ ⟨hz.1.le, hz.2.le⟩

end RealRooted.EffectiveBKW
