module

import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Convex.Function

/-!
# The reciprocal quartic of the 132 big-descent problem

For `s > 1` the quartic `W_s(X) = X⁴ - 4X³ + 6sX² - 4s²X + s²` has two real zeros
`0 < a < 1 < b < s` and a complex pair `U ± iV` (`V > 0`) of modulus `R` with `b < R` and
`s < R²`.  Both real zeros are simple and `W_s` is separable.  This is the algebraic leaf
#1698 of the big-descent problem #1623; the proofs are elementary (convexity, the intermediate
value theorem and Vieta's relations).

## Main results

* `RealRooted.BigDescents132.Quartic.exists_root_factorization`: the factorization
  `W_s = (X - a)(X - b)((X - U)² + V²)` with the root bounds and the modulus dominance.
* `RealRooted.BigDescents132.Quartic.eval_eq_zero_iff`, `derivative_signs`, `vieta`,
  `separable_polynomial`, and `quarter_lt_of_eval_eq_zero` (the small zero exceeds `1/4`).
* Over `ℂ`: `map_eq_prod` (the factorization `(X - a)(X - b)(X - λ)(X - conj λ)`),
  `eq_of_isRoot_of_im_pos` (`λ = U + Vi` is the unique zero in the upper half-plane) and
  `separable_map`.

The proofs were found by Aristotle (Harmonic) from a statement and proof sketch, and ported.
-/

@[expose] public section

open Polynomial

namespace RealRooted.BigDescents132.Quartic

/-- The reciprocal quartic `W_s(X) = X^4 - 4X^3 + 6sX^2 - 4s^2X + s^2`. -/
noncomputable def polynomial (s : ℝ) : ℝ[X] :=
  X ^ 4 - 4 * X ^ 3 + C (6 * s) * X ^ 2 - C (4 * s ^ 2) * X + C (s ^ 2)

theorem eval_polynomial (s x : ℝ) :
    (polynomial s).eval x = x ^ 4 - 4 * x ^ 3 + 6 * s * x ^ 2 - 4 * s ^ 2 * x + s ^ 2 := by
  simp [polynomial]

/-- `x ↦ W_s(x)` is strictly convex for `s > 1` (`W_s'' = 12((x-1)^2 + s - 1)`). -/
theorem strictConvexOn_eval {s : ℝ} (hs : 1 < s) :
    StrictConvexOn ℝ Set.univ fun x => (polynomial s).eval x := by
  apply strictConvexOn_univ_of_deriv2_pos (polynomial s).continuous
  intro x
  have h1 : deriv (fun x => (polynomial s).eval x) =
      fun x => (derivative (polynomial s)).eval x := funext fun y => Polynomial.deriv _
  have h2 : deriv^[2] (fun x => (polynomial s).eval x) x =
      (derivative (derivative (polynomial s))).eval x := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, h1]
    exact Polynomial.deriv _
  rw [h2]
  simp [polynomial, derivative_pow]
  nlinarith [sq_nonneg (x - 1)]

/-- A strictly convex function which is `≤ 0` at two points is `< 0` strictly between them. -/
private lemma neg_between {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) {x y z : ℝ}
    (hxy : x < y) (hyz : y < z) (hx : f x ≤ 0) (hz : f z ≤ 0) : f y < 0 := by
  have hxz : x < z := hxy.trans hyz
  set t := (z - y) / (z - x) with ht
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have ht1 : 0 < 1 - t := by
    rw [ht, one_sub_div (by linarith)]; exact div_pos (by linarith) (by linarith)
  have hy : t • x + (1 - t) • z = y := by
    have hne : z - x ≠ 0 := by linarith
    simp only [smul_eq_mul, ht]; field_simp; ring
  have := hf.2 (Set.mem_univ x) (Set.mem_univ z) hxz.ne ht0 ht1 (by ring)
  rw [hy] at this
  simp only [smul_eq_mul] at this
  nlinarith

/-- The bound `a b³ < s²` behind `b < |λ|`, via `h = √b` and `k = (h + 2) / (2h + 1)`. -/
private lemma sq_bound {s a b : ℝ} (hs : 1 < s) (hab : a < b) (hb1 : 1 < b) (hbs : b < s)
    (hfa : (polynomial s).eval a = 0) (hfb : (polynomial s).eval b = 0) : a * b ^ 3 < s ^ 2 := by
  have hconv := strictConvexOn_eval hs
  set h := Real.sqrt b with hh
  have hh2 : h ^ 2 = b := Real.sq_sqrt (by linarith)
  have hh1 : 1 < h := by nlinarith [Real.sqrt_nonneg b]
  have hid : ∀ t : ℝ, (polynomial s).eval (t ^ 2) =
      -(((2 * t - 1) * s - t ^ 3 * (2 - t)) * ((2 * t + 1) * s - t ^ 3 * (t + 2))) := by
    intro t; rw [eval_polynomial]; ring
  have hF1 : 0 < (2 * h - 1) * s - h ^ 3 * (2 - h) := by
    have : (2 * h - 1) * h ^ 2 < (2 * h - 1) * s := by
      apply mul_lt_mul_of_pos_left (by linarith) (by linarith)
    nlinarith
  have hseq : (2 * h + 1) * s = h ^ 3 * (h + 2) := by
    have := hid h
    rw [hh2, hfb] at this
    have h0 : ((2 * h - 1) * s - h ^ 3 * (2 - h)) * ((2 * h + 1) * s - h ^ 3 * (h + 2)) = 0 := by
      linarith
    rcases mul_eq_zero.1 h0 with h0 | h0
    · linarith
    · linarith
  set k := (h + 2) / (2 * h + 1) with hk
  have hkh : k * (2 * h + 1) = h + 2 := by rw [hk]; field_simp
  have hk1 : k < 1 := by rw [hk, div_lt_one (by linarith)]; linarith
  have hk0 : 1 / 2 < k := by rw [hk, lt_div_iff₀ (by linarith)]; linarith
  have hsk : s = h ^ 3 * k := by
    have : (2 * h + 1) * s = (2 * h + 1) * (h ^ 3 * k) := by rw [hseq]; rw [← hkh]; ring
    exact mul_left_cancel₀ (by linarith) this
  have hhk : h * (2 * k - 1) = 2 - k := by linarith
  have hG1 : 0 < (2 * k - 1) * s - k ^ 3 * (2 - k) := by
    have : (2 * k - 1) * s - k ^ 3 * (2 - k) = k * (2 - k) * (h ^ 2 - k ^ 2) := by
      rw [hsk]; linear_combination (k * h ^ 2) * hhk
    rw [this]
    apply mul_pos (mul_pos (by linarith) (by linarith))
    nlinarith [mul_pos (show (0:ℝ) < h - k by linarith) (show (0:ℝ) < h + k by linarith)]
  have hG2 : 0 < (2 * k + 1) * s - k ^ 3 * (k + 2) := by
    have hh3 : 1 < h ^ 3 := by nlinarith
    rw [hsk]
    have : 0 < k := by linarith
    have : k ^ 2 * (k + 2) < 2 * k + 1 := by nlinarith
    have : (2 * k + 1) < (2 * k + 1) * h ^ 3 := by nlinarith
    nlinarith
  have hWk : (polynomial s).eval (k ^ 2) < 0 := by
    rw [hid k]; nlinarith [mul_pos hG1 hG2]
  have hak : a < k ^ 2 := by
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hlt | heq
    · have := neg_between hconv hlt hab hWk.le hfb.le
      linarith
    · rw [heq] at hWk; linarith
  have hs2 : s ^ 2 = b ^ 3 * k ^ 2 := by
    rw [hsk, ← hh2]; ring
  rw [hs2]
  have : 0 < b ^ 3 := by positivity
  nlinarith

/-- The quartic has roots in `(0, 1)` and `(1, s)`. -/
private lemma exists_bounded_roots {s : ℝ} (hs : 1 < s) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ b < s ∧
      (polynomial s).eval a = 0 ∧ (polynomial s).eval b = 0 := by
  have hcont : Continuous fun x => (polynomial s).eval x := (polynomial s).continuous
  have hf0 : 0 < (polynomial s).eval 0 := by rw [eval_polynomial]; nlinarith
  have hf1 : (polynomial s).eval 1 < 0 := by rw [eval_polynomial]; nlinarith
  have hfs : 0 < (polynomial s).eval s := by
    rw [eval_polynomial]
    have : 0 < s * (s - 1) := by nlinarith
    nlinarith
  obtain ⟨a, ⟨ha0, ha1⟩, hfa⟩ :=
    intermediate_value_Ioo' zero_le_one hcont.continuousOn ⟨hf1, hf0⟩
  obtain ⟨b, ⟨hb1, hbs⟩, hfb⟩ :=
    intermediate_value_Ioo hs.le hcont.continuousOn ⟨hf1, hfs⟩
  simp only at hfa hfb
  exact ⟨a, b, ha0, ha1, hb1, hbs, hfa, hfb⟩

/-- Strict convexity makes the two bounded roots the only real roots. -/
private lemma eq_left_or_right_of_eval_eq_zero {s a b c : ℝ} (hs : 1 < s) (hab : a < b)
    (hfa : (polynomial s).eval a = 0) (hfb : (polynomial s).eval b = 0)
    (hc : (polynomial s).eval c = 0) : c = a ∨ c = b := by
  have hconv := strictConvexOn_eval hs
  by_contra hne
  push Not at hne
  rcases lt_or_gt_of_ne hne.1 with h1 | h1
  · have := neg_between hconv h1 hab hc.le hfb.le
    linarith
  rcases lt_or_gt_of_ne hne.2 with h2 | h2
  · have := neg_between hconv h1 h2 hfa.le hfb.le
    linarith
  · have := neg_between hconv hab h2 hfa.le hc.le
    linarith

/-- Two distinct real roots leave a quadratic cofactor with negative discriminant. -/
private lemma exists_quadratic_factor_of_roots {s a b : ℝ} (hs : 1 < s) (hab : a < b)
    (hfa : (polynomial s).eval a = 0) (hfb : (polynomial s).eval b = 0)
    (hzero : ∀ c, (polynomial s).eval c = 0 → c = a ∨ c = b) :
    ∃ p q : ℝ,
      (∀ x, (polynomial s).eval x = (x - a) * (x - b) * (x ^ 2 + p * x + q)) ∧
      s ^ 2 = a * b * q ∧ 0 < 4 * q - p ^ 2 := by
  set p := a + b - 4 with hp
  set q := 6 * s + (a + b) * (a + b - 4) - a * b with hq
  set r1 := -4 * s ^ 2 + (a + b) * q - a * b * p with hr1
  set r0 := s ^ 2 - a * b * q with hr0
  have hR : ∀ x, (polynomial s).eval x =
      (x ^ 2 - (a + b) * x + a * b) * (x ^ 2 + p * x + q) + r1 * x + r0 := by
    intro x
    rw [eval_polynomial, hp, hq, hr1, hr0]
    ring
  have hRa : r1 * a + r0 = 0 := by
    have := hR a
    rw [hfa] at this
    linear_combination -this
  have hRb : r1 * b + r0 = 0 := by
    have := hR b
    rw [hfb] at this
    linear_combination -this
  have hr1z : r1 = 0 := by
    have : r1 * (b - a) = 0 := by linear_combination hRb - hRa
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (by linarith)
  have hr0z : r0 = 0 := by rw [hr1z] at hRa; linarith
  have hW : ∀ x, (polynomial s).eval x =
      (x - a) * (x - b) * (x ^ 2 + p * x + q) := by
    intro x
    rw [hR, hr1z, hr0z]
    ring
  have hsq : s ^ 2 = a * b * q := by linarith
  refine ⟨p, q, hW, hsq, ?_⟩
  by_contra hneg
  push Not at hneg
  set r := Real.sqrt (p ^ 2 - 4 * q) with hr
  have hr2 : r ^ 2 = p ^ 2 - 4 * q := Real.sq_sqrt (by linarith)
  have hq1 : ((-p + r) / 2) ^ 2 + p * ((-p + r) / 2) + q = 0 := by
    linear_combination hr2 / 4
  have hq2 : ((-p - r) / 2) ^ 2 + p * ((-p - r) / 2) + q = 0 := by
    linear_combination hr2 / 4
  have hc1 := hzero ((-p + r) / 2) (by rw [hW, hq1, mul_zero])
  have hc2 := hzero ((-p - r) / 2) (by rw [hW, hq2, mul_zero])
  have hsum : (-p + r) / 2 + (-p - r) / 2 = -p := by ring
  have hprod : (-p + r) / 2 * ((-p - r) / 2) = q := by
    linear_combination -hr2 / 4
  have hW1 := hW 1
  have hf1 : (polynomial s).eval 1 < 0 := by rw [eval_polynomial]; nlinarith
  rcases hc1 with h1 | h1 <;> rcases hc2 with h2 | h2 <;> rw [h1, h2] at hsum hprod
  · have hb' : b = 4 - 3 * a := by linarith
    have e := hprod.trans hq
    rw [hb'] at e
    have : s = 2 * a - a ^ 2 := by linear_combination -e / 6
    linarith [sq_nonneg (a - 1)]
  · have : (polynomial s).eval 1 = ((1 - a) * (1 - b)) ^ 2 := by
      linear_combination hW1 + (1 - a) * (1 - b) * hsum - (1 - a) * (1 - b) * hprod
    linarith [sq_nonneg ((1 - a) * (1 - b))]
  · have : (polynomial s).eval 1 = ((1 - a) * (1 - b)) ^ 2 := by
      linear_combination hW1 + (1 - a) * (1 - b) * hsum - (1 - a) * (1 - b) * hprod
    linarith [sq_nonneg ((1 - a) * (1 - b))]
  · have ha' : a = 4 - 3 * b := by linarith
    have e := hprod.trans hq
    rw [ha'] at e
    have : s = 2 * b - b ^ 2 := by linear_combination -e / 6
    linarith [sq_nonneg (b - 1)]

/-- For `s > 1`, `W_s` has exactly two real zeros `a ∈ (0,1)` and `b ∈ (1,s)`, a complex pair
`U ± iV` with `V > 0`, and the modulus of that pair dominates strictly: `b^2 < U^2+V^2` and
`s < U^2+V^2`.
Hint: two real roots by IVT (`W(0)=s^2>0`, `W(1)=-3(s-1)^2<0`, `W(s)=s^2(s-1)^2>0`), divide off
the two linear factors, the monic quadratic quotient has no real root since `W'(a)<0<W'(b)`
by strict convexity. For `R > b` use the ring identity
`W_s(h^2) = -((2h-1)s - h^3(2-h)) * ((2h+1)s - h^3(h+2))` with `h = √b`: the first factor is
positive since `s > b`, so `s = h^3(h+2)/(2h+1)`; put `k = (h+2)/(2h+1)`, so `1/2 < k < 1 < h`,
`s = h^3 k`, and both factors of the identity at `k` are positive, giving `W_s(k^2) < 0`… then
compare with Vieta `ab R^2 = s^2`. -/
theorem exists_root_factorization {s : ℝ} (hs : 1 < s) :
    ∃ a b U V : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ b < s ∧ 0 < V ∧
      polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2)) ∧
      b ^ 2 < U ^ 2 + V ^ 2 ∧ s < U ^ 2 + V ^ 2 := by
  obtain ⟨a, b, ha0, ha1, hb1, hbs, hfa, hfb⟩ := exists_bounded_roots hs
  have hab : a < b := by linarith
  have hzero : ∀ c, (polynomial s).eval c = 0 → c = a ∨ c = b :=
    fun c hc => eq_left_or_right_of_eval_eq_zero hs hab hfa hfb hc
  obtain ⟨p, q, hW, hsq, hdisc⟩ :=
    exists_quadratic_factor_of_roots hs hab hfa hfb hzero
  set U := -p / 2 with hU
  set V := Real.sqrt (q - p ^ 2 / 4) with hVdef
  have hV2 : V ^ 2 = q - p ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have hVpos : 0 < V := Real.sqrt_pos.2 (by linarith)
  have hmod : U ^ 2 + V ^ 2 = q := by rw [hV2, hU]; ring
  refine ⟨a, b, U, V, ha0, ha1, hb1, hbs, hVpos, ?_, ?_, ?_⟩
  · apply Polynomial.funext
    intro x
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
    rw [hW, hV2, hU]; ring
  · rw [hmod]
    have := sq_bound hs hab hb1 hbs hfa hfb
    have hab0 : 0 < a * b := by positivity
    have e : (a * b) * b ^ 2 < (a * b) * q := by
      calc (a * b) * b ^ 2 = a * b ^ 3 := by ring
        _ < s ^ 2 := this
        _ = (a * b) * q := hsq
    exact lt_of_mul_lt_mul_left e hab0.le
  · rw [hmod]
    have hab0 : 0 < a * b := by positivity
    have habs : a * b < s := by
      calc a * b < 1 * b := mul_lt_mul_of_pos_right ha1 (by linarith)
        _ = b := one_mul b
        _ < s := hbs
    have hq0 : 0 < q := by
      have : 0 < (a * b) * q := by rw [← hsq]; positivity
      exact pos_of_mul_pos_right this hab0.le
    have e : s * s < s * q := by
      calc s * s = (a * b) * q := by rw [← hsq]; ring
        _ < s * q := mul_lt_mul_of_pos_right habs hq0
    exact lt_of_mul_lt_mul_left e (by linarith)

/-- The real zeros are exactly `a` and `b` of the factorization. -/
theorem eval_eq_zero_iff {s a b U V : ℝ} (hV : 0 < V)
    (h : polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2))) (x : ℝ) :
    (polynomial s).eval x = 0 ↔ x = a ∨ x = b := by
  rw [h]
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
  have : 0 < (x - U) ^ 2 + V ^ 2 := by positivity
  rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro ((h1 | h1) | h1)
    · exact Or.inl h1
    · exact Or.inr h1
    · linarith
  · rintro (h1 | h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)

/-- Simplicity of the real roots: `W_s'(a) < 0 < W_s'(b)`. -/
theorem derivative_signs {s a b U V : ℝ} (hab : a < b) (hV : 0 < V)
    (h : polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2))) :
    (derivative (polynomial s)).eval a < 0 ∧ 0 < (derivative (polynomial s)).eval b := by
  rw [h]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, derivative_add,
    derivative_pow, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow, eval_one,
    sub_zero, add_zero, sub_self, mul_zero, zero_mul, zero_add]
  have : 0 < (a - U) ^ 2 + V ^ 2 := by positivity
  have : 0 < (b - U) ^ 2 + V ^ 2 := by positivity
  constructor <;> nlinarith

/-- Vieta's identities for the factorization, with `R² = U² + V²`. -/
theorem vieta {s a b U V : ℝ}
    (h : polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2))) :
    a + b + 2 * U = 4 ∧ a * b + 2 * U * (a + b) + (U ^ 2 + V ^ 2) = 6 * s ∧
      a * b * (U ^ 2 + V ^ 2) = s ^ 2 ∧
      (a + b) * (U ^ 2 + V ^ 2) + 2 * U * (a * b) = 4 * s ^ 2 := by
  have e (x : ℝ) := congrArg (eval x) h
  simp only [eval_polynomial, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow] at e
  have := e 0; have := e 1; have := e (-1); have := e 2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- `W_s` is separable for `s > 1`. -/
theorem separable_polynomial {s : ℝ} (hs : 1 < s) : (polynomial s).Separable := by
  obtain ⟨a, b, U, V, -, ha1, hb1, -, hV, h, -, -⟩ := exists_root_factorization hs
  have hcop : ∀ (r : ℝ) (g : ℝ[X]), g.eval r ≠ 0 → IsCoprime (X - C r) g := by
    intro r g hg
    rw [(irreducible_X_sub_C r).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact hg
  have hQ : ∀ r, ((X - C U) ^ 2 + C (V ^ 2)).eval r ≠ 0 := by
    intro r
    simp only [eval_add, eval_pow, eval_sub, eval_X, eval_C]
    positivity
  rw [h]
  refine Separable.mul (Separable.mul (separable_X_sub_C) (separable_X_sub_C) ?_) ?_
    (IsCoprime.mul_left (hcop a _ (hQ a)) (hcop b _ (hQ b)))
  · exact hcop a _ (by simp only [eval_sub, eval_X, eval_C]; linarith)
  · refine ⟨C (1 / V ^ 2), -C (1 / (2 * V ^ 2)) * (X - C U), ?_⟩
    apply Polynomial.funext
    intro x
    simp [derivative_pow]
    field_simp
    ring

/-! ### The complex zeros -/

/-- Any zero of `W_s` in `(0, 1)` is larger than `1/4` (for `s > 1`): `W_s` is positive on
`[0, 1/4]`. -/
theorem quarter_lt_of_eval_eq_zero {s a : ℝ} (hs : 1 < s) (ha0 : 0 < a) (ha1 : a < 1)
    (h : (polynomial s).eval a = 0) : 1 / 4 < a := by
  rw [eval_polynomial] at h
  by_contra hc
  push Not at hc
  have h1 : 0 ≤ 1 - 4 * a := by linarith
  have h2 : (1 - 4 * a) ≤ s ^ 2 * (1 - 4 * a) := by
    have : 1 ≤ s ^ 2 := by nlinarith
    nlinarith
  have h3 : 6 * a ^ 2 ≤ 6 * a ^ 2 * s := by nlinarith [sq_nonneg a]
  have h4 : 0 < (1 - a) ^ 4 := pow_pos (by linarith) 4
  nlinarith

/-- Linear factors at distinct points are coprime. -/
private lemma isCoprime_X_sub_C_X_sub_C {x y : ℂ} (h : x ≠ y) : IsCoprime (X - C x) (X - C y) :=
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit

/-- Over `ℂ`, the factorization `(X - a)(X - b)((X - U)^2 + V^2)` splits as
`(X - a)(X - b)(X - λ)(X - conj λ)` with `λ = U + V i`. -/
theorem map_eq_prod {s a b U V : ℝ}
    (h : polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2))) :
    (polynomial s).map (algebraMap ℝ ℂ) =
      (X - C (a : ℂ)) * (X - C (b : ℂ)) * (X - C (⟨U, V⟩ : ℂ)) *
        (X - C (⟨U, -V⟩ : ℂ)) := by
  rw [h]
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    map_X, map_C]
  have e1 : (⟨U, V⟩ : ℂ) = (U : ℂ) + (V : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have e2 : (⟨U, -V⟩ : ℂ) = (U : ℂ) - (V : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [e1, e2]
  simp only [Complex.coe_algebraMap, map_add, map_sub, map_mul, map_pow]
  have hI : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq]; simp
  linear_combination (X - C (a : ℂ)) * (X - C (b : ℂ)) * (C (V : ℂ)) ^ 2 * hI

/-- With `V > 0`, `λ = U + V i` is the unique zero of `W_s` in the open upper half-plane. -/
theorem eq_of_isRoot_of_im_pos {s a b U V : ℝ} (hV : 0 < V)
    (h : polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2)))
    {z : ℂ} (hz : ((polynomial s).map (algebraMap ℝ ℂ)).IsRoot z) (him : 0 < z.im) :
    z = ⟨U, V⟩ := by
  rw [map_eq_prod h] at hz
  simp only [IsRoot, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hz
  rcases hz with ((h1 | h1) | h1) | h1
  · rw [h1] at him; simp at him
  · rw [h1] at him; simp at him
  · exact h1
  · rw [h1] at him; simp at him; linarith

/-- The complexified quartic is separable when `a ≠ b` and `V ≠ 0`. -/
theorem separable_map {s a b U V : ℝ} (hab : a ≠ b) (hV : V ≠ 0)
    (h : polynomial s = (X - C a) * (X - C b) * ((X - C U) ^ 2 + C (V ^ 2))) :
    ((polynomial s).map (algebraMap ℝ ℂ)).Separable := by
  rw [map_eq_prod h]
  have hab' : (a : ℂ) ≠ (b : ℂ) := by exact_mod_cast hab
  have ha1 : (a : ℂ) ≠ ⟨U, V⟩ := fun e => hV (by simpa using (congrArg Complex.im e).symm)
  have ha2 : (a : ℂ) ≠ ⟨U, -V⟩ := fun e => hV (by simpa using (congrArg Complex.im e).symm)
  have hb1 : (b : ℂ) ≠ ⟨U, V⟩ := fun e => hV (by simpa using (congrArg Complex.im e).symm)
  have hb2 : (b : ℂ) ≠ ⟨U, -V⟩ := fun e => hV (by simpa using (congrArg Complex.im e).symm)
  have h12 : (⟨U, V⟩ : ℂ) ≠ ⟨U, -V⟩ := fun e => hV (by
    have h : V = -V := congrArg Complex.im e
    linarith)
  refine Separable.mul (Separable.mul (Separable.mul (separable_X_sub_C) (separable_X_sub_C)
    ?_) separable_X_sub_C ?_) separable_X_sub_C ?_
  · exact isCoprime_X_sub_C_X_sub_C hab'
  · exact IsCoprime.mul_left (isCoprime_X_sub_C_X_sub_C ha1) (isCoprime_X_sub_C_X_sub_C hb1)
  · exact IsCoprime.mul_left
      (IsCoprime.mul_left (isCoprime_X_sub_C_X_sub_C ha2) (isCoprime_X_sub_C_X_sub_C hb2))
      (isCoprime_X_sub_C_X_sub_C h12)

end RealRooted.BigDescents132.Quartic
