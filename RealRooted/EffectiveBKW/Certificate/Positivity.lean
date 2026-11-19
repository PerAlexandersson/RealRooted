module

public import RealRooted.EffectiveBKW.Certificate.ListPoly
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bernstein positivity certificates

The checker forms the denominator-cleared homogenized Bernstein transform and
checks its reconstruction by integer-list equality. This extra identity check
keeps the soundness proof independent of the conversion algorithm. No rational
arithmetic is performed by the kernel.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open BigDescents321.SmallCases Polynomial Set

/-- Homogeneous evaluation of a coefficient list of degree `length - 1`. -/
def bernsteinEval : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: p, x, z => a * z ^ p.length + x * bernsteinEval p x z

/-- Nonnegative coefficients give nonnegative homogeneous evaluation. -/
theorem bernsteinEval_nonneg {p : List ℝ} (hp : ∀ a ∈ p, 0 ≤ a)
    {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : 0 ≤ bernsteinEval p x z := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    exact add_nonneg (mul_nonneg (hp a (by simp)) (pow_nonneg hz _))
      (mul_nonneg hx (ih (fun b hb => hp b (by simp [hb]))))

/-- Strictly positive coefficients give positivity on the closed positive simplex. -/
theorem bernsteinEval_pos {p : List ℝ} (hne : p ≠ []) (hp : ∀ a ∈ p, 0 < a)
    {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) (hs : 0 < x + z) :
    0 < bernsteinEval p x z := by
  induction p with
  | nil => exact (hne rfl).elim
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht : ∀ b ∈ p, 0 < b := fun b hb => hp b (by simp [hb])
    cases p with
    | nil => simpa [bernsteinEval] using ha
    | cons b p =>
      by_cases hz' : 0 < z
      · exact add_pos_of_pos_of_nonneg (mul_pos ha (pow_pos hz' _))
          (mul_nonneg hx (bernsteinEval_nonneg (fun c hc => (ht c hc).le) hx hz))
      · have hx' : 0 < x := by linarith
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (pow_nonneg hz _))
          (mul_pos hx' (ih (by simp) ht))

namespace IntPoly

/-- Remove trailing zeros, only in the computational coefficient converter. -/
def trim (p : IntPoly) : IntPoly := (p.reverse.dropWhile (· == 0)).reverse

/-- Homogeneous substitution, with output interpreted as an ordinary integer polynomial. -/
def homogenize (x z : IntPoly) : IntPoly → IntPoly
  | [] => []
  | a :: p => addList (scale a (z.pow p.length)) (mulList x (homogenize x z p))

/-- Common-denominator interval data `(denominator, lower numerator, upper numerator)`. -/
def intervalData (lo hi : QNum) : ℤ × ℤ × ℤ :=
  (lo.den * hi.den, lo.num * hi.den, hi.num * lo.den)

/-- Denominator-cleared homogenized Bernstein coefficients. -/
def bernsteinCoeffs (p : IntPoly) (lo hi : QNum) : IntPoly :=
  let (d, l, u) := intervalData lo hi
  trim (homogenize [l, u] [d, d] p)

/-- Reconstruct a polynomial from homogeneous interval coefficients. -/
def bernsteinList (lower upper : IntPoly) : IntPoly → IntPoly
  | [] => []
  | a :: p => addList (scale a (upper.pow p.length))
      (mulList lower (bernsteinList lower upper p))

/-- Evaluation of the checked Bernstein reconstruction. -/
theorem eval_bernsteinList (lower upper p : IntPoly) (x : ℝ) :
    (bernsteinList lower upper p).eval x =
      bernsteinEval (p.map (fun a : ℤ => (a : ℝ))) (lower.eval x) (upper.eval x) := by
  induction p with
  | nil => simp [bernsteinList, eval, polynomial, bernsteinEval]
  | cons a p ih =>
    simp only [bernsteinList, eval_addList, eval_scale, eval_pow, eval_mulList, ih,
      List.map_cons, bernsteinEval, List.length_map]

/-- A positive Bernstein expansion, with an independently checked reconstruction scale. -/
structure PosCert where
  /-- Homogeneous coefficients in ascending order. -/
  coeffs : IntPoly
  /-- Positive integer multiplying the original polynomial. -/
  scale : ℤ
  deriving Repr

/-- Check a positive expansion on a nondegenerate closed rational interval. -/
def PosCert.check (c : PosCert) (p : IntPoly) (lo hi : QNum) : Bool :=
  let (d, l, u) := intervalData lo hi
  lo.valid && hi.valid && lo.lt hi && decide (0 < c.scale) &&
    decide (c.coeffs ≠ []) && c.coeffs.all (fun a => decide (0 < a)) &&
    (IntPoly.scale c.scale p).eqCheck (bernsteinList [-l, d] [u, -d] c.coeffs)

/-- A checked positive expansion is strictly positive on the entire closed interval. -/
theorem PosCert.check_sound {c : PosCert} {p : IntPoly} {lo hi : QNum}
    (h : c.check p lo hi = true) {x : ℝ} (hx : x ∈ Icc lo.val hi.val) :
    0 < p.eval x := by
  simp only [PosCert.check, intervalData, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hlt⟩, hs⟩, hne⟩, hc⟩, he⟩ := h
  have hdlo : (0 : ℝ) < lo.den := by
    exact_mod_cast (of_decide_eq_true hlo : 0 < lo.den)
  have hdhi : (0 : ℝ) < hi.den := by
    exact_mod_cast (of_decide_eq_true hhi : 0 < hi.den)
  have hlx : (lo.num : ℝ) ≤ x * lo.den := (div_le_iff₀ hdlo).mp hx.1
  have hxu : x * hi.den ≤ (hi.num : ℝ) := (le_div_iff₀ hdhi).mp hx.2
  have hgap' : (lo.num : ℝ) * hi.den < hi.num * lo.den := by
    exact_mod_cast (of_decide_eq_true hlt : lo.num * hi.den < hi.num * lo.den)
  let lower : ℝ := -(lo.num * (hi.den : ℤ) : ℤ) +
    x * ((lo.den : ℤ) * hi.den : ℤ)
  let upper : ℝ := (hi.num * (lo.den : ℤ) : ℤ) +
    x * (-((lo.den : ℤ) * hi.den) : ℤ)
  have hl : 0 ≤ lower := by
    dsimp [lower]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlx hdhi.le]
  have hu : 0 ≤ upper := by
    dsimp [upper]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hxu hdlo.le]
  have hsum : 0 < lower + upper := by
    dsimp [lower, upper]
    push_cast
    nlinarith
  have hc' : ∀ a ∈ c.coeffs.map (fun a : ℤ => (a : ℝ)), 0 < a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact_mod_cast (of_decide_eq_true (List.all_eq_true.mp hc b hb) : 0 < b)
  have hm : c.coeffs.map (fun a : ℤ => (a : ℝ)) ≠ [] := by
    intro hm
    exact hne (List.map_eq_nil_iff.mp hm)
  have hp := bernsteinEval_pos hm hc' hl hu hsum
  have hid := congrArg (Polynomial.eval x) (eqCheck_sound he)
  change (IntPoly.scale c.scale p).eval x = _ at hid
  rw [eval_scale, ← eval, eval_bernsteinList] at hid
  have hlin (a b : ℤ) : eval [a, b] x = a + x * b := by
    simp [eval, polynomial, ofList_cons]
  simp only [hlin] at hid
  have hs' : (0 : ℝ) < c.scale := by exact_mod_cast hs
  have hprod : 0 < (c.scale : ℝ) * p.eval x := by simpa [hid, lower, upper] using hp
  exact (mul_pos_iff_of_pos_left hs').mp hprod

/-- Automatic interval positivity using the homogenized Bernstein transform.
The reconstruction is checked as well as the signs. -/
def posOn (p : IntPoly) (lo hi : QNum) : Bool :=
  let (d, l, u) := intervalData lo hi
  let c : PosCert := ⟨bernsteinCoeffs p lo hi, (d * (u - l)) ^ (p.length - 1)⟩
  if lo.lt hi then c.check p lo hi
  else lo.valid && hi.valid && lo.le hi && hi.le lo &&
    decide (0 < p.evalScaled lo.num lo.den)

/-- Soundness of the automatic interval checker. -/
theorem posOn_sound {p : IntPoly} {lo hi : QNum} (h : p.posOn lo hi = true)
    {x : ℝ} (hx : x ∈ Icc lo.val hi.val) : 0 < p.eval x := by
  dsimp only [posOn, intervalData] at h
  split at h
  · exact PosCert.check_sound h hx
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hlo, hhi⟩, hlh⟩, hhl⟩, hp⟩ := h
    have heq := le_antisymm (QNum.le_sound hlo hhi hlh) (QNum.le_sound hhi hlo hhl)
    have hx' : x = lo.val := le_antisymm (hx.2.trans heq.ge) hx.1
    rw [hx']
    have hd : (0 : ℝ) < lo.den := by
      exact_mod_cast (of_decide_eq_true hlo : 0 < lo.den)
    have hp' : (0 : ℝ) < p.evalScaled lo.num lo.den := by exact_mod_cast hp
    rw [evalScaled_eq p lo hlo] at hp'
    exact (mul_pos_iff_of_pos_left (pow_pos hd _)).mp hp'

end IntPoly

namespace IntPoly2

/-- Bivariate list powers. -/
def pow (f : IntPoly2) : ℕ → IntPoly2
  | 0 => [[1]]
  | n + 1 => mul f (pow f n)

/-- Evaluation of bivariate list powers. -/
theorem eval_pow (f : IntPoly2) (n : ℕ) (t y : ℝ) :
    (f.pow n).eval t y = f.eval t y ^ n := by
  induction n with
  | zero => simp [pow, eval, IntPoly.eval, IntPoly.polynomial, ofList_cons]
  | succ n ih => simp only [pow, eval_mul, ih, pow_succ']

/-- Homogeneous substitution in `y`, leaving `t` symbolic. -/
def homogenize (x z : IntPoly2) : IntPoly2 → IntPoly2
  | [] => []
  | p :: f => add (scale p (z.pow f.length)) (mul x (homogenize x z f))

/-- Remove zero rows left by dense list arithmetic. -/
def trim (f : IntPoly2) : IntPoly2 :=
  (f.reverse.dropWhile (fun p => p.all (· == 0))).reverse

/-- Homogeneous Bernstein coefficients in `y`, each a polynomial in `t`. -/
def bernsteinCoeffs (f : IntPoly2) (lo hi : QNum) : IntPoly2 :=
  let (d, l, u) := IntPoly.intervalData lo hi
  trim (homogenize [[l], [u]] [[d], [d]] f)

/-- Bivariate reconstruction in the `y` direction. -/
def bernsteinList (lower upper : IntPoly2) : IntPoly2 → IntPoly2
  | [] => []
  | p :: f => add (scale p (upper.pow f.length))
      (mul lower (bernsteinList lower upper f))

/-- The bivariate reconstruction is homogeneous evaluation after specializing `t`. -/
theorem eval_bernsteinList (lower upper f : IntPoly2) (t y : ℝ) :
    (bernsteinList lower upper f).eval t y =
      bernsteinEval (f.map (fun p : IntPoly => p.eval t)) (lower.eval t y)
        (upper.eval t y) := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    simp only [bernsteinList, eval_add, eval_scale, eval_pow, eval_mul, ih,
      List.map_cons, bernsteinEval, List.length_map]

/-- A box positivity certificate: Bernstein coefficients in `y`, positive on the `t` interval. -/
structure PosCert where
  /-- Coefficient polynomials. -/
  coeffs : IntPoly2
  /-- Positive reconstruction scale. -/
  scale : ℤ
  deriving Repr

/-- Check the tensor-product Bernstein expansion and its reconstruction. -/
def PosCert.check (c : PosCert) (f : IntPoly2) (tlo thi lo hi : QNum) : Bool :=
  let (d, l, u) := IntPoly.intervalData lo hi
  lo.valid && hi.valid && lo.lt hi && decide (0 < c.scale) &&
    decide (c.coeffs ≠ []) && c.coeffs.all (fun p => p.posOn tlo thi) &&
    (smul c.scale f).eqCheck (bernsteinList [[-l], [d]] [[u], [-d]] c.coeffs)

/-- Box positivity follows from the checked tensor-product expansion. -/
theorem PosCert.check_sound {c : PosCert} {f : IntPoly2} {tlo thi lo hi : QNum}
    (h : c.check f tlo thi lo hi = true) {t y : ℝ}
    (ht : t ∈ Icc tlo.val thi.val) (hy : y ∈ Icc lo.val hi.val) :
    0 < f.eval t y := by
  simp only [PosCert.check, IntPoly.intervalData, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hlt⟩, hs⟩, hne⟩, hc⟩, he⟩ := h
  have hdlo : (0 : ℝ) < lo.den := by
    exact_mod_cast (of_decide_eq_true hlo : 0 < lo.den)
  have hdhi : (0 : ℝ) < hi.den := by
    exact_mod_cast (of_decide_eq_true hhi : 0 < hi.den)
  have hly := (div_le_iff₀ hdlo).mp hy.1
  have hyu := (le_div_iff₀ hdhi).mp hy.2
  have hgap : (lo.num : ℝ) * hi.den < hi.num * lo.den := by
    exact_mod_cast (of_decide_eq_true hlt : lo.num * hi.den < hi.num * lo.den)
  let lower : ℝ := -(lo.num * (hi.den : ℤ) : ℤ) +
    y * ((lo.den : ℤ) * hi.den : ℤ)
  let upper : ℝ := (hi.num * (lo.den : ℤ) : ℤ) +
    y * (-((lo.den : ℤ) * hi.den) : ℤ)
  have hl : 0 ≤ lower := by
    dsimp [lower]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hly hdhi.le]
  have hu : 0 ≤ upper := by
    dsimp [upper]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hyu hdlo.le]
  have hsum : 0 < lower + upper := by
    dsimp [lower, upper]
    push_cast
    nlinarith
  have hc' : ∀ a ∈ c.coeffs.map (fun p : IntPoly => p.eval t), 0 < a := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact IntPoly.posOn_sound (List.all_eq_true.mp hc p hp) ht
  have hm : c.coeffs.map (fun p : IntPoly => p.eval t) ≠ [] := by
    intro hm
    exact hne (List.map_eq_nil_iff.mp hm)
  have hp := bernsteinEval_pos hm hc' hl hu hsum
  have hid := eqCheck_sound he t y
  rw [eval_smul, eval_bernsteinList] at hid
  have hlin (a b : ℤ) : eval [[a], [b]] t y = a + y * b := by
    simp [eval, IntPoly.eval, IntPoly.polynomial, ofList_cons]
  simp only [hlin] at hid
  have hs' : (0 : ℝ) < c.scale := by exact_mod_cast hs
  have hprod : 0 < (c.scale : ℝ) * f.eval t y := by simpa [hid, lower, upper] using hp
  exact (mul_pos_iff_of_pos_left hs').mp hprod

/-- Automatic box positivity, by Bernstein conversion in both directions. -/
def posOnBox (f : IntPoly2) (tlo thi lo hi : QNum) : Bool :=
  let (d, l, u) := IntPoly.intervalData lo hi
  let c : PosCert := ⟨bernsteinCoeffs f lo hi, (d * (u - l)) ^ (f.length - 1)⟩
  c.check f tlo thi lo hi

/-- Soundness of the automatic box checker. -/
theorem posOnBox_sound {f : IntPoly2} {tlo thi lo hi : QNum}
    (h : f.posOnBox tlo thi lo hi = true) {t y : ℝ}
    (ht : t ∈ Icc tlo.val thi.val) (hy : y ∈ Icc lo.val hi.val) :
    0 < f.eval t y := PosCert.check_sound h ht hy

end IntPoly2
end RealRooted.EffectiveBKW
