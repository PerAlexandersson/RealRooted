module

public import RealRooted.EffectiveBKW.Certificate.ListPoly
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Bernstein positivity certificates

The automatic interval checker uses a proved homogeneous substitution identity,
positive transformed coefficients and a separate upper-endpoint check. Explicit
certificates and the bivariate reconstruction use integer-list identities. Normalized
coefficient conversions can be checked separately to avoid repeated kernel reduction.
No rational arithmetic is performed by the kernel.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open BigDescents321.SmallCases Polynomial Set

/-- Homogeneous evaluation of a coefficient list of degree `length - 1`. -/
def bernsteinEval : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: p, x, z => a * z ^ p.length + x * bernsteinEval p x z

private theorem bernsteinEval_append_singleton (p : List ℝ) (a x z : ℝ) :
    bernsteinEval (p ++ [a]) x z =
      z * bernsteinEval p x z + a * x ^ p.length := by
  induction p with
  | nil => simp [bernsteinEval]
  | cons b p ih =>
    simp only [List.cons_append, bernsteinEval, List.length_append,
      List.length_cons, List.length_nil, ih, pow_succ]
    ring

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

/-- Fused coefficients of `(a + b X) r + c s`, carrying the preceding coefficient of `r`. -/
def linearStep (a b c : ℤ) : ℤ → IntPoly → IntPoly → IntPoly
  | v, [], s => addList [b * v] (scale c s)
  | v, r :: rs, [] => (a * r + b * v) :: linearStep a b c r rs []
  | v, r :: rs, s :: ss => (a * r + b * v + c * s) :: linearStep a b c r rs ss

/-- Evaluation of the fused linear step. -/
theorem eval_linearStep (a b c v : ℤ) (r s : IntPoly) (t : ℝ) :
    (linearStep a b c v r s).eval t =
      (a + t * b) * r.eval t + b * v + c * s.eval t := by
  induction r generalizing v s with
  | nil =>
    rw [linearStep, eval_addList, eval_scale]
    simp [eval, polynomial, ofList_singleton]
  | cons r rs ih =>
    cases s with
    | nil =>
      simp only [linearStep, eval, polynomial, ofList_cons, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Int.cast_add,
        Int.cast_mul] at *
      rw [ih]
      simp only [ofList_nil, Polynomial.eval_zero]
      ring
    | cons s ss =>
      simp only [linearStep, eval, polynomial, ofList_cons, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Int.cast_add,
        Int.cast_mul] at *
      rw [ih]
      ring

/-- A homogeneous Horner step, specializing the common linear substitution. -/
def homogenizeStep (x : IntPoly) (a : ℤ) (r s : IntPoly) : IntPoly :=
  match x with
  | [l, u] => linearStep l u a 0 r s
  | _ => addList (mulList x r) (scale a s)

/-- Evaluation of a homogeneous Horner step. -/
theorem eval_homogenizeStep (x : IntPoly) (a : ℤ) (r s : IntPoly) (t : ℝ) :
    (homogenizeStep x a r s).eval t = x.eval t * r.eval t + a * s.eval t := by
  unfold homogenizeStep
  split
  · rw [eval_linearStep]
    simp [eval, polynomial, ofList_cons]
  · rw [eval_addList, eval_mulList, eval_scale]

/-- Linear multiplication used to advance the homogeneous power accumulator. -/
def mulLinearOrList (x r : IntPoly) : IntPoly := homogenizeStep x 0 r []

/-- Evaluation of the specialized power update. -/
theorem eval_mulLinearOrList (x r : IntPoly) (t : ℝ) :
    (mulLinearOrList x r).eval t = x.eval t * r.eval t := by
  simp [mulLinearOrList, eval_homogenizeStep]

/-- Remove trailing zeros, only in the computational coefficient converter. -/
def trim (p : IntPoly) : IntPoly := (p.reverse.dropWhile (· == 0)).reverse

private theorem ofList_append_zero (p : IntPoly) :
    (ofList (p ++ [0]) : ℝ[X]) = ofList p := by
  induction p with
  | nil => simp [ofList_singleton]
  | cons a p ih => simp only [List.cons_append, ofList_cons, ih]

private theorem ofList_reverse_dropWhile (p : IntPoly) :
    (ofList ((p.dropWhile (· == 0)).reverse) : ℝ[X]) = ofList p.reverse := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases ha : a = 0
    · simp [ha, List.reverse_cons, ofList_append_zero, ih]
    · simp [ha]

/-- Trimming trailing zeros does not change evaluation. -/
theorem eval_trim (p : IntPoly) (t : ℝ) : p.trim.eval t = p.eval t := by
  have h := ofList_reverse_dropWhile p.reverse
  simpa only [trim, eval, polynomial, List.reverse_reverse] using
    congrArg (Polynomial.eval t) h

private theorem bernsteinEval_mul (p : IntPoly) (x z : ℝ) (hz : z ≠ 0) :
    z * bernsteinEval (p.map (fun a : ℤ => (a : ℝ))) x z =
      z ^ p.length * p.eval (x / z) := by
  induction p with
  | nil => simp [bernsteinEval, eval, polynomial]
  | cons a p ih =>
    simp only [List.map_cons, bernsteinEval, List.length_map, List.length_cons,
      eval, polynomial, ofList_cons, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, pow_succ] at *
    calc
      _ = (a : ℝ) * z ^ p.length * z + x *
          (z ^ p.length * Polynomial.eval (x / z) (ofList p)) := by rw [← ih]; ring
      _ = _ := by field_simp

private theorem eval_pos_of_all {p : IntPoly} (hne : p ≠ [])
    (hp : p.all (fun a => decide (0 < a)) = true) {x : ℝ} (hx : 0 ≤ x) :
    0 < p.eval x := by
  have hm : p.map (fun a : ℤ => (a : ℝ)) ≠ [] := by simpa using hne
  have hc : ∀ a ∈ p.map (fun a : ℤ => (a : ℝ)), 0 < a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact_mod_cast (of_decide_eq_true (List.all_eq_true.mp hp b hb) : 0 < b)
  have h := bernsteinEval_pos hm hc hx (by positivity) (by linarith : 0 < x + 1)
  simpa using (show 0 < (1 : ℝ) ^ p.length * p.eval (x / 1) by
    rw [← bernsteinEval_mul p x 1 one_ne_zero]
    simpa using h)

/-- Homogeneous Horner evaluation, consuming coefficients in descending order.
The second accumulator carries the next power of `z`. -/
def homogenizeFrom (x z : IntPoly) : IntPoly → IntPoly → IntPoly → IntPoly
  | [], r, _ => r
  | a :: p, r, s =>
    homogenizeFrom x z p (homogenizeStep x a r s) (mulLinearOrList z s)

private theorem eval_homogenizeFrom (x z p r s : IntPoly) (t : ℝ) :
    (homogenizeFrom x z p r s).eval t =
      r.eval t * x.eval t ^ p.length + s.eval t *
        bernsteinEval (p.reverse.map (fun a : ℤ => (a : ℝ))) (x.eval t) (z.eval t) := by
  induction p generalizing r s with
  | nil => simp [homogenizeFrom, bernsteinEval]
  | cons a p ih =>
    simp only [homogenizeFrom, ih, eval_homogenizeStep, eval_mulLinearOrList,
      List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      bernsteinEval_append_singleton, List.length_cons, List.length_map,
      List.length_reverse, pow_succ]
    ring

/-- Homogeneous substitution using one incremental power per coefficient. -/
def homogenize (x z p : IntPoly) : IntPoly :=
  homogenizeFrom x z p.reverse [] [1]

/-- Evaluation of homogeneous Horner substitution. -/
theorem eval_homogenize (x z p : IntPoly) (t : ℝ) :
    (homogenize x z p).eval t =
      bernsteinEval (p.map (fun a : ℤ => (a : ℝ))) (x.eval t) (z.eval t) := by
  rw [homogenize, eval_homogenizeFrom]
  simp [eval, polynomial, ofList_singleton]

/-- Common-denominator interval data `(denominator, lower numerator, upper numerator)`. -/
def intervalData (lo hi : QNum) : ℤ × ℤ × ℤ :=
  (lo.den * hi.den, lo.num * hi.den, hi.num * lo.den)

/-- Denominator-cleared homogenized Bernstein coefficients. -/
def bernsteinCoeffs (p : IntPoly) (lo hi : QNum) : IntPoly :=
  let (d, l, u) := intervalData lo hi
  trim (homogenize [l, u] [d, d] p)

/-- Reconstruct a polynomial from homogeneous interval coefficients. -/
def bernsteinList (lower upper p : IntPoly) : IntPoly := homogenize lower upper p

/-- Evaluation of the checked Bernstein reconstruction. -/
theorem eval_bernsteinList (lower upper p : IntPoly) (x : ℝ) :
    (bernsteinList lower upper p).eval x =
      bernsteinEval (p.map (fun a : ℤ => (a : ℝ))) (lower.eval x) (upper.eval x) := by
  exact eval_homogenize lower upper p x

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

/-- Assemble a check from a separately normalized reconstruction and its remaining tests.
The reconstruction equality is checked once, with literal coefficients as its input. -/
theorem PosCert.check_of_reconstruction {c : PosCert} {p result : IntPoly} {lo hi : QNum}
    (he : let (d, l, u) := intervalData lo hi
      bernsteinList [-l, d] [u, -d] c.coeffs = result)
    (h : (lo.valid && hi.valid && lo.lt hi && decide (0 < c.scale) &&
      decide (c.coeffs ≠ []) && c.coeffs.all (fun a => decide (0 < a)) &&
      (IntPoly.scale c.scale p).eqCheck result) = true) : c.check p lo hi = true := by
  dsimp only [PosCert.check, intervalData] at he ⊢
  rw [he]
  exact h

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
The substitution identity is proved once; the upper endpoint is checked separately. -/
def posOn (p : IntPoly) (lo hi : QNum) : Bool :=
  if lo.lt hi then
    let coeffs := bernsteinCoeffs p lo hi
    lo.valid && hi.valid && decide (coeffs ≠ []) &&
      coeffs.all (fun a => decide (0 < a)) && decide (0 < p.evalScaled hi.num hi.den)
  else lo.valid && hi.valid && lo.le hi && hi.le lo &&
    decide (0 < p.evalScaled lo.num lo.den)

/-- Assemble automatic positivity from a separately checked coefficient conversion. -/
theorem posOn_of_coeffs {p coeffs : IntPoly} {lo hi : QNum}
    (hlt : lo.lt hi = true) (hc : bernsteinCoeffs p lo hi = coeffs)
    (h : (lo.valid && hi.valid && decide (coeffs ≠ []) &&
      coeffs.all (fun a => decide (0 < a)) && decide (0 < p.evalScaled hi.num hi.den)) = true) :
    p.posOn lo hi = true := by
  simpa only [posOn, hlt, ite_true, hc] using h

/-- The homogeneous substitution proves interval positivity below the upper endpoint;
the separate endpoint check also covers cancellation of the top transformed coefficient. -/
private theorem eval_pos_of_bernsteinCoeffs {p : IntPoly} {lo hi : QNum}
    (hlo : lo.valid = true) (hhi : hi.valid = true)
    (hne : bernsteinCoeffs p lo hi ≠ [])
    (hc : (bernsteinCoeffs p lo hi).all (fun a => decide (0 < a)) = true)
    (hp : 0 < p.evalScaled hi.num hi.den) {x : ℝ} (hx : x ∈ Icc lo.val hi.val) :
    0 < p.eval x := by
  have hdlo : (0 : ℝ) < lo.den := by
    exact_mod_cast (of_decide_eq_true hlo : 0 < lo.den)
  have hdhi : (0 : ℝ) < hi.den := by
    exact_mod_cast (of_decide_eq_true hhi : 0 < hi.den)
  by_cases he : x = hi.val
  · have hp' : (0 : ℝ) < p.evalScaled hi.num hi.den := by exact_mod_cast hp
    rw [evalScaled_eq p hi hhi] at hp'
    rw [he]
    exact (mul_pos_iff_of_pos_left (pow_pos hdhi _)).mp hp'
  · let d : ℝ := lo.den * hi.den
    let l : ℝ := lo.num * hi.den
    let u : ℝ := hi.num * lo.den
    have hlx := (div_le_iff₀ hdlo).mp hx.1
    have hxu := (lt_div_iff₀ hdhi).mp (lt_of_le_of_ne hx.2 he)
    have hl : 0 ≤ d * x - l := by
      dsimp [d, l]
      nlinarith [mul_le_mul_of_nonneg_right hlx hdhi.le]
    have hu : 0 < u - d * x := by
      dsimp [u, d]
      nlinarith [mul_lt_mul_of_pos_right hxu hdlo]
    let s := (d * x - l) / (u - d * x)
    have hs : 0 ≤ s := div_nonneg hl hu.le
    have hz : 0 < d + d * s := by dsimp [d]; positivity
    have harg : (l + u * s) / (d + d * s) = x := by
      apply (div_eq_iff hz.ne').mpr
      dsimp [s]
      field_simp
      ring
    have hq := eval_pos_of_all hne hc hs
    rw [bernsteinCoeffs, eval_trim, eval_homogenize] at hq
    have hlin (a b : ℤ) : eval [a, b] s = a + s * b := by
      simp [eval, polynomial, ofList_cons]
    simp only [intervalData] at hq
    simp only [hlin, Int.cast_mul, Int.cast_natCast] at hq
    have hq' : 0 < bernsteinEval (p.map (fun a : ℤ => (a : ℝ)))
        (l + u * s) (d + d * s) := by simpa [d, l, u, mul_comm] using hq
    have hid := bernsteinEval_mul p (l + u * s) (d + d * s) hz.ne'
    rw [harg] at hid
    have hprod : 0 < (d + d * s) ^ p.length * p.eval x := by
      rw [← hid]
      exact mul_pos hz hq'
    exact (mul_pos_iff_of_pos_left (pow_pos hz _)).mp hprod

/-- Soundness of the automatic interval checker. -/
theorem posOn_sound {p : IntPoly} {lo hi : QNum} (h : p.posOn lo hi = true)
    {x : ℝ} (hx : x ∈ Icc lo.val hi.val) : 0 < p.eval x := by
  dsimp only [posOn] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hlo, hhi⟩, hne⟩, hc⟩, hp⟩ := h
    exact eval_pos_of_bernsteinCoeffs hlo hhi hne hc hp hx
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

/-- Homogeneous Horner evaluation in `y`, carrying the next power of `z`. -/
def homogenizeFrom (x z : IntPoly2) : IntPoly2 → IntPoly2 → IntPoly2 → IntPoly2
  | [], r, _ => r
  | p :: f, r, s => homogenizeFrom x z f (add (mul x r) (scale p s)) (mul z s)

private theorem eval_homogenizeFrom (x z f r s : IntPoly2) (t y : ℝ) :
    (homogenizeFrom x z f r s).eval t y =
      r.eval t y * x.eval t y ^ f.length + s.eval t y *
        bernsteinEval (f.reverse.map (fun p : IntPoly => p.eval t))
          (x.eval t y) (z.eval t y) := by
  induction f generalizing r s with
  | nil => simp [homogenizeFrom, bernsteinEval]
  | cons p f ih =>
    simp only [homogenizeFrom, ih, eval_add, eval_mul, eval_scale,
      List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      bernsteinEval_append_singleton, List.length_cons, List.length_map,
      List.length_reverse, pow_succ]
    ring

/-- Homogeneous substitution in `y`, using incremental powers and leaving `t` symbolic. -/
def homogenize (x z f : IntPoly2) : IntPoly2 :=
  homogenizeFrom x z f.reverse [] [[1]]

/-- Evaluation of bivariate homogeneous Horner substitution. -/
theorem eval_homogenize (x z f : IntPoly2) (t y : ℝ) :
    (homogenize x z f).eval t y =
      bernsteinEval (f.map (fun p : IntPoly => p.eval t)) (x.eval t y) (z.eval t y) := by
  simp [homogenize, eval_homogenizeFrom, eval, IntPoly.eval, IntPoly.polynomial,
    ofList_singleton]

/-- Remove zero rows left by dense list arithmetic. -/
def trim (f : IntPoly2) : IntPoly2 :=
  (f.reverse.dropWhile (fun p => p.all (· == 0))).reverse

/-- Homogeneous Bernstein coefficients in `y`, each a polynomial in `t`. -/
def bernsteinCoeffs (f : IntPoly2) (lo hi : QNum) : IntPoly2 :=
  let (d, l, u) := IntPoly.intervalData lo hi
  trim (homogenize [[l], [u]] [[d], [d]] f)

/-- Bivariate reconstruction in the `y` direction. -/
def bernsteinList (lower upper f : IntPoly2) : IntPoly2 := homogenize lower upper f

/-- The bivariate reconstruction is homogeneous evaluation after specializing `t`. -/
theorem eval_bernsteinList (lower upper f : IntPoly2) (t y : ℝ) :
    (bernsteinList lower upper f).eval t y =
      bernsteinEval (f.map (fun p : IntPoly => p.eval t)) (lower.eval t y)
        (upper.eval t y) := by
  exact eval_homogenize lower upper f t y

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

/-- Assemble a box check from individually checked coefficient intervals and reconstruction. -/
theorem PosCert.check_of_reconstruction {c : PosCert} {f result : IntPoly2}
    {tlo thi lo hi : QNum}
    (he : let (d, l, u) := IntPoly.intervalData lo hi
      bernsteinList [[-l], [d]] [[u], [-d]] c.coeffs = result)
    (hc : c.coeffs.all (fun p => p.posOn tlo thi) = true)
    (h : (lo.valid && hi.valid && lo.lt hi && decide (0 < c.scale) &&
      decide (c.coeffs ≠ []) && (smul c.scale f).eqCheck result) = true) :
    c.check f tlo thi lo hi = true := by
  dsimp only [PosCert.check, IntPoly.intervalData] at he ⊢
  rw [he, hc]
  simpa only [Bool.and_true] using h

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

/-- Assemble automatic box positivity from a separately checked Bernstein conversion. -/
theorem posOnBox_of_coeffs {f coeffs : IntPoly2} {tlo thi lo hi : QNum}
    (hc : bernsteinCoeffs f lo hi = coeffs)
    (h : let (d, l, u) := IntPoly.intervalData lo hi
      (PosCert.mk coeffs ((d * (u - l)) ^ (f.length - 1))).check f tlo thi lo hi = true) :
    f.posOnBox tlo thi lo hi = true := by
  simpa only [posOnBox, hc] using h

/-- Soundness of the automatic box checker. -/
theorem posOnBox_sound {f : IntPoly2} {tlo thi lo hi : QNum}
    (h : f.posOnBox tlo thi lo hi = true) {t y : ℝ}
    (ht : t ∈ Icc tlo.val thi.val) (hy : y ∈ Icc lo.val hi.val) :
    0 < f.eval t y := PosCert.check_sound h ht hy

/-- Assemble individually checked boxes without reducing one large `List.all` computation. -/
theorem posOnBox_all {α : Type*} {f : IntPoly2} {boxes : List α}
    (tlo thi lo hi : α → QNum)
    (h : ∀ c ∈ boxes, f.posOnBox (tlo c) (thi c) (lo c) (hi c) = true) :
    boxes.all (fun c => f.posOnBox (tlo c) (thi c) (lo c) (hi c)) = true :=
  List.all_eq_true.mpr h

end IntPoly2
end RealRooted.EffectiveBKW
