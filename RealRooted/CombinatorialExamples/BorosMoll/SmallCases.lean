module

public import RealRooted.CombinatorialExamples.BorosMoll.Transform
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Eval
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Polynomial
import RealRooted.Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import RealRooted.Mathlib.Algebra.Polynomial.Coeff

/-!
# Boros–Moll finite certificates

For `1 ≤ n ≤ 35` we certify interlacing by explicit dyadic sample points. Integer
coefficient formulas and the Boolean checker are kept with their kernel-checked
tables. All finite cases are needed: the large-index estimates begin at `n = 36`.

Coefficient tables are quoted from the integer formulas, then verified by the kernel.
The original dyadic sample points remain literal certificate data.
-/

@[expose] public section

namespace RealRooted.BorosMoll

open Polynomial

section SmallCasesCore

/-! ### Integer versions of the coefficients -/

/-- A kernel-friendly binomial coefficient. -/
private def chooseF (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

private lemma chooseF_eq (n k : ℕ) : chooseF n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- `4^n d_i(n)`, an integer. -/
private def bmDF (n i : ℕ) : ℕ :=
  ((List.range (n + 1 - i)).map (fun r =>
    2 ^ (i + r) * chooseF (2 * n - 2 * (i + r)) (n - (i + r)) * chooseF (n + (i + r)) n *
      chooseF (i + r) i)).sum

/-- The common summand weights, shared by every coefficient in one row. -/
private def factorRow (n : ℕ) : List ℕ :=
  (List.range (n + 1)).map (fun k =>
    2 ^ k * chooseF (2 * n - 2 * k) (n - k) * chooseF (n + k) n)

/-- Compute each coefficient from a previously checked list of common weights. -/
private def bmFromRow (weights : List ℕ) (n i : ℕ) : ℕ :=
  ((List.range (n + 1 - i)).map (fun r =>
    weights.getD (i + r) 0 * chooseF (i + r) i)).sum

/-- Looking up the common weights recovers the original coefficient formula. -/
private lemma bmDF_eq_fromRow (n i : ℕ) : bmDF n i = bmFromRow (factorRow n) n i := by
  unfold bmDF bmFromRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hir : i + r < n + 1 := by
    have := List.mem_range.mp hr
    lia
  simp [factorRow, List.getD_eq_getElem?_getD, hir]

/-- `16^n L(d(n))_i`, an integer. -/
private def LintF (n i : ℕ) : ℤ :=
  (bmDF n i : ℤ) ^ 2 - (if i = 0 then 0 else (bmDF n (i - 1) : ℤ)) * (bmDF n (i + 1) : ℤ)

/-- The Narayana number, written as `C(n,i)^2 - C(n,i-1) C(n,i+1)`. -/
private def NintF (n i : ℕ) : ℤ :=
  (chooseF n i : ℤ) ^ 2 - (if i = 0 then 0 else (chooseF n (i - 1) : ℤ)) * (chooseF n (i + 1) : ℤ)

/-- Reduce the dyadic point before performing integer evaluation. -/
private def dyadic (a : ℤ) : ℚ := (a : ℚ) / 1024

/-- Homogeneous Horner evaluation with a carried denominator power. -/
private def hornerPair (a : ℤ) (d : ℕ) : List ℤ → ℤ × ℤ
  | [] => (0, 1)
  | c :: cs =>
    let (r, z) := hornerPair a d cs
    (c * z + a * r, (d : ℤ) * z)

/-- Integer evaluation at the reduced rational point. -/
private def hornerAt (cs : List ℤ) (a : ℤ) : ℤ :=
  (hornerPair (dyadic a).num (dyadic a).den cs).1

/-- The power accumulator counts the processed coefficients. -/
private lemma hornerPair_snd (cs : List ℤ) (a : ℤ) (d : ℕ) :
    (hornerPair a d cs).2 = (d : ℤ) ^ cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simpa only [hornerPair, List.length_cons, pow_succ, mul_comm] using
      congrArg (fun z : ℤ => (d : ℤ) * z) ih

/-- Homogeneous integer evaluation agrees with ordinary rational Horner evaluation. -/
private lemma hornerPair_mul_cast (cs : List ℤ) (a : ℤ) (d : ℕ) (hd : 0 < d) :
    (d : ℝ) * ((hornerPair a d cs).1 : ℝ) = (d : ℝ) ^ cs.length *
      cs.foldr (fun (c : ℤ) (r : ℝ) => (c : ℝ) + (a : ℝ) / d * r) 0 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  induction cs with
  | nil => simp [hornerPair]
  | cons c cs ih =>
    have hs : ((hornerPair a d cs).2 : ℝ) = (d : ℝ) ^ cs.length := by
      rw [hornerPair_snd, Int.cast_pow, Int.cast_natCast]
    simp only [hornerPair, Int.cast_add, Int.cast_mul, List.length_cons,
      List.foldr_cons, pow_succ] at ih ⊢
    rw [hs]
    calc
      _ = (d : ℝ) * ((c : ℝ) * d ^ cs.length) +
          (a : ℝ) * ((d : ℝ) * ((hornerPair a d cs).1 : ℝ)) := by ring
      _ = (d : ℝ) * ((c : ℝ) * d ^ cs.length) + (a : ℝ) *
          ((d : ℝ) ^ cs.length * cs.foldr
            (fun (c : ℤ) (r : ℝ) => (c : ℝ) + (a : ℝ) / d * r) 0) := by rw [ih]
      _ = _ := by field_simp

/-- Horner evaluation is the finite coefficient sum. -/
private lemma hornerFold_eq_sum (cs : List ℤ) (x : ℝ) :
    cs.foldr (fun (c : ℤ) (r : ℝ) => (c : ℝ) + x * r) 0 =
      ∑ i ∈ Finset.range cs.length, (cs.getD i 0 : ℝ) * x ^ i := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldr_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [pow_succ, Finset.mul_sum, mul_comm, mul_assoc, add_comm]

private lemma bmCoeff_eq_bmDF (n i : ℕ) : bmCoeff n i = (bmDF n i : ℝ) / 4 ^ n := by
  unfold bmCoeff bmDF
  have : ∀ m (f : ℕ → ℕ), ((((List.range m).map f).sum : ℕ) : ℝ) =
      ∑ r ∈ Finset.range m, (f r : ℝ) := by
    intro m f
    simp [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Function.comp_def]
  rw [this, show Finset.Icc i n = Finset.Ico i (n + 1) from rfl, Finset.sum_Ico_eq_sum_range]
  simp only [chooseF_eq]
  push_cast
  rw [eq_div_iff (by positivity), mul_comm, ← mul_assoc, ← mul_pow]
  norm_num

private lemma bmL_eq_LintF (n i : ℕ) : bmL n i = (LintF n i : ℝ) / 16 ^ n := by
  unfold bmL LintF
  rw [bmCoeff_eq_bmDF, bmCoeff_eq_bmDF]
  have h16 : (16:ℝ)^n = 4^n * 4^n := by rw [← mul_pow]; norm_num
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [↓reduceIte, zero_add, zero_mul, sub_zero, Int.cast_pow, Int.cast_natCast]; rw [h16];
        field_simp
  · simp only [show i ≠ 0 by lia, ite_false]
    rw [bmCoeff_eq_bmDF]
    push_cast
    rw [h16]; field_simp

private lemma narC_eq_NintF (n i : ℕ) : narC n i = (NintF n i : ℝ) := by
  unfold narC NintF
  simp only [chooseF_eq]
  rcases le_or_gt i n with hin | hin
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
      simp only [show j + 1 ≠ 0 by lia, ite_false, Nat.add_sub_cancel]
      have h1 := Nat.choose_succ_right_eq n j
      have h2 := Nat.choose_succ_right_eq n (j+1)
      have h3 := Nat.add_one_mul_choose_eq n j
      have c1 : ((n.choose (j+1) : ℕ) : ℝ) * ((j:ℝ)+1) = (n.choose j) * ((n:ℝ) - j) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h1
        push_cast [Nat.cast_sub (show j ≤ n by lia)] at this; linarith
      have c2 : (((n+1).choose (j+1) : ℕ) : ℝ) * ((j:ℝ)+1) = ((n:ℝ)+1) * (n.choose j) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h3
        push_cast at this; linarith
      have h4 : ((n + 1).choose (j + 1) : ℝ) * ((n:ℝ) - j) = ((n:ℝ) + 1) * (n.choose (j+1)) := by
        have hj : (0:ℝ) < (j:ℝ) + 1 := by positivity
        have : (((n+1).choose (j+1) : ℕ) : ℝ) * ((n:ℝ) - j) * ((j:ℝ)+1) =
            ((n:ℝ) + 1) * (n.choose (j+1)) * ((j:ℝ)+1) := by
          linear_combination ((n:ℝ)-j) * c2 - ((n:ℝ)+1) * c1
        exact mul_right_cancel₀ hj.ne' this
      have c3 : ((n.choose (j+2) : ℕ) : ℝ) * ((j:ℝ)+2) = (n.choose (j+1)) * ((n:ℝ) - j - 1) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h2
        push_cast [Nat.cast_sub (show j + 1 ≤ n by lia)] at this; linarith
      have hnj : (0:ℝ) < (n:ℝ) - j := by
        have : (j:ℝ) + 1 ≤ n := by exact_mod_cast hin
        linarith
      push_cast
      have e1 : ((n+1).choose (j+1) : ℝ) = ((n:ℝ) + 1) * (n.choose (j+1)) / ((n:ℝ) - j) := by
        rw [eq_div_iff hnj.ne']; exact h4
      have e2 : (n.choose j : ℝ) = (n.choose (j+1)) * ((j:ℝ)+1) / ((n:ℝ) - j) := by
        rw [eq_div_iff hnj.ne']; linarith
      have e3 : (n.choose (j+2) : ℝ) = (n.choose (j+1)) * ((n:ℝ) - j - 1) / ((j:ℝ)+2) := by
        rw [eq_div_iff (by positivity)]; linarith
      rw [e1, e2, e3]
      field_simp
      ring
  · rw [Nat.choose_eq_zero_of_lt hin, Nat.choose_eq_zero_of_lt (show n < i + 1 by lia)]
    simp

private lemma hornerAt_cast (cs : List ℤ) (n : ℕ) (a : ℤ) (c : ℕ → ℝ)
    (hlen : cs.length = n + 1) (hc : ∀ i < n + 1, (cs.getD i 0 : ℝ) = c i) :
    (hornerAt cs a : ℝ) = ((dyadic a).den : ℝ) ^ n *
      ∑ i ∈ Finset.range (n + 1), c i * ((a : ℝ) / 1024) ^ i := by
  have hr : ((dyadic a).num : ℝ) / (dyadic a).den = (a : ℝ) / 1024 := by
    rw [← Rat.cast_def]
    norm_num [dyadic]
  have h := hornerPair_mul_cast cs (dyadic a).num (dyadic a).den (dyadic a).pos
  rw [hornerFold_eq_sum, hlen, hr] at h
  have he : ∑ i ∈ Finset.range (n + 1), (cs.getD i 0 : ℝ) * ((a : ℝ) / 1024) ^ i =
      ∑ i ∈ Finset.range (n + 1), c i * ((a : ℝ) / 1024) ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hc i (Finset.mem_range.mp hi)]
  rw [he] at h
  have hd : (0 : ℝ) < (dyadic a).den := by exact_mod_cast (dyadic a).pos
  apply mul_left_cancel₀ hd.ne'
  change (dyadic a).den * ((hornerPair (dyadic a).num (dyadic a).den cs).1 : ℝ) = _
  rw [h, pow_succ]
  ring

private lemma eval_bmM_dyadic (n : ℕ) (cs : List ℤ) (hcs : (List.range (n + 1)).map (LintF n) = cs)
    (a : ℤ) : (bmM n).eval ((a : ℝ) / 1024) =
      (hornerAt cs a : ℝ) / (16 ^ n * ((dyadic a).den : ℝ) ^ n) := by
  rw [hornerAt_cast cs n a (fun i => (LintF n i : ℝ)) (by rw [← hcs]; simp)]
  · unfold bmM
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bmL_eq_LintF]
    field_simp
  · intro i hi
    rw [← hcs]; simp [List.getD_eq_getElem?_getD, hi]

private lemma eval_narayanaN_dyadic (n : ℕ) (cs : List ℤ)
    (hcs : (List.range (n + 1)).map (NintF n) = cs)
    (a : ℤ) : (narayanaN n).eval ((a : ℝ) / 1024) =
      (hornerAt cs a : ℝ) / ((dyadic a).den : ℝ) ^ n := by
  rw [hornerAt_cast cs n a (fun i => (NintF n i : ℝ)) (by rw [← hcs]; simp)]
  · unfold narayanaN
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← narC, narC_eq_NintF]
    field_simp
  · intro i hi
    rw [← hcs]; simp [List.getD_eq_getElem?_getD, hi]

/-- The Boolean certificate check. -/
private def checkN (n : ℕ) (cm cn l : List ℤ) : Bool :=
  l.length == 2 * n + 1 &&
  (List.range (2 * n)).all (fun i => decide (l.getD i 0 < l.getD (i + 1) 0)) &&
  decide (l.getD (2 * n) 0 ≤ 0) &&
  (List.range n).all (fun j =>
    decide (hornerAt cm (l.getD (2 * j) 0) * hornerAt cm (l.getD (2 * j + 1) 0) < 0) &&
    decide (hornerAt cn (l.getD (2 * j + 1) 0) * hornerAt cn (l.getD (2 * j + 2) 0) < 0))

private lemma bmInterlace_of_check (n : ℕ) (hn : 1 ≤ n) (cm cn l : List ℤ)
    (hcm : (List.range (n + 1)).map (LintF n) = cm) (hcn : (List.range (n + 1)).map (NintF n) = cn)
    (h : checkN n cm cn l = true) : BMInterlace n := by
  simp only [checkN, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h
  have hden (a : ℤ) : (0 : ℝ) < (dyadic a).den := by exact_mod_cast (dyadic a).pos
  refine bmInterlace_of_points n hn (fun i => ((l.getD i 0 : ℤ) : ℝ) / 1024) ?_ ?_ ?_ ?_
  · intro i hi
    have := h1 i hi
    have : ((l.getD i 0 : ℤ) : ℝ) < ((l.getD (i+1) 0 : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · have : ((l.getD (2*n) 0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h2
    linarith
  · intro j hj
    rw [eval_bmM_dyadic n cm hcm, eval_bmM_dyadic n cm hcm, div_mul_div_comm]
    apply div_neg_of_neg_of_pos
    · exact_mod_cast (h3 j hj).1
    · have hd₁ := hden (l.getD (2 * j) 0)
      have hd₂ := hden (l.getD (2 * j + 1) 0)
      positivity
  · intro j hj
    rw [eval_narayanaN_dyadic n cn hcn, eval_narayanaN_dyadic n cn hcn, div_mul_div_comm]
    apply div_neg_of_neg_of_pos
    · exact_mod_cast (h3 j hj).2
    · have hd₁ := hden (l.getD (2 * j + 1) 0)
      have hd₂ := hden (l.getD (2 * j + 2) 0)
      positivity

/-- Reuse one checked common-weight row in all coefficient computations. -/
private lemma bmInterlace_of_factored_check (n : ℕ) (hn : 1 ≤ n)
    (weights : List ℕ) (cm cn l : List ℤ) (hw : factorRow n = weights)
    (hcm : (List.range (n + 1)).map (fun i =>
      (bmFromRow weights n i : ℤ) ^ 2 -
        (if i = 0 then 0 else (bmFromRow weights n (i - 1) : ℤ)) *
          (bmFromRow weights n (i + 1) : ℤ)) = cm)
    (hcn : (List.range (n + 1)).map (NintF n) = cn)
    (h : checkN n cm cn l = true) : BMInterlace n := by
  apply bmInterlace_of_check n hn cm cn l
  · rw [← hcm]
    apply List.map_congr_left
    intro i _
    simp only [LintF, bmDF_eq_fromRow, hw]
  · exact hcn
  · exact h

end SmallCasesCore

section SmallCases

/-- Quote coefficient data, leaving the kernel to verify the same integer formulas. -/
local elab "quoteCoeffs% " t:term : term => Lean.withoutExporting do
  Lean.Elab.Term.elabTerm (← `(eval% $t)) none

/-- Quote data and validate all four certificate obligations by kernel computation. -/
local macro "bm_interlace_certificate " n:term ", " pts:term : tactic =>
  `(tactic| (
    apply bmInterlace_of_factored_check $n (by decide +kernel)
      (quoteCoeffs% factorRow $n)
      (quoteCoeffs% (List.range ($n + 1)).map (LintF $n))
      (quoteCoeffs% (List.range ($n + 1)).map (NintF $n)) $pts <;> decide +kernel))

/-! Certificates for `1 ≤ n ≤ 35` (generated tables, checked by the kernel). -/

private def ptT1 : List ℤ := [-4096, -2048, 0]

private theorem bmInterlace_1 : BMInterlace 1 := by
  bm_interlace_certificate 1, ptT1

private def ptT2 : List ℤ := [-6144, -3072, -2048, -512, 0]

private theorem bmInterlace_2 : BMInterlace 2 := by
  bm_interlace_certificate 2, ptT2

private def ptT3 : List ℤ := [-10240, -5120, -3072, -1280, -512, -256, 0]

private theorem bmInterlace_3 : BMInterlace 3 := by
  bm_interlace_certificate 3, ptT3

private def ptT4 : List ℤ := [-14336, -8192, -5120, -2048, -1024, -768, -512, -256, 0]

private theorem bmInterlace_4 : BMInterlace 4 := by
  bm_interlace_certificate 4, ptT4

private def ptT5 : List ℤ := [-19456, -12288, -7168, -3072, -2048, -1280, -768, -512, -256, -128, 0]

private theorem bmInterlace_5 : BMInterlace 5 := by
  bm_interlace_certificate 5, ptT5

private def ptT6 : List ℤ := [-26624, -16384, -10240, -4096, -3072, -1792, -1024, -768, -512, -320,
    -256, -128, 0]

private theorem bmInterlace_6 : BMInterlace 6 := by
  bm_interlace_certificate 6, ptT6

private def ptT7 : List ℤ := [-33792, -20480, -12288, -5632, -4096, -2304, -2048, -1152, -768, -512,
    -384, -256, -128, -64, 0]

private theorem bmInterlace_7 : BMInterlace 7 := by
  bm_interlace_certificate 7, ptT7

private def ptT8 : List ℤ := [-40960, -25600, -16384, -7168, -5120, -3072, -2048, -1536, -1024,
    -768, -512, -384, -256, -192, -128, -64, 0]

private theorem bmInterlace_8 : BMInterlace 8 := by
  bm_interlace_certificate 8, ptT8

private def ptT9 : List ℤ := [-50176, -31744, -19456, -9216, -6144, -4096, -3072, -2048, -1536,
    -1152, -768, -640, -512, -320, -256, -128, -64, -48, 0]

private theorem bmInterlace_9 : BMInterlace 9 := by
  bm_interlace_certificate 9, ptT9

private def ptT10 : List ℤ := [-59392, -37888, -23552, -11264, -7168, -4608, -4096, -2560, -2048,
    -1408, -1024, -896, -768, -512, -384, -256, -192, -128, -64, -32, 0]

private theorem bmInterlace_10 : BMInterlace 10 := by
  bm_interlace_certificate 10, ptT10

private def ptT11 : List ℤ := [-69632, -45056, -27648, -13312, -9216, -5632, -4096, -3072, -2048,
    -1792, -1536, -1152, -768, -640, -512, -384, -256, -192, -128, -96, -64, -32, 0]

private theorem bmInterlace_11 : BMInterlace 11 := by
  bm_interlace_certificate 11, ptT11

private def ptT12 : List ℤ := [-81920, -52224, -32768, -15360, -11264, -6656, -5120, -3584, -3072,
    -2176, -2048, -1408, -1024, -896, -768, -512, -384, -320, -256, -192, -128, -96, -64, -32, 0]

private theorem bmInterlace_12 : BMInterlace 12 := by
  bm_interlace_certificate 12, ptT12

private def ptT13 : List ℤ := [-93184, -60416, -37888, -17408, -12288, -8192, -6144, -4352, -3072,
    -2560, -2048, -1664, -1536, -1088, -768, -704, -512, -448, -384, -256, -192, -160, -128, -64,
    -32, -24, 0]

private theorem bmInterlace_13 : BMInterlace 13 := by
  bm_interlace_certificate 13, ptT13

private def ptT14 : List ℤ := [-106496, -68608, -43008, -19456, -14336, -9216, -7168, -5120, -4096,
    -3072, -2560, -2048, -1536, -1280, -1024, -896, -768, -576, -512, -384, -320, -256, -192, -128,
    -96, -64, -32, -16, 0]

private theorem bmInterlace_14 : BMInterlace 14 := by
  bm_interlace_certificate 14, ptT14

private def ptT15 : List ℤ := [-120832, -77824, -49152, -22528, -16384, -10240, -8192, -5632, -5120,
    -3584, -3072, -2304, -2048, -1536, -1280, -1088, -896, -768, -640, -512, -384, -320, -256, -192,
    -160, -128, -96, -64, -32, -16, 0]

private theorem bmInterlace_15 : BMInterlace 15 := by
  bm_interlace_certificate 15, ptT15

private def ptT16 : List ℤ := [-135168, -87040, -55296, -25600, -18432, -11776, -9216, -6656, -5120,
    -4096, -3072, -2688, -2048, -1792, -1536, -1280, -1024, -896, -768, -640, -512, -448, -384,
    -288, -256, -192, -128, -96, -64, -48, -32, -16, 0]

private theorem bmInterlace_16 : BMInterlace 16 := by
  bm_interlace_certificate 16, ptT16

private def ptT17 : List ℤ := [-150528, -97280, -62464, -28672, -20480, -13312, -10240, -7424,
    -6144, -4608, -4096, -3072, -2560, -2176, -2048, -1536, -1280, -1088, -896, -768, -640, -512,
    -448, -384, -320, -256, -192, -160, -128, -96, -64, -48, -32, -16, 0]

private theorem bmInterlace_17 : BMInterlace 17 := by
  bm_interlace_certificate 17, ptT17

private def ptT18 : List ℤ := [-166912, -108544, -68608, -31744, -23552, -14848, -11264, -8192,
    -7168, -5120, -4096, -3584, -3072, -2432, -2048, -1728, -1536, -1280, -1024, -896, -768, -640,
    -512, -448, -384, -320, -256, -224, -192, -144, -128, -80, -64, -40, -32, -12, 0]

private theorem bmInterlace_18 : BMInterlace 18 := by
  bm_interlace_certificate 18, ptT18

private def ptT19 : List ℤ := [-184320, -119808, -75776, -34816, -25600, -16384, -12288, -9216,
    -7168, -5888, -5120, -3840, -3072, -2816, -2048, -1920, -1536, -1408, -1280, -1088, -896, -768,
    -640, -576, -512, -416, -384, -288, -256, -192, -160, -128, -96, -80, -64, -32, -16, -12, 0]

private theorem bmInterlace_19 : BMInterlace 19 := by
  bm_interlace_certificate 19, ptT19

private def ptT20 : List ℤ := [-201728, -131072, -83968, -38912, -27648, -18432, -14336, -10240,
    -8192, -6400, -5120, -4352, -4096, -3072, -2560, -2176, -2048, -1664, -1536, -1216, -1024, -896,
    -768, -704, -640, -512, -448, -384, -320, -256, -224, -192, -128, -112, -96, -64, -48, -32, -16,
    -10, 0]

private theorem bmInterlace_20 : BMInterlace 20 := by
  bm_interlace_certificate 20, ptT20

private def ptT21 : List ℤ := [-221184, -143360, -92160, -41984, -30720, -19456, -15360, -11264,
    -9216, -7168, -6144, -4864, -4096, -3456, -3072, -2560, -2048, -1856, -1536, -1408, -1280,
    -1088, -896, -832, -768, -608, -512, -448, -384, -320, -256, -224, -192, -160, -128, -96, -80,
    -64, -48, -32, -16, -8, 0]

private theorem bmInterlace_21 : BMInterlace 21 := by
  bm_interlace_certificate 21, ptT21

private def ptT22 : List ℤ := [-240640, -156672, -100352, -46080, -33792, -21504, -16384, -12288,
    -10240, -7680, -6144, -5376, -4096, -3840, -3072, -2816, -2560, -2048, -1792, -1536, -1280,
    -1216, -1024, -896, -768, -704, -640, -544, -512, -416, -384, -288, -256, -224, -192, -144,
    -128, -96, -64, -56, -32, -24, -16, -8, 0]

private theorem bmInterlace_22 : BMInterlace 22 := by
  bm_interlace_certificate 22, ptT22

private def ptT23 : List ℤ := [-261120, -169984, -108544, -50176, -36864, -23552, -18432, -13312,
    -11264, -8704, -7168, -5888, -5120, -4096, -3584, -3072, -2560, -2304, -2048, -1792, -1536,
    -1344, -1280, -1088, -896, -832, -768, -640, -512, -480, -448, -384, -320, -272, -256, -192,
    -160, -128, -112, -96, -64, -48, -32, -24, -16, -8, 0]

private theorem bmInterlace_23 : BMInterlace 23 := by
  bm_interlace_certificate 23, ptT23

private def ptT24 : List ℤ := [-282624, -184320, -117760, -54272, -39936, -25600, -20480, -14336,
    -12288, -9216, -8192, -6400, -5120, -4608, -4096, -3328, -3072, -2560, -2048, -1920, -1792,
    -1536, -1280, -1216, -1024, -960, -768, -736, -640, -576, -512, -448, -384, -320, -288, -256,
    -192, -176, -160, -128, -96, -80, -64, -48, -32, -24, -16, -6, 0]

private theorem bmInterlace_24 : BMInterlace 24 := by
  bm_interlace_certificate 24, ptT24

private def ptT25 : List ℤ := [-304128, -198656, -128000, -58368, -43008, -27648, -21504, -15872,
    -13312, -10240, -8192, -6912, -6144, -4992, -4096, -3712, -3072, -2816, -2560, -2176, -2048,
    -1664, -1536, -1344, -1280, -1056, -896, -832, -768, -640, -576, -512, -448, -384, -320, -304,
    -256, -224, -192, -160, -128, -112, -96, -80, -64, -48, -32, -20, -16, -6, 0]

private theorem bmInterlace_25 : BMInterlace 25 := by
  bm_interlace_certificate 25, ptT25

private def ptT26 : List ℤ := [-327680, -214016, -137216, -63488, -46080, -29696, -23552, -16896,
    -14336, -10752, -9216, -7424, -6144, -5376, -5120, -4096, -3584, -3072, -2560, -2432, -2048,
    -1856, -1536, -1472, -1280, -1152, -1024, -960, -896, -768, -640, -576, -512, -480, -384, -352,
    -320, -288, -256, -208, -192, -160, -128, -112, -96, -64, -48, -40, -32, -20, -16, -6, 0]

private theorem bmInterlace_26 : BMInterlace 26 := by
  bm_interlace_certificate 26, ptT26

private def ptT27 : List ℤ := [-351232, -229376, -147456, -67584, -50176, -31744, -24576, -18432,
    -15360, -11776, -10240, -8192, -7168, -5888, -5120, -4352, -4096, -3328, -3072, -2560, -2304,
    -2048, -1792, -1664, -1536, -1280, -1152, -1056, -896, -832, -768, -672, -640, -544, -512, -416,
    -384, -320, -288, -256, -224, -192, -160, -144, -128, -96, -80, -64, -48, -40, -32, -16, -8, -6,
    0]

private theorem bmInterlace_27 : BMInterlace 27 := by
  bm_interlace_certificate 27, ptT27

private def ptT28 : List ℤ := [-375808, -245760, -157696, -72704, -53248, -34816, -26624, -19456,
    -16384, -12800, -10240, -8704, -7168, -6400, -5120, -4736, -4096, -3584, -3072, -2816, -2560,
    -2240, -2048, -1792, -1536, -1472, -1280, -1152, -1024, -960, -896, -768, -640, -608, -512,
    -480, -448, -384, -352, -320, -256, -240, -192, -176, -160, -128, -112, -96, -80, -64, -48, -32,
    -24, -16, -8, -5, 0]

private theorem bmInterlace_28 : BMInterlace 28 := by
  bm_interlace_certificate 28, ptT28

private def ptT29 : List ℤ := [-401408, -263168, -168960, -77824, -57344, -36864, -28672, -20992,
    -17408, -13824, -11264, -9472, -8192, -6912, -6144, -5120, -4096, -3968, -3584, -3072, -2560,
    -2432, -2048, -1920, -1792, -1600, -1536, -1280, -1152, -1056, -896, -864, -768, -704, -640,
    -576, -512, -448, -384, -352, -320, -288, -256, -224, -192, -160, -144, -128, -96, -80, -64,
    -56, -48, -32, -24, -16, -8, -5, 0]

private theorem bmInterlace_29 : BMInterlace 29 := by
  bm_interlace_certificate 29, ptT29

private def ptT30 : List ℤ := [-428032, -280576, -180224, -82944, -60416, -38912, -30720, -22528,
    -18432, -14336, -12288, -9984, -8192, -7296, -6144, -5504, -5120, -4224, -4096, -3328, -3072,
    -2688, -2560, -2176, -2048, -1728, -1536, -1408, -1280, -1152, -1024, -960, -896, -768, -704,
    -640, -576, -512, -448, -416, -384, -336, -320, -256, -224, -208, -192, -160, -128, -112, -96,
    -80, -64, -48, -40, -32, -24, -16, -8, -4, 0]

private theorem bmInterlace_30 : BMInterlace 30 := by
  bm_interlace_certificate 30, ptT30

private def ptT31 : List ℤ := [-454656, -297984, -191488, -88064, -64512, -41984, -32768, -24064,
    -19456, -15360, -13312, -10752, -9216, -7680, -7168, -5888, -5120, -4608, -4096, -3584, -3072,
    -2816, -2560, -2304, -2048, -1920, -1792, -1536, -1408, -1280, -1152, -1056, -896, -864, -768,
    -704, -640, -576, -512, -480, -448, -384, -352, -320, -288, -256, -224, -192, -160, -144, -128,
    -112, -96, -80, -64, -48, -32, -28, -16, -14, -8, -4, 0]

private theorem bmInterlace_31 : BMInterlace 31 := by
  bm_interlace_certificate 31, ptT31

private def ptT32 : List ℤ := [-483328, -317440, -203776, -94208, -68608, -44032, -34816, -25600,
    -20480, -16384, -14336, -11520, -10240, -8448, -7168, -6272, -5120, -4864, -4096, -3840, -3584,
    -3072, -2560, -2496, -2304, -2048, -1792, -1664, -1536, -1408, -1280, -1152, -1024, -960, -896,
    -800, -768, -640, -576, -544, -512, -448, -384, -352, -320, -288, -256, -224, -192, -176, -160,
    -128, -112, -96, -80, -72, -64, -48, -32, -24, -16, -12, -8, -4, 0]

private theorem bmInterlace_32 : BMInterlace 32 := by
  bm_interlace_certificate 32, ptT32

private def ptT33 : List ℤ := [-512000, -335872, -216064, -99328, -72704, -47104, -36864, -27136,
    -22528, -17408, -14336, -12288, -10240, -8960, -8192, -6656, -6144, -5120, -4608, -4096, -3584,
    -3328, -3072, -2688, -2560, -2176, -2048, -1792, -1664, -1536, -1408, -1280, -1152, -1056, -896,
    -864, -768, -736, -640, -608, -576, -512, -448, -416, -384, -336, -320, -272, -256, -208, -192,
    -160, -144, -128, -112, -96, -80, -64, -48, -40, -32, -24, -16, -12, -8, -4, 0]

private theorem bmInterlace_33 : BMInterlace 33 := by
  bm_interlace_certificate 33, ptT33

private def ptT34 : List ℤ := [-541696, -355328, -229376, -105472, -77824, -50176, -38912, -28672,
    -23552, -18432, -15360, -12800, -11264, -9472, -8192, -7168, -6144, -5504, -5120, -4352, -4096,
    -3584, -3072, -2880, -2560, -2368, -2048, -1984, -1792, -1600, -1536, -1344, -1280, -1152,
    -1024, -960, -896, -800, -768, -672, -640, -576, -512, -464, -448, -384, -352, -320, -288, -256,
    -224, -208, -192, -160, -128, -120, -96, -88, -80, -64, -48, -40, -32, -24, -16, -12, -8, -3, 0]

private theorem bmInterlace_34 : BMInterlace 34 := by
  bm_interlace_certificate 34, ptT34

private def ptT35 : List ℤ := [-572416, -375808, -241664, -111616, -81920, -53248, -40960, -30720,
    -24576, -19456, -16384, -13824, -12288, -9984, -9216, -7680, -7168, -5888, -5120, -4608, -4096,
    -3712, -3584, -3072, -2816, -2560, -2304, -2112, -2048, -1728, -1536, -1472, -1280, -1248,
    -1152, -1056, -960, -896, -768, -736, -640, -608, -576, -512, -448, -432, -384, -352, -320,
    -288, -256, -240, -224, -192, -160, -144, -128, -112, -96, -80, -64, -56, -48, -40, -32, -24,
    -16, -12, -8, -3, 0]

private theorem bmInterlace_35 : BMInterlace 35 := by
  bm_interlace_certificate 35, ptT35

/-- The interlacing data `BMInterlace n` holds for `1 ≤ n ≤ 35`, by kernel-checked
certificates. -/
theorem bmInterlace_small (n : ℕ) (hn : 1 ≤ n) (h35 : n ≤ 35) : BMInterlace n := by
  interval_cases n <;>
    simp_all only [bmInterlace_1, bmInterlace_2, bmInterlace_3, bmInterlace_4, bmInterlace_5,
      bmInterlace_6, bmInterlace_7, bmInterlace_8, bmInterlace_9, bmInterlace_10, bmInterlace_11,
      bmInterlace_12, bmInterlace_13, bmInterlace_14, bmInterlace_15, bmInterlace_16,
      bmInterlace_17, bmInterlace_18, bmInterlace_19, bmInterlace_20, bmInterlace_21,
      bmInterlace_22, bmInterlace_23, bmInterlace_24, bmInterlace_25, bmInterlace_26,
      bmInterlace_27, bmInterlace_28, bmInterlace_29, bmInterlace_30, bmInterlace_31,
      bmInterlace_32, bmInterlace_33, bmInterlace_34, bmInterlace_35]

end SmallCases

end RealRooted.BorosMoll
