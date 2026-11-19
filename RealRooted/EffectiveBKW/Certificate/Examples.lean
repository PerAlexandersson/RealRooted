module

public import RealRooted.EffectiveBKW.Certificate.BranchSign
public import RealRooted.EffectiveBKW.Certificate.SignGrid
import Mathlib.Tactic.Linarith

/-! # Regression examples for effective BKW certificates -/

@[expose] public section

namespace RealRooted.EffectiveBKW.Examples

open Set BigDescents321.SmallCases

/-- A two-cell certificate for the positive root of `y² - t` on `[1,4]`. -/
def sqrtBranch : Branch where
  curve := [[0, -1], [], [1]]
  cells := [⟨⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩, ⟨3, 2⟩⟩,
    ⟨⟨2, 1⟩, ⟨4, 1⟩, ⟨1, 1⟩, ⟨5, 2⟩⟩]
  lo := ⟨1, 1⟩
  hi := ⟨4, 1⟩

/-- Kernel replay of both cells and the junction. -/
theorem sqrtBranch_check : sqrtBranch.check = true := by decide +kernel

/-- The certified toy branch is continuous. -/
theorem sqrtBranch_continuousOn : ContinuousOn sqrtBranch.y (Icc 1 4) := by
  simpa [sqrtBranch, QNum.val] using (Branch.check_sound sqrtBranch_check).1

/-- The toy branch solves the stated polynomial equation. -/
theorem sqrtBranch_sq {t : ℝ} (ht : t ∈ Icc 1 4) : sqrtBranch.y t ^ 2 = t := by
  have ht' : t ∈ Icc sqrtBranch.lo.val sqrtBranch.hi.val := by
    simpa [sqrtBranch, QNum.val] using ht
  have he := (Branch.check_sound sqrtBranch_check).2.1 t ht'
  generalize sqrtBranch.y t = y at he ⊢
  simp only [sqrtBranch, IntPoly2.eval, IntPoly.eval, IntPoly.polynomial,
    ofList_cons, ofList_nil, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_zero, Int.cast_zero,
    Int.cast_neg, Int.cast_one] at he
  nlinarith

/-- A positive sign condition on the toy branch. -/
def sqrtSign : SignCond where
  f := [[1], [1]]
  boxes := sqrtBranch.cells.zipIdx.map (fun v => (v.2, v.1))

/-- Kernel replay of the full-cell sign condition. -/
theorem sqrtSign_check : sqrtSign.check sqrtBranch = true := by decide +kernel

example {t : ℝ} (ht : t ∈ Icc 1 4) : 0 < 1 + sqrtBranch.y t := by
  have ht' : t ∈ Icc sqrtBranch.lo.val sqrtBranch.hi.val := by
    simpa [sqrtBranch, QNum.val] using ht
  have hp := SignCond.check_sound sqrtBranch_check sqrtSign_check ht'
  simpa [sqrtSign, IntPoly2.eval, IntPoly.eval, IntPoly.polynomial, ofList_cons] using hp

/-- A known degree-ten polynomial, represented only by checked list products. -/
def degreeTen : IntPoly :=
  (List.range 10).foldl (fun p k => mulList p [-((k : ℤ) + 1), 1]) [1]

/-- Half-integer samples separate its ten integer roots. -/
def degreeTenGrid : SignGrid where
  p := degreeTen
  pts := (List.range 11).map (fun k => ⟨2 * (k : ℤ) + 1, 2⟩)

/-- Kernel replay of the degree-ten sign grid. -/
theorem degreeTenGrid_check : degreeTenGrid.check = true := by decide +kernel

example : degreeTen.polynomial.Splits ∧ degreeTen.polynomial.roots.Nodup :=
  ⟨(SignGrid.check_sound degreeTenGrid_check).2.1,
    (SignGrid.check_sound degreeTenGrid_check).2.2.1⟩

example : IntPoly2.posOnBox [[1, 0, 1], [], [1]]
    ⟨0, 1⟩ ⟨1, 1⟩ ⟨0, 1⟩ ⟨1, 1⟩ = true := by decide +kernel

example : (IsolatedRoot.mk [-2, 0, 1] ⟨1, 1⟩ ⟨2, 1⟩ false).check = true := by
  decide +kernel

example : (IsolatedRoot.mk [2, 0, -1] ⟨1, 1⟩ ⟨2, 1⟩ true).check = true := by
  decide +kernel

example : IntPoly.posOn [1] ⟨0, 0⟩ ⟨1, 1⟩ = false := by decide +kernel

example : IntPoly.posOn [-1] ⟨0, 1⟩ ⟨1, 1⟩ = false := by decide +kernel

example : IntPoly.posOn [1] ⟨2, 1⟩ ⟨1, 1⟩ = false := by decide +kernel

example : IntPoly.posOn [1, 1] ⟨1, 2⟩ ⟨2, 4⟩ = true := by decide +kernel

example : ({ sqrtSign with boxes := [] } : SignCond).check sqrtBranch = false := by
  decide +kernel

/-- The phase-0 AMP polynomial, used only as reproducible synthetic test data. -/
def pilotPolynomial : IntPoly2 := [
  [0, 0, 0, 0, 0, -1584, 20781, -99779, 215721, -305011, 503063, -799057, 755003, -346501, 63056,
    -12664, 6856, 116],
  [0, 0, 0, 0, 3168, -44724, 181941, -312497, 451811, -881667, 1147957, -685741, 144297, -22661,
    17834, 282],
  [0, 0, -3168, 19386, 44636, -326056, 36734, -416730, 1342626, -438798, -154574, -99272, -4718,
    -66],
  [0, -4752, 40179, -226469, 89831, -147679, 1126110, -257282, -429740, -157918, -31848, -432],
  [3168, -30456, -33341, 174721, 770731, 861335, 299388, 31478, -3390, -34],
  [18204, 42482, 249337, 307059, 320817, 58021, 11930, 150]]

/-- Multiplying AMP by `-t` raises the parameter degree to eighteen. -/
def synthetic : IntPoly2 := pilotPolynomial.map (mulList [0, -1])

/-- One full-size box of the phase-0 path-cube certificate, at bidegree `(18,5)`.
The complete benchmark lives outside the library; checking boxes as separate theorems is
much faster than one `List.all` over all of them. -/
theorem synthetic_posOnBox :
    synthetic.posOnBox ⟨-170931182131, 4294967296⟩ ⟨-542710147080149, 13743895347200⟩
      ⟨43550297971, 16777216⟩ ⟨44398868247, 16777216⟩ = true := by
  decide +kernel

end RealRooted.EffectiveBKW.Examples
