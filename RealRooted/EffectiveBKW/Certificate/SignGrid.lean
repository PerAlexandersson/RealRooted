module

public import RealRooted.EffectiveBKW.Certificate.ListPoly
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Roots
import RealRooted.Mathlib.Algebra.Polynomial.IntervalSignChanges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact rational sign grids

Integer-scaled Horner evaluation checks successive strict sign changes. The
existing interval sign-change theorem supplies splitting and simple roots.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open Polynomial BigDescents321.SmallCases Set

/-- The coefficient-list length bounds the polynomial degree, including trailing zeros. -/
theorem IntPoly.natDegree_le (p : IntPoly) : p.polynomial.natDegree ≤ p.length - 1 := by
  induction p with
  | nil => simp [IntPoly.polynomial]
  | cons a p ih =>
    cases p with
    | nil => simp [IntPoly.polynomial, ofList_singleton]
    | cons b p =>
      change (C (a : ℝ) + X * ofList (b :: p)).natDegree ≤ _
      apply (natDegree_add_le _ _).trans
      apply max_le
      · simp
      · have hm := (natDegree_mul_le (p := (X : ℝ[X])) (q := ofList (b :: p)))
        simp only [natDegree_X, IntPoly.polynomial, List.length_cons] at ih hm ⊢
        lia

/-- A univariate polynomial and an increasing list of rational sample points. -/
structure SignGrid where
  /-- Polynomial coefficients. -/
  p : IntPoly
  /-- Rational sample points, in increasing order. -/
  pts : List QNum
  deriving Repr

/-- A total accessor; the checker ensures that every accessed point exists. -/
def SignGrid.point (c : SignGrid) (i : ℕ) : QNum := c.pts[i]?.getD ⟨0, 1⟩

/-- The degree inferred from the number of gaps. -/
def SignGrid.degree (c : SignGrid) : ℕ := c.pts.length - 1

/-- Integer evaluations at the grid points. -/
def SignGrid.value (c : SignGrid) (i : ℕ) : ℤ :=
  c.p.evalScaled (c.point i).num (c.point i).den

/-- Check denominators, ordering, degree bound and strict sign changes. -/
def SignGrid.check (c : SignGrid) : Bool :=
  decide (c.pts ≠ []) && c.pts.all QNum.valid &&
    decide (c.pts.Pairwise (fun a b => a.lt b = true)) &&
    decide (c.p.length ≤ c.pts.length) &&
    (List.range c.pts.length).all (fun i => decide (c.value i ≠ 0)) &&
    (List.range c.degree).all (fun i => decide (c.value i * c.value (i + 1) < 0))

/-- A checked grid accounts for every root, all of which are simple and between the endpoints. -/
theorem SignGrid.check_sound {c : SignGrid} (h : c.check = true) :
    c.p.polynomial.natDegree = c.degree ∧ c.p.polynomial.Splits ∧
      c.p.polynomial.roots.Nodup ∧
      ∀ z ∈ c.p.polynomial.roots, (c.point 0).val < z ∧ z < (c.point c.degree).val := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hne, hv⟩, ho⟩, hd⟩, hnz⟩, hs⟩ := h
  have hlen : c.pts.length = c.degree + 1 := by
    have : 0 < c.pts.length := List.length_pos_iff.mpr hne
    dsimp [degree]
    lia
  have hpoint (i : ℕ) (hi : i < c.pts.length) : c.point i = c.pts[i] := by
    simp [point, List.getElem?_eq_getElem hi]
  have hvalid (i : ℕ) (hi : i < c.pts.length) : (c.point i).valid = true := by
    rw [hpoint i hi]
    exact List.all_eq_true.mp hv _ (List.getElem_mem hi)
  let x : Fin (c.degree + 1) → ℝ := fun i => (c.point i).val
  have hx : StrictMono x := by
    intro i j hij
    have hi : i.val < c.pts.length := by lia
    have hj : j.val < c.pts.length := by lia
    apply QNum.lt_sound (hvalid i hi) (hvalid j hj)
    rw [hpoint i hi, hpoint j hj]
    exact List.pairwise_iff_getElem.mp ho _ _ hi hj hij
  have heval (i : ℕ) (hi : i < c.pts.length) :
      (c.value i : ℝ) = ((c.point i).den : ℝ) ^ c.p.length * c.p.eval (x ⟨i, by lia⟩) :=
    IntPoly.evalScaled_eq c.p (c.point i) (hvalid i hi)
  have hfac (i : ℕ) (hi : i < c.pts.length) :
      (0 : ℝ) < ((c.point i).den : ℝ) ^ c.p.length := by
    apply pow_pos
    exact_mod_cast (of_decide_eq_true (hvalid i hi) : 0 < (c.point i).den)
  have hp : c.p.polynomial ≠ 0 := by
    intro hp
    have hi : 0 < c.pts.length := by lia
    have hz : c.value 0 ≠ 0 := of_decide_eq_true
      (List.all_eq_true.mp hnz 0 (List.mem_range.mpr hi))
    have he := heval 0 hi
    simp only [IntPoly.eval, hp, Polynomial.eval_zero, mul_zero] at he
    exact hz (Int.cast_eq_zero.mp he)
  have hdegree : c.p.polynomial.natDegree ≤ c.degree := by
    have hb := c.p.natDegree_le
    dsimp [degree]
    lia
  have hsign (i : Fin c.degree) :
      c.p.polynomial.eval (x i.castSucc) * c.p.polynomial.eval (x i.succ) < 0 := by
    have hi : i.val < c.pts.length := by lia
    have hj : i.val + 1 < c.pts.length := by lia
    have hs' : c.value i * c.value (i + 1) < 0 := of_decide_eq_true
      (List.all_eq_true.mp hs i (List.mem_range.mpr i.isLt))
    have hsreal : (c.value i : ℝ) * (c.value (i + 1) : ℝ) < 0 := by exact_mod_cast hs'
    rw [heval i hi, heval (i + 1) hj] at hsreal
    have hf := mul_pos (hfac i hi) (hfac (i + 1) hj)
    have heq :
        (((c.point i).den : ℝ) ^ c.p.length * c.p.eval (x ⟨i, by lia⟩)) *
            (((c.point (i + 1)).den : ℝ) ^ c.p.length * c.p.eval (x ⟨i + 1, by lia⟩)) =
          (((c.point i).den : ℝ) ^ c.p.length *
            ((c.point (i + 1)).den : ℝ) ^ c.p.length) *
          (c.p.polynomial.eval (x i.castSucc) * c.p.polynomial.eval (x i.succ)) := by
      exact mul_mul_mul_comm _ _ _ _
    rw [heq] at hsreal
    rcases mul_neg_iff.mp hsreal with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact hb
    · exact (not_lt_of_gt hf ha).elim
  exact splits_nodup_roots_of_strict_sign_changes hp hdegree x hx hsign

end RealRooted.EffectiveBKW
