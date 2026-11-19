module

public import RealRooted.EffectiveBKW.Certificate.Branch

/-!
# Sign conditions on a certified root branch

Phase 1 uses full-cell references, as in the recommended pilot certificate.
Every branch cell must be referenced and every reference must equal its source
cell. Arbitrary subdivided boxes are deliberately rejected: containment alone
would not prove that such boxes contain the branch.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open Set

/-- A strict sign condition, with explicit references to full branch cells. -/
structure SignCond where
  /-- The polynomial whose sign is certified. -/
  f : IntPoly2
  /-- Whether the certified sign is negative. -/
  neg : Bool := false
  /-- Cell index together with its full rectangle. -/
  boxes : List (ℕ × BranchCell)
  deriving Repr

/-- Check full-cell coverage, reference integrity and Bernstein positivity. -/
def SignCond.check (c : SignCond) (b : Branch) : Bool :=
  (List.range b.cells.length).all (fun i => c.boxes.any (fun v => v.1 == i)) &&
    c.boxes.all (fun v => decide (b.cells[v.1]? = some v.2) &&
      (c.f.signed c.neg).posOnBox v.2.tlo v.2.thi v.2.lo v.2.hi)

/-- A checked sign condition has the requested strict sign everywhere on a checked branch. -/
theorem SignCond.check_sound {c : SignCond} {b : Branch} (hb : b.check = true)
    (h : c.check b = true) {t : ℝ} (ht : t ∈ Icc b.lo.val b.hi.val) :
    0 < (if c.neg then -1 else 1 : ℝ) * c.f.eval t (b.y t) := by
  have hcov : Branch.covers b.lo b.hi b.cells = true := by
    simp only [Branch.check, Bool.and_eq_true] at hb
    exact hb.1.1.2
  obtain ⟨cell, hcell, htc⟩ := Branch.covers_sound hcov ht
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hcell
  simp only [check, Bool.and_eq_true] at h
  have href := List.all_eq_true.mp h.1 i (List.mem_range.mpr hi)
  obtain ⟨v, hv, hvi⟩ := List.any_eq_true.mp href
  have hbox := List.all_eq_true.mp h.2 v hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbox
  have heq : v.2 = cell := by
    have hvi' : v.1 = i := beq_iff_eq.mp hvi
    rw [hvi', List.getElem?_eq_getElem hi, hci] at hbox
    exact Option.some.inj hbox.1.symm
  have hy := (Branch.check_sound hb).2.2 cell hcell t htc
  rw [heq] at hbox
  have hp := IntPoly2.posOnBox_sound hbox.2 htc hy
  simpa only [IntPoly2.eval_signed] using hp

end RealRooted.EffectiveBKW
