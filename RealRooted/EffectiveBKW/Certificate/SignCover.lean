module

public import RealRooted.EffectiveBKW.Certificate.Branch

/-!
# Reusing sign boxes across several branch cells

A positive polynomial can use a coarser cover than the root-branch certificate.
Every branch cell must be contained in a checked sign box; geometric containment
is checked in both coordinates, with valid rational denominators throughout.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open Set

/-- Check that one rational rectangle contains another, including denominator validity. -/
def BranchCell.contains (outer inner : BranchCell) : Bool :=
  outer.tlo.valid && outer.thi.valid && outer.lo.valid && outer.hi.valid &&
    inner.tlo.valid && inner.thi.valid && inner.lo.valid && inner.hi.valid &&
    outer.tlo.le inner.tlo && inner.thi.le outer.thi &&
    outer.lo.le inner.lo && inner.hi.le outer.hi

/-- Checked rectangle containment implies containment in both real coordinates. -/
theorem BranchCell.contains_sound {outer inner : BranchCell}
    (h : outer.contains inner = true) :
    inner.domain ⊆ outer.domain ∧ inner.strip ⊆ outer.strip := by
  simp only [contains, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hotl, hotu, hoyl, hoyu, hitl, hitu, hiyl, hiyu, htl, htu, hyl, hyu⟩ := h
  have htl' := QNum.le_sound hotl hitl htl
  have htu' := QNum.le_sound hitu hotu htu
  have hyl' := QNum.le_sound hoyl hiyl hyl
  have hyu' := QNum.le_sound hiyu hoyu hyu
  exact ⟨fun _ ht ↦ ⟨htl'.trans ht.1, ht.2.trans htu'⟩,
    fun _ hy ↦ ⟨hyl'.trans hy.1, hy.2.trans hyu'⟩⟩

/-- Positive sign boxes with a checked geometric cover of every root-branch cell. -/
structure SignCover where
  /-- Polynomial with strictly positive sign. -/
  f : IntPoly2
  /-- Rectangles on which positivity will be checked. -/
  boxes : List BranchCell
  deriving Repr

/-- Check full branch-cell coverage and positivity on each covering rectangle. -/
def SignCover.check (c : SignCover) (b : Branch) : Bool :=
  b.cells.all (fun inner ↦ c.boxes.any (fun outer ↦ outer.contains inner)) &&
    c.boxes.all (fun box ↦ c.f.posOnBox box.tlo box.thi box.lo box.hi)

/-- Positive covering boxes certify the sign on the entire checked branch. -/
theorem SignCover.check_sound {c : SignCover} {b : Branch}
    (hb : b.check = true) (h : c.check b = true) {t : ℝ}
    (ht : t ∈ Icc b.lo.val b.hi.val) : 0 < c.f.eval t (b.y t) := by
  have hcov : Branch.covers b.lo b.hi b.cells = true := by
    simp only [Branch.check, Bool.and_eq_true] at hb
    exact hb.1.1.2
  obtain ⟨inner, hi, hti⟩ := Branch.covers_sound hcov ht
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨outer, ho, hcontains⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp h.1 inner hi)
  obtain ⟨hdom, hstrip⟩ := BranchCell.contains_sound hcontains
  exact IntPoly2.posOnBox_sound (List.all_eq_true.mp h.2 outer ho) (hdom hti)
    (hstrip ((Branch.check_sound hb).2.2 inner hi t hti))

end RealRooted.EffectiveBKW
