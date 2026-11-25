module

public import RealRooted.EffectiveBKW.Certificate.IsolatedRoot
public import Mathlib.Topology.Instances.Real.Lemmas
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
