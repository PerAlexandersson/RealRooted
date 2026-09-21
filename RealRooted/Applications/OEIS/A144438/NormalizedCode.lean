import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Basic

/-!
# Normalized chronological codes for the deco construction

A height-`h` chronological code has an entry in row `j + 1` bounded by
`j + 1`.  Normalized codes contain no entry equal to one.  Their eligible
exceptional starts are the adjacent pairs `(0, 2)` beginning in rows at least
three.  This is distinct from the `(0, 1)` pairs obtained only after transport
to minimum-insertion codes.
-/

namespace RealRooted.Applications.OEIS

/-- A chronological deco construction code of height `h`. -/
structure DecoCode (h : ℕ) where
  entry : Fin h → ℕ
  entry_lt : ∀ j, entry j < j.1 + 1

namespace DecoCode

instance {h : ℕ} : CoeFun (DecoCode h) fun _ => Fin h → ℕ :=
  ⟨DecoCode.entry⟩

@[ext] theorem ext {h : ℕ} {c d : DecoCode h}
    (hentry : ∀ j, c j = d j) : c = d := by
  cases c with
  | mk centry centry_lt =>
      cases d with
      | mk dentry dentry_lt =>
          congr
          funext j
          exact hentry j

/-- The canonical chronological code of height two. -/
def seed : DecoCode 2 where
  entry := fun _ => 0
  entry_lt := fun j => Nat.zero_lt_succ j.1

@[simp] theorem seed_apply (j : Fin 2) : seed j = 0 := rfl

end DecoCode

/-- A normalized chronological code has no entry equal to one. -/
structure DecoNormalizedCode (h : ℕ) extends DecoCode h where
  entry_ne_one : ∀ j, toDecoCode j ≠ 1

namespace DecoNormalizedCode

instance {h : ℕ} : CoeFun (DecoNormalizedCode h) fun _ => Fin h → ℕ :=
  ⟨fun c => c.toDecoCode.entry⟩

@[ext] theorem ext {h : ℕ} {c d : DecoNormalizedCode h}
    (hentry : ∀ j, c j = d j) : c = d := by
  cases c with
  | mk c hc =>
      cases d with
      | mk d hd =>
          have : c = d := DecoCode.ext hentry
          subst d
          rfl

/-- The first entry of every nonempty chronological code is forced to be zero. -/
theorem first_eq_zero {h : ℕ} (c : DecoNormalizedCode h) (hh : 0 < h) :
    c ⟨0, hh⟩ = 0 := by
  have hlt := c.toDecoCode.entry_lt ⟨0, hh⟩
  simp only at hlt
  lia

/-- In a normalized code, the second entry is also forced to be zero. -/
theorem second_eq_zero {h : ℕ} (c : DecoNormalizedCode h) (hh : 1 < h) :
    c ⟨1, hh⟩ = 0 := by
  have hlt := c.toDecoCode.entry_lt ⟨1, hh⟩
  have hne := c.entry_ne_one ⟨1, hh⟩
  simp only at hlt
  lia

/-- A zero-based position `j` is eligible when the chronological entries in
one-based rows `j + 1` and `j + 2` are `(0, 2)`, with `j + 1 ≥ 3`. -/
def Eligible {h : ℕ} (c : DecoNormalizedCode h) (j : Fin h) : Prop :=
  2 ≤ j.1 ∧ ∃ hj : j.1 + 1 < h, c j = 0 ∧ c ⟨j.1 + 1, hj⟩ = 2

/-- The finite set of eligible chronological `(0, 2)` starts. -/
noncomputable def eligibleStarts {h : ℕ}
    (c : DecoNormalizedCode h) : Finset (Fin h) := by
  classical
  exact (Finset.univ : Finset (Fin h)).filter c.Eligible

@[simp] theorem mem_eligibleStarts {h : ℕ} {c : DecoNormalizedCode h}
    {j : Fin h} : j ∈ c.eligibleStarts ↔ c.Eligible j := by
  simp [eligibleStarts]

/-- Eligible `(0, 2)` pairs cannot overlap from left to right. -/
theorem eligible_succ_ne {h : ℕ} {c : DecoNormalizedCode h} {i j : Fin h}
    (hi : c.Eligible i) (hj : c.Eligible j) : i.1 + 1 ≠ j.1 := by
  intro hij
  rcases hi with ⟨_, hiBound, _, hiTwo⟩
  rcases hj with ⟨_, _, hjZero, _⟩
  have hfin : (⟨i.1 + 1, hiBound⟩ : Fin h) = j := Fin.ext hij
  rw [hfin] at hiTwo
  simp_all

/-- Eligible `(0, 2)` pairs cannot overlap from right to left. -/
theorem eligible_ne_succ {h : ℕ} {c : DecoNormalizedCode h} {i j : Fin h}
    (hi : c.Eligible i) (hj : c.Eligible j) : i.1 ≠ j.1 + 1 := by
  exact fun hij => eligible_succ_ne hj hi hij.symm

/-- A choice of eligible pairs to turn back into exceptional `(1, 0)` pairs. -/
structure Decoration {h : ℕ} (c : DecoNormalizedCode h) where
  starts : Finset (Fin h)
  starts_subset : starts ⊆ c.eligibleStarts

namespace Decoration

/-- No two selected starts overlap. -/
theorem nonoverlap {h : ℕ} {c : DecoNormalizedCode h}
    (D : Decoration c) {i j : Fin h} (hi : i ∈ D.starts) (hj : j ∈ D.starts) :
    i.1 + 1 ≠ j.1 := by
  apply eligible_succ_ne
  · exact mem_eligibleStarts.mp (D.starts_subset hi)
  · exact mem_eligibleStarts.mp (D.starts_subset hj)

end Decoration

end DecoNormalizedCode

namespace DecoCode

/-- Replace every entry `1` by `0` and the entry immediately following it by
`2`.  The row bounds alone guarantee that the replacement by `2` is valid. -/
def normalize {h : ℕ} (c : DecoCode h) : DecoNormalizedCode h where
  entry j :=
    if c j = 1 then 0
    else if ∃ i : Fin h, i.1 + 1 = j.1 ∧ c i = 1 then 2
    else c j
  entry_lt j := by
    split
    · lia
    next hcurrent =>
      split
      · next hprevious =>
          rcases hprevious with ⟨i, hij, hi⟩
          have hilt := c.entry_lt i
          lia
      · exact c.entry_lt j
  entry_ne_one j := by
    split
    · simp
    next hcurrent =>
      split
      · exact by decide
      · exact hcurrent

end DecoCode

namespace DecoNormalizedCode.Decoration

/-- Replace every selected eligible `(0, 2)` pair by `(1, 0)`. -/
def exceptionalize {h : ℕ} {c : DecoNormalizedCode h} (D : Decoration c) :
    DecoCode h where
  entry j :=
    if j ∈ D.starts then 1
    else if ∃ i ∈ D.starts, i.1 + 1 = j.1 then 0
    else c j
  entry_lt j := by
    split
    next hj =>
      have heligible := mem_eligibleStarts.mp (D.starts_subset hj)
      rcases heligible with ⟨hjLower, _⟩
      lia
    next hj =>
      split
      · lia
      · exact c.toDecoCode.entry_lt j

@[simp] theorem exceptionalize_apply_of_mem {h : ℕ}
    {c : DecoNormalizedCode h} (D : Decoration c) {j : Fin h}
    (hj : j ∈ D.starts) : D.exceptionalize j = 1 := by
  simp [exceptionalize, hj]

theorem exceptionalize_apply_of_predecessor {h : ℕ}
    {c : DecoNormalizedCode h} (D : Decoration c) {j : Fin h}
    (hj : j ∉ D.starts) (hprevious : ∃ i ∈ D.starts, i.1 + 1 = j.1) :
    D.exceptionalize j = 0 := by
  change (if j ∈ D.starts then 1
    else if ∃ i ∈ D.starts, i.1 + 1 = j.1 then 0 else c j) = 0
  rw [ite_eq_right hj, ite_eq_left hprevious]

theorem exceptionalize_apply_of_not_mem_of_no_predecessor {h : ℕ}
    {c : DecoNormalizedCode h} (D : Decoration c) {j : Fin h}
    (hj : j ∉ D.starts) (hprevious : ¬∃ i ∈ D.starts, i.1 + 1 = j.1) :
    D.exceptionalize j = c j := by
  change (if j ∈ D.starts then 1
    else if ∃ i ∈ D.starts, i.1 + 1 = j.1 then 0 else c j) = c j
  rw [ite_eq_right hj, ite_eq_right hprevious]

@[simp] theorem exceptionalize_apply_eq_one_iff {h : ℕ}
    {c : DecoNormalizedCode h} (D : Decoration c) (j : Fin h) :
    D.exceptionalize j = 1 ↔ j ∈ D.starts := by
  simp only [exceptionalize]
  by_cases hj : j ∈ D.starts
  · simp [hj]
  · by_cases hprevious : ∃ i ∈ D.starts, i.1 + 1 = j.1
    · simp [hj, hprevious]
    · simp [hj, hprevious, c.entry_ne_one j]

/-- Normalizing any selected decoration recovers its normalized base code. -/
@[simp] theorem normalize_exceptionalize {h : ℕ}
    {c : DecoNormalizedCode h} (D : Decoration c) :
    D.exceptionalize.normalize = c := by
  ext j
  by_cases hj : j ∈ D.starts
  · have heligible := mem_eligibleStarts.mp (D.starts_subset hj)
    rcases heligible with ⟨_, _, hjZero, _⟩
    have hjOne : D.exceptionalize j = 1 :=
      (exceptionalize_apply_eq_one_iff D j).2 hj
    change (if D.exceptionalize j = 1 then 0
      else if ∃ i : Fin h, i.1 + 1 = j.1 ∧ D.exceptionalize i = 1
      then 2 else D.exceptionalize j) = c j
    rw [ite_eq_left hjOne]
    exact hjZero.symm
  · by_cases hprevious : ∃ i ∈ D.starts, i.1 + 1 = j.1
    · obtain ⟨i, hi, hij⟩ := hprevious
      have hprevious' : ∃ i ∈ D.starts, i.1 + 1 = j.1 := ⟨i, hi, hij⟩
      have heligible := mem_eligibleStarts.mp (D.starts_subset hi)
      rcases heligible with ⟨_, hiBound, _, hiTwo⟩
      have hfin : (⟨i.1 + 1, hiBound⟩ : Fin h) = j := Fin.ext hij
      rw [hfin] at hiTwo
      have hiOne : D.exceptionalize i = 1 :=
        (exceptionalize_apply_eq_one_iff D i).2 hi
      have hjZero : D.exceptionalize j = 0 := by
        change (if j ∈ D.starts then 1
          else if ∃ i ∈ D.starts, i.1 + 1 = j.1 then 0 else c j) = 0
        rw [ite_eq_right hj, ite_eq_left hprevious']
      change (if D.exceptionalize j = 1 then 0
        else if ∃ i : Fin h, i.1 + 1 = j.1 ∧ D.exceptionalize i = 1
        then 2 else D.exceptionalize j) = c j
      rw [ite_eq_right (by simp [hjZero]), ite_eq_left ⟨i, hij, hiOne⟩]
      exact hiTwo.symm
    · have hnotOne : D.exceptionalize j ≠ 1 := by
        intro hjOne
        exact hj ((exceptionalize_apply_eq_one_iff D j).1 hjOne)
      have hnoPrevious :
          ¬∃ i : Fin h, i.1 + 1 = j.1 ∧ D.exceptionalize i = 1 := by
        intro hexists
        rcases hexists with ⟨i, hij, hiOne⟩
        apply hprevious
        exact ⟨i, (exceptionalize_apply_eq_one_iff D i).1 hiOne, hij⟩
      have hjBase : D.exceptionalize j = c j := by
        simp [exceptionalize, hj, hprevious]
      change (if D.exceptionalize j = 1 then 0
        else if ∃ i : Fin h, i.1 + 1 = j.1 ∧ D.exceptionalize i = 1
        then 2 else D.exceptionalize j) = c j
      rw [ite_eq_right hnotOne, ite_eq_right hnoPrevious, hjBase]

/-- The decorated code remembers exactly which eligible starts were selected. -/
theorem exceptionalize_injective {h : ℕ} {c : DecoNormalizedCode h} :
    Function.Injective
      (exceptionalize : Decoration c → DecoCode h) := by
  intro D E hcodes
  have hstarts : D.starts = E.starts := by
    ext j
    rw [← exceptionalize_apply_eq_one_iff,
      ← exceptionalize_apply_eq_one_iff, hcodes]
  cases D
  cases E
  simp_all

end DecoNormalizedCode.Decoration

namespace DecoNormalizedCode

/-- Normalization fixes every normalized code. -/
@[simp] theorem normalize_toDecoCode {h : ℕ} (c : DecoNormalizedCode h) :
    c.toDecoCode.normalize = c := by
  ext j
  have hcurrent : c j ≠ 1 := c.entry_ne_one j
  have hprevious : ¬∃ i : Fin h, i.1 + 1 = j.1 ∧ c i = 1 := by
    intro hexists
    rcases hexists with ⟨i, _, hiOne⟩
    exact c.entry_ne_one i hiOne
  change (if c j = 1 then 0
    else if ∃ i : Fin h, i.1 + 1 = j.1 ∧ c i = 1 then 2 else c j) = c j
  rw [ite_eq_right hcurrent, ite_eq_right hprevious]

end DecoNormalizedCode

end RealRooted.Applications.OEIS
