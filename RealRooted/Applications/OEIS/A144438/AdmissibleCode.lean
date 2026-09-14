import RealRooted.Applications.OEIS.A144438.NormalizedCode
import RealRooted.Applications.OEIS.A144438.ExceptionalHistory
import Mathlib.Data.Fintype.Pi

/-!
# Admissible chronological Deco codes

This file supplies the finite combinatorial foundation needed to sum over
chronological Deco codes.  An admissible code records every exceptional step
as a nonoverlapping pair `(1, 0)` beginning no earlier than the third row.
Such a code has a unique decoration over its normalized code.
-/

namespace RealRooted.Applications.OEIS

/-- The canonical bounded-entry model for chronological codes of height `h`. -/
abbrev DecoEntryData (h : Nat) := (j : Fin h) → Fin (j.1 + 1)

namespace DecoCode

/-- Chronological codes are equivalently functions with the row bound built
into every coordinate. -/
def equivEntryData (h : Nat) : DecoCode h ≃ DecoEntryData h where
  toFun c j := ⟨c j, c.entry_lt j⟩
  invFun a := ⟨fun j => a j, fun j => (a j).isLt⟩
  left_inv c := by
    ext j
    rfl
  right_inv a := by
    funext j
    apply Fin.ext
    rfl

noncomputable instance instFintype (h : Nat) : Fintype (DecoCode h) := by
  classical
  exact Fintype.ofEquiv (DecoEntryData h) (equivEntryData h).symm

/-- Every entry equal to one begins a valid exceptional `(1, 0)` pair. -/
def IsAdmissible {h : Nat} (c : DecoCode h) : Prop :=
  ∀ j, c j = 1 →
    2 ≤ j.1 ∧ ∃ hj : j.1 + 1 < h, c ⟨j.1 + 1, hj⟩ = 0

/-- The zero-based starts of the exceptional pairs in a chronological code. -/
def exceptionalStarts {h : Nat} (c : DecoCode h) : Finset (Fin h) :=
  Finset.univ.filter fun j => c j = 1

@[simp] theorem mem_exceptionalStarts {h : Nat} (c : DecoCode h)
    (j : Fin h) : j ∈ c.exceptionalStarts ↔ c j = 1 := by
  simp [exceptionalStarts]

/-- Convert a zero-based exceptional-code position to its one-based history
start. -/
def exceptionalStartHeightEmbedding {h : Nat} : Fin h ↪ Nat where
  toFun j := j.1 + 1
  inj' := by
    intro i j hij
    apply Fin.ext
    lia

/-- The exceptional history underlying an admissible code of height at least
two. -/
def exceptionalHistory {h : Nat} (c : DecoCode h) (hc : c.IsAdmissible)
    (hh : 2 ≤ h) : DecoExceptionalHistory h where
  starts := c.exceptionalStarts.map exceptionalStartHeightEmbedding
  admissible := by
    refine ⟨hh, ?_⟩
    intro r hr
    rw [Finset.mem_map] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    have hjOne := (mem_exceptionalStarts c j).mp hj
    rcases hc j hjOne with ⟨hjLower, hjBound, hsuccZero⟩
    change 3 ≤ j.1 + 1 ∧ j.1 + 1 < h ∧
      j.1 + 1 + 1 ∉ c.exceptionalStarts.map exceptionalStartHeightEmbedding
    refine ⟨by lia, hjBound, ?_⟩
    intro hnext
    rw [Finset.mem_map] at hnext
    obtain ⟨k, hk, hkj⟩ := hnext
    have hkOne := (mem_exceptionalStarts c k).mp hk
    have hkVal : k.1 = j.1 + 1 := by
      change k.1 + 1 = (j.1 + 1) + 1 at hkj
      lia
    have hkFin : k = ⟨j.1 + 1, hjBound⟩ := Fin.ext hkVal
    rw [hkFin, hsuccZero] at hkOne
    contradiction

@[simp] theorem exceptionalHistory_starts {h : Nat} (c : DecoCode h)
    (hc : c.IsAdmissible) (hh : 2 ≤ h) :
    (c.exceptionalHistory hc hh).starts =
      c.exceptionalStarts.map exceptionalStartHeightEmbedding := rfl

@[simp] theorem mem_exceptionalHistory_starts_iff {h : Nat} (c : DecoCode h)
    (hc : c.IsAdmissible) (hh : 2 ≤ h) (j : Fin h) :
    j.1 + 1 ∈ (c.exceptionalHistory hc hh).starts ↔ c j = 1 := by
  rw [exceptionalHistory_starts, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, hij⟩
    have hfin : i = j := by
      apply Fin.ext
      change i.1 + 1 = j.1 + 1 at hij
      lia
    subst i
    exact (mem_exceptionalStarts c j).mp hi
  · intro hj
    exact ⟨j, (mem_exceptionalStarts c j).mpr hj, rfl⟩

end DecoCode

namespace DecoNormalizedCode

/-- Normalized codes are equivalently chronological codes with no entry equal
to one. -/
def equivCodeSubtype (h : Nat) :
    DecoNormalizedCode h ≃ {c : DecoCode h // ∀ j, c j ≠ 1} where
  toFun c := ⟨c.toDecoCode, c.entry_ne_one⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

noncomputable instance instFintype (h : Nat) :
    Fintype (DecoNormalizedCode h) := by
  classical
  exact Fintype.ofEquiv {c : DecoCode h // ∀ j, c j ≠ 1}
    (equivCodeSubtype h).symm

namespace Decoration

/-- Every decoration produces an admissible chronological code. -/
theorem exceptionalize_isAdmissible {h : Nat} {c : DecoNormalizedCode h}
    (D : Decoration c) : D.exceptionalize.IsAdmissible := by
  intro j hjOne
  have hj : j ∈ D.starts := (exceptionalize_apply_eq_one_iff D j).mp hjOne
  have hjEligible := mem_eligibleStarts.mp (D.starts_subset hj)
  rcases hjEligible with ⟨hjLower, hjBound, _, _⟩
  refine ⟨hjLower, hjBound, ?_⟩
  apply exceptionalize_apply_of_predecessor D
  · intro hsucc
    exact D.nonoverlap hj hsucc rfl
  · exact ⟨j, hj, rfl⟩

end Decoration

end DecoNormalizedCode

namespace DecoCode

/-- The exceptional starts of an admissible code form a decoration of its
normalization. -/
def toDecoration {h : Nat} (c : DecoCode h) (hc : c.IsAdmissible) :
    DecoNormalizedCode.Decoration c.normalize where
  starts := c.exceptionalStarts
  starts_subset := by
    intro j hj
    rw [DecoNormalizedCode.mem_eligibleStarts]
    have hjOne := (mem_exceptionalStarts c j).mp hj
    rcases hc j hjOne with ⟨hjLower, hjBound, hsuccZero⟩
    refine ⟨hjLower, hjBound, ?_, ?_⟩
    · simp [normalize, hjOne]
    · change (if c ⟨j.1 + 1, hjBound⟩ = 1 then 0
        else if ∃ i : Fin h, i.1 + 1 = j.1 + 1 ∧ c i = 1
        then 2 else c ⟨j.1 + 1, hjBound⟩) = 2
      rw [if_neg (by simp [hsuccZero]), if_pos]
      exact ⟨j, rfl, hjOne⟩

@[simp] theorem toDecoration_starts {h : Nat} (c : DecoCode h)
    (hc : c.IsAdmissible) : (c.toDecoration hc).starts = c.exceptionalStarts :=
  rfl

/-- Exceptionalizing the canonical decoration recovers the admissible code. -/
@[simp] theorem exceptionalize_toDecoration {h : Nat} (c : DecoCode h)
    (hc : c.IsAdmissible) : (c.toDecoration hc).exceptionalize = c := by
  ext j
  by_cases hjOne : c j = 1
  · rw [DecoNormalizedCode.Decoration.exceptionalize_apply_of_mem]
    · exact hjOne.symm
    · rw [toDecoration_starts, mem_exceptionalStarts]
      exact hjOne
  · have hjNotMem : j ∉ (c.toDecoration hc).starts := by
      rw [toDecoration_starts, mem_exceptionalStarts]
      exact hjOne
    by_cases hprevious :
        ∃ i ∈ (c.toDecoration hc).starts, i.1 + 1 = j.1
    · rw [DecoNormalizedCode.Decoration.exceptionalize_apply_of_predecessor
          (c.toDecoration hc) hjNotMem hprevious]
      obtain ⟨i, hi, hij⟩ := hprevious
      rw [toDecoration_starts, mem_exceptionalStarts] at hi
      rcases hc i hi with ⟨_, hiBound, hsuccZero⟩
      have hsucc : (⟨i.1 + 1, hiBound⟩ : Fin h) = j := Fin.ext hij
      have hjZero : c j = 0 := by simpa [hsucc] using hsuccZero
      exact hjZero.symm
    · rw [DecoNormalizedCode.Decoration.exceptionalize_apply_of_not_mem_of_no_predecessor
          (c.toDecoration hc) hjNotMem hprevious]
      change (if c j = 1 then 0
        else if ∃ i : Fin h, i.1 + 1 = j.1 ∧ c i = 1 then 2 else c j) = c j
      rw [if_neg hjOne, if_neg]
      intro hexists
      obtain ⟨i, hij, hiOne⟩ := hexists
      apply hprevious
      refine ⟨i, ?_, hij⟩
      rw [toDecoration_starts, mem_exceptionalStarts]
      exact hiOne

/-- Every admissible code is produced by a unique decoration of its
normalization. -/
theorem existsUnique_decoration {h : Nat} (c : DecoCode h)
    (hc : c.IsAdmissible) :
    ∃! D : DecoNormalizedCode.Decoration c.normalize,
      D.exceptionalize = c := by
  refine ⟨c.toDecoration hc, exceptionalize_toDecoration c hc, ?_⟩
  intro D hD
  apply DecoNormalizedCode.Decoration.exceptionalize_injective
  rw [hD, exceptionalize_toDecoration]

end DecoCode

/-- An admissible chronological code, bundled with its exceptional-pair
condition. -/
abbrev DecoAdmissibleCode (h : Nat) :=
  {c : DecoCode h // c.IsAdmissible}

noncomputable instance (h : Nat) : Fintype (DecoAdmissibleCode h) := by
  classical
  exact Fintype.ofFinite (DecoAdmissibleCode h)

/-- A normalized code together with a set of eligible starts, flattened into
one nondependent finite index type. -/
structure DecoratedDecoNormalizedCode (h : Nat) where
  code : DecoNormalizedCode h
  starts : Finset (Fin h)
  starts_subset : starts ⊆ code.eligibleStarts

namespace DecoratedDecoNormalizedCode

@[ext] theorem ext {h : Nat} {C D : DecoratedDecoNormalizedCode h}
    (hcode : C.code = D.code) (hstarts : C.starts = D.starts) : C = D := by
  cases C
  cases D
  cases hcode
  cases hstarts
  rfl

/-- Recover the decoration carried by the flat decorated-code index. -/
def decoration {h : Nat} (D : DecoratedDecoNormalizedCode h) :
    DecoNormalizedCode.Decoration D.code :=
  ⟨D.starts, D.starts_subset⟩

@[simp] theorem decoration_starts {h : Nat}
    (D : DecoratedDecoNormalizedCode h) : D.decoration.starts = D.starts := rfl

/-- Package a dependent normalized-code decoration into the flat index. -/
def ofDecoration {h : Nat} {c : DecoNormalizedCode h}
    (D : DecoNormalizedCode.Decoration c) : DecoratedDecoNormalizedCode h :=
  ⟨c, D.starts, D.starts_subset⟩

@[simp] theorem ofDecoration_code {h : Nat} {c : DecoNormalizedCode h}
    (D : DecoNormalizedCode.Decoration c) : (ofDecoration D).code = c := rfl

@[simp] theorem ofDecoration_starts {h : Nat} {c : DecoNormalizedCode h}
    (D : DecoNormalizedCode.Decoration c) : (ofDecoration D).starts = D.starts :=
  rfl

/-- The flat decorated-code index is equivalent to the natural dependent
sum, but has simpler extensional equality for partition arguments. -/
def equivSigma (h : Nat) :
    DecoratedDecoNormalizedCode h ≃
      Σ c : DecoNormalizedCode h, DecoNormalizedCode.Decoration c where
  toFun D := ⟨D.code, D.decoration⟩
  invFun p := ofDecoration p.2
  left_inv D := by
    apply ext <;> rfl
  right_inv p := by
    rcases p with ⟨c, ⟨starts, hstarts⟩⟩
    rfl

end DecoratedDecoNormalizedCode

/-- Normalization and its unique exceptional decoration identify admissible
codes with the flat decorated-normalized-code index. -/
def admissibleCodeEquivDecoratedNormalized (h : Nat) :
    DecoAdmissibleCode h ≃ DecoratedDecoNormalizedCode h where
  toFun c :=
    ⟨c.1.normalize, c.1.exceptionalStarts,
      (c.1.toDecoration c.2).starts_subset⟩
  invFun D :=
    ⟨D.decoration.exceptionalize, D.decoration.exceptionalize_isAdmissible⟩
  left_inv c := by
    apply Subtype.ext
    exact DecoCode.exceptionalize_toDecoration c.1 c.2
  right_inv D := by
    apply DecoratedDecoNormalizedCode.ext
    · exact DecoNormalizedCode.Decoration.normalize_exceptionalize D.decoration
    · ext j
      rw [DecoCode.mem_exceptionalStarts]
      exact DecoNormalizedCode.Decoration.exceptionalize_apply_eq_one_iff
        D.decoration j

noncomputable instance (h : Nat) :
    Fintype (DecoratedDecoNormalizedCode h) :=
  Fintype.ofEquiv (DecoAdmissibleCode h)
    (admissibleCodeEquivDecoratedNormalized h)

end RealRooted.Applications.OEIS
