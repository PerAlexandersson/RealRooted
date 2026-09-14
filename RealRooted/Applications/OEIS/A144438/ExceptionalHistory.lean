import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi

/-!
# Exceptional histories for the deco construction

This file packages the chronological exceptional steps in a deco construction
as their finite set of starting heights.  This canonical representation makes
the height bounds and nonconsecutivity condition explicit and avoids carrying
redundant step-list data into the exact-layer polynomial recursion.
-/

namespace RealRooted.Applications.OEIS

/-- Exceptional starts for a height-`h` deco history lie in `3, ..., h - 1`
and no start is immediately followed by another. -/
def IsDecoExceptionalSet (h : ℕ) (R : Finset ℕ) : Prop :=
  2 ≤ h ∧ ∀ j ∈ R, 3 ≤ j ∧ j < h ∧ j + 1 ∉ R

/-- A deco construction history, canonically represented by the exact set of
exceptional two-step starts. -/
structure DecoExceptionalHistory (h : ℕ) where
  starts : Finset ℕ
  admissible : IsDecoExceptionalSet h starts

namespace DecoExceptionalHistory

@[ext] theorem ext {h : ℕ} {H K : DecoExceptionalHistory h}
    (hstarts : H.starts = K.starts) : H = K := by
  cases H
  cases K
  cases hstarts
  rfl

/-- Histories are exactly admissible exceptional-start sets. -/
def equivAdmissibleSet (h : ℕ) :
    DecoExceptionalHistory h ≃
      {R : Finset ℕ // IsDecoExceptionalSet h R} where
  toFun H := ⟨H.starts, H.admissible⟩
  invFun R := ⟨R.1, R.2⟩
  left_inv H := by cases H; rfl
  right_inv R := by cases R; rfl

/-- The unique height-two seed history. -/
def seed : DecoExceptionalHistory 2 :=
  ⟨∅, by simp [IsDecoExceptionalSet]⟩

/-- Append one normal construction step. -/
def normal {h : ℕ} (H : DecoExceptionalHistory h) :
    DecoExceptionalHistory (h + 1) :=
  ⟨H.starts, by
    refine ⟨by exact Nat.le.step H.admissible.1, ?_⟩
    intro j hj
    obtain ⟨hj3, hjh, hjnext⟩ := H.admissible.2 j hj
    exact ⟨hj3, hjh.trans (Nat.lt_succ_self h), hjnext⟩⟩

/-- Append one exceptional two-step construction. -/
def exceptional {h : ℕ} (H : DecoExceptionalHistory h) :
    DecoExceptionalHistory (h + 2) :=
  ⟨insert (h + 1) H.starts, by
    refine ⟨by lia, ?_⟩
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · have hh := H.admissible.1
      refine ⟨by lia, by lia, ?_⟩
      simp only [Finset.mem_insert]
      push Not
      refine ⟨by lia, ?_⟩
      intro hmem
      have := (H.admissible.2 (h + 2) hmem).2.1
      lia
    · obtain ⟨hj3, hjh, hjnext⟩ := H.admissible.2 j hj
      refine ⟨hj3, by lia, ?_⟩
      simp only [Finset.mem_insert]
      push Not
      exact ⟨by lia, hjnext⟩⟩

@[simp] theorem starts_seed : seed.starts = ∅ := rfl

@[simp] theorem starts_normal {h : ℕ} (H : DecoExceptionalHistory h) :
    (normal H).starts = H.starts := rfl

@[simp] theorem starts_exceptional {h : ℕ} (H : DecoExceptionalHistory h) :
    (exceptional H).starts = insert (h + 1) H.starts := rfl

theorem mem_bounds {h j : ℕ} (H : DecoExceptionalHistory h)
    (hj : j ∈ H.starts) : 3 ≤ j ∧ j < h :=
  ⟨(H.admissible.2 j hj).1, (H.admissible.2 j hj).2.1⟩

/-- Every height-two history is the seed history. -/
theorem eq_seed (H : DecoExceptionalHistory 2) : H = seed := by
  apply DecoExceptionalHistory.ext
  ext j
  constructor
  · intro hj
    have := H.mem_bounds hj
    lia
  · simp

theorem succ_not_mem {h j : ℕ} (H : DecoExceptionalHistory h)
    (hj : j ∈ H.starts) : j + 1 ∉ H.starts :=
  (H.admissible.2 j hj).2.2

/-- Encode a history by membership of its bounded possible starts. -/
def membershipCode {h : Nat} (H : DecoExceptionalHistory h) : Fin h → Bool :=
  fun j => decide (j.1 ∈ H.starts)

theorem membershipCode_injective {h : Nat} :
    Function.Injective
      (membershipCode : DecoExceptionalHistory h → Fin h → Bool) := by
  intro H K hcode
  apply ext
  ext r
  constructor
  · intro hr
    have hrBound := (mem_bounds H hr).2
    have hvalue := congrFun hcode (⟨r, hrBound⟩ : Fin h)
    simpa [membershipCode, hr] using hvalue
  · intro hr
    have hrBound := (mem_bounds K hr).2
    have hvalue := congrFun hcode (⟨r, hrBound⟩ : Fin h)
    simpa [membershipCode, hr] using hvalue.symm

noncomputable instance instFintype (h : Nat) :
    Fintype (DecoExceptionalHistory h) := by
  classical
  exact Fintype.ofInjective membershipCode membershipCode_injective

theorem last_not_mem_normal {h : ℕ} (H : DecoExceptionalHistory h) :
    h ∉ (normal H).starts := by
  intro hh
  have := (mem_bounds H hh).2
  lia

@[simp] theorem last_mem_exceptional {h : ℕ} (H : DecoExceptionalHistory h) :
    h + 1 ∈ (exceptional H).starts := by
  simp

@[simp] theorem erase_last_exceptional {h : ℕ} (H : DecoExceptionalHistory h) :
    (exceptional H).starts.erase (h + 1) = H.starts := by
  rw [starts_exceptional, Finset.erase_insert]
  intro hmem
  have := (mem_bounds H hmem).2
  lia

theorem normal_injective {h : ℕ} :
    Function.Injective (normal : DecoExceptionalHistory h →
      DecoExceptionalHistory (h + 1)) := by
  intro H K hHK
  apply ext
  have := congrArg starts hHK
  simpa using this

theorem exceptional_injective {h : ℕ} :
    Function.Injective (exceptional : DecoExceptionalHistory h →
      DecoExceptionalHistory (h + 2)) := by
  intro H K hHK
  apply ext
  have := congrArg (fun L => L.starts.erase (h + 1)) hHK
  calc
    H.starts = (exceptional H).starts.erase (h + 1) :=
      (erase_last_exceptional H).symm
    _ = (exceptional K).starts.erase (h + 1) := this
    _ = K.starts := erase_last_exceptional K

theorem normal_ne_exceptional {n : ℕ}
    (H : DecoExceptionalHistory (n + 2))
    (K : DecoExceptionalHistory (n + 1)) :
    normal H ≠ exceptional K := by
  intro heq
  have hmem : n + 2 ∈ (exceptional K).starts := by
    simpa only [Nat.add_assoc] using last_mem_exceptional K
  rw [← heq] at hmem
  exact last_not_mem_normal H hmem

/-- A history whose final available start is absent uniquely comes from a
normal last step. -/
theorem exists_normal_of_last_not_mem {n : ℕ}
    (H : DecoExceptionalHistory (n + 3)) (hlast : n + 2 ∉ H.starts) :
    ∃ H' : DecoExceptionalHistory (n + 2), normal H' = H := by
  let H' : DecoExceptionalHistory (n + 2) :=
    ⟨H.starts, by
      refine ⟨by lia, ?_⟩
      intro j hj
      obtain ⟨hj3, hjlt, hjnext⟩ := H.admissible.2 j hj
      refine ⟨hj3, ?_, hjnext⟩
      have hjle : j ≤ n + 2 := by lia
      exact lt_of_le_of_ne hjle fun h => hlast (h ▸ hj)⟩
  exact ⟨H', by cases H; rfl⟩

/-- A history whose final available start is present uniquely comes from an
exceptional last step. -/
theorem exists_exceptional_of_last_mem {n : ℕ}
    (H : DecoExceptionalHistory (n + 3)) (hlast : n + 2 ∈ H.starts) :
    ∃ H' : DecoExceptionalHistory (n + 1), exceptional H' = H := by
  have hn1 : 1 ≤ n := by
    have := (mem_bounds H hlast).1
    lia
  have hbefore : n + 1 ∉ H.starts := by
    intro hmem
    have := succ_not_mem H hmem
    apply this
    simpa only [Nat.add_assoc] using hlast
  let H' : DecoExceptionalHistory (n + 1) :=
    ⟨H.starts.erase (n + 2), by
      refine ⟨by lia, ?_⟩
      intro j hj
      rw [Finset.mem_erase] at hj
      obtain ⟨hjh, hjmem⟩ := hj
      obtain ⟨hj3, hjlt, hjnext⟩ := H.admissible.2 j hjmem
      refine ⟨hj3, ?_, ?_⟩
      · have hjle : j ≤ n + 2 := by lia
        have hjnebefore : j ≠ n + 1 := fun heq => hbefore (heq ▸ hjmem)
        lia
      · intro hjnextErase
        exact hjnext (Finset.mem_of_mem_erase hjnextErase)⟩
  refine ⟨H', ?_⟩
  apply ext
  dsimp [H']
  rw [show n + 1 + 1 = n + 2 by lia, Finset.insert_erase hlast]

/-- Every history above the seed has exactly the normal or exceptional last
step determined by membership of the final available start. -/
theorem exists_last_step {n : ℕ} (H : DecoExceptionalHistory (n + 3)) :
    (∃ H' : DecoExceptionalHistory (n + 2), normal H' = H) ∨
      (∃ H' : DecoExceptionalHistory (n + 1), exceptional H' = H) := by
  by_cases hlast : n + 2 ∈ H.starts
  · exact Or.inr (exists_exceptional_of_last_mem H hlast)
  · exact Or.inl (exists_normal_of_last_not_mem H hlast)

end DecoExceptionalHistory

end RealRooted.Applications.OEIS
