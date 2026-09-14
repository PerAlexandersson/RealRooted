import RealRooted.Applications.OEIS.A144438.CodeExtension
import RealRooted.Applications.OEIS.A144438.HistoryPartition

/-!
# Last-step decomposition of Deco history fibers

This file gives the inverse direction to the chronological extension maps:
an admissible code in a normal or exceptional history fiber can be recovered
from the appropriate shorter admissible prefix.  Polynomial recurrences are
kept in a higher module.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

namespace DecoCode

/-- Removing the last entry of a code in a normal history fiber preserves
admissibility. -/
theorem init_isAdmissible_of_exceptionalHistory_normal {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) {c : DecoCode (n + 3)}
    (hc : c.IsAdmissible)
    (hhistory : c.exceptionalHistory hc (by lia) =
      DecoExceptionalHistory.normal H) :
    c.init.IsAdmissible := by
  intro j hj
  have hjOne : c j.castSucc = 1 := hj
  rcases hc j.castSucc hjOne with ⟨hjLower, hjBound, hjZero⟩
  have hjPrefixBound : j.1 + 1 < n + 2 := by
    by_contra hnot
    have heq : j.1 + 1 = n + 2 := by lia
    have hmem : n + 2 ∈ (c.exceptionalHistory hc (by lia)).starts := by
      simpa [heq] using
        (mem_exceptionalHistory_starts_iff c hc (by lia) j.castSucc).mpr
          hjOne
    rw [hhistory] at hmem
    have hmemH : n + 2 ∈ H.starts := by simpa using hmem
    have := (DecoExceptionalHistory.mem_bounds H hmemH).2
    lia
  refine ⟨hjLower, ⟨hjPrefixBound, ?_⟩⟩
  have hindex :
      (⟨j.castSucc.1 + 1, hjBound⟩ : Fin (n + 3)) =
        (⟨j.1 + 1, hjPrefixBound⟩ : Fin (n + 2)).castSucc := by
    apply Fin.ext
    rfl
  rw [init_apply, ← hindex, hjZero]

/-- Removing the final exceptional pair from a code in an exceptional history
fiber preserves admissibility. -/
theorem init_init_isAdmissible_of_exceptionalHistory_exceptional {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) {c : DecoCode (n + 4)}
    (hc : c.IsAdmissible)
    (hhistory : c.exceptionalHistory hc (by lia) =
      DecoExceptionalHistory.exceptional H) :
    c.init.init.IsAdmissible := by
  intro j hj
  have hjOne : c j.castSucc.castSucc = 1 := hj
  rcases hc j.castSucc.castSucc hjOne with
    ⟨hjLower, hjBound, hjZero⟩
  have hjPrefixBound : j.1 + 1 < n + 2 := by
    by_contra hnot
    have heq : j.1 + 1 = n + 2 := by lia
    have hmem : n + 2 ∈ (c.exceptionalHistory hc (by lia)).starts := by
      simpa [heq] using
        (mem_exceptionalHistory_starts_iff c hc (by lia)
          j.castSucc.castSucc).mpr hjOne
    rw [hhistory] at hmem
    rw [DecoExceptionalHistory.starts_exceptional,
      Finset.mem_insert] at hmem
    rcases hmem with hfalse | hmem
    · lia
    · have := (DecoExceptionalHistory.mem_bounds H hmem).2
      lia
  refine ⟨hjLower, ⟨hjPrefixBound, ?_⟩⟩
  have hindex :
      (⟨j.castSucc.castSucc.1 + 1, hjBound⟩ : Fin (n + 4)) =
        ((⟨j.1 + 1, hjPrefixBound⟩ : Fin (n + 2)).castSucc).castSucc := by
    apply Fin.ext
    rfl
  rw [init_apply, init_apply, ← hindex, hjZero]

/-- A code in an exceptional history fiber has one in its penultimate
construction position. -/
theorem penultimate_eq_one_of_exceptionalHistory_exceptional {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) {c : DecoCode (n + 4)}
    (hc : c.IsAdmissible)
    (hhistory : c.exceptionalHistory hc (by lia) =
      DecoExceptionalHistory.exceptional H) :
    c (Fin.last (n + 2)).castSucc = 1 := by
  apply (mem_exceptionalHistory_starts_iff c hc (by lia)
    (Fin.last (n + 2)).castSucc).mp
  rw [hhistory]
  exact DecoExceptionalHistory.last_mem_exceptional H

/-- A code in an exceptional history fiber ends in zero. -/
theorem last_eq_zero_of_exceptionalHistory_exceptional {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) {c : DecoCode (n + 4)}
    (hc : c.IsAdmissible)
    (hhistory : c.exceptionalHistory hc (by lia) =
      DecoExceptionalHistory.exceptional H) :
    c (Fin.last (n + 3)) = 0 := by
  let j : Fin (n + 4) := (Fin.last (n + 2)).castSucc
  have hjOne : c j = 1 := by
    exact penultimate_eq_one_of_exceptionalHistory_exceptional H hc hhistory
  obtain ⟨_, hjBound, hjZero⟩ := hc j hjOne
  have hindex : (⟨j.1 + 1, hjBound⟩ : Fin (n + 4)) =
      Fin.last (n + 3) := by
    apply Fin.ext
    simp [j]
  rw [← hindex]
  exact hjZero

end DecoCode

/-- A code in a fixed history fiber together with a nonexceptional final
entry. -/
abbrev DecoNormalHistoryExtension {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :=
  {p : DecoHistoryFiber H × Fin (n + 3) // (p.2 : Nat) ≠ 1}

/-- Separate a normal history extension into its old fiber element and its
bounded nonexceptional final entry. -/
def normalHistoryExtensionSigmaEquiv {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    DecoNormalHistoryExtension H ≃
      Σ _c : DecoHistoryFiber H,
        {r : Fin (n + 3) // (r : Nat) ≠ 1} where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

noncomputable instance {n : Nat} (H : DecoExceptionalHistory (n + 2)) :
    Fintype (DecoNormalHistoryExtension H) := by
  classical
  exact Fintype.ofFinite (DecoNormalHistoryExtension H)

/-- Append the selected nonexceptional entry to a fixed-history code. -/
def normalHistoryExtension {n : Nat} (H : DecoExceptionalHistory (n + 2))
    (p : DecoNormalHistoryExtension H) :
    DecoHistoryFiber (DecoExceptionalHistory.normal H) := by
  let c := p.1.1.1.1
  let hc := p.1.1.1.2
  let r := p.1.2
  let hc' := DecoCode.snoc_isAdmissible hc r p.2
  refine ⟨⟨c.snoc r, hc'⟩, ?_⟩
  change (c.snoc r).exceptionalHistory hc' (by lia) =
    DecoExceptionalHistory.normal H
  rw [DecoCode.exceptionalHistory_snoc hc (by lia) r p.2]
  exact congrArg DecoExceptionalHistory.normal p.1.1.2

/-- Split a code in a normal history fiber into its shorter history code and
nonexceptional final entry. -/
def normalHistoryRestriction {n : Nat}
    (H : DecoExceptionalHistory (n + 2))
    (c : DecoHistoryFiber (DecoExceptionalHistory.normal H)) :
    DecoNormalHistoryExtension H := by
  let d := c.1.1
  let hd := c.1.2
  have hhistory : d.exceptionalHistory hd (by lia) =
      DecoExceptionalHistory.normal H := c.2
  let dinit : DecoAdmissibleCode (n + 2) :=
    ⟨d.init, DecoCode.init_isAdmissible_of_exceptionalHistory_normal
      H hd hhistory⟩
  have hlast : d (Fin.last (n + 2)) ≠ 1 :=
    DecoCode.last_ne_one_of_isAdmissible hd
  have hinitHistory : admissibleCodeExceptionalHistory n dinit = H := by
    apply DecoExceptionalHistory.normal_injective
    have hstep := DecoCode.exceptionalHistory_snoc dinit.2 (by lia)
      (⟨d (Fin.last (n + 2)), d.entry_lt (Fin.last (n + 2))⟩ : Fin (n + 3))
      hlast
    have hcode := DecoCode.snoc_init_last d
    have hcodeHistory :
        (dinit.1.snoc
          ⟨d (Fin.last (n + 2)), d.entry_lt (Fin.last (n + 2))⟩).exceptionalHistory
            (DecoCode.snoc_isAdmissible dinit.2 _ hlast) (by lia) =
          d.exceptionalHistory hd (by lia) := by
      apply DecoExceptionalHistory.ext
      rw [DecoCode.exceptionalHistory_starts,
        DecoCode.exceptionalHistory_starts]
      exact congrArg
        (fun s => s.map DecoCode.exceptionalStartHeightEmbedding)
        (congrArg DecoCode.exceptionalStarts hcode)
    exact hstep.symm.trans (hcodeHistory.trans hhistory)
  exact ⟨⟨⟨dinit, hinitHistory⟩,
    ⟨d (Fin.last (n + 2)), d.entry_lt (Fin.last (n + 2))⟩⟩, hlast⟩

/-- Normal height extension is exactly a product with one nonexceptional
bounded final entry. -/
def normalHistoryExtensionEquiv {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    DecoNormalHistoryExtension H ≃
      DecoHistoryFiber (DecoExceptionalHistory.normal H) where
  toFun := normalHistoryExtension H
  invFun := normalHistoryRestriction H
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact DecoCode.init_snoc _ _
    · apply Fin.ext
      simp [normalHistoryExtension, normalHistoryRestriction]
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact DecoCode.snoc_init_last _

/-- Append the exceptional pair to a fixed-history admissible code. -/
def exceptionalHistoryExtension {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) (c : DecoHistoryFiber H) :
    DecoHistoryFiber (DecoExceptionalHistory.exceptional H) := by
  let d := c.1.1
  let hd := c.1.2
  let hd' := DecoCode.exceptionalExtension_isAdmissible hd (by lia)
  refine ⟨⟨d.exceptionalExtension (by lia), hd'⟩, ?_⟩
  change (d.exceptionalExtension (by lia)).exceptionalHistory hd' (by lia) =
    DecoExceptionalHistory.exceptional H
  rw [DecoCode.exceptionalHistory_exceptionalExtension hd (by lia)]
  exact congrArg DecoExceptionalHistory.exceptional c.2

/-- Remove the final exceptional pair from a code in an exceptional history
fiber. -/
def exceptionalHistoryRestriction {n : Nat}
    (H : DecoExceptionalHistory (n + 2))
    (c : DecoHistoryFiber (DecoExceptionalHistory.exceptional H)) :
    DecoHistoryFiber H := by
  let d := c.1.1
  let hd := c.1.2
  have hhistory : d.exceptionalHistory hd (by lia) =
      DecoExceptionalHistory.exceptional H := c.2
  have hjOne :=
    DecoCode.penultimate_eq_one_of_exceptionalHistory_exceptional H hd hhistory
  have hlast :=
    DecoCode.last_eq_zero_of_exceptionalHistory_exceptional H hd hhistory
  let dinit : DecoAdmissibleCode (n + 2) :=
    ⟨d.init.init,
      DecoCode.init_init_isAdmissible_of_exceptionalHistory_exceptional
        H hd hhistory⟩
  have hinitHistory : admissibleCodeExceptionalHistory n dinit = H := by
    apply DecoExceptionalHistory.exceptional_injective
    have hstep := DecoCode.exceptionalHistory_exceptionalExtension
      dinit.2 (by lia)
    have hcode := DecoCode.exceptionalExtension_init_init d (by lia)
      hjOne hlast
    have hcodeHistory :
        (dinit.1.exceptionalExtension (by lia)).exceptionalHistory
            (DecoCode.exceptionalExtension_isAdmissible dinit.2 (by lia))
              (by lia) =
          d.exceptionalHistory hd (by lia) := by
      apply DecoExceptionalHistory.ext
      rw [DecoCode.exceptionalHistory_starts,
        DecoCode.exceptionalHistory_starts]
      exact congrArg
        (fun s => s.map DecoCode.exceptionalStartHeightEmbedding)
        (congrArg DecoCode.exceptionalStarts hcode)
    exact hstep.symm.trans (hcodeHistory.trans hhistory)
  exact ⟨dinit, hinitHistory⟩

/-- Exceptional height extension is an equivalence of the corresponding
history fibers. -/
def exceptionalHistoryExtensionEquiv {n : Nat}
    (H : DecoExceptionalHistory (n + 2)) :
    DecoHistoryFiber H ≃
      DecoHistoryFiber (DecoExceptionalHistory.exceptional H) where
  toFun := exceptionalHistoryExtension H
  invFun := exceptionalHistoryRestriction H
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    simp [exceptionalHistoryRestriction, exceptionalHistoryExtension,
      DecoCode.exceptionalExtension]
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact DecoCode.exceptionalExtension_init_init c.1.1 (by lia)
      (DecoCode.penultimate_eq_one_of_exceptionalHistory_exceptional
        H c.1.2 c.2)
      (DecoCode.last_eq_zero_of_exceptionalHistory_exceptional
        H c.1.2 c.2)

end

end RealRooted.Applications.OEIS
