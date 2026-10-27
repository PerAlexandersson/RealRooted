module

public import RealRooted.CommonInterleaver.Sequence
public import RealRooted.RootPolynomial

/-!
# Common interleavers: descending-root polynomials

Construction of a polynomial from descending prescribed roots, and the
root-slot arguments which produce right and left `StrictInterl` witnesses.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The descending root sequence of the root polynomial of a descending list is the list. -/
@[simp] theorem rootSeqDesc_rootPolynomial
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (rootPolynomial (xs : Multiset ℝ)) = xs := by
  simpa using rootSeqDesc_eq_reverse_of_pairwise
    (f := rootPolynomial (xs : Multiset ℝ)) (rs := xs.reverse)
    (by simpa using hxs.reverse) (by simp [roots_rootPolynomial])

/-- Slot data against `rootSeqDesc f` give a `StrictInterl` witness with the root polynomial
of the slot choices. -/
theorem strictInterl_of_slots_rootPolynomial
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [hf] using this⟩) :
    StrictInterl f (rootPolynomial (xs : Multiset ℝ)) := by
  rw [strictInterl_iff_rootSeqDesc]
  refine ⟨⟨hf₀, hf⟩, ⟨rootPolynomial_ne_zero _, rootPolynomial_splits _⟩, ?_, ?_, ?_⟩
  · simp [natDegree_rootPolynomial]
    lia
  · intro j hj
    have hjx : j < xs.length := by lia
    have hroot : j < (rootSeqDesc f).length := by simpa [rootSeqDesc_length hf]
    have hbound := CommonInterleaver.RootSlots.rootSlot_lower_bound
      (rs := rootSeqDesc f) (by grind) hroot (hslot j hjx)
    rw [rootSeqDesc_rootPolynomial hxs, List.getD_eq_getElem _ _ hroot,
      List.getD_eq_getElem _ _ hjx]
    exact hbound
  · intro j hj hjx
    have hjx' : j + 1 < xs.length := by
      simpa [natDegree_rootPolynomial] using hjx
    have hroot : j < (rootSeqDesc f).length := by simpa [rootSeqDesc_length hf]
    have hbound := CommonInterleaver.RootSlots.rootSlot_upper_bound
      (rs := rootSeqDesc f) (by grind) (by lia) (by simpa [rootSeqDesc_length hf])
      (hslot (j + 1) hjx')
    rw [rootSeqDesc_rootPolynomial hxs, List.getD_eq_getElem _ _ hjx',
      List.getD_eq_getElem _ _ hroot]
    simpa using hbound

/-- Shifted slot data against `rootSeqDesc f` give a left `StrictInterl` witness with the root
polynomial of the slot choices. -/
theorem strictInterl_left_of_shifted_slots_rootPolynomial
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : xs.length ≤ f.natDegree)
    (hdeg_hi : f.natDegree ≤ xs.length + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j + 1, by
          have : j < f.natDegree := lt_of_lt_of_le hj hdeg_lo
          simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this⟩) :
    StrictInterl (rootPolynomial (xs : Multiset ℝ)) f := by
  rw [strictInterl_iff_rootSeqDesc]
  refine ⟨⟨rootPolynomial_ne_zero _, rootPolynomial_splits _⟩, ⟨hf₀, hf⟩, ?_, ?_, ?_⟩
  · simp [natDegree_rootPolynomial]
    lia
  · intro j hj
    have hjx : j < xs.length := by
      simpa [natDegree_rootPolynomial] using hj
    have hjf : j < f.natDegree := lt_of_lt_of_le hjx hdeg_lo
    have hroot : j < (rootSeqDesc f).length := by simpa [rootSeqDesc_length hf]
    have hbound := CommonInterleaver.RootSlots.rootSlot_upper_bound
      (rs := rootSeqDesc f) (by grind) (by lia) (by simpa [rootSeqDesc_length hf])
      (hslot j hjx)
    rw [rootSeqDesc_rootPolynomial hxs, List.getD_eq_getElem _ _ hjx,
      List.getD_eq_getElem _ _ hroot]
    simpa using hbound
  · intro j hj hjf
    have hjx : j < xs.length := by
      simpa [natDegree_rootPolynomial] using hj
    have hroot : j + 1 < (rootSeqDesc f).length := by
      simpa [rootSeqDesc_length hf] using hjf
    have hbound := CommonInterleaver.RootSlots.rootSlot_lower_bound
      (rs := rootSeqDesc f) (by grind) hroot (hslot j hjx)
    rw [rootSeqDesc_rootPolynomial hxs, List.getD_eq_getElem _ _ hroot,
      List.getD_eq_getElem _ _ hjx]
    exact hbound

end RealRooted
