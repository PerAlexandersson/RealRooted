import RealRooted.Combinatorics.MinimumInsertionWord
import RealRooted.Mathlib.RingTheory.MvPolynomial.BooleanSwapOrbit

/-!
# Comparison-bottom supports of finite words

For a word without repeated labels, the value following a non-ascent is
exactly a descent bottom. This file defines its finite support and squarefree
monomial, proves minimum-insertion decoders remain nodup, and proves
equivariance under injective relabelings that preserve every comparison.
-/

namespace RealRooted.MinimumInsertionWord

theorem nodup_insertIdx {a : Nat} {w : List Nat} (hw : w.Nodup)
    (ha : a ∉ w) {r : Nat} (hr : r ≤ w.length) :
    (w.insertIdx r a).Nodup := by
  induction r generalizing w with
  | zero => simpa using List.nodup_cons.mpr ⟨ha, hw⟩
  | succ r ih =>
      cases w with
      | nil => simp at hr
      | cons b w =>
          rw [List.nodup_cons] at hw
          have haTail : a ∉ w := fun hmem => ha (by simp [hmem])
          have hrTail : r ≤ w.length := by simpa using hr
          simp only [List.insertIdx_succ_cons, List.nodup_cons]
          refine ⟨?_, ih hw.2 haTail hrTail⟩
          intro hb
          rcases List.eq_or_mem_of_mem_insertIdx hb with hba | hbTail
          · exact ha (by simp [hba])
          · exact hw.1 hbTail

theorem nodup_raise {w : List Nat} (hw : w.Nodup) : (raise w).Nodup := by
  exact hw.map Nat.succ_injective

theorem nodup_step {w : List Nat} (hw : w.Nodup) (hpos : IsPositive w)
    {r : Nat}
    (hr : r ≤ w.length) : (step r w).Nodup := by
  apply nodup_insertIdx (nodup_raise hw)
  · intro hone
    rw [raise, List.mem_map] at hone
    obtain ⟨a, ha, hsucc⟩ := hone
    have hapos := hpos a ha
    lia
  · simpa [raise] using hr

theorem Nodup.decodeFrom {w code : List Nat} (hw : w.Nodup)
    (hpos : IsPositive w)
    (hcode : ValidFrom w.length code) : (decodeFrom w code).Nodup := by
  induction code generalizing w with
  | nil => exact hw
  | cons r code ih =>
      have hstep := nodup_step hw hpos hcode.1
      have hlength := length_step hcode.1
      rw [decodeFrom_cons]
      apply ih hstep (isPositive_step r w)
      rw [hlength]
      exact hcode.2

theorem Nodup.decode {code : List Nat} (hcode : ValidFrom 0 code) :
    (decode code).Nodup := by
  exact Nodup.decodeFrom (by simp) (by simp [IsPositive]) hcode

/-- Values following a non-ascent, represented as a finite support. On a
nodup word these are exactly its descent bottoms. -/
def comparisonBottomSupport : List Nat → Finset Nat
  | a :: b :: w =>
      if a < b then comparisonBottomSupport (b :: w)
      else insert b (comparisonBottomSupport (b :: w))
  | _ => ∅

theorem mem_comparisonBottomSupport_iff {w : List Nat} (hw : w.Nodup)
    (x : Nat) :
    x ∈ comparisonBottomSupport w ↔
      ∃ a, (a, x) ∈ w.consecutivePairs ∧ x < a := by
  induction w with
  | nil => simp [comparisonBottomSupport, List.consecutivePairs]
  | cons a w ih =>
      cases w with
      | nil => simp [comparisonBottomSupport, List.consecutivePairs]
      | cons b w =>
          rw [List.nodup_cons] at hw
          have htail : (b :: w).Nodup := hw.2
          have habNe : a ≠ b := fun hab => hw.1 (by simp [hab])
          by_cases hab : a < b
          · have hnba : ¬ b < a := by lia
            rw [comparisonBottomSupport, if_pos hab]
            constructor
            · intro hx
              rw [ih htail] at hx
              obtain ⟨z, hz, hzx⟩ := hx
              exact ⟨z, by
                change (z, x) ∈ (a, b) :: (b :: w).consecutivePairs
                exact List.mem_cons_of_mem _ hz, hzx⟩
            · rintro ⟨z, hz, hzx⟩
              change (z, x) ∈ (a, b) ::
                (b :: w).consecutivePairs at hz
              have hor := List.mem_cons.mp hz
              cases hor with
              | inl hhead =>
                have hza : z = a := congrArg Prod.fst hhead
                have hxb : x = b := congrArg Prod.snd hhead
                subst z
                subst x
                exact (hnba hzx).elim
              | inr hrest =>
                rw [ih htail]
                exact ⟨z, hrest, hzx⟩
          · have hba : b < a := by lia
            rw [comparisonBottomSupport, if_neg hab]
            constructor
            · intro hx
              rw [Finset.mem_insert] at hx
              rcases hx with hxb | hx
              · subst x
                exact ⟨a, by
                  change (a, b) ∈ (a, b) ::
                    (b :: w).consecutivePairs
                  simp, hba⟩
              · rw [ih htail] at hx
                obtain ⟨z, hz, hzx⟩ := hx
                exact ⟨z, by
                  change (z, x) ∈ (a, b) ::
                    (b :: w).consecutivePairs
                  exact List.mem_cons_of_mem _ hz, hzx⟩
            · rintro ⟨z, hz, hzx⟩
              change (z, x) ∈ (a, b) ::
                (b :: w).consecutivePairs at hz
              rw [Finset.mem_insert]
              have hor := List.mem_cons.mp hz
              cases hor with
              | inl hhead =>
                have hxb : x = b := congrArg Prod.snd hhead
                exact Or.inl hxb
              | inr hrest =>
                right
                rw [ih htail]
                exact ⟨z, hrest, hzx⟩

/-- Comparison-bottom support commutes with an injective relabeling whenever
that relabeling preserves the complete comparison word. -/
theorem comparisonBottomSupport_map (f : Nat ↪ Nat) (w : List Nat)
    (hcomp : comparisonWord (w.map f) = comparisonWord w) :
    comparisonBottomSupport (w.map f) =
      (comparisonBottomSupport w).map f := by
  induction w with
  | nil => simp [comparisonBottomSupport]
  | cons a w ih =>
      cases w with
      | nil => simp [comparisonBottomSupport]
      | cons b w =>
          simp only [List.map_cons, comparisonWord] at hcomp
          have hdecide : decide (f a < f b) = decide (a < b) :=
            List.cons.inj hcomp |>.1
          have htail :
              comparisonWord ((b :: w).map f) =
                comparisonWord (b :: w) := by
            exact List.cons.inj hcomp |>.2
          by_cases hab : a < b
          · have hfab : f a < f b := by
              by_contra hn
              simp [hab, hn] at hdecide
            simp only [List.map_cons]
            rw [comparisonBottomSupport, if_pos hfab,
              comparisonBottomSupport, if_pos hab]
            change comparisonBottomSupport ((b :: w).map f) =
              (comparisonBottomSupport (b :: w)).map f
            exact ih htail
          · have hfab : ¬ f a < f b := by
              intro hf
              simp [hab, hf] at hdecide
            simp only [List.map_cons]
            rw [comparisonBottomSupport, if_neg hfab,
              comparisonBottomSupport, if_neg hab, Finset.map_insert]
            congr 1
            change comparisonBottomSupport ((b :: w).map f) =
              (comparisonBottomSupport (b :: w)).map f
            exact ih htail

/-- The squarefree monomial on the comparison-bottom support. -/
noncomputable def comparisonBottomMonomial {R : Type*} [CommSemiring R]
    (w : List Nat) : MvPolynomial Nat R :=
  MvPolynomial.finsetMonomial (comparisonBottomSupport w)

/-- Comparison-bottom monomials commute with comparison-preserving injective
relabelings. -/
theorem rename_comparisonBottomMonomial {R : Type*} [CommSemiring R]
    (f : Nat ↪ Nat) (w : List Nat)
    (hcomp : comparisonWord (w.map f) = comparisonWord w) :
    MvPolynomial.rename f
        (comparisonBottomMonomial w : MvPolynomial Nat R) =
      comparisonBottomMonomial (w.map f) := by
  rw [comparisonBottomMonomial,
    MvPolynomial.rename_finsetMonomial (f : Nat → Nat) f.injective,
    comparisonBottomMonomial, comparisonBottomSupport_map f w hcomp]
  congr

end RealRooted.MinimumInsertionWord
