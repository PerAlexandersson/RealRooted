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
  | [] => ∅
  | [_] => ∅
  | a :: b :: w =>
      if a < b then comparisonBottomSupport (b :: w)
      else insert b (comparisonBottomSupport (b :: w))

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

def succEmbedding : Nat ↪ Nat where
  toFun := Nat.succ
  inj' := Nat.succ_injective

theorem comparisonBottomSupport_raise (w : List Nat) :
    comparisonBottomSupport (raise w) =
      (comparisonBottomSupport w).map succEmbedding := by
  exact comparisonBottomSupport_map succEmbedding w (comparisonWord_raise w)

theorem succ_mem_comparisonBottomSupport_raise_iff (w : List Nat) (x : Nat) :
    x + 1 ∈ comparisonBottomSupport (raise w) ↔
      x ∈ comparisonBottomSupport w := by
  rw [comparisonBottomSupport_raise, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := by
      change y + 1 = x + 1 at hyx
      lia
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, by simp [succEmbedding]⟩

/-- A minimum insertion can remove an old comparison or introduce bottom
`1`, but it cannot create a new positive old label as a comparison bottom. -/
theorem succ_mem_comparisonBottomSupport_step_imp {w : List Nat}
    (hpos : IsPositive w) {r x : Nat} (hr : r ≤ w.length) (hx : 0 < x)
    (hmem : x + 1 ∈ comparisonBottomSupport (step r w)) :
    x ∈ comparisonBottomSupport w := by
  induction r generalizing w with
  | zero =>
      cases w with
      | nil => simp [step, raise, comparisonBottomSupport] at hmem
      | cons a w =>
          have ha := hpos a (by simp)
          rw [step_zero] at hmem
          simp only [raise, List.map_cons] at hmem
          rw [comparisonBottomSupport, if_pos (by lia)] at hmem
          apply (succ_mem_comparisonBottomSupport_raise_iff (a :: w) x).mp
          simpa [raise] using hmem
  | succ r ih =>
      cases w with
      | nil => simp at hr
      | cons a w =>
          have ha := hpos a (by simp)
          have hposTail : IsPositive w := by
            intro y hy
            exact hpos y (by simp [hy])
          have hrTail : r ≤ w.length := by simpa using hr
          cases r with
          | zero =>
              cases w with
              | nil =>
                  simp [step, raise, comparisonBottomSupport] at hmem
                  exfalso
                  lia
              | cons b w =>
                  have hb := hposTail b (by simp)
                  rw [step_succ, step_zero] at hmem
                  simp only [raise, List.map_cons] at hmem
                  rw [comparisonBottomSupport, if_neg (by lia),
                    comparisonBottomSupport, if_pos (by lia),
                    Finset.mem_insert] at hmem
                  rcases hmem with hOne | hmem
                  · lia
                  · have htail :=
                      (succ_mem_comparisonBottomSupport_raise_iff
                        (b :: w) x).mp hmem
                    rw [comparisonBottomSupport]
                    split
                    · exact htail
                    · exact Finset.mem_insert_of_mem htail
          | succ r =>
              cases w with
              | nil => simp at hrTail
              | cons b w =>
                  rw [step_succ, step_succ] at hmem
                  rw [comparisonBottomSupport] at hmem ⊢
                  by_cases hab : a < b
                  · rw [if_pos (by lia)] at hmem
                    rw [if_pos hab]
                    apply ih hposTail hrTail
                    simpa [step_succ] using hmem
                  · rw [if_neg (by lia)] at hmem
                    rw [if_neg hab]
                    rw [Finset.mem_insert] at hmem ⊢
                    rcases hmem with hxb | hmem
                    · left
                      change x + 1 = b + 1 at hxb
                      lia
                    · right
                      apply ih hposTail hrTail
                      simpa [step_succ] using hmem

theorem zero_not_mem_comparisonBottomSupport {w : List Nat}
    (hpos : IsPositive w) : 0 ∉ comparisonBottomSupport w := by
  induction w with
  | nil => simp [comparisonBottomSupport]
  | cons a w ih =>
      cases w with
      | nil => simp [comparisonBottomSupport]
      | cons b w =>
          have hb := hpos b (by simp)
          have htail : IsPositive (b :: w) := by
            intro x hx
            exact hpos x (by simp [hx])
          rw [comparisonBottomSupport]
          split
          · exact ih htail
          · intro hzero
            rw [Finset.mem_insert] at hzero
            rcases hzero with hzero | hzero
            · lia
            · exact ih htail hzero

theorem one_not_mem_comparisonBottomSupport_step_zero {w : List Nat}
    (hpos : IsPositive w) :
    1 ∉ comparisonBottomSupport (step 0 w) := by
  rw [step_zero]
  cases w with
  | nil => simp [raise, comparisonBottomSupport]
  | cons a w =>
      have ha := hpos a (by simp)
      simp only [raise, List.map_cons]
      rw [comparisonBottomSupport, if_pos (by lia)]
      change 1 ∉ comparisonBottomSupport (raise (a :: w))
      rw [comparisonBottomSupport_raise]
      simpa [succEmbedding] using zero_not_mem_comparisonBottomSupport hpos

theorem add_length_mem_comparisonBottomSupport_decodeFrom_imp
    {w code : List Nat} (hpos : IsPositive w)
    (hcode : ValidFrom w.length code) {x : Nat} (hx : 0 < x)
    (hmem : x + code.length ∈
      comparisonBottomSupport (decodeFrom w code)) :
    x ∈ comparisonBottomSupport w := by
  induction code generalizing w x with
  | nil => simpa using hmem
  | cons r code ih =>
      have hlength := length_step hcode.1
      have htail : ValidFrom (step r w).length code := by
        rw [hlength]
        exact hcode.2
      have hmemTail : x + 1 + code.length ∈
          comparisonBottomSupport (decodeFrom (step r w) code) := by
        rw [decodeFrom_cons] at hmem
        have hadd : x + (r :: code).length = x + 1 + code.length := by
          simp
          lia
        rw [hadd] at hmem
        exact hmem
      have hstep := ih (isPositive_step r w) htail (by lia) hmemTail
      exact succ_mem_comparisonBottomSupport_step_imp hpos hcode.1 hx hstep

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
