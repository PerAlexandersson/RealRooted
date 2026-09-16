import Mathlib.Data.List.InsertIdx
import Mathlib.Logic.Equiv.Basic

/-!
# Words built by repeated minimum insertion

A chronological insertion code builds a word by raising every old positive
label and inserting the new minimum `1`.  This file records the exact local
forms and the transport of label swaps through later insertion steps.
-/

namespace RealRooted.MinimumInsertionWord

/-- Raise every label in a word by one. -/
def raise (w : List Nat) : List Nat := w.map Nat.succ

/-- Raise every old label and insert the new minimum `1` at position `r`. -/
def step (r : Nat) (w : List Nat) : List Nat :=
  (raise w).insertIdx r 1

/-- Every label in the word is strictly positive. -/
def IsPositive (w : List Nat) : Prop := ∀ x ∈ w, 0 < x

/-- The first two entries of a word form a strict ascent. -/
def StartsWithAscent : List Nat → Prop
  | a :: b :: _ => a < b
  | _ => False

/-- Raising a word makes all its labels positive. -/
theorem isPositive_raise (w : List Nat) : IsPositive (raise w) := by
  intro x hx
  rw [RealRooted.MinimumInsertionWord.raise, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Nat.succ_pos y

/-- A minimum-insertion step has only positive labels. -/
theorem isPositive_step (r : Nat) (w : List Nat) : IsPositive (step r w) := by
  intro x hx
  rcases List.eq_or_mem_of_mem_insertIdx hx with rfl | hx
  · exact Nat.zero_lt_one
  · exact isPositive_raise w x hx

/-- Inserting a fresh value into a nodup list preserves nodupness. -/
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

/-- Raising every entry preserves nodupness. -/
theorem nodup_raise {w : List Nat} (hw : w.Nodup) : (raise w).Nodup := by
  induction w with
  | nil => simp [raise]
  | cons a w ih =>
      rw [List.nodup_cons] at hw
      rw [raise, List.map_cons, List.nodup_cons]
      constructor
      · intro ha
        rw [List.mem_map] at ha
        obtain ⟨b, hb, hab⟩ := ha
        have hba : b = a := Nat.succ.inj hab
        exact hw.1 (hba ▸ hb)
      · exact ih hw.2

/-- A valid minimum insertion into a positive nodup word remains nodup. -/
theorem nodup_step {w : List Nat} (hw : w.Nodup) (hpos : IsPositive w)
    {r : Nat} (hr : r ≤ w.length) : (step r w).Nodup := by
  apply nodup_insertIdx (nodup_raise hw)
  · intro hone
    rw [raise, List.mem_map] at hone
    obtain ⟨a, ha, hsucc⟩ := hone
    have hapos := hpos a ha
    lia
  · simpa [raise] using hr

/-- Validity of a suffix of insertion positions beginning with a word of
length `n`. -/
def ValidFrom : Nat → List Nat → Prop
  | _, [] => True
  | n, r :: code => r ≤ n ∧ ValidFrom (n + 1) code

/-- A code suffix is valid exactly when its indexed positions satisfy the
corresponding running length bounds. -/
theorem validFrom_iff_get (n : Nat) (code : List Nat) :
    ValidFrom n code ↔
      ∀ i : Fin code.length, code.get i ≤ n + i.1 := by
  induction code generalizing n with
  | nil => simp [ValidFrom]
  | cons r code ih =>
      rw [ValidFrom, ih]
      constructor
      · rintro ⟨hr, hcode⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hr
        · change code.get j ≤ n + (j.1 + 1)
          have hj := hcode j
          lia
      · intro h
        constructor
        · simpa using h ⟨0, by simp⟩
        · intro i
          have hi := h i.succ
          change code.get i ≤ n + (i.1 + 1) at hi
          lia

/-- Every prefix of a valid insertion code is valid. -/
theorem ValidFrom.take {n : Nat} {code : List Nat}
    (hcode : ValidFrom n code) (k : Nat) :
    ValidFrom n (code.take k) := by
  induction code generalizing n k with
  | nil => simp [ValidFrom]
  | cons r code ih =>
      cases k with
      | zero => simp [ValidFrom]
      | succ k =>
          simp only [List.take_succ_cons, ValidFrom]
          exact ⟨hcode.1, ih hcode.2 k⟩

/-- Dropping `k` entries from a valid code advances the running length by
`k`. -/
theorem ValidFrom.drop {n : Nat} {code : List Nat}
    (hcode : ValidFrom n code) {k : Nat} (hk : k ≤ code.length) :
    ValidFrom (n + k) (code.drop k) := by
  induction k generalizing n code with
  | zero => simpa
  | succ k ih =>
      cases code with
      | nil => simp at hk
      | cons r code =>
          simp only [List.drop_succ_cons]
          have hkTail : k ≤ code.length := by simpa using hk
          have htail := ih hcode.2 hkTail
          have hadd : n + Nat.succ k = n + 1 + k := by lia
          rw [hadd]
          exact htail

@[simp] theorem step_zero (w : List Nat) :
    step 0 w = 1 :: raise w := by
  rfl

/-- A valid minimum insertion increases the word length by one. -/
theorem length_step {r : Nat} {w : List Nat} (hr : r ≤ w.length) :
    (step r w).length = w.length + 1 := by
  rw [step, List.length_insertIdx_of_le_length]
  · simp [raise]
  · simpa [raise] using hr

/-- Inserting a new minimum at the beginning produces an initial ascent when
the old word is positive and nonempty. -/
theorem StartsWithAscent.step_zero {w : List Nat} (hw : w ≠ [])
    (hpos : IsPositive w) : StartsWithAscent (step 0 w) := by
  cases w with
  | nil => contradiction
  | cons a w =>
    have ha := hpos a (by simp)
    simp [raise, StartsWithAscent, ha]

/-- Insertion after the first two positions preserves the initial ascent. -/
theorem StartsWithAscent.step_add_two {w : List Nat}
    (hw : StartsWithAscent w) (r : Nat) :
    StartsWithAscent (step (r + 2) w) := by
  cases w with
  | nil => simp [StartsWithAscent] at hw
  | cons a w =>
    cases w with
    | nil => simp [StartsWithAscent] at hw
    | cons b w =>
      simpa [step, raise, StartsWithAscent] using hw

/-- The displayed inverse-word form of a normal `(0,2)` extension. -/
@[simp] theorem step_normal_pair (a : Nat) (w : List Nat) :
    step 2 (step 0 (a :: w)) =
      2 :: (a + 2) :: 1 :: w.map (fun x => x + 2) := by
  simp [step, raise, Nat.succ_eq_add_one,
    Nat.add_comm, Nat.add_left_comm]

/-- The displayed inverse-word form of an exceptional `(1,0)` extension. -/
@[simp] theorem step_exceptional_pair (a : Nat) (w : List Nat) :
    step 0 (step 1 (a :: w)) =
      1 :: (a + 2) :: 2 :: w.map (fun x => x + 2) := by
  simp [step, raise, Nat.succ_eq_add_one,
    Nat.add_comm, Nat.add_left_comm]

/-- Raising all labels transports a swap to the two successor labels. -/
theorem swap_succ (a b n : Nat) :
    Equiv.swap (a + 1) (b + 1) (n + 1) = Equiv.swap a b n + 1 := by
  by_cases hab : a = b
  · subst b
    simp
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  by_cases hna : n = a
  · subst n
    simp
  · by_cases hnb : n = b
    · subst n
      simp [Ne.symm hab]
    · simp [hna, hnb]

/-- A swap of positive successor labels fixes the newly inserted minimum. -/
theorem swap_succ_fix_one (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Equiv.swap (a + 1) (b + 1) 1 = 1 := by
  apply Equiv.swap_apply_of_ne_of_ne <;> lia

/-- A later minimum insertion raises both labels in a transported swap. -/
theorem step_map_swap (r a b : Nat) (w : List Nat)
    (ha : 0 < a) (hb : 0 < b) :
    step r (w.map (Equiv.swap a b)) =
      (step r w).map (Equiv.swap (a + 1) (b + 1)) := by
  simp only [step, raise, List.map_insertIdx, List.map_map]
  rw [swap_succ_fix_one a b ha hb]
  congr 1
  apply List.map_congr_left
  intro n hn
  exact (swap_succ a b n).symm

/-- Decode a suffix of chronological insertion positions from an existing
word. -/
def decodeFrom (w : List Nat) (code : List Nat) : List Nat :=
  code.foldl (fun word r => step r word) w

@[simp] theorem decodeFrom_nil (w : List Nat) : decodeFrom w [] = w := rfl

@[simp] theorem decodeFrom_cons (w : List Nat) (r : Nat) (code : List Nat) :
    decodeFrom w (r :: code) = decodeFrom (step r w) code := rfl

/-- Decoding a concatenated code is successive decoding. -/
theorem decodeFrom_append (w : List Nat) (left right : List Nat) :
    decodeFrom w (left ++ right) = decodeFrom (decodeFrom w left) right := by
  exact List.foldl_append

/-- Decode a complete chronological insertion code from the empty word. -/
def decode (code : List Nat) : List Nat := decodeFrom [] code

/-- A positive starting word stays positive through any decoded suffix. -/
theorem IsPositive.decodeFrom {w code : List Nat} (hw : IsPositive w) :
    IsPositive (decodeFrom w code) := by
  induction code generalizing w with
  | nil => exact hw
  | cons r code ih => exact ih (isPositive_step r w)

/-- Every word decoded from the empty word has positive labels. -/
theorem IsPositive.decode (code : List Nat) : IsPositive (decode code) := by
  exact IsPositive.decodeFrom (by simp [IsPositive])

/-- Decoding a valid suffix adds exactly its length to the word length. -/
theorem length_decodeFrom {w code : List Nat}
    (hcode : ValidFrom w.length code) :
    (decodeFrom w code).length = w.length + code.length := by
  induction code generalizing w with
  | nil => simp
  | cons r code ih =>
      have hlength := length_step hcode.1
      have htail : ValidFrom (step r w).length code := by
        rw [hlength]
        exact hcode.2
      rw [decodeFrom_cons, ih htail, hlength]
      simp only [List.length_cons]
      lia

/-- A valid complete code decodes to a word of the same length. -/
theorem length_decode {code : List Nat} (hcode : ValidFrom 0 code) :
    (decode code).length = code.length := by
  simpa [decode] using length_decodeFrom (w := []) (code := code) hcode

/-- Decoding a valid suffix from a positive nodup word preserves nodupness. -/
theorem Nodup.decodeFrom {w code : List Nat} (hw : w.Nodup)
    (hpos : IsPositive w) (hcode : ValidFrom w.length code) :
    (decodeFrom w code).Nodup := by
  induction code generalizing w with
  | nil => exact hw
  | cons r code ih =>
      have hstep := nodup_step hw hpos hcode.1
      have hlength := length_step hcode.1
      rw [decodeFrom_cons]
      apply ih hstep (isPositive_step r w)
      rw [hlength]
      exact hcode.2

/-- Decoding a valid insertion code produces a nodup word. -/
theorem Nodup.decode {code : List Nat} (hcode : ValidFrom 0 code) :
    (decode code).Nodup := by
  exact Nodup.decodeFrom (by simp) (by simp [IsPositive]) hcode

/-- A common suffix transports a swap by the length of that suffix. -/
theorem decodeFrom_map_swap (code w : List Nat) (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) :
    decodeFrom (w.map (Equiv.swap a b)) code =
      (decodeFrom w code).map
        (Equiv.swap (a + code.length) (b + code.length)) := by
  induction code generalizing w a b with
  | nil => simp
  | cons r code ih =>
      rw [decodeFrom_cons, step_map_swap r a b w ha hb]
      rw [ih (w := step r w) (a := a + 1) (b := b + 1)
        (by lia) (by lia)]
      simp only [List.length_cons]
      congr 1
      lia

/-- The exceptional pair is the normal pair with labels `1,2` swapped. -/
theorem step_exceptional_pair_eq_map_swap (a : Nat) (w : List Nat)
    (ha : 0 < a) (hw : ∀ x ∈ w, 0 < x) :
    step 0 (step 1 (a :: w)) =
      (step 2 (step 0 (a :: w))).map (Equiv.swap 1 2) := by
  have haSwap : Equiv.swap 1 2 (a + 2) = a + 2 :=
    Equiv.swap_apply_of_ne_of_ne (by lia) (by lia)
  have hwSwap :
      (w.map (fun x => x + 2)).map (Equiv.swap 1 2) =
        w.map (fun x => x + 2) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (by lia) (by have := hw x hx; lia)
  rw [step_normal_pair, step_exceptional_pair]
  simp only [List.map_cons, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [haSwap, hwSwap]

/-- After any common suffix of later insertions, the local swap of labels
`1,2` is transported by the suffix length. -/
theorem decodeFrom_exceptional_pair_eq_map_swap
    (code : List Nat) (a : Nat) (w : List Nat)
    (ha : 0 < a) (hw : ∀ x ∈ w, 0 < x) :
    decodeFrom (step 0 (step 1 (a :: w))) code =
      (decodeFrom (step 2 (step 0 (a :: w))) code).map
        (Equiv.swap (1 + code.length) (2 + code.length)) := by
  rw [step_exceptional_pair_eq_map_swap a w ha hw]
  exact decodeFrom_map_swap code (step 2 (step 0 (a :: w))) 1 2
    Nat.zero_lt_one (by decide)

/-- The ascent/descent comparison word, with `true` for an ascent. -/
def comparisonWord : List Nat → List Bool
  | a :: b :: w => decide (a < b) :: comparisonWord (b :: w)
  | _ => []

/-- Raising every label preserves the complete comparison word. -/
theorem comparisonWord_raise (w : List Nat) :
    comparisonWord (raise w) = comparisonWord w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases w with
      | nil => rfl
      | cons b w =>
          simp only [raise, List.map_cons, comparisonWord,
            Nat.succ_lt_succ_iff]
          change decide (a < b) :: comparisonWord (raise (b :: w)) =
            decide (a < b) :: comparisonWord (b :: w)
          rw [ih]

/-- The comparison word after insertion at the front. -/
theorem comparisonWord_step_zero {w : List Nat} (hw : IsPositive w) :
    comparisonWord (step 0 w) =
      if w = [] then [] else true :: comparisonWord w := by
  cases w with
  | nil => rfl
  | cons a w =>
      have ha := hw a (by simp)
      simp only [step, raise, List.map_cons, List.insertIdx_zero,
        comparisonWord]
      rw [if_neg (List.cons_ne_nil a w)]
      change decide (1 < a.succ) :: comparisonWord (raise (a :: w)) =
        true :: comparisonWord (a :: w)
      rw [comparisonWord_raise]
      simp [ha]

/-- Insertion past a head recurses on the tail. -/
theorem step_succ (r a : Nat) (w : List Nat) :
    step (r + 1) (a :: w) = (a + 1) :: step r w := by
  rfl

/-- Applying the same valid minimum insertion to positive words with the same
comparison word preserves comparison-word equality. -/
theorem comparisonWord_step_congr {w v : List Nat}
    (hw : IsPositive w) (hv : IsPositive v)
    (hlen : w.length = v.length)
    (hcomp : comparisonWord w = comparisonWord v)
    {r : Nat} (hr : r ≤ w.length) :
    comparisonWord (step r w) = comparisonWord (step r v) := by
  induction r generalizing w v with
  | zero =>
      rw [comparisonWord_step_zero hw, comparisonWord_step_zero hv]
      cases w <;> cases v <;> simp_all
  | succ r ih =>
      cases w with
      | nil => simp at hr
      | cons a w =>
          cases v with
          | nil => simp at hlen
          | cons b v =>
              rw [step_succ, step_succ]
              have hwTail : IsPositive w := by
                intro x hx
                exact hw x (by simp [hx])
              have hvTail : IsPositive v := by
                intro x hx
                exact hv x (by simp [hx])
              have hlenTail : w.length = v.length := by simpa using hlen
              have hrTail : r ≤ w.length := by simpa using hr
              have hcompTail : comparisonWord w = comparisonWord v := by
                cases w with
                | nil =>
                    have hvNil : v = [] :=
                      List.eq_nil_of_length_eq_zero hlenTail.symm
                    subst v
                    rfl
                | cons c w =>
                    cases v with
                    | nil => simp at hlenTail
                    | cons d v =>
                        simp only [comparisonWord] at hcomp
                        exact List.cons.inj hcomp |>.2
              have hstep := ih hwTail hvTail hlenTail hcompTail hrTail
              cases r with
              | zero =>
                  cases w with
                  | nil =>
                      have hvNil : v = [] :=
                        List.eq_nil_of_length_eq_zero hlenTail.symm
                      subst v
                      rfl
                  | cons c w =>
                      cases v with
                      | nil => simp at hlenTail
                      | cons d v =>
                          have hc := hwTail c (by simp)
                          have hd := hvTail d (by simp)
                          simp only [step, raise, List.map_cons,
                            List.insertIdx_zero, comparisonWord]
                          have hraise : comparisonWord (raise (c :: w)) =
                              comparisonWord (raise (d :: v)) := by
                            rw [comparisonWord_raise, comparisonWord_raise]
                            exact hcompTail
                          simpa [raise, hc, hd] using
                            congrArg (fun z => false :: true :: z) hraise
              | succ r =>
                  cases w with
                  | nil => simp at hrTail
                  | cons c w =>
                      cases v with
                      | nil => simp at hlenTail
                      | cons d v =>
                          simp only [step_succ, comparisonWord,
                            Nat.add_lt_add_iff_right]
                          simp only [comparisonWord] at hcomp
                          exact congrArg₂ List.cons (List.cons.inj hcomp |>.1)
                            hstep

/-- The local normal and exceptional two-step words have the same complete
comparison word. -/
theorem comparisonWord_step_pair (a : Nat) (w : List Nat)
    (ha : 0 < a) (hw : ∀ x ∈ w, 0 < x) :
    comparisonWord (step 0 (step 1 (a :: w))) =
      comparisonWord (step 2 (step 0 (a :: w))) := by
  rw [step_exceptional_pair, step_normal_pair]
  cases w with
  | nil => simp [comparisonWord, ha]
  | cons b w =>
      have hb := hw b (by simp)
      simp [comparisonWord, ha, hb]

/-- A common valid suffix preserves equality of comparison words. -/
theorem comparisonWord_decodeFrom_congr {w v code : List Nat}
    (hw : IsPositive w) (hv : IsPositive v)
    (hlen : w.length = v.length)
    (hcomp : comparisonWord w = comparisonWord v)
    (hcode : ValidFrom w.length code) :
    comparisonWord (decodeFrom w code) =
      comparisonWord (decodeFrom v code) := by
  induction code generalizing w v with
  | nil => exact hcomp
  | cons r code ih =>
      rw [decodeFrom_cons, decodeFrom_cons]
      have hrW : r ≤ w.length := hcode.1
      have hstep := comparisonWord_step_congr hw hv hlen hcomp hrW
      have hlengthW := length_step hrW
      have hrV : r ≤ v.length := by simpa [hlen] using hrW
      have hlengthV := length_step hrV
      have htail : ValidFrom (step r w).length code := by
        rw [hlengthW]
        exact hcode.2
      apply ih (isPositive_step r w) (isPositive_step r v)
      · rw [hlengthW, hlengthV, hlen]
      · exact hstep
      · exact htail

end RealRooted.MinimumInsertionWord
