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

/-- Validity of a suffix of insertion positions beginning with a word of
length `n`. -/
def ValidFrom : Nat → List Nat → Prop
  | _, [] => True
  | n, r :: code => r ≤ n ∧ ValidFrom (n + 1) code

@[simp] theorem step_zero (w : List Nat) :
    step 0 w = 1 :: raise w := by
  rfl

/-- A valid minimum insertion increases the word length by one. -/
theorem length_step {r : Nat} {w : List Nat} (hr : r ≤ w.length) :
    (step r w).length = w.length + 1 := by
  rw [step, List.length_insertIdx_of_le_length]
  · simp [raise]
  · simpa [raise] using hr

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

end RealRooted.MinimumInsertionWord
