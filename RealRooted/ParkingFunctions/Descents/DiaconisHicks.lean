import RealRooted.ParkingFunctions.Descents.Basic
import RealRooted.Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Sort

/-!
# Cyclic value action for parking-function descents

This low finite-action layer records the cyclic value shifts used in the
Diaconis--Hicks comparison between parking functions and words on an alphabet
of size one larger.  It proves only the orbit facts; sorting values along
chains and selecting the unique parking representative are later work.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- Cyclically shift every value of a word on `Fin (n + 1)`. -/
def cyclicValueShiftEquiv (n : ℕ) (c : Fin (n + 1)) :
    (Fin n → Fin (n + 1)) ≃ (Fin n → Fin (n + 1)) :=
  Equiv.piCongrRight fun _ => finCycle c

/-- The word obtained by cyclically shifting all values by `c`. -/
def cyclicValueShift {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) : Fin n → Fin (n + 1) :=
  cyclicValueShiftEquiv n c w

/-- Sort the values of a word along its `Fin n` chain of positions. -/
def chainSortedWord {n m : ℕ} (w : Fin n → Fin m) : Fin n → Fin m :=
  fun i => (List.insertionSort (· ≤ ·) (List.ofFn w)).get ⟨i, by simp⟩

/-- Sorting a word along one chain makes it monotone. -/
theorem chainSortedWord_monotone {n m : ℕ} (w : Fin n → Fin m) :
    Monotone (chainSortedWord w) := by
  intro i j hij
  exact (List.pairwise_insertionSort (r := (· ≤ ·)) (List.ofFn w)).sortedLE.monotone_get hij

/-- Sorting a word along one chain preserves its value multiset. -/
theorem chainSortedWord_perm {n m : ℕ} (w : Fin n → Fin m) :
    List.Perm (List.ofFn (chainSortedWord w)) (List.ofFn w) := by
  rw [show List.ofFn (chainSortedWord w) =
      List.insertionSort (· ≤ ·) (List.ofFn w) by
    apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      simp [chainSortedWord]]
  exact List.perm_insertionSort _ _

/-- A permutation of a word's values preserves every lower-alphabet count. -/
theorem card_lt_eq_of_ofFn_perm {n : ℕ} {w v : Fin n → Fin n}
    (h : List.Perm (List.ofFn w) (List.ofFn v)) (k : ℕ) :
    (Finset.univ.filter fun i => (w i).val < k).card =
      (Finset.univ.filter fun i => (v i).val < k).card := by
  rw [show (Finset.univ.filter fun i => (w i).val < k).card =
        List.countP (fun x => decide (x.val < k)) (List.ofFn w) by
      simpa using List.card_filter_univ_eq_countP_ofFn w (fun x => decide (x.val < k))]
  rw [h.countP_eq]
  simpa using (List.card_filter_univ_eq_countP_ofFn v (fun x => decide (x.val < k))).symm

/-- The parking-function condition depends only on the word's value multiset. -/
theorem isParkingFunction_iff_of_ofFn_perm {n : ℕ} {w v : Fin n → Fin n}
    (h : List.Perm (List.ofFn w) (List.ofFn v)) :
    IsParkingFunction w ↔ IsParkingFunction v := by
  constructor <;> intro hw k hk
  · rw [← card_lt_eq_of_ofFn_perm h k]
    exact hw k hk
  · rw [card_lt_eq_of_ofFn_perm h k]
    exact hw k hk

@[simp]
theorem cyclicValueShift_apply {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) (i : Fin n) :
    cyclicValueShift c w i = finCycle c (w i) := rfl

/-- Every fixed cyclic value shift is a bijection on words. -/
theorem cyclicValueShift_bijective {n : ℕ} (c : Fin (n + 1)) :
    Function.Bijective (cyclicValueShift c :
      (Fin n → Fin (n + 1)) → Fin n → Fin (n + 1)) :=
  (cyclicValueShiftEquiv n c).bijective

/-- Cyclic value shifts preserve equality relations between positions. -/
theorem cyclicValueShift_eq_iff {n : ℕ} (c : Fin (n + 1))
    (w : Fin n → Fin (n + 1)) (i j : Fin n) :
    cyclicValueShift c w i = cyclicValueShift c w j ↔ w i = w j := by
  change finCycle c (w i) = finCycle c (w j) ↔ w i = w j
  exact (finCycle c).injective.eq_iff

/-- For a nonempty word, distinct cyclic shifts produce distinct words. -/
theorem cyclicValueShift_injective_in_shift {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (n + 1)) :
    Function.Injective (fun c : Fin (n + 1) => cyclicValueShift c w) := by
  intro c d h
  have hzero := congrFun h ⟨0, hn⟩
  change w ⟨0, hn⟩ + c = w ⟨0, hn⟩ + d at hzero
  exact add_left_cancel hzero

/-- The cyclic value orbit of a nonempty word has the full alphabet size. -/
theorem card_cyclicValueShift_orbit {n : ℕ} (hn : 0 < n)
    (w : Fin n → Fin (n + 1)) :
    (Finset.univ.image fun c => cyclicValueShift c w).card = n + 1 := by
  rw [Finset.card_image_of_injective _ (cyclicValueShift_injective_in_shift hn w)]
  simp

/-- Regard a parking word as a word on the alphabet with one additional
letter. -/
def parkingWordEmbed {n : ℕ} (w : Fin n → Fin n) : Fin n → Fin (n + 1) :=
  fun i => (w i).castSucc

@[simp]
theorem parkingWordEmbed_apply {n : ℕ} (w : Fin n → Fin n) (i : Fin n) :
    parkingWordEmbed w i = (w i).castSucc := rfl

/-- The alphabet embedding of parking words is injective. -/
theorem parkingWordEmbed_injective {n : ℕ} :
    Function.Injective (parkingWordEmbed :
      (Fin n → Fin n) → Fin n → Fin (n + 1)) := by
  intro w v h
  funext i
  apply Fin.castSucc_injective
  exact congrFun h i

/-- Embedding the alphabet of a nonempty parking word preserves its descent
set. -/
theorem descentSet_parkingWordEmbed {n : ℕ} (w : Fin (n + 1) → Fin (n + 1)) :
    descentSet (parkingWordEmbed w) = descentSet w := by
  ext i
  simp [mem_descentSet_iff, parkingWordEmbed]

/-- Embedding the alphabet of a nonempty parking word preserves its descent
number. -/
theorem descentNumber_parkingWordEmbed {n : ℕ} (w : Fin (n + 1) → Fin (n + 1)) :
    descentNumber (parkingWordEmbed w) = descentNumber w := by
  rw [descentNumber, descentNumber, descentSet_parkingWordEmbed]

/-- The embedded parking functions form a literal subfamily of words over the
alphabet with one additional letter. -/
def embeddedParkingFunctions (n : ℕ) : Finset (Fin (n + 1) → Fin (n + 2)) :=
  (parkingFunctions (n + 1)).image parkingWordEmbed

/-- The parking descent polynomial is the descent-generating polynomial of its
embedded finite word family. -/
theorem parkingDescentPolynomial_succ_eq_descentGeneratingPolynomial_embedded
    (n : ℕ) :
    parkingDescentPolynomial (n + 1) =
      descentGeneratingPolynomial (R := ℝ) (embeddedParkingFunctions n) := by
  unfold parkingDescentPolynomial descentGeneratingPolynomial embeddedParkingFunctions
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [descentNumber_parkingWordEmbed]
  · intro w hw v hv hwv
    exact parkingWordEmbed_injective hwv

end

end RealRooted.ParkingFunctions
