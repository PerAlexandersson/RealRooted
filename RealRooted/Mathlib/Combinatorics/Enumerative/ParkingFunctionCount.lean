import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import RealRooted.Mathlib.Combinatorics.Enumerative.ParkingFunction

namespace ParkingFunction

section Pollak

variable {n : ℕ}

private def countBelow (w : Fin n → Fin (n + 1)) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (w i).val < j).card

private def validWord (u : Fin n → Fin (n + 1)) : Prop :=
  ∀ k : Fin (n + 1), k.val ≤ countBelow u k.val

private instance (u : Fin n → Fin (n + 1)) : Decidable (validWord u) := by
  unfold validWord
  infer_instance

private lemma sub_val_cases (a r : Fin (n + 1)) :
    (r ≤ a ∧ (a - r).val = a.val - r.val) ∨
      (a < r ∧ (a - r).val = n + 1 + a.val - r.val) := by
  rcases le_or_gt r a with h | h
  · exact Or.inl ⟨h, Fin.coe_sub_iff_le.2 h⟩
  · exact Or.inr ⟨h, Fin.coe_sub_iff_lt.2 h⟩

private lemma shift_count_le (w : Fin n → Fin (n + 1)) (r : Fin (n + 1))
    (k j : ℕ) (hk : r.val + k = j) (hj : j ≤ n + 1) :
    countBelow (fun i => w i - r) k + countBelow w r = countBelow w j := by
  unfold countBelow
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := (w i).isLt
  rcases sub_val_cases (w i) r with ⟨h, e⟩ | ⟨h, e⟩ <;>
    simp only [Fin.le_def, Fin.lt_def] at h <;> rw [e] <;> split_ifs <;> lia

private lemma shift_count_gt (w : Fin n → Fin (n + 1)) (r : Fin (n + 1))
    (k j : ℕ) (hk : r.val + k = j + (n + 1)) (hkn : k ≤ n) :
    countBelow (fun i => w i - r) k + countBelow w r = n + countBelow w j := by
  unfold countBelow
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  have key : ∀ i : Fin n,
      (if ((w i - r : Fin (n + 1)) : ℕ) < k then 1 else 0) +
          (if ((w i : Fin (n + 1)) : ℕ) < (r : ℕ) then 1 else 0) =
        1 + (if ((w i : Fin (n + 1)) : ℕ) < j then 1 else 0) := by
    intro i
    have h1 := (w i).isLt
    rcases sub_val_cases (w i) r with ⟨h, e⟩ | ⟨h, e⟩ <;>
      simp only [Fin.le_def, Fin.lt_def] at h <;> rw [e] <;> split_ifs <;> lia
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  simp

private lemma countBelow_zero (w : Fin n → Fin (n + 1)) : countBelow w 0 = 0 := by
  simp [countBelow]

private lemma countBelow_top (w : Fin n → Fin (n + 1)) :
    countBelow w (n + 1) = n := by
  simp [countBelow, Finset.filter_true_of_mem, (Fin.isLt _)]

private lemma validWord_iff (w : Fin n → Fin (n + 1)) (r : Fin (n + 1)) :
    validWord (fun i => w i - r) ↔ ∀ j : ℕ, j ≤ n →
      (j < r.val → countBelow w r + j < countBelow w j + r) ∧
      (r.val ≤ j → countBelow w r + j ≤ countBelow w j + r) := by
  have hr := r.isLt
  have h0 := countBelow_zero w
  have htop := countBelow_top w
  constructor
  · intro hv j hj
    have hv' : ∀ k, k ≤ n → k ≤ countBelow (fun i => w i - r) k :=
      fun k hk => hv ⟨k, by lia⟩
    refine ⟨fun hjr => ?_, fun hrj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · have := shift_count_le w r (n + 1 - r) (n + 1) (by lia) le_rfl
        have := hv' (n + 1 - r) (by lia)
        lia
      · have := shift_count_gt w r (j + (n + 1) - r) j (by lia) (by lia)
        have := hv' (j + (n + 1) - r) (by lia)
        lia
    · have := shift_count_le w r (j - r) j (by lia) (by lia)
      have := hv' (j - r) (by lia)
      lia
  · intro h k
    have hk := k.isLt
    by_cases h1 : r.val + k.val ≤ n
    · have := shift_count_le w r k (r + k) rfl (by lia)
      have := (h (r + k) h1).2 (by lia)
      lia
    · by_cases h2 : r.val + k.val = n + 1
      · have := shift_count_le w r k (n + 1) h2 le_rfl
        have := (h 0 (by lia)).1 (by lia)
        lia
      · have := shift_count_gt w r k (r + k - (n + 1)) (by lia) (by lia)
        have := (h (r + k - (n + 1)) (by lia)).1 (by lia)
        lia

private lemma existsUnique_validWord (w : Fin n → Fin (n + 1)) :
    ∃! r : Fin (n + 1), validWord (fun i => w i - r) := by
  have hex : ∃ j, j ≤ n ∧ ∀ i, i ≤ n → countBelow w j + i ≤ countBelow w i + j := by
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.range (n + 1))
      (fun j => (countBelow w j : ℤ) - j) ⟨0, by simp⟩
    refine ⟨j, by simpa [Nat.lt_succ_iff] using hj, fun i hi => ?_⟩
    have := hmin i (by simp only [Finset.mem_range]; lia)
    lia
  classical
  have hspec := Nat.find_spec hex
  have hvalid : validWord (fun i => w i - ⟨Nat.find hex, by lia⟩) := by
    refine (validWord_iff w _).2 fun j hj => ⟨fun hjr => ?_, fun _ => hspec.2 j hj⟩
    have := Nat.find_min hex hjr
    push Not at this
    obtain ⟨i, hi, hlt⟩ := this hj
    have := hspec.2 i hi
    simp only at *
    lia
  refine ⟨⟨Nat.find hex, by lia⟩, hvalid, ?_⟩
  · intro r hr
    have hr' := (validWord_iff w r).1 hr
    have hs := (validWord_iff w _).1 hvalid
    apply Fin.ext
    simp only at hs ⊢
    have hrn := r.isLt
    rcases lt_trichotomy r.val (Nat.find hex) with h | h | h
    · have := (hs r (by lia)).1 h
      have := (hr' (Nat.find hex) hspec.1).2 h.le
      lia
    · exact h
    · have := (hr' (Nat.find hex) hspec.1).1 h
      have := (hs r (by lia)).2 h.le
      lia

private def validWords (n : ℕ) : Finset (Fin n → Fin (n + 1)) :=
  Finset.univ.filter validWord

private lemma card_validWords_mul (n : ℕ) :
    (n + 1) * (validWords n).card = (n + 1) ^ n := by
  have h1 : ∀ w : Fin n → Fin (n + 1),
      (∑ c : Fin (n + 1), if validWord (fun i => w i - c) then 1 else 0) = 1 := by
    intro w
    obtain ⟨r, hr, huniq⟩ := existsUnique_validWord w
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro b _ hb
      have hnot : ¬ validWord (fun i => w i - b) := fun h => hb (huniq b h)
      simp [hnot]
    · simp
  have h2 : ∀ c : Fin (n + 1),
      (∑ w : Fin n → Fin (n + 1), if validWord (fun i => w i - c) then 1 else 0) =
        (validWords n).card := by
    intro c
    rw [← Finset.card_filter]
    apply Finset.card_nbij' (fun w i => w i - c) (fun u i => u i + c)
    · intro w hw
      simpa [validWords] using hw
    · intro u hu
      simpa [validWords] using hu
    · intro w _
      simp
    · intro u _
      simp
  calc
    (n + 1) * (validWords n).card =
        ∑ c : Fin (n + 1), ∑ w : Fin n → Fin (n + 1),
          (if validWord (fun i => w i - c) then 1 else 0) := by simp [h2]
    _ = ∑ w : Fin n → Fin (n + 1), ∑ c : Fin (n + 1),
          (if validWord (fun i => w i - c) then 1 else 0) := Finset.sum_comm
    _ = (n + 1) ^ n := by simp [h1]

private lemma validWord_lt (u : Fin n → Fin (n + 1)) (hu : validWord u) (i : Fin n) :
    (u i).val < n := by
  by_contra h
  have hi : (u i).val = n := by
    have := (u i).isLt
    lia
  have h1 := hu ⟨n, by lia⟩
  have h2 : countBelow u n < n := by
    unfold countBelow
    calc
      _ < (Finset.univ : Finset (Fin n)).card :=
        Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, by simp, by simp [hi]⟩)
      _ = n := by simp
  simp only at h1
  lia

private lemma validWord_castSucc_iff (w : Fin n → Fin n) :
    validWord (fun i => (w i).castSucc) ↔ IsParkingFunction w := by
  simp [validWord, IsParkingFunction, countBelow]

private lemma card_validWords (n : ℕ) :
    (validWords n).card = (parkingFunctions n).card := by
  symm
  refine Finset.card_bij (fun w _ i => (w i).castSucc) ?_ ?_ ?_
  · intro w hw
    simp only [parkingFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simpa [validWords, validWord_castSucc_iff] using hw
  · intro a _ b _ h
    funext i
    have := congrFun h i
    simpa using this
  · intro u hu
    simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨fun i => (u i).castLT (validWord_lt u hu i), ?_, ?_⟩
    · simp only [parkingFunctions, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← validWord_castSucc_iff]
      simpa using hu
    · funext i
      simp

end Pollak

/-- Aristotle (Harmonic)'s Pollak cyclic-shift argument gives the parking-function count. -/
theorem card_parkingFunctions (n : ℕ) :
    (parkingFunctions n).card = (n + 1) ^ (n - 1) := by
  have h := card_validWords_mul n
  rw [card_validWords] at h
  rcases n with _ | n
  · simpa using h
  · rw [pow_succ', Nat.add_sub_cancel] at *
    exact Nat.eq_of_mul_eq_mul_left (by lia) h

end ParkingFunction
