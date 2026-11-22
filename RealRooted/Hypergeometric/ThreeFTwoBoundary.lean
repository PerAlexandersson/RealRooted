module

public import RealRooted.Hypergeometric.ThreeFTwo
import Mathlib.Tactic

/-!
# Strict interlacing at the weak three-over-two parameter boundary

We formalize the section “Strict interlacing at the weak parameter boundary”
of the unpublished manuscript supplied with RealRooted issue #1877.
We use the existing Lima parameter conventions and characteristic-polynomial identity.
The weak parameter range gives simple positive roots and strictly separated consecutive
rows exactly away from the face `b = a`, `d = c`.
-/

public section

open Polynomial

namespace RealRooted.Hypergeometric

/-- The diagonal-factor subsequence stays positive even at the weak boundary. -/
theorem branchedWeight_diag_pos {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d) (i : ℕ) :
    0 < branchedWeight a c b d (3 * i + 2) := by
  obtain ⟨m, he | ho⟩ := Nat.even_or_odd' i
  · subst i
    cases m with
    | zero => simpa [branchedWeight] using div_pos (mul_pos ha hc) (mul_pos hb hd)
    | succ m =>
        norm_num [branchedWeight, Nat.mul_add, Nat.add_div, Nat.add_mod, ← Nat.mul_assoc]
        positivity
  · subst i
    norm_num [branchedWeight, Nat.mul_add, Nat.add_div, Nat.add_mod, ← Nat.mul_assoc]
    positivity

/-- Every weight from index nine onward is positive throughout the weak range. -/
theorem branchedWeight_pos_of_nine_le {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a ≤ b) (h₂ : c - 1 ≤ b) (h₃ : a ≤ d) (h₄ : c ≤ d)
    {j : ℕ} (hj : 9 ≤ j) : 0 < branchedWeight a c b d j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hm : (0 : ℝ) < ((k + 6) / 6 : ℕ) := by
    exact_mod_cast (show 0 < (k + 6) / 6 by lia)
  have hba : 0 < b - a + ((k + 6) / 6 : ℕ) := by linarith
  have hdc : 0 < d - c + ((k + 6) / 6 : ℕ) := by linarith
  have hda : 0 < d - a + ((k + 6) / 6 : ℕ) := by linarith
  have hbc : 0 < b - c + ((k + 6) / 6 : ℕ) + 1 := by linarith
  rw [show 9 + k = (k + 6) + 3 by lia]
  dsimp only [branchedWeight]
  split <;> positivity

/-- The first subdiagonal is positive exactly away from the exceptional face. -/
theorem branchedWeight_initial_sub_pos_iff {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a ≤ b) (h₄ : c ≤ d) :
    0 < branchedWeight a c b d 2 *
      (branchedWeight a c b d 3 + branchedWeight a c b d 4) ↔ a < b ∨ c < d := by
  have h₂ := branchedWeight_diag_pos ha hc hb hd 0
  have hba : 0 ≤ b - a := sub_nonneg.mpr h₁
  have hdc : 0 ≤ d - c := sub_nonneg.mpr h₄
  have h₃ : 0 ≤ branchedWeight a c b d 3 := by
    norm_num [branchedWeight]
    positivity
  have h₅ : 0 ≤ branchedWeight a c b d 4 := by
    norm_num [branchedWeight]
    positivity
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hab : b = a := le_antisymm hn.1 h₁
    have hdc : d = c := le_antisymm hn.2 h₄
    simp [hab, hdc, branchedWeight] at h
  · intro h
    apply mul_pos h₂
    rcases h with h | h
    · have hp : 0 < branchedWeight a c b d 3 := by
        have hba : 0 < b - a := sub_pos.mpr h
        norm_num [branchedWeight]
        positivity
      exact add_pos_of_pos_of_nonneg hp h₅
    · have hp : 0 < branchedWeight a c b d 4 := by
        have hdc : 0 < d - c := sub_pos.mpr h
        norm_num [branchedWeight]
        positivity
      exact add_pos_of_nonneg_of_pos h₃ hp

/-- Every subsequent first-subdiagonal entry is positive on the entire weak range. -/
theorem branchedWeight_sub_pos_of_one_le {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a ≤ b) (h₂ : c - 1 ≤ b) (h₃ : a ≤ d) (h₄ : c ≤ d)
    {i : ℕ} (hi : 1 ≤ i) :
    0 < branchedWeight a c b d (3 * i + 2) *
        (branchedWeight a c b d (3 * i + 3) + branchedWeight a c b d (3 * i + 4)) +
      branchedWeight a c b d (3 * i + 1) * branchedWeight a c b d (3 * i + 3) := by
  have hn := branchedWeight_nonneg ha hc hb hd h₁ h₂ h₃ h₄
  have hsum : 0 < branchedWeight a c b d (3 * i + 3) +
      branchedWeight a c b d (3 * i + 4) := by
    by_cases hi₁ : i = 1
    · subst i
      have hor : a < d ∨ c - 1 < b := by
        by_contra h
        push Not at h
        linarith
      rcases hor with h | h
      · have hp : 0 < branchedWeight a c b d 6 := by
          have hda : 0 < d - a := sub_pos.mpr h
          norm_num [branchedWeight]
          positivity
        exact add_pos_of_pos_of_nonneg hp (hn 7)
      · have hp : 0 < branchedWeight a c b d 7 := by
          have hbc : 0 < b - c + 1 := by linarith
          norm_num [branchedWeight]
          positivity
        exact add_pos_of_nonneg_of_pos (hn 6) hp
    · exact add_pos_of_pos_of_nonneg
        (branchedWeight_pos_of_nine_le ha hc hb hd h₁ h₂ h₃ h₄ (by lia)) (hn _)
  exact add_pos_of_pos_of_nonneg (mul_pos (branchedWeight_diag_pos ha hc hb hd i) hsum)
    (mul_nonneg (hn _) (hn _))

/-- On the weak range, a nonexceptional initial subdiagonal gives simple,
disjoint positive roots and consecutive interlacing of the monic rows. -/
theorem monicThreeFTwo_interlaces_and_isCoprime_of_weak {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a ≤ b) (h₂ : c - 1 ≤ b) (h₃ : a ≤ d) (h₄ : c ≤ d)
    (hstrict : a < b ∨ c < d) (n : ℕ) :
    let P := monicThreeFTwo a c b d
    Interlaces (P n) (P (n + 1)) ∧ IsCoprime (P n) (P (n + 1)) ∧
      HasSimpleRoots (P n) ∧ HasSimpleRoots (P (n + 1)) ∧
      ∀ x ∈ (P (n + 1)).roots, 0 < x := by
  let α := branchedWeight a c b d
  have hn := branchedWeight_nonneg ha hc hb hd h₁ h₂ h₃ h₄
  have hsub (i : ℕ) : 0 < Matrix.threeBidiagonalSub
      (fun _ => 1) (fun i => α (3 * i + 3))
      (fun _ => 1) (fun i => α (3 * i + 4)) (fun i => α (3 * i + 2))
      (fun _ => 1) i := by
    rw [Matrix.threeBidiagonalSub_branched α (by simp [α, branchedWeight])]
    cases i with
    | zero =>
        have hp := (branchedWeight_initial_sub_pos_iff ha hc hb hd h₁ h₄).mpr hstrict
        have hz : α 1 = 0 := by simp [α, branchedWeight]
        simp only [Nat.mul_zero, Nat.zero_add, hz, zero_mul, add_zero]
        dsimp only [α]
        nlinarith only [hp]
    | succ i =>
        have hp := branchedWeight_sub_pos_of_one_le ha hc hb hd h₁ h₂ h₃ h₄
          (i := i + 1) (by lia)
        dsimp only [α]
        nlinarith only [hp]
  have h := Matrix.threeBidiagonalProduction_charpoly_interlaces_and_isCoprime
    (fun _ => 1) (fun i => α (3 * i + 3))
    (fun _ => 1) (fun i => α (3 * i + 4)) (fun i => α (3 * i + 2))
    (fun _ => 1)
    (fun i => ⟨by norm_num, hn _, by norm_num, hn _, hn _, by norm_num⟩)
    (fun i => by simpa only [one_mul] using branchedWeight_diag_pos ha hc hb hd i)
    (fun _ => by norm_num) hsub n
  change Interlaces (production a c b d n).charpoly
      (production a c b d (n + 1)).charpoly ∧
    IsCoprime (production a c b d n).charpoly (production a c b d (n + 1)).charpoly ∧
    (∀ x ∈ (production a c b d (n + 1)).charpoly.roots, 0 < x) at h
  simp_rw [← monicThreeFTwo_eq_charpoly ha hc hb hd] at h
  exact ⟨h.1, h.2.1, (h.1.toStrictInterl.hasSimpleRoots_of_isCoprime h.2.1).1,
    (h.1.toStrictInterl.hasSimpleRoots_of_isCoprime h.2.1).2, h.2.2⟩

/-- On the exceptional face the first two nonconstant monic rows share the root one. -/
theorem isRoot_one_monicThreeFTwo_one_two {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (monicThreeFTwo a c a c 1).IsRoot 1 ∧ (monicThreeFTwo a c a c 2).IsRoot 1 := by
  rw [monicThreeFTwo_eq_charpoly ha hc ha hc,
    monicThreeFTwo_eq_charpoly ha hc ha hc]
  simp only [production, Matrix.twoBranchedProduction]
  rw [Matrix.threeBidiagonalProduction_charpoly_one,
    Matrix.threeBidiagonalProduction_charpoly_two]
  simp [Polynomial.IsRoot.def, Matrix.threeBidiagonalSub, branchedWeight,
    ha.ne', hc.ne']

/-- In the weak parameter range, all consecutive monic rows have simple roots
and strictly interlace exactly when `a < b` or `c < d`.
Strict separation is expressed by interlacing together with coprimality. -/
theorem monicThreeFTwo_simple_interlaces_iff {a c b d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hd : 0 < d)
    (h₁ : a ≤ b) (h₂ : c - 1 ≤ b) (h₃ : a ≤ d) (h₄ : c ≤ d) :
    (∀ n : ℕ, Interlaces (monicThreeFTwo a c b d n) (monicThreeFTwo a c b d (n + 1)) ∧
      IsCoprime (monicThreeFTwo a c b d n) (monicThreeFTwo a c b d (n + 1)) ∧
      HasSimpleRoots (monicThreeFTwo a c b d n) ∧
      HasSimpleRoots (monicThreeFTwo a c b d (n + 1))) ↔ a < b ∨ c < d := by
  constructor
  · intro hall
    by_contra hn
    push Not at hn
    have hab : b = a := le_antisymm hn.1 h₁
    have hdc : d = c := le_antisymm hn.2 h₄
    subst b d
    obtain ⟨hr₁, hr₂⟩ := isRoot_one_monicThreeFTwo_one_two ha hc
    exact (hall 1).2.1.not_isRoot_right hr₁ hr₂
  · intro hstrict n
    obtain ⟨hi, hcop, hs₁, hs₂, _⟩ :=
      monicThreeFTwo_interlaces_and_isCoprime_of_weak ha hc hb hd h₁ h₂ h₃ h₄ hstrict n
    exact ⟨hi, hcop, hs₁, hs₂⟩

/-- The monic three-over-two specialization underlying A087727 has simple,
disjoint positive roots and consecutive interlacing at every rank. -/
theorem monicThreeFTwo_two_three_interlaces_and_isCoprime (n : ℕ) :
    let P := monicThreeFTwo 2 3 (5 / 2) 3
    Interlaces (P n) (P (n + 1)) ∧ IsCoprime (P n) (P (n + 1)) ∧
      HasSimpleRoots (P n) ∧ HasSimpleRoots (P (n + 1)) ∧
      ∀ x ∈ (P (n + 1)).roots, 0 < x := by
  exact monicThreeFTwo_interlaces_and_isCoprime_of_weak
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n

/-- The monic three-over-two specialization underlying A318107 has simple,
disjoint positive roots and consecutive interlacing at every rank. -/
theorem monicThreeFTwo_one_one_interlaces_and_isCoprime (n : ℕ) :
    let P := monicThreeFTwo 1 1 1 (3 / 2)
    Interlaces (P n) (P (n + 1)) ∧ IsCoprime (P n) (P (n + 1)) ∧
      HasSimpleRoots (P n) ∧ HasSimpleRoots (P (n + 1)) ∧
      ∀ x ∈ (P (n + 1)).roots, 0 < x := by
  exact monicThreeFTwo_interlaces_and_isCoprime_of_weak
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n

end RealRooted.Hypergeometric
