import RealRooted.GeneralizedSnakePosets.SnakeBand
import RealRooted.GeneralizedSnakePosets.SnakeTheorem41

/-!
# Braun–Jal Theorem 3.5 for the concrete snake board

Let `w` have last-change index `k`, with a final constant block of length
`s = |w| - (k + 1)`.  In band coordinates (`SnakeBand`) the final block is gaps
`0, …, s - 1`, and gap `s` carries the other letter.  Suppose the final letter
is `R`; the `L` case is its transpose.  The band then splits into three parts:

* the staircase `i ≤ j < s`, whose chains give `P_s`;
* the column cells `(i, s)` with `i < s`, an antichain;
* the part in `[s, n]²`, which is the band of `w[:k+1]`.

Chains that avoid the column contribute `M_{w[:k+1]} P_s`.  A chain through
`(i, s)` consists of a chain of the staircase rows below `i` (which give
`R(s, i)`) together with a chain of the band of `w[:k]`.  Summing over `i < s`
gives `X M_{w[:k]} G_s`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

open FiniteSkewBoard

/-- The cells `(r, j)` with `r < i` and `r ≤ j < n`: the truncated staircase
`μ_{n,i}` in increasing-chain coordinates. -/
def stairCells (n i : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range i) ×ˢ (Finset.range n)).filter fun p => p.1 ≤ p.2

@[simp] theorem mem_stairCells {n i r j : ℕ} :
    (r, j) ∈ stairCells n i ↔ r < i ∧ j < n ∧ r ≤ j := by
  simp [stairCells, and_assoc]

theorem truncatedStaircaseRookPolynomial_eq_chainPolynomial (n i : ℕ) :
    truncatedStaircaseRookPolynomial n i = chainPolynomial incRel (stairCells n i) := by
  rw [truncatedStaircaseRookPolynomial, rookPolynomial_eq_chainPolynomial_reflect (N := n - 1)]
  · congr 1
    ext ⟨r, j⟩
    simp only [Finset.mem_image, mem_stairCells, Prod.exists, Prod.mk.injEq,
      mem_truncatedStaircase_cells]
    constructor
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
      lia
    · rintro ⟨hr, hj, hrj⟩
      exact ⟨r, n - 1 - j, ⟨hr, by lia⟩, rfl, by lia⟩
  · rintro ⟨a, b⟩ hp
    have := mem_truncatedStaircase_cells.mp hp
    simp only
    lia

section Split

variable {ℓ : ℕ → SnakeLetter} {n s : ℕ}

/-- With tail letters `R` below gap `s` and `L` at gap `s`, every band cell
lies in the staircase `i ≤ j ≤ s` or in `[s, n]²`. -/
private theorem mem_bandCells_split (htail : ∀ g < s, ℓ g = .R) (hchange : ℓ s = .L)
    (hsn : s < n) {i j : ℕ} :
    (i, j) ∈ bandCells n ℓ ↔ (i ≤ j ∧ j ≤ s) ∨ (s ≤ i ∧ s ≤ j ∧ (i, j) ∈ bandCells n ℓ) := by
  constructor
  · intro h
    by_cases hij : s ≤ i ∧ s ≤ j
    · exact Or.inr ⟨hij.1, hij.2, h⟩
    · left
      obtain ⟨-, -, hR, hL⟩ := mem_bandCells.mp h
      have h₁ : ¬ (i ≤ s ∧ s < j) := fun ⟨h₁, h₂⟩ => by
        have := hR s h₁ h₂
        rw [hchange] at this
        cases this
      have h₂ : ¬ (j < s ∧ j < i) := fun ⟨h₁, h₂⟩ => by
        have := hL j le_rfl h₂
        rw [htail j h₁] at this
        cases this
      lia
  · rintro (⟨hij, hjs⟩ | ⟨-, -, h⟩)
    · exact mem_bandCells.mpr ⟨by lia, by lia, fun g _ h₂ => htail g (by lia),
        fun g h₁ h₂ => by lia⟩
    · exact h

private theorem mem_image_shift_iff {m t : ℕ} {i j : ℕ} :
    (i, j) ∈ (bandCells m fun g => ℓ (g + t)).image (fun p => (p.1 + t, p.2 + t)) ↔
      (i, j) ∈ bandCells (m + t) ℓ ∧ t ≤ i ∧ t ≤ j := by
  rw [image_bandCells_shift, Finset.mem_filter]

/-- **The band splitting, final letter `R`.** -/
theorem chainPolynomial_bandCells_split_R {m : ℕ} (htail : ∀ g < s, ℓ g = .R)
    (hchange : ℓ s = .L) :
    chainPolynomial incRel (bandCells (m + 1 + s) ℓ) =
      chainPolynomial incRel (bandCells (m + 1) fun g => ℓ (g + s)) *
          truncatedStaircaseRookPolynomial s s +
        X * chainPolynomial incRel (bandCells m fun g => ℓ (g + (s + 1))) * auxiliaryG s := by
  classical
  have hsn : s < m + 1 + s := by lia
  set D := bandCells (m + 1 + s) ℓ with hD
  set Q : Finset (ℕ × ℕ) := (Finset.range s).image fun i => (i, s) with hQdef
  have hmemQ : ∀ {i j : ℕ}, (i, j) ∈ Q ↔ i < s ∧ j = s := by
    intro i j
    simp only [hQdef, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩
      exact ⟨ha, rfl⟩
    · rintro ⟨hi, rfl⟩
      exact ⟨i, hi, rfl, rfl⟩
  have hQD : Q ⊆ D := by
    rintro ⟨i, j⟩ h
    obtain ⟨hi, rfl⟩ := hmemQ.mp h
    exact (mem_bandCells_split htail hchange hsn).mpr (Or.inl ⟨hi.le, le_rfl⟩)
  have hanti : ∀ q ∈ Q, ∀ q' ∈ Q, ¬ incRel q q' := by
    rintro ⟨a, b⟩ hq ⟨c, d⟩ hq' h
    rw [(hmemQ.mp hq).2, (hmemQ.mp hq').2] at h
    exact lt_irrefl _ h.2
  rw [chainPolynomial_eq_sdiff_add_sum incRel_irrefl hQD hanti]
  -- Chains avoiding the column `s`.
  set U := (bandCells (m + 1) fun g => ℓ (g + s)).image (fun p => (p.1 + s, p.2 + s)) with hU
  have hsdiff : D \ Q = stairCells s s ∪ U := by
    ext ⟨i, j⟩
    rw [Finset.mem_sdiff, Finset.mem_union, hmemQ, mem_stairCells, hU, mem_image_shift_iff]
    constructor
    · rintro ⟨h, hnq⟩
      rcases (mem_bandCells_split htail hchange hsn).mp h with ⟨hij, hjs⟩ | ⟨hi, hj, -⟩
      · by_cases hjs' : j < s
        · exact Or.inl ⟨by lia, hjs', hij⟩
        · exact Or.inr ⟨h, by lia, by lia⟩
      · exact Or.inr ⟨h, hi, hj⟩
    · rintro (⟨hi, hj, hij⟩ | ⟨h, hi, -⟩)
      · exact ⟨(mem_bandCells_split htail hchange hsn).mpr (Or.inl ⟨hij, hj.le⟩),
          fun h => by lia⟩
      · exact ⟨h, fun h => by lia⟩
  have hdisjU : Disjoint (stairCells s s) U := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h h'
    rw [hU, mem_image_shift_iff] at h'
    rw [mem_stairCells] at h
    lia
  have hbelowU : ∀ a ∈ stairCells s s, ∀ b ∈ U, incRel a b := by
    rintro ⟨i, j⟩ h ⟨i', j'⟩ h'
    rw [hU, mem_image_shift_iff] at h'
    rw [mem_stairCells] at h
    exact ⟨by lia, by lia⟩
  rw [hsdiff, chainPolynomial_union_of_forall_rel hdisjU hbelowU, hU,
    chainPolynomial_incRel_image_shift, ← truncatedStaircaseRookPolynomial_eq_chainPolynomial]
  -- Chains through a column cell `(i, s)`.
  set V := (bandCells m fun g => ℓ (g + (s + 1))).image
    (fun p => (p.1 + (s + 1), p.2 + (s + 1))) with hV
  have hmemV : ∀ {a b : ℕ}, (a, b) ∈ V ↔ (a, b) ∈ D ∧ s + 1 ≤ a ∧ s + 1 ≤ b := by
    intro a b
    rw [hV, mem_image_shift_iff, show m + (s + 1) = m + 1 + s by lia]
  have hcomp : ∀ i < s, comparableWith incRel D (i, s) = stairCells s i ∪ V := by
    intro i hi
    ext ⟨a, b⟩
    rw [mem_comparableWith, Finset.mem_union, mem_stairCells, hmemV]
    simp only [incRel]
    constructor
    · rintro ⟨h, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
      · rcases (mem_bandCells_split htail hchange hsn).mp h with ⟨hab, -⟩ | ⟨hsa, -, -⟩
        · exact Or.inl ⟨ha, hb, hab⟩
        · lia
      · refine Or.inr ⟨h, ?_, hb⟩
        rcases (mem_bandCells_split htail hchange hsn).mp h with ⟨-, hbs⟩ | ⟨hsa, -, -⟩
        · lia
        · by_contra has
          have := (mem_bandCells.mp h).2.2.1 s (by lia) hb
          rw [hchange] at this
          cases this
    · rintro (⟨ha, hb, hab⟩ | ⟨h, ha, hb⟩)
      · exact ⟨(mem_bandCells_split htail hchange hsn).mpr (Or.inl ⟨hab, hb.le⟩),
          Or.inl ⟨ha, hb⟩⟩
      · exact ⟨h, Or.inr ⟨by lia, by lia⟩⟩
  have hterm : ∀ i < s, chainPolynomial incRel (comparableWith incRel D (i, s)) =
      truncatedStaircaseRookPolynomial s i *
        chainPolynomial incRel (bandCells m fun g => ℓ (g + (s + 1))) := by
    intro i hi
    have hdisj : Disjoint (stairCells s i) V := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h h'
      rw [hmemV] at h'
      rw [mem_stairCells] at h
      lia
    have hbelow : ∀ p ∈ stairCells s i, ∀ q ∈ V, incRel p q := by
      rintro ⟨a, b⟩ h ⟨a', b'⟩ h'
      rw [hmemV] at h'
      rw [mem_stairCells] at h
      exact ⟨by lia, by lia⟩
    rw [hcomp i hi, chainPolynomial_union_of_forall_rel hdisj hbelow, hV,
      chainPolynomial_incRel_image_shift, ← truncatedStaircaseRookPolynomial_eq_chainPolynomial]
  rw [hQdef, Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1), auxiliaryG_eq_sum_range,
    Finset.mul_sum]
  refine congrArg₂ (· + ·) (mul_comm _ _) (Finset.sum_congr rfl fun i hi => ?_)
  rw [hterm i (Finset.mem_range.mp hi)]
  ring

/-- **The band splitting.** If the gaps below `s` all carry the letter `b`
and gap `s` does not, the band polynomial splits as in Braun–Jal
Theorem 3.5. -/
theorem chainPolynomial_bandCells_split {m : ℕ} {b : SnakeLetter}
    (htail : ∀ g < s, ℓ g = b) (hchange : ℓ s ≠ b) :
    chainPolynomial incRel (bandCells (m + 1 + s) ℓ) =
      chainPolynomial incRel (bandCells (m + 1) fun g => ℓ (g + s)) *
          truncatedStaircaseRookPolynomial s s +
        X * chainPolynomial incRel (bandCells m fun g => ℓ (g + (s + 1))) * auxiliaryG s := by
  cases b with
  | R =>
      refine chainPolynomial_bandCells_split_R htail ?_
      cases h : ℓ s
      · rfl
      · exact absurd h hchange
  | L =>
      have hR : ℓ s = .R := by
        cases h : ℓ s
        · exact absurd h hchange
        · rfl
      have h := chainPolynomial_bandCells_split_R (ℓ := fun g => (ℓ g).flip) (m := m) (s := s)
        (fun g hg => SnakeLetter.flip_eq_R.mpr (htail g hg)) (SnakeLetter.flip_eq_L.mpr hR)
      simpa only [chainPolynomial_bandCells_flip] using h

end Split

/-- **Braun–Jal Theorem 3.5 for the concrete snake board.** -/
theorem generalizedSnakeTheorem35 : GeneralizedSnakeTheorem35 := by
  intro w k _ hk
  have hk1 := hk.succ_lt_length
  obtain ⟨s, hs⟩ : ∃ s, w.length = k + 1 + s := ⟨w.length - (k + 1), by lia⟩
  have hs' : w.length - (k + 1) = s := by lia
  rw [hs', generalizedSnakeRookModel_snakePolynomial_eq_chainPolynomial,
    generalizedSnakeRookModel_snakePolynomial_eq_chainPolynomial,
    generalizedSnakeRookModel_snakePolynomial_eq_chainPolynomial,
    hk.takePrefix_succ_length, hk.takePrefix_length,
    ← truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial s]
  have hpre1 : bandCells (k + 1) (gapLetter (w.takePrefix (k + 1))) =
      bandCells (k + 1) fun g => gapLetter w (g + s) := by
    refine bandCells_congr fun g hg => ?_
    rw [gapLetter, gapLetter, hk.takePrefix_succ_length,
      SnakeWord.getD_takePrefix_of_lt (by lia), show w.length - (g + s + 1) = k + 1 - (g + 1) by
        lia]
  have hpre0 : bandCells k (gapLetter (w.takePrefix k)) =
      bandCells k fun g => gapLetter w (g + (s + 1)) := by
    refine bandCells_congr fun g hg => ?_
    rw [gapLetter, gapLetter, hk.takePrefix_length,
      SnakeWord.getD_takePrefix_of_lt (by lia), show w.length - (g + (s + 1) + 1) = k - (g + 1) by
        lia]
  rw [hpre1, hpre0, hs]
  refine chainPolynomial_bandCells_split (b := w.getD (w.length - 1) SnakeLetter.L)
    (fun g hg => ?_) ?_
  · rw [gapLetter]
    exact hk.getD_eq_final_of_lt (by lia) (by lia) _
  · intro h
    apply hk.letter_ne_final
    rw [gapLetter, show w.length - (s + 1) = k by lia] at h
    rw [List.getElem?_eq_getElem (by lia), List.getElem?_eq_getElem (by lia)]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < w.length by lia),
      List.getElem?_eq_getElem (show w.length - 1 < w.length by lia)] using h

/-- Every generalized snake polynomial has degree `|w| + 1`. -/
theorem generalizedSnakeRookModel_natDegree_eq (w : SnakeWord) :
    (generalizedSnakeRookModel.snakePolynomial w).natDegree = w.length + 1 :=
  generalizedSnakeRookModel_natDegree generalizedSnakeTheorem35 w

/-- **Braun–Jal Theorem 4.1.** Every generalized snake polynomial is
real-rooted, and deleting the final letter gives an interlacing polynomial. -/
theorem theorem41_generalizedSnakeRookModel :
    Theorem41NonNestingRookStatement generalizedSnakeRookModel.snakePolynomial :=
  theorem41_generalizedSnakeRookModel_of_theorem35 generalizedSnakeTheorem35

end GeneralizedSnakePosets
end RealRooted
