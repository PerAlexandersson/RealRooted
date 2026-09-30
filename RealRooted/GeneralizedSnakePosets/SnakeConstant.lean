import RealRooted.GeneralizedSnakePosets.SnakeBoard
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.ColumnRecurrence

/-!
# Constant snake words

For a constant word of length `n`, the generalized snake board is the full
truncated staircase `μ_{n+1,n+1}` (all `R`) or its half-turn rotation (all
`L`).  A half-turn reverses both coordinate orders and so preserves
non-nesting placements.  Hence the snake polynomial of a constant word is the
modified Narayana polynomial `P_{n+1}`, which is the constant-word input of
Braun–Jal Theorem 4.1.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets
namespace FiniteSkewBoard

theorem ext_cells {A B : FiniteSkewBoard} (h : A.cells = B.cells) : A = B := by
  cases A
  cases B
  simp_all

/-- The half-turn `(r, c) ↦ (N - r, N - c)` of a board. -/
def rotate (N : ℕ) (B : FiniteSkewBoard) : FiniteSkewBoard where
  cells := B.cells.image fun p => (N - p.1, N - p.2)

private def rot (N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (N - p.1, N - p.2)

private theorem rot_rot {N : ℕ} {p : ℕ × ℕ} (h : p.1 ≤ N ∧ p.2 ≤ N) :
    rot N (rot N p) = p := by
  obtain ⟨a, b⟩ := p
  simp only [rot, Prod.mk.injEq]
  exact ⟨Nat.sub_sub_self h.1, Nat.sub_sub_self h.2⟩

private theorem isNonNestingPlacement_image_rot {N : ℕ} {B C : FiniteSkewBoard}
    {P : Finset (ℕ × ℕ)} (hP : B.IsNonNestingPlacement P)
    (hbox : ∀ p ∈ B.cells, p.1 ≤ N ∧ p.2 ≤ N)
    (hsub : ∀ p ∈ B.cells, rot N p ∈ C.cells) :
    C.IsNonNestingPlacement (P.image (rot N)) := by
  obtain ⟨hPB, hrow, hord⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hsub p (hPB hp)
  · intro q hq q' hq' hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq'
    have hpp : p ≠ p' := fun h => hne (by rw [h])
    have h1 := hrow p hp p' hp' hpp
    have hb := hbox p (hPB hp)
    have hb' := hbox p' (hPB hp')
    simp only [rot]
    lia
  · intro q hq q' hq' hlt
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq'
    have hb := hbox p (hPB hp)
    have hb' := hbox p' (hPB hp')
    simp only [rot] at hlt ⊢
    have := hord p' hp' p hp (by lia)
    lia

/-- A half-turn inside a bounding box preserves the rook polynomial. -/
theorem rookPolynomial_rotate {N : ℕ} {B : FiniteSkewBoard}
    (hbox : ∀ p ∈ B.cells, p.1 ≤ N ∧ p.2 ≤ N) :
    (rotate N B).rookPolynomial = B.rookPolynomial := by
  classical
  have hbox' : ∀ p ∈ (rotate N B).cells, p.1 ≤ N ∧ p.2 ≤ N := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨Nat.sub_le _ _, Nat.sub_le _ _⟩
  have hsub : ∀ p ∈ B.cells, rot N p ∈ (rotate N B).cells := fun p hp =>
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hsub' : ∀ p ∈ (rotate N B).cells, rot N p ∈ B.cells := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    change rot N (rot N q) ∈ B.cells
    rwa [rot_rot (hbox q hq)]
  have hinv : ∀ {D : FiniteSkewBoard}, (∀ p ∈ D.cells, p.1 ≤ N ∧ p.2 ≤ N) →
      ∀ {P : Finset (ℕ × ℕ)}, D.IsNonNestingPlacement P →
        (P.image (rot N)).image (rot N) = P := by
    intro D hD P hP
    rw [Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := P)]
    exact Finset.image_congr fun p hp => rot_rot (hD p (hP.1 hp))
  rw [rookPolynomial_eq_nonNestingPlacements_sum, rookPolynomial_eq_nonNestingPlacements_sum]
  refine Finset.sum_nbij' (fun Q => Q.image (rot N)) (fun P => P.image (rot N)) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    exact mem_nonNestingPlacements.mpr (isNonNestingPlacement_image_rot
      (mem_nonNestingPlacements.mp hQ) hbox' hsub')
  · intro P hP
    exact mem_nonNestingPlacements.mpr (isNonNestingPlacement_image_rot
      (mem_nonNestingPlacements.mp hP) hbox hsub)
  · intro Q hQ
    exact hinv hbox' (mem_nonNestingPlacements.mp hQ)
  · intro P hP
    exact hinv hbox (mem_nonNestingPlacements.mp hP)
  · intro Q hQ
    have hQ' := mem_nonNestingPlacements.mp hQ
    rw [Finset.card_image_of_injOn]
    intro p hp p' hp' h
    rw [← rot_rot (hbox' p (hQ'.1 hp)), ← rot_rot (hbox' p' (hQ'.1 hp'))]
    exact congrArg (rot N) h

end FiniteSkewBoard

open FiniteSkewBoard

/-- The all-`R` snake board is the full truncated staircase. -/
theorem generalizedSnakeBoard_replicate_R (n : ℕ) :
    generalizedSnakeBoard (List.replicate n SnakeLetter.R) =
      truncatedStaircase (n + 1) (n + 1) := by
  apply ext_cells
  ext ⟨r, c⟩
  rw [mem_generalizedSnakeBoard_cells, mem_snakeIncomparableBoard_replicate_R_cells,
    mem_truncatedStaircase_cells]
  simp only [List.length_replicate]
  lia

/-- The all-`L` snake board is the half-turn of the full truncated staircase. -/
theorem generalizedSnakeBoard_replicate_L (n : ℕ) :
    generalizedSnakeBoard (List.replicate n SnakeLetter.L) =
      rotate n (truncatedStaircase (n + 1) (n + 1)) := by
  apply ext_cells
  ext ⟨r, c⟩
  rw [mem_generalizedSnakeBoard_cells, mem_snakeIncomparableBoard_replicate_L_cells]
  simp only [List.length_replicate, rotate, Finset.mem_image, mem_truncatedStaircase_cells,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨hc, hr, -, hcr⟩
    exact ⟨n - r, n - c, ⟨by lia, by lia⟩, by lia, by lia⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
    exact ⟨Nat.sub_le _ _, Nat.sub_le _ _, Nat.sub_le _ _, by lia⟩

/-- **Constant-word input of Braun–Jal Theorem 4.1:** the snake polynomial of a
constant word of length `n` is the modified Narayana polynomial `P_{n+1}`. -/
theorem generalizedSnakeRookModel_snakePolynomial_of_isConstant {w : SnakeWord}
    (hw : w.IsConstant) :
    generalizedSnakeRookModel.snakePolynomial w = modifiedNarayanaPolynomial (w.length + 1) := by
  have hstair : (truncatedStaircase (w.length + 1) (w.length + 1)).rookPolynomial =
      modifiedNarayanaPolynomial (w.length + 1) :=
    truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial (w.length + 1)
  set n := w.length with hn
  have hrep : w = List.replicate n (w.headD SnakeLetter.R) := by
    rcases w with _ | ⟨a, t⟩
    · rfl
    · exact List.eq_replicate_iff.mpr ⟨rfl, fun b hb => hw b hb a List.mem_cons_self⟩
  rw [generalizedSnakeRookModel_snakePolynomial, hrep]
  cases w.headD SnakeLetter.R with
  | R => rw [generalizedSnakeBoard_replicate_R]; exact hstair
  | L =>
      rw [generalizedSnakeBoard_replicate_L, rookPolynomial_rotate]
      · exact hstair
      · rintro ⟨a, b⟩ hp
        have := mem_truncatedStaircase_cells.mp hp
        simp only
        lia

end GeneralizedSnakePosets
end RealRooted
