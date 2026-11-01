module

public import RealRooted.MatrixInterlacing.SeparatedCharacteristicDeterminant
public import RealRooted.MatrixInterlacing.SeparatedCharacteristicRecurrence
import RealRooted.AffineProperPosition
import RealRooted.Compatibility.NDCutInvariant

/-!
# Concrete separated-characteristic matrices

This module records the two cubic matrices and the path matrices that motivate
the separated-characteristic API.  The examples check their characteristic
polynomials, ordered seeds, initial rows, PF preservation, and consecutive
coordinate interlacing without referring to a sequence-specific graph model.
-/

@[expose] public section

open Polynomial
open scoped Matrix

noncomputable section

namespace RealRooted.SeparatedCharacteristicExamples

/-- Parameters `a = (0,1,1)` of the first cubic matrix. -/
def cubicA : Fin 3 → ℝ := ![0, 1, 1]

/-- Parameters `b = (-1,-1)` of the first cubic matrix. -/
def cubicB : Fin 2 → ℝ := ![-1, -1]

/-- The matrix with characteristic polynomial `z(z-1)^2 - X(z+1)^2`. -/
def cubicMatrix : Matrix (Fin 3) (Fin 3) ℝ[X] :=
  separatedCharacteristicFinMatrix (h := 1) (m := 2) cubicA cubicB

/-- The first cubic matrix in explicit form. -/
theorem cubicMatrix_eq :
    cubicMatrix = !![X, 1 + 1, 1 + 1; X, C 1, 1 + 1; X, C 0, C 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicMatrix, cubicA, cubicB, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff]

/-- Characteristic polynomial of the first cubic matrix. -/
theorem cubicMatrix_charpoly :
    cubicMatrix.charpoly = X * (X - 1) ^ 2 - C (X : ℝ[X]) * (X + 1) ^ 2 := by
  rw [cubicMatrix]
  have h := separatedCharacteristicFinMatrix_charpoly
    (h := 1) (m := 2) (by norm_num) cubicA cubicB
  rw [h]
  simp [Fin.prod_univ_succ, cubicA, cubicB]
  ring

/-- All-ones seed for the first cubic matrix. -/
def cubicSeed : Fin 3 → ℝ[X] := fun i ↦ C (![1, 1, 1] i)

/-- The all-ones cubic seed is an ordered PF vector. -/
theorem cubicSeed_interlacing :
    IsInterlacingSeq0NonnegRealRooted (List.ofFn cubicSeed) := by
  apply isInterlacingSeq0NonnegRealRooted_of_mem_C_nonneg
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨![1, 1, 1] i, by fin_cases i <;> norm_num, rfl⟩

/-- The first three rows of coordinate two are `1`, `1+X`, and `1+5X+X²`. -/
theorem cubicRows_coordinate_two_initial :
    (fun n ↦ separatedCharacteristicRows cubicA cubicB cubicSeed n 2) 0 = 1 ∧
      (fun n ↦ separatedCharacteristicRows cubicA cubicB cubicSeed n 2) 1 = 1 + X ∧
      (fun n ↦ separatedCharacteristicRows cubicA cubicB cubicSeed n 2) 2 =
        1 + 5 * X + X ^ 2 := by
  constructor
  · rfl
  constructor <;>
    norm_num [separatedCharacteristicRows, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff, cubicA, cubicB, cubicSeed, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- The first three rows of coordinate one are `1`, `3+X`, and `5+7X+X²`. -/
theorem cubicRows_coordinate_one_initial :
    (fun n ↦ separatedCharacteristicRows cubicA cubicB cubicSeed n 1) 0 = 1 ∧
      (fun n ↦ separatedCharacteristicRows cubicA cubicB cubicSeed n 1) 1 = 3 + X ∧
      (fun n ↦ separatedCharacteristicRows cubicA cubicB cubicSeed n 1) 2 =
        5 + 7 * X + X ^ 2 := by
  constructor
  · rfl
  constructor <;>
    norm_num [separatedCharacteristicRows, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff, cubicA, cubicB, cubicSeed, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- Every coordinate in the first cubic orbit is PF. -/
theorem cubicRows_isPFPolynomial (n : ℕ) (i : Fin 3) :
    IsPFPolynomial (separatedCharacteristicRows cubicA cubicB cubicSeed n i) := by
  exact separatedCharacteristicRows_isPFPolynomial
    (a := cubicA) (b := cubicB) (seed := cubicSeed)
    (by intro j; fin_cases j <;> norm_num [cubicA])
    (by intro j; fin_cases j <;> norm_num [cubicB])
    cubicSeed_interlacing n i

/-- Each coordinate in the first cubic orbit interlaces its next value. -/
theorem interl_cubicRows_succ (n : ℕ) (i : Fin 3) :
    Interl (separatedCharacteristicRows cubicA cubicB cubicSeed n i)
      (separatedCharacteristicRows cubicA cubicB cubicSeed (n + 1) i) := by
  exact separatedCharacteristicRows_interl_succ
    (a := cubicA) (b := cubicB) (seed := cubicSeed)
    (by intro j; fin_cases j <;> norm_num [cubicA])
    (by intro j; fin_cases j <;> norm_num [cubicB])
    cubicSeed_interlacing n i

/-- Parameters `a = (0,0,0)` of the delayed cubic matrix. -/
def delayedA : Fin 3 → ℝ := ![0, 0, 0]

/-- The single parameter `b = (-1)` of the delayed cubic matrix. -/
def delayedB : Fin 1 → ℝ := ![-1]

/-- The matrix with characteristic polynomial `z³ - X(z+1)`. -/
def delayedMatrix : Matrix (Fin 3) (Fin 3) ℝ[X] :=
  separatedCharacteristicFinMatrix (h := 2) (m := 1) delayedA delayedB

/-- The delayed cubic matrix in explicit form. -/
theorem delayedMatrix_eq :
    delayedMatrix = !![C 0, C 1, C 0; X, C 0, C 1; X, C 0, C 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [delayedMatrix, delayedA, delayedB, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff]

/-- Characteristic polynomial of the delayed cubic matrix. -/
theorem delayedMatrix_charpoly :
    delayedMatrix.charpoly = X ^ 3 - C (X : ℝ[X]) * (X + 1) := by
  rw [delayedMatrix]
  have h := separatedCharacteristicFinMatrix_charpoly
    (h := 2) (m := 1) (by norm_num) delayedA delayedB
  rw [h]
  simp [Fin.prod_univ_succ, delayedA, delayedB]
  ring

/-- Seed `(1,2,1)` for the delayed cubic matrix. -/
def delayedSeed : Fin 3 → ℝ[X] := fun i ↦ C (![1, 2, 1] i)

/-- The seed `(1,2,1)` is an ordered PF vector. -/
theorem delayedSeed_interlacing :
    IsInterlacingSeq0NonnegRealRooted (List.ofFn delayedSeed) := by
  apply isInterlacingSeq0NonnegRealRooted_of_mem_C_nonneg
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨![1, 2, 1] i, by fin_cases i <;> norm_num, rfl⟩

/-- The first three rows of coordinate two from seed `(1,2,1)` are `1`, `X`, and `2X`. -/
theorem delayedRows_coordinate_two_initial :
    (fun n ↦ separatedCharacteristicRows delayedA delayedB delayedSeed n 2) 0 = 1 ∧
      (fun n ↦ separatedCharacteristicRows delayedA delayedB delayedSeed n 2) 1 = X ∧
      (fun n ↦ separatedCharacteristicRows delayedA delayedB delayedSeed n 2) 2 =
        C 2 * X := by
  constructor
  · rfl
  constructor <;>
    norm_num [separatedCharacteristicRows, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff, delayedA, delayedB, delayedSeed, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Seed `(3,2X,2X)` for the delayed tail with two exceptional prefix rows. -/
def delayedTailSeed : Fin 3 → ℝ[X] := ![C 3, C 2 * X, C 2 * X]

/-- The seed `(3,2X,2X)` is an ordered PF vector. -/
theorem delayedTailSeed_interlacing :
    IsInterlacingSeq0NonnegRealRooted (List.ofFn delayedTailSeed) := by
  change IsInterlacingSeq0NonnegRealRooted [C 3, C 2 * X, C 2 * X]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases hp with rfl | rfl
      all_goals simpa using
        interl_C_affine_linear (c := 3) (u := 2) (v := 0) (by norm_num)
    · refine ⟨?_, ?_, List.Pairwise.nil⟩
      · intro p hp
        rcases hp with rfl
        exact Interl.refl fun _ ↦ isRealRooted_X.2.C_mul 2
      · intro p hp
        exact hp.elim
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact hasNonnegCoeffs_C (by norm_num)
    all_goals exact hasNonnegCoeffs_C_mul (by norm_num) hasNonnegCoeffs_X
  · intro p hp hp0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨hp0, Splits.C 3⟩
    all_goals exact ⟨hp0, isRealRooted_X.2.C_mul 2⟩

/-- The first three rows of coordinate two from seed `(3,2X,2X)` are
`2X`, `3X`, and `2X²`. -/
theorem delayedTailRows_coordinate_two_initial :
    (fun n ↦ separatedCharacteristicRows delayedA delayedB delayedTailSeed n 2) 0 =
        C 2 * X ∧
      (fun n ↦ separatedCharacteristicRows delayedA delayedB delayedTailSeed n 2) 1 =
        C 3 * X ∧
      (fun n ↦ separatedCharacteristicRows delayedA delayedB delayedTailSeed n 2) 2 =
        C 2 * X ^ 2 := by
  constructor
  · rfl
  constructor
  · norm_num [separatedCharacteristicRows, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff, delayedA, delayedB, delayedTailSeed,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [separatedCharacteristicRows, separatedCharacteristicFinMatrix,
      separatedCharacteristicTailCoeff, delayedA, delayedB, delayedTailSeed,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- Every coordinate in either delayed cubic orbit is PF. -/
theorem delayedRows_isPFPolynomial
    {seed : Fin 3 → ℝ[X]}
    (hseed : seed = delayedSeed ∨ seed = delayedTailSeed)
    (n : ℕ) (i : Fin 3) :
    IsPFPolynomial (separatedCharacteristicRows delayedA delayedB seed n i) := by
  rcases hseed with rfl | rfl
  · exact separatedCharacteristicRows_isPFPolynomial
      (a := delayedA) (b := delayedB) (seed := delayedSeed)
      (by intro j; fin_cases j <;> norm_num [delayedA])
      (by intro j; fin_cases j; norm_num [delayedB])
      delayedSeed_interlacing n i
  · exact separatedCharacteristicRows_isPFPolynomial
      (a := delayedA) (b := delayedB) (seed := delayedTailSeed)
      (by intro j; fin_cases j <;> norm_num [delayedA])
      (by intro j; fin_cases j; norm_num [delayedB])
      delayedTailSeed_interlacing n i

/-- Each coordinate in either delayed cubic orbit interlaces its next value. -/
theorem interl_delayedRows_succ
    {seed : Fin 3 → ℝ[X]}
    (hseed : seed = delayedSeed ∨ seed = delayedTailSeed)
    (n : ℕ) (i : Fin 3) :
    Interl (separatedCharacteristicRows delayedA delayedB seed n i)
      (separatedCharacteristicRows delayedA delayedB seed (n + 1) i) := by
  rcases hseed with rfl | rfl
  · exact separatedCharacteristicRows_interl_succ
      (a := delayedA) (b := delayedB) (seed := delayedSeed)
      (by intro j; fin_cases j <;> norm_num [delayedA])
      (by intro j; fin_cases j; norm_num [delayedB])
      delayedSeed_interlacing n i
  · exact separatedCharacteristicRows_interl_succ
      (a := delayedA) (b := delayedB) (seed := delayedTailSeed)
      (by intro j; fin_cases j <;> norm_num [delayedA])
      (by intro j; fin_cases j; norm_num [delayedB])
      delayedTailSeed_interlacing n i

/-- The delayed scalar recurrence with two exceptional prefix rows. -/
def delayedTailSequence : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => C 2 * X
  | 3 => C 3 * X
  | 4 => C 2 * X ^ 2
  | n + 5 => X * delayedTailSequence (n + 3) + X * delayedTailSequence (n + 2)

private theorem delayedTailSequence_isSolution :
    (LinearRecurrence.ofMatrix delayedMatrix).IsSolution
      (fun n ↦ delayedTailSequence (2 + n)) := by
  unfold LinearRecurrence.IsSolution LinearRecurrence.ofMatrix
  intro n
  change delayedTailSequence (2 + (n + 3)) =
    ∑ i : Fin 3, (-delayedMatrix.charpoly.coeff i) *
      delayedTailSequence (2 + (n + i))
  rw [show 2 + (n + 3) = n + 5 by lia, delayedTailSequence,
    delayedMatrix_charpoly]
  simp [Fin.sum_univ_succ, coeff_sub, coeff_add, coeff_C_mul,
    coeff_X_pow, coeff_X, coeff_one]
  ring_nf

/-- Recurrence uniqueness identifies the delayed tail from its actual starting
index `2`; the rows at indices `0` and `1` remain exceptional. -/
theorem delayedTailSequence_eq_rows (n : ℕ) :
    delayedTailSequence (2 + n) =
      separatedCharacteristicRows delayedA delayedB delayedTailSeed n 2 := by
  apply eq_separatedCharacteristicRows_coordinate_from
    (h := 2) (m := 1)
    (a := delayedA) (b := delayedB) (seed := delayedTailSeed)
    (i := (2 : Fin 3)) (P := delayedTailSequence) (start := 2)
    delayedTailSequence_isSolution
  rcases delayedTailRows_coordinate_two_initial with ⟨h0, h1, h2⟩
  intro r hr
  interval_cases r
  · simpa [delayedTailSequence] using h0.symm
  · simpa [delayedTailSequence] using h1.symm
  · simpa [delayedTailSequence] using h2.symm

/-- Parameters of the path matrix `N_(n+1) + rho I`. -/
def pathA (rho : ℝ) (n : ℕ) : Fin (1 + n) → ℝ := fun _ ↦ rho

/-- Tail parameters of the path matrix `N_(n+1) + rho I`. -/
def pathB (rho : ℝ) (n : ℕ) : Fin n → ℝ := fun _ ↦ rho - 1

/-- The path matrix `N_(n+1) + rho I`. -/
def pathMatrix (rho : ℝ) (n : ℕ) :
    Matrix (Fin (1 + n)) (Fin (1 + n)) ℝ[X] :=
  separatedCharacteristicFinMatrix (h := 1) (m := n) (pathA rho n) (pathB rho n)

/-- Characteristic polynomial of `N_(n+1) + rho I`. -/
theorem pathMatrix_charpoly (rho : ℝ) (n : ℕ) :
    (pathMatrix rho n).charpoly =
      (X - C (C rho)) ^ (n + 1) -
        C (X : ℝ[X]) * (X - C (C (rho - 1))) ^ n := by
  rw [pathMatrix]
  simpa [pathA, pathB, Nat.add_comm] using
    separatedCharacteristicFinMatrix_charpoly
      (h := 1) (m := n) (by norm_num) (pathA rho n) (pathB rho n)

/-- All-ones seed for the path matrices. -/
def pathSeed (n : ℕ) : Fin (1 + n) → ℝ[X] := fun _ ↦ C 1

/-- The all-ones path seed is an ordered PF vector. -/
theorem pathSeed_interlacing (n : ℕ) :
    IsInterlacingSeq0NonnegRealRooted (List.ofFn (pathSeed n)) := by
  apply isInterlacingSeq0NonnegRealRooted_of_mem_C_nonneg
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨1, by norm_num, rfl⟩

/-- For `0 ≤ rho ≤ 1`, every coordinate in the path-matrix orbit is PF. -/
theorem pathRows_isPFPolynomial {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (n row : ℕ) (i : Fin (1 + n)) :
    IsPFPolynomial
      (separatedCharacteristicRows (pathA rho n) (pathB rho n) (pathSeed n) row i) := by
  exact separatedCharacteristicRows_isPFPolynomial
    (a := pathA rho n) (b := pathB rho n) (seed := pathSeed n)
    (fun _ ↦ hrho0) (fun _ ↦ by simp [pathB]; linarith)
    (pathSeed_interlacing n) row i

/-- For `0 ≤ rho ≤ 1`, every path-orbit coordinate interlaces its next value. -/
theorem interl_pathRows_succ {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (n row : ℕ) (i : Fin (1 + n)) :
    Interl
      (separatedCharacteristicRows (pathA rho n) (pathB rho n) (pathSeed n) row i)
      (separatedCharacteristicRows (pathA rho n) (pathB rho n) (pathSeed n)
        (row + 1) i) := by
  exact separatedCharacteristicRows_interl_succ
    (a := pathA rho n) (b := pathB rho n) (seed := pathSeed n)
    (fun _ ↦ hrho0) (fun _ ↦ by simp [pathB]; linarith)
    (pathSeed_interlacing n) row i

end RealRooted.SeparatedCharacteristicExamples
