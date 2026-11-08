module

public import RealRooted.Schur.ElementaryToeplitz
import RealRooted.Schur.PositiveRoots
import RealRooted.Schur.Roots

/-! # Horizontal stretching and boundary parity for elementary determinants -/

@[expose] public section

namespace RealRooted.Schur

/-- The original column containing an index after each column is repeated `m` times.
The empty stretch is included because its index type is empty. -/
def unstretchColumn {n : ℕ} (m : ℕ) (i : Fin (n * m)) : Fin n :=
  ⟨i.val / m, Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using i.isLt)⟩

/-- Horizontal stretching repeats column heights; it does not multiply them. -/
def repeatColumns {n : ℕ} (h : Fin n → ℕ) (m : ℕ) : Fin (n * m) → ℕ :=
  h ∘ unstretchColumn m

/-- Repetition respects the ordering of columns. -/
theorem unstretchColumn_monotone {n : ℕ} (m : ℕ) :
    Monotone (unstretchColumn (n := n) m) := by
  intro i j hij
  exact Nat.div_le_div_right hij

/-- A horizontally stretched partition still has weakly decreasing column heights. -/
theorem repeatColumns_antitone {n : ℕ} {h : Fin n → ℕ} (hh : Antitone h) (m : ℕ) :
    Antitone (repeatColumns h m) := hh.comp_monotone (unstretchColumn_monotone m)

/-- Boundary parity implies active-position parity. Pairwise boundary sums express
uniform parity of both padded boundary lists without selecting a first column. -/
theorem even_active_of_even_boundary {n : ℕ} {h k : Fin n → ℕ} {r : ℕ}
    (hpar : ∀ i j, Even (h i + k j + r)) :
    ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r → Even (i.val + j.val) := by
  intro i j hij
  have hp := hpar i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Nat.even_iff] at hp ⊢
  dsimp [columnIndex] at hij
  lia

/-- The corresponding odd boundary condition gives odd active positions. -/
theorem odd_active_of_odd_boundary {n : ℕ} {h k : Fin n → ℕ} {r : ℕ}
    (hpar : ∀ i j, Odd (h i + k j + r)) :
    ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r → Odd (i.val + j.val) := by
  intro i j hij
  have hp := hpar i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Nat.odd_iff] at hp ⊢
  dsimp [columnIndex] at hij
  lia

variable {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → ℝ)
  (ha : ∀ i ∈ s, 0 ≤ a i) {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
  (hkh : ∀ i, k i ≤ h i)
  (hsize : ∀ i, h i ≤ k i + (s.filter fun j => 0 < a j).card) (r : ℕ)

include ha hh hk hkh hsize

/-- Every simultaneous horizontal stretch of an even-boundary-parity skew shape
has a nonzero, real-rooted elementary-coordinate specialization. -/
theorem repeatColumns_isRealRooted (hpar : ∀ i j, Even (h i + k j + r)) (m : ℕ) :
    elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r ≠ 0 ∧
      (elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r).Splits :=
  elementarySubstitution_isRealRooted s a ha
    (repeatColumns_antitone hh m) (repeatColumns_antitone hk m)
    (fun i => hkh (unstretchColumn m i)) (fun i => hsize (unstretchColumn m i))
    r (even_active_of_even_boundary fun i j =>
      hpar (unstretchColumn m i) (unstretchColumn m j))

/-- All roots remain strictly negative under every horizontal stretch. -/
theorem roots_repeatColumns_neg (hpar : ∀ i j, Even (h i + k j + r)) (m : ℕ) :
    ∀ x ∈ (elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r).roots,
      x < 0 :=
  roots_elementarySubstitution_neg s a ha
    (repeatColumns_antitone hh m) (repeatColumns_antitone hk m)
    (fun i => hkh (unstretchColumn m i)) (fun i => hsize (unstretchColumn m i))
    r (even_active_of_even_boundary fun i j =>
      hpar (unstretchColumn m i) (unstretchColumn m j))

/-- Odd-boundary-parity skew shapes stay real-rooted under every horizontal stretch. -/
theorem repeatColumns_isRealRooted_of_odd (hpar : ∀ i j, Odd (h i + k j + r)) (m : ℕ) :
    elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r ≠ 0 ∧
      (elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r).Splits :=
  elementarySubstitution_isRealRooted_of_odd s a ha
    (repeatColumns_antitone hh m) (repeatColumns_antitone hk m)
    (fun i => hkh (unstretchColumn m i)) (fun i => hsize (unstretchColumn m i))
    r (odd_active_of_odd_boundary fun i j =>
      hpar (unstretchColumn m i) (unstretchColumn m j))

/-- All roots remain strictly positive in the odd-boundary-parity case. -/
theorem roots_repeatColumns_pos (hpar : ∀ i j, Odd (h i + k j + r)) (m : ℕ) :
    ∀ x ∈ (elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r).roots,
      0 < x :=
  roots_elementarySubstitution_pos_of_odd s a ha
    (repeatColumns_antitone hh m) (repeatColumns_antitone hk m)
    (fun i => hkh (unstretchColumn m i)) (fun i => hsize (unstretchColumn m i))
    r (odd_active_of_odd_boundary fun i j =>
      hpar (unstretchColumn m i) (unstretchColumn m j))

end RealRooted.Schur
