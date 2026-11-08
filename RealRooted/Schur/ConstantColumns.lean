module

public import RealRooted.Schur.Stretching
import RealRooted.Schur.Roots

/-! # Constant-height columns and duplicated-row families for elementary determinants -/

public section

open Matrix Polynomial

namespace RealRooted.Schur

/-- Constant skew column height equal to the moving coordinate makes the active
matrix the identity, without any uniform boundary-parity assumption. -/
theorem activeMatrix_eq_one_of_constant_height {n : ℕ} {h k : Fin n → ℕ}
    (hk : Antitone k) (r : ℕ) (hheight : ∀ i, h i = k i + r) :
    activeMatrix (fun i => (columnIndex h i : ℤ))
      (fun i => (columnIndex k i : ℤ)) r = 1 := by
  have heq (i : Fin n) : (columnIndex h i : ℤ) = columnIndex k i + r := by
    have hi := i.isLt
    have hhi := hheight i
    dsimp [columnIndex]
    lia
  have hinj : Function.Injective (fun i => (columnIndex k i : ℤ)) :=
    Int.ofNat_injective.comp (columnIndex_strictAnti hk).injective
  ext i j
  simp [activeMatrix, heq, hinj.eq_iff, Matrix.one_apply]

/-- The constant-height specialization is the characteristic determinant `det(M + t I)`. -/
theorem elementarySubstitution_eq_det_add_X_one {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) {h k : Fin n → ℕ}
    (hk : Antitone k) (r : ℕ) (hheight : ∀ i, h i = k i + r) :
    elementarySubstitution s a h k r =
      det ((elementaryMatrix s a h k).map C + (X : ℝ[X]) • 1) := by
  simp [elementarySubstitution, activeMatrix_eq_one_of_constant_height hk r hheight]

/-- Constant column height forces even active-position parity. -/
private theorem even_active_of_constant_height {n : ℕ} {h k : Fin n → ℕ}
    (hk : Antitone k) (r : ℕ) (hheight : ∀ i, h i = k i + r) :
    ∀ i j, (columnIndex h i : ℤ) = columnIndex k j + r → Even (i.val + j.val) := by
  intro i j hij
  have he := congrFun (congrFun (activeMatrix_eq_one_of_constant_height hk r hheight) i) j
  have heq : i = j := by
    by_contra hne
    simp [activeMatrix, hij, hne] at he
  subst j
  exact ⟨i.val, rfl⟩

/-- Constant column height `r ≤ #positive letters` satisfies the shape hypotheses of every
horizontal stretch. -/
private theorem repeatColumns_constant_height_bounds {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) {h k : Fin n → ℕ} (r : ℕ)
    (hheight : ∀ i, h i = k i + r) (hsize : r ≤ (s.filter fun i => 0 < a i).card) (m : ℕ) :
    (∀ i, repeatColumns k m i ≤ repeatColumns h m i) ∧
      ∀ i, repeatColumns h m i ≤ repeatColumns k m i + (s.filter fun i => 0 < a i).card := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hi := hheight (unstretchColumn m i)
    change k (unstretchColumn m i) ≤ h (unstretchColumn m i)
    lia
  · have hi := hheight (unstretchColumn m i)
    change h (unstretchColumn m i) ≤ k (unstretchColumn m i) + _
    lia

/-- Every stretched constant-height skew specialization is nonzero and real-rooted. -/
theorem repeatColumns_isRealRooted_of_constant_height {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
    (r : ℕ) (hheight : ∀ i, h i = k i + r)
    (hsize : r ≤ (s.filter fun i => 0 < a i).card) (m : ℕ) :
    elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r ≠ 0 ∧
      (elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r).Splits :=
  have hb := repeatColumns_constant_height_bounds s a r hheight hsize m
  elementarySubstitution_isRealRooted s a ha
    (repeatColumns_antitone hh m) (repeatColumns_antitone hk m) hb.1 hb.2 r
    (even_active_of_constant_height (repeatColumns_antitone hk m) r
      (fun i => hheight (unstretchColumn m i)))

/-- Every stretched constant-height skew specialization has strictly negative roots. -/
theorem roots_repeatColumns_neg_of_constant_height {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k)
    (r : ℕ) (hheight : ∀ i, h i = k i + r)
    (hsize : r ≤ (s.filter fun i => 0 < a i).card) (m : ℕ) :
    ∀ x ∈ (elementarySubstitution s a (repeatColumns h m) (repeatColumns k m) r).roots,
      x < 0 :=
  have hb := repeatColumns_constant_height_bounds s a r hheight hsize m
  roots_elementarySubstitution_neg s a ha
    (repeatColumns_antitone hh m) (repeatColumns_antitone hk m) hb.1 hb.2 r
    (even_active_of_constant_height (repeatColumns_antitone hk m) r
      (fun i => hheight (unstretchColumn m i)))

/-- Duplicated-row skew shapes give real-rooted families for every even moving coordinate. -/
theorem repeatColumns_double_isRealRooted {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k) (hkh : ∀ i, k i ≤ h i)
    (hsize : ∀ i, 2 * h i ≤ 2 * k i + (s.filter fun j => 0 < a j).card)
    (r m : ℕ) :
    elementarySubstitution s a (repeatColumns (fun i => 2 * h i) m)
      (repeatColumns (fun i => 2 * k i) m) (2 * r) ≠ 0 ∧
    (elementarySubstitution s a (repeatColumns (fun i => 2 * h i) m)
      (repeatColumns (fun i => 2 * k i) m) (2 * r)).Splits := by
  apply repeatColumns_isRealRooted s a ha
    (fun i j hij => Nat.mul_le_mul_left 2 (hh hij))
    (fun i j hij => Nat.mul_le_mul_left 2 (hk hij))
    (fun i => Nat.mul_le_mul_left 2 (hkh i)) hsize (2 * r)
  intro i j
  exact ⟨h i + k j + r, by ring⟩

/-- Duplicating every row doubles both column boundaries. Every even moving
coordinate then gives negative roots under arbitrary horizontal stretching. -/
theorem roots_repeatColumns_double_neg {ι : Type*} {n : ℕ}
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {h k : Fin n → ℕ} (hh : Antitone h) (hk : Antitone k) (hkh : ∀ i, k i ≤ h i)
    (hsize : ∀ i, 2 * h i ≤ 2 * k i + (s.filter fun j => 0 < a j).card)
    (r m : ℕ) :
    ∀ x ∈ (elementarySubstitution s a (repeatColumns (fun i => 2 * h i) m)
      (repeatColumns (fun i => 2 * k i) m) (2 * r)).roots, x < 0 := by
  apply roots_repeatColumns_neg s a ha
    (fun i j hij => Nat.mul_le_mul_left 2 (hh hij))
    (fun i j hij => Nat.mul_le_mul_left 2 (hk hij))
    (fun i => Nat.mul_le_mul_left 2 (hkh i)) hsize (2 * r)
  intro i j
  exact ⟨h i + k j + r, by ring⟩

end RealRooted.Schur
