module

public import RealRooted.MatrixInterlacing.TotallyNonnegative
public import RealRooted.MatrixInterlacing.Converse
import RealRooted.AffineFamily
import RealRooted.AffineProperPosition
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Constant transitions with a variable last row

A nonnegative constant matrix followed by a row of variable multiples preserves interlacing
when its constant minors and its cross products with the last row have the required signs.
This is a specialization of the checked Brändén matrix criterion. It packages the transition
used in the unpublished exponential-row argument of RealRooted issue #2415.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- A constant matrix augmented by the row `(q₀ X, …, qₙ₋₁ X, 1)`. -/
noncomputable def variableLastRowMatrix {m n : ℕ}
    (A : Fin m → Fin (n + 1) → ℝ) (q : Fin n → ℝ) : List (List ℝ[X]) :=
  List.ofFn fun i : Fin (m + 1) => List.ofFn fun j : Fin (n + 1) =>
    Fin.lastCases (Fin.lastCases 1 (fun j => C (q j) * X) j) (fun i => C (A i j)) i

private lemma affine_interl_of_nonneg {u v U V : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hcross : u * V ≤ U * v) :
    Interl (C u * X + C v) (C U * X + C V) := by
  convert interl_const_entries_affine_of_det_nonneg hU hu hV hv zero_lt_one hcross
    (t := 0) using 1 <;>
    simp only [C_1, C_0, one_mul, add_zero] <;> ring

private lemma constant_variable_pencil {a b q r s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hcross : a * r ≤ b * q) (hs : 0 < s) (ht : 0 < t) :
    Interl ((C s * X + C t) * C b + C r * X)
      ((C s * X + C t) * C a + C q * X) := by
  convert affine_interl_of_nonneg
    (u := s * b + r) (v := t * b) (U := s * a + q) (V := t * a)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hcross)]) using 1 <;>
    simp only [map_add, map_mul] <;> ring

private lemma constant_variable_last_pencil {a b q s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hs : 0 < s) (ht : 0 < t) :
    Interl ((C s * X + C t) * C b + 1)
      ((C s * X + C t) * C a + C q * X) := by
  convert affine_interl_of_nonneg
    (u := s * b) (v := t * b + 1) (U := s * a + q) (V := t * a)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by nlinarith [mul_nonneg hq (mul_nonneg ht.le hb)]) using 1 <;>
    simp only [map_add, map_mul, map_one] <;> ring

private lemma variable_self_pencil {q r s t : ℝ}
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 < s) :
    Interl ((C s * X + C t) * (C r * X) + C r * X)
      ((C s * X + C t) * (C q * X) + C q * X) := by
  have h := (interl_affine_mul_X_add_X_self (t := t) hs).C_mul_left_of_nonneg hr
    |>.C_mul_right_of_nonneg hq
  convert h using 1 <;> ring

private lemma variable_last_self_pencil {q s t : ℝ}
    (hq : 0 ≤ q) (hs : 0 < s) (ht : 0 < t) :
    Interl ((C s * X + C t) * 1 + 1)
      ((C s * X + C t) * (C q * X) + C q * X) := by
  have h := strictInterl_self_X_mul_of_nonneg
    (isRealRooted_affine_factor (t := t + 1) hs).1
    (isRealRooted_affine_factor (t := t + 1) hs).2
    ((hasNonnegCoeffs_C hs.le).mul hasNonnegCoeffs_X |>.add
      (hasNonnegCoeffs_C (by positivity : 0 ≤ t + 1)))
  convert h.toInterl.C_mul_right_of_nonneg hq using 1 <;> simp only [map_add, map_one] <;>
    ring

/-- The affine pencil test for a constant block and a variable last row. -/
private lemma variableLastRow_has2x2 {m n : ℕ}
    {A : Fin m → Fin (n + 1) → ℝ} (hA : Matrix.IsTP2 A)
    {q : Fin n → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hcross : ∀ i j k, j ≤ k → A i j.castSucc * q k ≤ A i k.castSucc * q j) :
    ∀ (i₁ i₂ : Fin (m + 1)) (j₁ j₂ : Fin (n + 1)),
        i₁ ≤ i₂ → j₁ ≤ j₂ → Has2x2InterlacingProperty0
          (Fin.lastCases (Fin.lastCases 1 (fun j => C (q j) * X) j₁)
            (fun i => C (A i j₁)) i₁)
          (Fin.lastCases (Fin.lastCases 1 (fun j => C (q j) * X) j₂)
            (fun i => C (A i j₂)) i₁)
          (Fin.lastCases (Fin.lastCases 1 (fun j => C (q j) * X) j₁)
            (fun i => C (A i j₁)) i₂)
          (Fin.lastCases (Fin.lastCases 1 (fun j => C (q j) * X) j₂)
            (fun i => C (A i j₂)) i₂) := by
  intro i₁ i₂ j₁ j₂ hi hj
  induction i₂ using Fin.lastCases with
  | cast i₂ =>
    obtain ⟨i₁, rfl⟩ := Fin.exists_castSucc_eq.mpr
      (Fin.ne_last_of_lt (lt_of_le_of_lt hi (Fin.castSucc_lt_last i₂)))
    simp only [Fin.lastCases_castSucc]
    intro s t hs ht
    apply interl_const_entries_affine_of_det_nonneg
      (A := A i₁ j₁) (b := A i₁ j₂) (c := A i₂ j₁) (d := A i₂ j₂)
      (hA.nonneg _ _) (hA.nonneg _ _) (hA.nonneg _ _) (hA.nonneg _ _) hs
    by_cases hi' : i₁ = i₂
    · subst i₂
      exact le_of_eq (mul_comm _ _)
    by_cases hj' : j₁ = j₂
    · subst j₂
      exact le_rfl
    have hminor := hA.minor_nonneg
      (lt_of_le_of_ne (show i₁ ≤ i₂ from hi) hi')
      (lt_of_le_of_ne hj hj')
    linarith
  | last =>
    induction i₁ using Fin.lastCases with
    | cast i₁ =>
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      induction j₂ using Fin.lastCases with
      | cast j₂ =>
        obtain ⟨j₁, rfl⟩ := Fin.exists_castSucc_eq.mpr
          (Fin.ne_last_of_lt (lt_of_le_of_lt hj (Fin.castSucc_lt_last j₂)))
        simp only [Fin.lastCases_castSucc]
        exact fun s t hs ht => constant_variable_pencil
          (hA.nonneg _ _) (hA.nonneg _ _) (hq _) (hq _)
          (hcross _ _ _ (Fin.castSucc_le_castSucc_iff.mp hj)) hs ht
      | last =>
        simp only [Fin.lastCases_last]
        induction j₁ using Fin.lastCases with
        | cast j₁ =>
          simp only [Fin.lastCases_castSucc]
          exact fun s t hs ht => constant_variable_last_pencil
            (hA.nonneg _ _) (hA.nonneg _ _) (hq _) hs ht
        | last =>
          simp only [Fin.lastCases_last]
          intro s t hs ht
          exact interl_const_entries_affine_of_det_nonneg
            (hA.nonneg _ _) (hA.nonneg _ _) zero_le_one zero_le_one hs (by simp)
    | last =>
      simp only [Fin.lastCases_last]
      induction j₂ using Fin.lastCases with
      | cast j₂ =>
        obtain ⟨j₁, rfl⟩ := Fin.exists_castSucc_eq.mpr
          (Fin.ne_last_of_lt (lt_of_le_of_lt hj (Fin.castSucc_lt_last j₂)))
        simp only [Fin.lastCases_castSucc]
        exact fun s t hs _ => variable_self_pencil (hq _) (hq _) hs
      | last =>
        simp only [Fin.lastCases_last]
        induction j₁ using Fin.lastCases with
        | cast j₁ =>
          simp only [Fin.lastCases_castSucc]
          exact fun s t hs ht => variable_last_self_pencil (hq _) hs ht
        | last =>
          simp only [Fin.lastCases_last]
          intro s t hs ht
          simpa [add_assoc] using interl_affine_self (t := t + 1) hs

/-- The augmented matrix preserves zero-aware nonnegative real-rooted interlacing sequences.
The cross-product hypothesis is opposite to the constant-minor inequality because the last
row contains multiples of the variable. -/
theorem variableLastRowMatrix_preserves {m n : ℕ}
    {A : Fin m → Fin (n + 1) → ℝ} (hA : Matrix.IsTP2 A)
    {q : Fin n → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hcross : ∀ i j k, j ≤ k → A i j.castSucc * q k ≤ A i k.castSucc * q j) :
    PreservesInterlacingSeq0 (n + 1) (variableLastRowMatrix A q) := by
  have hrect : ∀ row ∈ variableLastRowMatrix A q, row.length = n + 1 := by
    simp [variableLastRowMatrix]
  rw [PreservesInterlacingSeq0.iff_nonneg_and_2x2 _ hrect]
  constructor
  · simp only [variableLastRowMatrix, List.forall_mem_ofFn_iff]
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa using hasNonnegCoeffs_one
      | cast j => simpa using (hasNonnegCoeffs_C (hq j)).mul hasNonnegCoeffs_X
    | cast i => simpa using hasNonnegCoeffs_C (hA.nonneg i j)
  · intro i₁ i₂ j₁ j₂ hi hj
    have hi₁ : (i₁ : ℕ) < m + 1 := by simpa [variableLastRowMatrix] using i₁.isLt
    have hi₂ : (i₂ : ℕ) < m + 1 := by simpa [variableLastRowMatrix] using i₂.isLt
    unfold variableLastRowMatrix at *
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact variableLastRow_has2x2 hA hq hcross ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ j₁ j₂ hi hj

/-- The list matrix acts on a typed polynomial vector by the expected scalar sums. -/
theorem variableLastRowMatrix_action {m n : ℕ}
    (A : Fin m → Fin (n + 1) → ℝ) (q : Fin n → ℝ) (f : Fin (n + 1) → ℝ[X]) :
    matPolyAction (variableLastRowMatrix A q) (List.ofFn f) =
      List.ofFn (Fin.lastCases
        (f (Fin.last n) + X * ∑ j : Fin n, C (q j) * f j.castSucc)
        (fun i => ∑ j, C (A i j) * f j)) := by
  let G : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ[X] := Matrix.of
    (fun i j => Fin.lastCases (Fin.lastCases 1 (fun j => C (q j) * X) j)
      (fun i => C (A i j)) i)
  change matPolyAction (List.ofFn fun i => List.ofFn fun j => G i j) (List.ofFn f) = _
  rw [matPolyAction_ofFn G f]
  apply congrArg List.ofFn
  funext i
  induction i using Fin.lastCases with
  | cast i => simp [G, Matrix.mulVec, dotProduct]
  | last =>
    simp only [G, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.lastCases_last]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, one_mul]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

end RealRooted
