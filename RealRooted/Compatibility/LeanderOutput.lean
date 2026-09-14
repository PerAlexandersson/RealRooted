import RealRooted.Compatibility.LeanderTransform
import RealRooted.Compatibility.Three

open Polynomial

noncomputable section

namespace RealRooted

/-- The nonnegative affine factor appearing in the middle region of
Leander's compatibility argument. -/
def leanderAffineFactor (a b : ℝ) : ℝ[X] := C a + C b * X

theorem leanderAffineFactor_hasNonnegCoeffs {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasNonnegCoeffs (leanderAffineFactor a b) := by
  exact (hasNonnegCoeffs_C ha).add
    (nonnegCoeffs_C_mul hb hasNonnegCoeffs_X)

theorem leanderAffineFactor_eq_zero_iff (a b : ℝ) :
    leanderAffineFactor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hzero
    constructor
    · simpa [leanderAffineFactor] using
        congrArg (fun p : ℝ[X] => p.coeff 0) hzero
    · simpa [leanderAffineFactor] using
        congrArg (fun p : ℝ[X] => p.coeff 1) hzero
  · rintro ⟨rfl, rfl⟩
    simp [leanderAffineFactor]

theorem leanderAffineFactor_splits (a b : ℝ) :
    (leanderAffineFactor a b).Splits := by
  apply Polynomial.Splits.of_natDegree_le_one
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact (Polynomial.natDegree_mul_le (p := C b) (q := X)).trans (by simp)

theorem leanderAffineFactor_hasPosLeadingCoeff {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ 0 ∨ b ≠ 0) :
    HasPosLeadingCoeff (leanderAffineFactor a b) := by
  apply (leanderAffineFactor_hasNonnegCoeffs ha hb).pos_leadingCoeff
  intro hzero
  have hz := (leanderAffineFactor_eq_zero_iff a b).mp hzero
  exact hab.elim (fun ha0 => ha0 hz.1) (fun hb0 => hb0 hz.2)

private def leanderOutputRegion {n : ℕ} (f : Fin n → ℝ[X])
    (i j : Fin n) (a b : ℝ) (h : Fin n) : ℝ[X] :=
  if h ≤ i then X * f h
  else if h < j then leanderAffineFactor a b * f h
  else f h

private def leanderOutputWeight {n : ℕ} (i j : Fin n)
    (a b : ℝ) (h : Fin n) : ℝ :=
  if h < i then a + b
  else if h = i then if i < j then b else 0
  else if h < j then 1
  else if h = j then if i < j then a else 0
  else a + b

private theorem leanderOutputWeight_nonneg {n : ℕ} (i j : Fin n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Fin n) :
    0 ≤ leanderOutputWeight i j a b h := by
  unfold leanderOutputWeight
  split_ifs <;> positivity

private theorem leanderOutputRegion_ne_zero_and_splits {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits) (h : Fin n) :
    leanderOutputRegion f i j a b h ≠ 0 ∧
      (leanderOutputRegion f i j a b h).Splits := by
  unfold leanderOutputRegion
  split
  next => exact isRealRooted_X_mul_of_isRealRooted (hrr h)
  next =>
    split
    next =>
      exact ⟨mul_ne_zero
          (fun hz => hab.elim (fun ha0 => ha0 <| by
              have := (leanderAffineFactor_eq_zero_iff a b).mp hz
              exact this.1) (fun hb0 => hb0 <| by
              have := (leanderAffineFactor_eq_zero_iff a b).mp hz
              exact this.2))
          (hrr h).1,
        (leanderAffineFactor_splits a b).mul (hrr h).2⟩
    next => exact hrr h

private theorem leanderOutputRegion_hasPosLeadingCoeff {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ 0 ∨ b ≠ 0)
    (hpos : ∀ h, HasPosLeadingCoeff (f h)) (h : Fin n) :
    HasPosLeadingCoeff (leanderOutputRegion f i j a b h) := by
  unfold leanderOutputRegion
  split
  next => exact (hpos h).X_mul
  next =>
    split
    next => exact (leanderAffineFactor_hasPosLeadingCoeff ha hb hab).mul (hpos h)
    next => exact hpos h

private theorem leanderOutputRegion_hasNonnegCoeffs {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hnn : ∀ h, HasNonnegCoeffs (f h)) (h : Fin n) :
    HasNonnegCoeffs (leanderOutputRegion f i j a b h) := by
  unfold leanderOutputRegion
  split
  next => exact (hnn h).X_mul
  next =>
    split
    next => exact (leanderAffineFactor_hasNonnegCoeffs ha hb).mul (hnn h)
    next => exact hnn h

private theorem leanderOutputRegion_compatible_of_lt {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits)
    (hpos : ∀ h, HasPosLeadingCoeff (f h))
    (hnn : ∀ h, HasNonnegCoeffs (f h))
    (hff : ∀ ⦃h k⦄, h < k → Compatible (f h) (f k))
    (hXf : ∀ ⦃h k⦄, h < k → Compatible (X * f h) (f k))
    {h k : Fin n} (hhk : h < k) :
    Compatible (leanderOutputRegion f i j a b h)
      (leanderOutputRegion f i j a b k) := by
  by_cases hleft : h ≤ i
  · by_cases kleft : k ≤ i
    · simpa [leanderOutputRegion, hleft, kleft] using (hff hhk).X_mul
    · have hik : i < k := lt_of_not_ge kleft
      by_cases kmiddle : k < j
      · have hmidleft : Compatible
            (leanderAffineFactor a b * f k) (X * f h) := by
          simpa [leanderAffineFactor, add_mul, mul_assoc] using
            Compatible.C_mul_add_C_mul_left_of_pairwise_three
              (a := f k) (b := X * f k) (c := X * f h) ha hb
              (hrr k) (isRealRooted_X_mul_of_isRealRooted (hrr k))
              (isRealRooted_X_mul_of_isRealRooted (hrr h))
              (hpos k) (hpos k).X_mul (hpos h).X_mul
              (hnn k) (hnn k).X_mul (hnn h).X_mul
              (Compatible.self_X_mul_of_splits (hrr k).2)
              (hXf hhk).comm ((hff hhk).X_mul).comm
        simpa [leanderOutputRegion, hleft, kleft, kmiddle] using hmidleft.comm
      · simpa [leanderOutputRegion, hleft, kleft, kmiddle] using hXf hhk
  · have hil : i < h := lt_of_not_ge hleft
    have kileft : ¬k ≤ i := not_le_of_gt (lt_trans hil hhk)
    by_cases hmiddle : h < j
    · by_cases kmiddle : k < j
      · simpa [leanderOutputRegion, hleft, kileft, hmiddle, kmiddle] using
          (hff hhk).mul_common_factor (leanderAffineFactor_splits a b)
      · have hmidright : Compatible
            (leanderAffineFactor a b * f h) (f k) := by
          simpa [leanderAffineFactor, add_mul, mul_assoc] using
            Compatible.C_mul_add_C_mul_left_of_pairwise_three
              (a := f h) (b := X * f h) (c := f k) ha hb
              (hrr h) (isRealRooted_X_mul_of_isRealRooted (hrr h)) (hrr k)
              (hpos h) (hpos h).X_mul (hpos k)
              (hnn h) (hnn h).X_mul (hnn k)
              (Compatible.self_X_mul_of_splits (hrr h).2)
              (hff hhk) (hXf hhk)
        simpa [leanderOutputRegion, hleft, kileft, hmiddle, kmiddle] using
          hmidright
    · have kmiddle : ¬k < j := fun hkj => hmiddle (lt_trans hhk hkj)
      simpa [leanderOutputRegion, hleft, kileft, hmiddle, kmiddle] using hff hhk

private theorem weightedSum_leanderOutputRegion {n : ℕ}
    (f : Fin n → ℝ[X]) {i j : Fin n} (hij : i ≤ j) (a b : ℝ) :
    weightedSum (List.ofFn fun h =>
        (leanderOutputWeight i j a b h,
          leanderOutputRegion f i j a b h)) =
      C a * leanderTransform f i + C b * leanderTransform f j := by
  rw [weightedSum_ofFn,
    C_mul_leanderTransform_add_C_mul_leanderTransform f hij a b]
  apply Fintype.sum_congr
  intro h
  by_cases hhi : h < i
  · have hle : h ≤ i := hhi.le
    simp [leanderOutputWeight, leanderOutputRegion, hhi, hle]
    ring
  · by_cases hEqI : h = i
    · subst h
      by_cases hijlt : i < j
      · simp [leanderOutputWeight, leanderOutputRegion, hijlt]
        ring
      · have hEq : i = j := le_antisymm hij (le_of_not_gt hijlt)
        subst j
        simp [leanderOutputWeight, leanderOutputRegion]
    · have ih : i < h :=
        lt_of_le_of_ne (le_of_not_gt hhi) (Ne.symm hEqI)
      have hnle : ¬h ≤ i := not_le_of_gt ih
      by_cases hhj : h < j
      · simp [leanderOutputWeight, leanderOutputRegion, hhi, hEqI, hnle,
          hhj, leanderAffineFactor]
      · by_cases hEqJ : h = j
        · subst h
          have hijlt : i < j := ih
          simp [leanderOutputWeight, leanderOutputRegion, hhi, hEqI, hnle,
            hijlt]
        · simp [leanderOutputWeight, leanderOutputRegion, hhi, hEqI, hnle,
            hhj, hEqJ]

/-- Leander Theorem 2.3, condition (a'): ordered output coordinates of the
diagonal-omitting transform are compatible. -/
theorem compatible_leanderTransform {n : ℕ} (f : Fin n → ℝ[X])
    (hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits)
    (hpos : ∀ h, HasPosLeadingCoeff (f h))
    (hnn : ∀ h, HasNonnegCoeffs (f h))
    (hff : ∀ ⦃h k⦄, h < k → Compatible (f h) (f k))
    (hXf : ∀ ⦃h k⦄, h < k → Compatible (X * f h) (f k))
    {i j : Fin n} (hij : i ≤ j) :
    Compatible (leanderTransform f i) (leanderTransform f j) := by
  intro a b ha hb
  by_cases habzero : a = 0 ∧ b = 0
  · rcases habzero with ⟨rfl, rfl⟩
    simp
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha0 : a = 0
    · exact Or.inr fun hb0 => habzero ⟨ha0, hb0⟩
    · exact Or.inl ha0
  let region : Fin n → ℝ[X] := leanderOutputRegion f i j a b
  let fs : List ℝ[X] := List.ofFn region
  have hregions_rr : ∀ p ∈ fs, p ≠ 0 ∧ p.Splits := by
    intro p hp
    simp only [fs, List.mem_ofFn] at hp
    rcases hp with ⟨h, rfl⟩
    exact leanderOutputRegion_ne_zero_and_splits f i j hab hrr h
  have hregions_pos : ∀ p ∈ fs, HasPosLeadingCoeff p := by
    intro p hp
    simp only [fs, List.mem_ofFn] at hp
    rcases hp with ⟨h, rfl⟩
    exact leanderOutputRegion_hasPosLeadingCoeff f i j ha hb hab hpos h
  have hregions_nn : ∀ p ∈ fs, HasNonnegCoeffs p := by
    intro p hp
    simp only [fs, List.mem_ofFn] at hp
    rcases hp with ⟨h, rfl⟩
    exact leanderOutputRegion_hasNonnegCoeffs f i j ha hb hnn h
  have hregions_pair : PairwiseCompatible fs := by
    apply pairwiseCompatible_of_forall_mem
    intro p hp q hq
    simp only [fs, List.mem_ofFn] at hp hq
    rcases hp with ⟨h, rfl⟩
    rcases hq with ⟨k, rfl⟩
    rcases lt_trichotomy h k with hhk | heq | hkh
    · exact leanderOutputRegion_compatible_of_lt f i j ha hb hrr hpos hnn
        hff hXf hhk
    · subst k
      exact Compatible.self_of_splits
        (leanderOutputRegion_ne_zero_and_splits f i j hab hrr h).2
    · exact (leanderOutputRegion_compatible_of_lt f i j ha hb hrr hpos hnn
        hff hXf hkh).comm
  have hfamily : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      hregions_rr hregions_pos hregions_nn).1 hregions_pair
  let ws : List (ℝ × ℝ[X]) := List.ofFn fun h =>
    (leanderOutputWeight i j a b h, region h)
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_ofFn] at hap
    rcases hap with ⟨h, rfl⟩
    simp [fs]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_ofFn] at hap
    rcases hap with ⟨h, rfl⟩
    exact leanderOutputWeight_nonneg i j ha hb h
  simpa [ws, region] using
    (weightedSum_leanderOutputRegion f hij a b ▸ hfamily ws hmem hnonneg)

end RealRooted
