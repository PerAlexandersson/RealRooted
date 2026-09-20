import RealRooted.Compatibility.LeanderOutput

open Polynomial

noncomputable section

namespace RealRooted

private def leanderXOutputRegion {n : ℕ} (f : Fin n → ℝ[X])
    (i j : Fin n) (a b : ℝ) (h : Fin n) : ℝ[X] :=
  if h < i then leanderAffineFactor b a * (X * f h)
  else if h ≤ j then X * f h
  else leanderAffineFactor b a * f h

private def leanderXOutputWeight {n : ℕ} (i j : Fin n)
    (a b : ℝ) (h : Fin n) : ℝ :=
  if h < i then 1
  else if h = i then if i < j then b else 0
  else if h < j then a + b
  else if h = j then if i < j then a else 0
  else 1

private theorem leanderXOutputWeight_nonneg {n : ℕ} (i j : Fin n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Fin n) :
    0 ≤ leanderXOutputWeight i j a b h := by
  unfold leanderXOutputWeight
  split_ifs <;> positivity

private theorem leanderXOutputRegion_ne_zero_and_splits {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits) (h : Fin n) :
    leanderXOutputRegion f i j a b h ≠ 0 ∧
      (leanderXOutputRegion f i j a b h).Splits := by
  have hba : b ≠ 0 ∨ a ≠ 0 := hab.symm
  unfold leanderXOutputRegion
  split
  next =>
    exact ⟨mul_ne_zero
        (fun hz => hba.elim (fun hb0 => hb0 <| by
            exact (leanderAffineFactor_eq_zero_iff b a).mp hz |>.1)
          (fun ha0 => ha0 <| by
            exact (leanderAffineFactor_eq_zero_iff b a).mp hz |>.2))
        (isRealRooted_X_mul_of_isRealRooted (hrr h)).1,
      (leanderAffineFactor_splits b a).mul
        (isRealRooted_X_mul_of_isRealRooted (hrr h)).2⟩
  next =>
    split
    next => exact isRealRooted_X_mul_of_isRealRooted (hrr h)
    next =>
      exact ⟨mul_ne_zero
          (fun hz => hba.elim (fun hb0 => hb0 <| by
              exact (leanderAffineFactor_eq_zero_iff b a).mp hz |>.1)
            (fun ha0 => ha0 <| by
              exact (leanderAffineFactor_eq_zero_iff b a).mp hz |>.2))
          (hrr h).1,
        (leanderAffineFactor_splits b a).mul (hrr h).2⟩

private theorem leanderXOutputRegion_hasPosLeadingCoeff {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ 0 ∨ b ≠ 0)
    (hpos : ∀ h, HasPosLeadingCoeff (f h)) (h : Fin n) :
    HasPosLeadingCoeff (leanderXOutputRegion f i j a b h) := by
  have hba : b ≠ 0 ∨ a ≠ 0 := hab.symm
  unfold leanderXOutputRegion
  split
  next =>
    exact (leanderAffineFactor_hasPosLeadingCoeff hb ha hba).mul (hpos h).X_mul
  next =>
    split
    next => exact (hpos h).X_mul
    next => exact (leanderAffineFactor_hasPosLeadingCoeff hb ha hba).mul (hpos h)

private theorem leanderXOutputRegion_hasNonnegCoeffs {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hnn : ∀ h, HasNonnegCoeffs (f h)) (h : Fin n) :
    HasNonnegCoeffs (leanderXOutputRegion f i j a b h) := by
  unfold leanderXOutputRegion
  split
  next => exact (leanderAffineFactor_hasNonnegCoeffs hb ha).mul (hnn h).X_mul
  next =>
    split
    next => exact (hnn h).X_mul
    next => exact (leanderAffineFactor_hasNonnegCoeffs hb ha).mul (hnn h)

private theorem leanderXOutputRegion_compatible_of_lt {n : ℕ}
    (f : Fin n → ℝ[X]) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits)
    (hpos : ∀ h, HasPosLeadingCoeff (f h))
    (hnn : ∀ h, HasNonnegCoeffs (f h))
    (hff : ∀ ⦃h k⦄, h < k → Compatible (f h) (f k))
    (hXf : ∀ ⦃h k⦄, h < k → Compatible (X * f h) (f k))
    {h k : Fin n} (hhk : h < k) :
    Compatible (leanderXOutputRegion f i j a b h)
      (leanderXOutputRegion f i j a b k) := by
  by_cases hleft : h < i
  · by_cases kleft : k < i
    · simpa [leanderXOutputRegion, hleft, kleft] using
        (hff hhk).X_mul.mul_common_factor (leanderAffineFactor_splits b a)
    · by_cases kmiddle : k ≤ j
      · have hleftmiddle : Compatible
            (leanderAffineFactor b a * (X * f h)) (X * f k) := by
          simpa [leanderAffineFactor, add_mul, mul_assoc] using
            Compatible.C_mul_add_C_mul_left_of_pairwise_three
              (a := X * f h) (b := X * (X * f h)) (c := X * f k) hb ha
              (isRealRooted_X_mul_of_isRealRooted (hrr h))
              (isRealRooted_X_mul_of_isRealRooted
                (isRealRooted_X_mul_of_isRealRooted (hrr h)))
              (isRealRooted_X_mul_of_isRealRooted (hrr k))
              (hpos h).X_mul (hpos h).X_mul.X_mul (hpos k).X_mul
              (hnn h).X_mul (hnn h).X_mul.X_mul (hnn k).X_mul
              (Compatible.self_X_mul_of_splits
                (isRealRooted_X_mul_of_isRealRooted (hrr h)).2)
              ((hff hhk).X_mul) ((hXf hhk).X_mul)
        simpa [leanderXOutputRegion, hleft, kleft, kmiddle] using hleftmiddle
      · simpa [leanderXOutputRegion, hleft, kleft, kmiddle] using
          (hXf hhk).mul_common_factor (leanderAffineFactor_splits b a)
  · have ik : ¬k < i := fun hki => hleft (lt_trans hhk hki)
    by_cases hmiddle : h ≤ j
    · by_cases kmiddle : k ≤ j
      · simpa [leanderXOutputRegion, hleft, ik, hmiddle, kmiddle] using
          (hff hhk).X_mul
      · have hmiddleright : Compatible
            (leanderAffineFactor b a * f k) (X * f h) := by
          simpa [leanderAffineFactor, add_mul, mul_assoc] using
            Compatible.C_mul_add_C_mul_left_of_pairwise_three
              (a := f k) (b := X * f k) (c := X * f h) hb ha
              (hrr k) (isRealRooted_X_mul_of_isRealRooted (hrr k))
              (isRealRooted_X_mul_of_isRealRooted (hrr h))
              (hpos k) (hpos k).X_mul (hpos h).X_mul
              (hnn k) (hnn k).X_mul (hnn h).X_mul
              (Compatible.self_X_mul_of_splits (hrr k).2)
              (hXf hhk).comm ((hff hhk).X_mul).comm
        simpa [leanderXOutputRegion, hleft, ik, hmiddle, kmiddle] using
          hmiddleright.comm
    · have kmiddle : ¬k ≤ j := fun hkj => hmiddle (le_trans hhk.le hkj)
      simpa [leanderXOutputRegion, hleft, ik, hmiddle, kmiddle] using
        (hff hhk).mul_common_factor (leanderAffineFactor_splits b a)

private theorem weightedSum_leanderXOutputRegion {n : ℕ}
    (f : Fin n → ℝ[X]) {i j : Fin n} (hij : i ≤ j) (a b : ℝ) :
    weightedSum (List.ofFn fun h =>
        (leanderXOutputWeight i j a b h,
          leanderXOutputRegion f i j a b h)) =
      C a * (X * leanderTransform f i) + C b * leanderTransform f j := by
  rw [weightedSum_ofFn,
    C_mul_X_mul_leanderTransform_add_C_mul_leanderTransform f hij a b]
  apply Fintype.sum_congr
  intro h
  by_cases hhi : h < i
  · simp [leanderXOutputWeight, leanderXOutputRegion, hhi,
      leanderAffineFactor]
    ring
  · by_cases hEqI : h = i
    · subst h
      by_cases hijlt : i < j
      · simp [leanderXOutputWeight, leanderXOutputRegion, hijlt, hij]
        ring
      · have hEq : i = j := le_antisymm hij (le_of_not_gt hijlt)
        subst j
        simp [leanderXOutputWeight, leanderXOutputRegion]
    · have ih : i < h :=
        lt_of_le_of_ne (le_of_not_gt hhi) (Ne.symm hEqI)
      by_cases hhj : h < j
      · have hle : h ≤ j := hhj.le
        simp [leanderXOutputWeight, leanderXOutputRegion, hhi, hEqI, hhj,
          hle]
        ring
      · by_cases hEqJ : h = j
        · subst h
          have hijlt : i < j := ih
          simp [leanderXOutputWeight, leanderXOutputRegion, hhi, hEqI,
            hijlt]
          ring
        · have hnle : ¬h ≤ j := by
            intro hle
            exact hEqJ (le_antisymm hle (le_of_not_gt hhj))
          simp only [leanderXOutputWeight, hhi, hEqI, hhj, hEqJ, ite_false,
            leanderXOutputRegion, hnle, map_one, one_mul, leanderAffineFactor]
          ring

/-- Leander Theorem 2.3, condition (b'): an `X`-multiple of an earlier output
is compatible with a later output of the diagonal-omitting transform. -/
theorem compatible_X_mul_leanderTransform {n : ℕ} (f : Fin n → ℝ[X])
    (hrr : ∀ h, f h ≠ 0 ∧ (f h).Splits)
    (hpos : ∀ h, HasPosLeadingCoeff (f h))
    (hnn : ∀ h, HasNonnegCoeffs (f h))
    (hff : ∀ ⦃h k⦄, h < k → Compatible (f h) (f k))
    (hXf : ∀ ⦃h k⦄, h < k → Compatible (X * f h) (f k))
    {i j : Fin n} (hij : i ≤ j) :
    Compatible (X * leanderTransform f i) (leanderTransform f j) := by
  intro a b ha hb
  by_cases habzero : a = 0 ∧ b = 0
  · rcases habzero with ⟨rfl, rfl⟩
    simp
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha0 : a = 0
    · exact Or.inr fun hb0 => habzero ⟨ha0, hb0⟩
    · exact Or.inl ha0
  let region : Fin n → ℝ[X] := leanderXOutputRegion f i j a b
  let fs : List ℝ[X] := List.ofFn region
  have hregions_rr : ∀ p ∈ fs, p ≠ 0 ∧ p.Splits := by
    intro p hp
    simp only [fs, List.mem_ofFn] at hp
    rcases hp with ⟨h, rfl⟩
    exact leanderXOutputRegion_ne_zero_and_splits f i j hab hrr h
  have hregions_pos : ∀ p ∈ fs, HasPosLeadingCoeff p := by
    intro p hp
    simp only [fs, List.mem_ofFn] at hp
    rcases hp with ⟨h, rfl⟩
    exact leanderXOutputRegion_hasPosLeadingCoeff f i j ha hb hab hpos h
  have hregions_nn : ∀ p ∈ fs, HasNonnegCoeffs p := by
    intro p hp
    simp only [fs, List.mem_ofFn] at hp
    rcases hp with ⟨h, rfl⟩
    exact leanderXOutputRegion_hasNonnegCoeffs f i j ha hb hnn h
  have hregions_pair : PairwiseCompatible fs := by
    apply pairwiseCompatible_of_forall_mem
    intro p hp q hq
    simp only [fs, List.mem_ofFn] at hp hq
    rcases hp with ⟨h, rfl⟩
    rcases hq with ⟨k, rfl⟩
    rcases lt_trichotomy h k with hhk | heq | hkh
    · exact leanderXOutputRegion_compatible_of_lt f i j ha hb hrr hpos hnn
        hff hXf hhk
    · subst k
      exact Compatible.self_of_splits
        (leanderXOutputRegion_ne_zero_and_splits f i j hab hrr h).2
    · exact (leanderXOutputRegion_compatible_of_lt f i j ha hb hrr hpos hnn
        hff hXf hkh).comm
  have hfamily : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      hregions_rr hregions_pos hregions_nn).1 hregions_pair
  let ws : List (ℝ × ℝ[X]) := List.ofFn fun h =>
    (leanderXOutputWeight i j a b h, region h)
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_ofFn] at hap
    rcases hap with ⟨h, rfl⟩
    simp [fs]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_ofFn] at hap
    rcases hap with ⟨h, rfl⟩
    exact leanderXOutputWeight_nonneg i j ha hb h
  simpa [ws, region] using
    (weightedSum_leanderXOutputRegion f hij a b ▸ hfamily ws hmem hnonneg)

end RealRooted
