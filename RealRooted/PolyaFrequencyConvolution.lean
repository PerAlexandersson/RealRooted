import RealRooted.AissenSchoenbergWhitney

open Matrix

noncomputable section

namespace RealRooted

/-!
# Elementary Pólya-frequency convolutions

This file develops finite prefix-sum matrices from adjacent row additions.  It
uses them to certify the constant-one sequence and its first two elementary
convolution consequences.
-/

/-- Add row `k` to the following row. -/
def addPreviousRow {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (k : Fin N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  M.updateRow k.succ (M k.succ + M k.castSucc)

/-- Total nonnegativity is preserved by adding a row to the following row. -/
protected theorem Matrix.IsTotallyNonneg.addPreviousRow {N : ℕ}
    {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hM : M.IsTotallyNonneg)
    (k : Fin N) : (addPreviousRow M k).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  by_cases hk : ∃ i, rows i = k.succ
  · obtain ⟨i, hi⟩ := hk
    let S := M.submatrix rows cols
    let prev : Fin (N + 1) := k.castSucc
    have htarget_ne_prev : k.succ ≠ prev := by
      intro h
      have := congrArg Fin.val h
      simp [prev] at this
    have hsub : (addPreviousRow M k).submatrix rows cols =
        S.updateRow i (S i + fun j => M prev (cols j)) := by
      ext x j
      by_cases hxi : x = i
      · subst x
        simp [addPreviousRow, S, prev, hi]
      · have hrow_ne : rows x ≠ k.succ := by
          intro hx
          exact hxi (hrows.injective (hx.trans hi.symm))
        simp [addPreviousRow, S, prev, hxi, hrow_ne]
    rw [hsub, det_updateRow_add]
    have hfirst : (S.updateRow i (S i)).det = S.det := by
      rw [updateRow_eq_self]
    rw [hfirst]
    have hS : 0 ≤ S.det := hM hrows hcols
    by_cases hprev : ∃ l, rows l = prev
    · obtain ⟨l, hl⟩ := hprev
      have hli : l ≠ i := by
        intro h
        subst l
        exact htarget_ne_prev (hi.symm.trans hl)
      have hzero : (S.updateRow i (fun j => M prev (cols j))).det = 0 := by
        apply det_zero_of_row_eq hli
        funext j
        simp [S, hli, hl]
      rw [hzero]
      simpa using hS
    · let rows' : Fin n → Fin (N + 1) := Function.update rows i prev
      have hrows' : StrictMono rows' := by
        intro x y hxy
        by_cases hx : x = i
        · subst x
          have hy : y ≠ i := ne_of_gt hxy
          have hprev_target : prev < rows i := by
            rw [hi]
            exact k.castSucc_lt_succ
          simpa [rows', hy] using lt_trans hprev_target (hrows hxy)
        · by_cases hy : y = i
          · subst y
            have hxprev : rows x ≠ prev := fun h => hprev ⟨x, h⟩
            have hlt := hrows hxy
            simp only [rows', Function.update_of_ne hx]
            apply Fin.lt_def.mpr
            have hlt_val := Fin.lt_def.mp hlt
            have hi_val := congrArg Fin.val hi
            have hxprev_val : (rows x).val ≠ prev.val := fun h => hxprev (Fin.ext h)
            simp [prev] at hi_val hxprev_val ⊢
            lia
          · simpa [rows', hx, hy] using hrows hxy
      have hreplace : S.updateRow i (fun j => M prev (cols j)) =
          M.submatrix rows' cols := by
        ext x j
        by_cases hxi : x = i
        · subst x
          simp [S, rows', prev]
        · simp [S, rows', prev, hxi]
      rw [hreplace]
      exact add_nonneg hS (hM hrows' hcols)
  · have hsub : (addPreviousRow M k).submatrix rows cols = M.submatrix rows cols := by
      ext i j
      have hne : rows i ≠ k.succ := fun h => hk ⟨i, h⟩
      simp [addPreviousRow, hne]
    rw [hsub]
    exact hM hrows hcols

/-- After stage `s`, rows through `s` have been replaced by their prefix sums. -/
def prefixRowStage {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (s : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  .of fun i j =>
    if i.val ≤ s then
      ∑ k ∈ Finset.Iic i, M k j
    else
      M i j

@[simp]
lemma prefixRowStage_zero {N : ℕ}
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    prefixRowStage M 0 = M := by
  ext i j
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    subst i
    have hIic : Finset.Iic (0 : Fin (N + 1)) = {0} := by
      ext k
      constructor
      · intro hk
        have hk0 := Finset.mem_Iic.mp hk
        exact Finset.mem_singleton.mpr (le_antisymm hk0 (Fin.zero_le k))
      · intro hk
        rw [Finset.mem_singleton.mp hk]
        exact Finset.mem_Iic.mpr le_rfl
    simp only [prefixRowStage, Matrix.of_apply, Fin.val_zero, le_refl, if_pos]
    rw [hIic]
    simp
  · have hi0 : ¬i.val ≤ 0 := Nat.not_le_of_lt (Nat.pos_of_ne_zero hi)
    simp only [prefixRowStage, Matrix.of_apply, if_neg hi0]

lemma prefixRowStage_succ {N s : ℕ} (hs : s < N)
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    prefixRowStage M (s + 1) =
      addPreviousRow (prefixRowStage M s) ⟨s, hs⟩ := by
  ext i j
  let target : Fin (N + 1) := Fin.succ ⟨s, hs⟩
  by_cases hi : i = target
  · subst i
    have hIic : Finset.Iic target = insert target (Finset.Iic ⟨s, by lia⟩) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro hk
        by_cases hkt : k = target
        · exact Or.inl hkt
        · right
          apply Fin.le_def.mpr
          have hkval := Fin.le_def.mp hk
          simp [target] at hkval
          have hkne : k.val ≠ s + 1 := fun h => hkt (Fin.ext (by simpa [target] using h))
          lia
      · rintro (rfl | hk)
        · exact le_rfl
        · apply Fin.le_def.mpr
          have hkval := Fin.le_def.mp hk
          simp [target] at hkval ⊢
          lia
    simp only [addPreviousRow]
    simp only [prefixRowStage, Matrix.of_apply]
    rw [if_pos (by simp [target]), updateRow_self]
    simp only [Pi.add_apply]
    simp only [Matrix.of_apply]
    rw [if_neg (by simp), if_pos (by simp)]
    change (∑ k ∈ Finset.Iic target, M k j) =
      M target j + ∑ k ∈ Finset.Iic ⟨s, by lia⟩, M k j
    rw [hIic, Finset.sum_insert]
    simp [target]
  · have hupdate : i ≠ Fin.succ ⟨s, hs⟩ := hi
    simp only [addPreviousRow, updateRow_ne hupdate, prefixRowStage, Matrix.of_apply]
    by_cases his : i.val ≤ s
    · rw [if_pos his, if_pos (le_trans his (Nat.le_succ s))]
    · have his' : ¬i.val ≤ s + 1 := by
        intro h
        have hieq : i.val = s + 1 := by lia
        exact hi (Fin.ext (by simpa [target] using hieq))
      rw [if_neg his, if_neg his']

/-- A finite matrix stays totally nonnegative after any bounded prefix-row stage. -/
theorem prefixRowStage_isTotallyNonneg {N s : ℕ} (hs : s ≤ N)
    {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hM : M.IsTotallyNonneg) :
    (prefixRowStage M s).IsTotallyNonneg := by
  induction s with
  | zero => simpa using hM
  | succ s ih =>
      rw [prefixRowStage_succ (Nat.lt_of_succ_le hs)]
      exact Matrix.IsTotallyNonneg.addPreviousRow (ih (Nat.le_of_succ_le hs))
        ⟨s, Nat.lt_of_succ_le hs⟩

/-- Total nonnegativity can be checked on compatible finite truncations. -/
theorem isTotallyNonneg_of_fin_truncations (M : Matrix ℕ ℕ ℝ)
    (Mfin : (N : ℕ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hentry : ∀ (N : ℕ) (i j : Fin (N + 1)), Mfin N i j = M i.val j.val)
    (hfin : ∀ N, (Mfin N).IsTotallyNonneg) : M.IsTotallyNonneg := by
  intro n rows cols hrows hcols
  cases n with
  | zero => simp
  | succ n =>
      let B := max (rows (Fin.last n)) (cols (Fin.last n))
      let rows' : Fin (n + 1) → Fin (B + 1) := fun i =>
        ⟨rows i, Nat.lt_succ_of_le <|
          le_trans (hrows.monotone (Fin.le_last i)) (le_max_left _ _)⟩
      let cols' : Fin (n + 1) → Fin (B + 1) := fun i =>
        ⟨cols i, Nat.lt_succ_of_le <|
          le_trans (hcols.monotone (Fin.le_last i)) (le_max_right _ _)⟩
      have hrows' : StrictMono rows' := by
        intro i j hij
        exact Fin.lt_def.mpr (hrows hij)
      have hcols' : StrictMono cols' := by
        intro i j hij
        exact Fin.lt_def.mpr (hcols hij)
      have hminor : M.submatrix rows cols = (Mfin B).submatrix rows' cols' := by
        ext i j
        symm
        exact hentry B (rows' i) (cols' j)
      rw [hminor]
      exact hfin B hrows' hcols'

/-- The finite lower-triangular matrix whose nonzero entries are all one. -/
def lowerOnesFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  .of fun i j => if j ≤ i then 1 else 0

lemma finIdentity_isTotallyNonneg (N : ℕ) :
    (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).IsTotallyNonneg := by
  have h := Matrix.IsTotallyNonneg.submatrix
    (Matrix.IsTotallyNonneg.one : (1 : Matrix ℕ ℕ ℝ).IsTotallyNonneg)
    (f := fun i : Fin (N + 1) => i.val) (g := fun i : Fin (N + 1) => i.val)
    Fin.val_strictMono Fin.val_strictMono
  convert h using 1
  ext i j
  simp only [submatrix_apply, one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : i.val ≠ j.val := fun hv => hij (Fin.ext hv)
    simp [hij, hval]

lemma prefixRowStage_identity (N : ℕ) :
    prefixRowStage (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) N = lowerOnesFin N := by
  ext i j
  have hiN : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  simp only [prefixRowStage, Matrix.of_apply, if_pos hiN, lowerOnesFin, Matrix.one_apply]
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    have hfilter : {k ∈ Finset.Iic i | k = j} = {j} := by
      ext k
      constructor
      · intro hk
        exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hk).2
      · intro hk
        have hkj := Finset.mem_singleton.mp hk
        subst k
        exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hji, rfl⟩
    rw [Finset.sum_boole, hfilter]
    simp
  · rw [if_neg hji]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [ite_eq_right_iff]
    intro hkj
    subst k
    exact (hji (Finset.mem_Iic.mp hk)).elim

/-- Every finite lower-triangular constant-one matrix is totally nonnegative. -/
theorem lowerOnesFin_isTotallyNonneg (N : ℕ) :
    (lowerOnesFin N).IsTotallyNonneg := by
  rw [← prefixRowStage_identity N]
  exact prefixRowStage_isTotallyNonneg (le_refl N) (finIdentity_isTotallyNonneg N)

/-- The finite lower-triangular matrix with entry `i - j + 1` below the diagonal. -/
def lowerLinearFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  prefixRowStage (lowerOnesFin N) N

theorem lowerLinearFin_isTotallyNonneg (N : ℕ) :
    (lowerLinearFin N).IsTotallyNonneg :=
  prefixRowStage_isTotallyNonneg (le_refl N) (lowerOnesFin_isTotallyNonneg N)

lemma lowerLinearFin_apply (N : ℕ) (i j : Fin (N + 1)) :
    lowerLinearFin N i j = if j ≤ i then (i.val - j.val + 1 : ℕ) else 0 := by
  have hiN : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  simp only [lowerLinearFin, prefixRowStage, Matrix.of_apply, if_pos hiN, lowerOnesFin]
  rw [Finset.sum_boole]
  have hfilter : {k ∈ Finset.Iic i | j ≤ k} = Finset.Icc j i := by
    ext k
    simp [and_comm]
  rw [hfilter, Fin.card_Icc]
  by_cases hji : j ≤ i
  · rw [if_pos hji]
    norm_cast
    have hval := Fin.le_def.mp hji
    lia
  · rw [if_neg hji]
    have hlt : i.val + 1 ≤ j.val := by
      have := Fin.lt_def.mp (lt_of_not_ge hji)
      lia
    norm_num
    exact Nat.sub_eq_zero_of_le hlt

/-- The sequence constantly equal to one is Pólya-frequency. -/
theorem constantOne_isPolyaFreqSeq :
    IsPolyaFreqSeq (fun _ : ℕ => (1 : ℝ)) := by
  rw [IsPolyaFreqSeq]
  exact isTotallyNonneg_of_fin_truncations _ lowerOnesFin
    (by intro N i j; simp [lowerOnesFin, toeplitz]) lowerOnesFin_isTotallyNonneg

/-- The sequence `1, 2, 3, ...` is Pólya-frequency. -/
theorem natSucc_isPolyaFreqSeq :
    IsPolyaFreqSeq (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
  rw [IsPolyaFreqSeq]
  refine isTotallyNonneg_of_fin_truncations _ lowerLinearFin ?_
    lowerLinearFin_isTotallyNonneg
  intro N i j
  rw [lowerLinearFin_apply, toeplitz_apply]
  by_cases hji : j ≤ i
  · rw [if_pos hji, if_pos (Fin.le_def.mp hji)]
  · rw [if_neg hji, if_neg (fun h => hji (Fin.le_def.mpr h))]
    norm_num

/-- Finite truncation of the bidiagonal matrix with both diagonals equal to one. -/
def bidiagonalOneFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (bidiagonal 1).submatrix (fun i => i.val) (fun j => j.val)

theorem bidiagonalOneFin_isTotallyNonneg (N : ℕ) :
    (bidiagonalOneFin N).IsTotallyNonneg := by
  exact Matrix.IsTotallyNonneg.submatrix
    (bidiagonal_isTotallyNonneg 1 (by norm_num)) Fin.val_strictMono Fin.val_strictMono

/-- Finite lower-triangular matrix with diagonal one and all lower entries two. -/
def lowerOneThenTwoFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  prefixRowStage (bidiagonalOneFin N) N

theorem lowerOneThenTwoFin_isTotallyNonneg (N : ℕ) :
    (lowerOneThenTwoFin N).IsTotallyNonneg :=
  prefixRowStage_isTotallyNonneg (le_refl N) (bidiagonalOneFin_isTotallyNonneg N)

lemma lowerOneThenTwoFin_apply (N : ℕ) (i j : Fin (N + 1)) :
    lowerOneThenTwoFin N i j =
      if j.val = i.val then 1 else if j.val < i.val then 2 else 0 := by
  have hiN : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  simp only [lowerOneThenTwoFin, prefixRowStage, Matrix.of_apply, if_pos hiN,
    bidiagonalOneFin, submatrix_apply, bidiagonal_apply]
  rcases Nat.lt_trichotomy j.val i.val with hji | hji | hji
  · rw [if_neg hji.ne, if_pos hji]
    let js : Fin (N + 1) := ⟨j.val + 1, by lia⟩
    have hjmem : j ∈ Finset.Iic i := Finset.mem_Iic.mpr (Fin.le_def.mpr hji.le)
    have hjsmem : js ∈ Finset.Iic i := Finset.mem_Iic.mpr (Fin.le_def.mpr (by
      dsimp only [js]
      lia))
    have hterm (k : Fin (N + 1)) :
        (if k.val = j.val then (1 : ℝ) else if k.val = j.val + 1 then 1 else 0) =
          (if k = j then 1 else 0) + (if k = js then 1 else 0) := by
      by_cases hkj : k = j
      · subst k
        have hjne : j ≠ js := by
          intro h
          have := congrArg Fin.val h
          simp [js] at this
        norm_num [js, hjne]
      · have hvalj : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        by_cases hkjs : k = js
        · subst k
          norm_num [js, hkj]
        · have hvaljs : k.val ≠ j.val + 1 :=
            fun h => hkjs (Fin.ext (by simpa [js] using h))
          simp [hkj, hkjs, hvalj, hvaljs]
    simp_rw [hterm, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
    norm_num [hjmem, hjsmem]
  · rw [hji, if_pos rfl]
    have hs := Finset.sum_eq_single i
      (s := Finset.Iic i)
      (f := fun k : Fin (N + 1) =>
        if k.val = i.val then (1 : ℝ) else if k.val = i.val + 1 then 1 else 0)
      (by
        intro k hk hki
        rw [if_neg (fun h => hki (Fin.ext h))]
        rw [if_neg (by
          intro h
          have hki' := Fin.le_def.mp (Finset.mem_Iic.mp hk)
          lia)])
      (by simp)
    simpa using hs
  · rw [if_neg hji.ne', if_neg (not_lt_of_ge hji.le)]
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k.val ≤ i.val := Fin.le_def.mp (Finset.mem_Iic.mp hk)
    rw [if_neg (by lia), if_neg (by lia)]

/-- The sequence `1, 2, 2, ...` is Pólya-frequency. -/
theorem oneThenTwo_isPolyaFreqSeq :
    IsPolyaFreqSeq (fun n : ℕ => if n = 0 then (1 : ℝ) else 2) := by
  rw [IsPolyaFreqSeq]
  refine isTotallyNonneg_of_fin_truncations _ lowerOneThenTwoFin ?_
    lowerOneThenTwoFin_isTotallyNonneg
  intro N i j
  rw [lowerOneThenTwoFin_apply, toeplitz_apply]
  rcases Nat.lt_trichotomy j.val i.val with hji | hji | hji
  · rw [if_neg hji.ne, if_pos hji, if_pos hji.le,
      if_neg (by lia)]
  · simp [hji]
  · have hnle : ¬j.val ≤ i.val := Nat.not_le_of_lt hji
    rw [if_neg hji.ne', if_neg (not_lt_of_ge hji.le), if_neg hnle]

end RealRooted
