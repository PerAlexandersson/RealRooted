import RealRooted.OperatorMatrix.OneThetaX

/-!
# Two-letter boards over `{1, θ}` and `{θ, X}`

For matrices with at least two rows and columns:

* over `{1, θ}`, ordered PF vectors are preserved exactly when the `1` entries form an upper-right
  rectangle, possibly empty (`preservesOrderedPF_one_theta_iff_upperRightRectangle`);
* over `{θ, X}`, exactly when either all rows are equal (`X` columns, then `θ` columns) or all
  columns are equal (`θ` rows, then `X` rows)
  (`preservesOrderedPF_theta_x_iff_rowCut_or_columnCut`).
-/

noncomputable section

namespace RealRooted.OperatorMatrix

/-- Every entry of a letter matrix belongs to the alphabet `{1, θ}`. -/
def IsOneThetaMatrix {m n : ℕ} (L : Fin m → Fin n → Letter) : Prop :=
  ∀ i j, L i j = .one ∨ L i j = .theta

/-- The `1` entries of a letter matrix form an upper-right rectangle.
The natural cut parameters permit an empty rectangle. -/
def OnesFormUpperRightRectangle {m n : ℕ} (L : Fin m → Fin n → Letter) : Prop :=
  ∃ r, r ≤ m ∧ ∃ c, c ≤ n ∧
    ∀ i j, L i j = .one ↔ i.1 < r ∧ c ≤ j.1

private theorem exists_fin_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : ∃ k : Fin n, k ≠ i :=
  haveI := Fin.nontrivial_iff_two_le.mpr hn
  exists_ne i

private theorem allowed_one_theta_top_right_one
    {a b c d : Letter}
    (ha : a = .one ∨ a = .theta) (hb : b = .one ∨ b = .theta)
    (hc : c = .one ∨ c = .theta) (hd : d = .one ∨ d = .theta)
    (hallowed : a.IsAllowedBlock b c d) (hatop : a = .one) :
    b = .one := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_one_theta_bottom_right_one
    {a b c d : Letter}
    (ha : a = .one ∨ a = .theta) (hb : b = .one ∨ b = .theta)
    (hc : c = .one ∨ c = .theta) (hd : d = .one ∨ d = .theta)
    (hallowed : a.IsAllowedBlock b c d) (hcbottom : c = .one) :
    d = .one := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_one_theta_top_right_of_bottom_right
    {a b c d : Letter}
    (ha : a = .one ∨ a = .theta) (hb : b = .one ∨ b = .theta)
    (hc : c = .one ∨ c = .theta) (hd : d = .one ∨ d = .theta)
    (hallowed : a.IsAllowedBlock b c d) (hdbottom : d = .one) :
    b = .one := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_one_theta_top_left_one
    {a b c d : Letter}
    (ha : a = .one ∨ a = .theta) (hb : b = .one ∨ b = .theta)
    (hc : c = .one ∨ c = .theta) (hd : d = .one ∨ d = .theta)
    (hallowed : a.IsAllowedBlock b c d) (hcbottom : c = .one) :
    a = .one := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_one_theta_bottom_left_one
    {a b c d : Letter}
    (ha : a = .one ∨ a = .theta) (hb : b = .one ∨ b = .theta)
    (hc : c = .one ∨ c = .theta) (hd : d = .one ∨ d = .theta)
    (hallowed : a.IsAllowedBlock b c d) (hatop : a = .one)
    (hdbottom : d = .one) :
    c = .one := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem one_right_of_allowed_blocks {m n : ℕ}
    (L : Fin m → Fin n → Letter) (hm : 2 ≤ m)
    (halpha : IsOneThetaMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    (i : Fin m) {j l : Fin n} (hjl : j < l) (hij : L i j = .one) :
    L i l = .one := by
  obtain ⟨k, hki⟩ := exists_fin_ne hm i
  rcases lt_or_gt_of_ne hki with hki | hik
  · exact allowed_one_theta_bottom_right_one
      (halpha k j) (halpha k l) (halpha i j) (halpha i l)
      (hblocks k i j l hki hjl) hij
  · exact allowed_one_theta_top_right_one
      (halpha i j) (halpha i l) (halpha k j) (halpha k l)
      (hblocks i k j l hik hjl) hij

private theorem one_above_of_allowed_blocks {m n : ℕ}
    (L : Fin m → Fin n → Letter) (halpha : IsOneThetaMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    {i k : Fin m} (hik : i < k) (j : Fin n) (hkj : L k j = .one)
    (l : Fin n) (hjl : j < l) :
    L i j = .one := by
  exact allowed_one_theta_top_left_one
    (halpha i j) (halpha i l) (halpha k j) (halpha k l)
    (hblocks i k j l hik hjl) hkj

private theorem bottom_left_one_of_allowed_blocks {m n : ℕ}
    (L : Fin m → Fin n → Letter) (halpha : IsOneThetaMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    {i k : Fin m} {j l : Fin n} (hik : i < k) (hjl : j < l)
    (hij : L i j = .one) (hkl : L k l = .one) :
    L k j = .one := by
  exact allowed_one_theta_bottom_left_one
    (halpha i j) (halpha i l) (halpha k j) (halpha k l)
    (hblocks i k j l hik hjl) hij hkl

/-- For matrices with at least two rows and columns over `{1, θ}`, ordered-PF
preservation is equivalent to the `1` entries forming an upper-right rectangle. -/
theorem preservesOrderedPF_one_theta_iff_upperRightRectangle
    {m n : ℕ} (L : Fin m → Fin n → Letter)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (halpha : IsOneThetaMatrix L) :
    PreservesOrderedPF (fun i j ↦ (L i j).linearMap) ↔
      OnesFormUpperRightRectangle L := by
  classical
  rw [preservesOrderedPF_letters_iff L hm hn]
  constructor
  · intro hblocks
    by_cases hone : ∃ i j, L i j = .one
    · obtain ⟨i₀, j₀, hi₀j₀⟩ := hone
      let rows : Finset (Fin m) :=
        Finset.univ.filter fun i ↦ ∃ j, L i j = .one
      have hrows : rows.Nonempty := by
        refine ⟨i₀, ?_⟩
        simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j₀, hi₀j₀⟩
      let a : Fin m := rows.max' hrows
      have ha_rows : a ∈ rows := Finset.max'_mem rows hrows
      obtain ⟨jₐ, hajₐ⟩ : ∃ j, L a j = .one := by
        simpa only [rows, Finset.mem_filter, Finset.mem_univ, true_and] using ha_rows
      let cols : Finset (Fin n) :=
        Finset.univ.filter fun j ↦ L a j = .one
      have hcols : cols.Nonempty := by
        refine ⟨jₐ, ?_⟩
        simpa only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
      let c : Fin n := cols.min' hcols
      have hc_cols : c ∈ cols := Finset.min'_mem cols hcols
      have hac : L a c = .one := by
        simpa only [cols, Finset.mem_filter, Finset.mem_univ, true_and] using hc_cols
      refine ⟨a.1 + 1, by lia, c.1, c.2.le, ?_⟩
      intro i j
      constructor
      · intro hij
        have hi_rows : i ∈ rows := by
          simp only [rows, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hij⟩
        have hia : i ≤ a := Finset.le_max' rows i hi_rows
        have hcj : c ≤ j := by
          by_contra hnot
          have hjc : j < c := lt_of_not_ge hnot
          have hia_ne : i ≠ a := by
            intro hieq
            subst i
            exact (not_le_of_gt hjc) (Finset.min'_le cols j (by
              simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hij))
          have hia_lt : i < a := lt_of_le_of_ne hia hia_ne
          have haj : L a j = .one :=
            bottom_left_one_of_allowed_blocks L halpha hblocks hia_lt hjc hij hac
          exact (not_le_of_gt hjc) (Finset.min'_le cols j (by
            simp only [cols, Finset.mem_filter, Finset.mem_univ, true_and]
            exact haj))
        exact ⟨by simpa using hia, by simpa using hcj⟩
      · rintro ⟨hia, hcj⟩
        have hia' : i ≤ a := by simpa using (Nat.le_of_lt_succ hia)
        have hic : L i c = .one := by
          rcases hia'.eq_or_lt with rfl | hia_lt
          · exact hac
          · obtain ⟨l, hcl⟩ := exists_fin_ne hn c
            rcases lt_or_gt_of_ne hcl with hlc | hcl
            · exact allowed_one_theta_top_right_of_bottom_right
                (halpha i l) (halpha i c) (halpha a l) (halpha a c)
                (hblocks i a l c hia_lt hlc) hac
            · exact one_above_of_allowed_blocks L halpha hblocks hia_lt c hac l hcl
        rcases hcj.eq_or_lt with hcj_eq | hcj_lt
        · have hc_eq_j : c = j := Fin.ext hcj_eq
          simpa only [hc_eq_j] using hic
        · have hc_lt_j : c < j := by simpa using hcj_lt
          exact one_right_of_allowed_blocks L hm halpha hblocks i hc_lt_j hic
    · refine ⟨0, Nat.zero_le m, 0, Nat.zero_le n, ?_⟩
      intro i j
      constructor
      · intro hij
        exact (hone ⟨i, j, hij⟩).elim
      · intro hfalse
        exact (Nat.not_lt_zero i.1 hfalse.1).elim
  · rintro ⟨r, hr, c, hc, hrect⟩
    intro i k j l hik hjl
    have hij := hrect i j
    have hil := hrect i l
    have hkj := hrect k j
    have hkl := hrect k l
    have ha_alpha := halpha i j
    have hb_alpha := halpha i l
    have hc_alpha := halpha k j
    have hd_alpha := halpha k l
    clear hrect halpha
    rcases ha_alpha with ha | ha <;> rcases hb_alpha with hb | hb <;>
      rcases hc_alpha with hcc | hcc <;> rcases hd_alpha with hd | hd <;>
      simp only [ha, hb, hcc, hd, Letter.IsAllowedBlock] <;> grind

/-- Every entry of a letter matrix belongs to the alphabet `{θ, X}`. -/
def IsThetaXMatrix {m n : ℕ} (L : Fin m → Fin n → Letter) : Prop :=
  ∀ i j, L i j = .theta ∨ L i j = .x

/-- All rows are identical, with `X` columns followed by `θ` columns. -/
def XsFormLeftColumns {m n : ℕ} (L : Fin m → Fin n → Letter) : Prop :=
  ∃ c, c ≤ n ∧ ∀ i j, L i j = .x ↔ j.1 < c

/-- All columns are identical, with `θ` rows followed by `X` rows. -/
def XsFormBottomRows {m n : ℕ} (L : Fin m → Fin n → Letter) : Prop :=
  ∃ r, r ≤ m ∧ ∀ i j, L i j = .x ↔ r ≤ i.1

private theorem allowed_theta_x_top_left_x_of_top_right_x
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hbtop : b = .x) :
    a = .x := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_theta_x_bottom_left_x_of_bottom_right_x
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hdbottom : d = .x) :
    c = .x := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_theta_x_bottom_left_x_of_top_left_x
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hatop : a = .x) :
    c = .x := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_theta_x_bottom_right_x_of_top_right_x
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hbtop : b = .x) :
    d = .x := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_theta_x_bottom_of_top_mixed
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hatop : a = .x) (hbtop : b = .theta) :
    c = .x ∧ d = .theta := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_theta_x_top_of_bottom_mixed
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hcbottom : c = .x)
    (hdbottom : d = .theta) :
    a = .x ∧ b = .theta := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem allowed_theta_x_right_eq_of_left_x
    {a b c d : Letter}
    (ha : a = .theta ∨ a = .x) (hb : b = .theta ∨ b = .x)
    (hc : c = .theta ∨ c = .x) (hd : d = .theta ∨ d = .x)
    (hallowed : a.IsAllowedBlock b c d) (hatop : a = .x) (hcbottom : c = .x) :
    b = d := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    simp_all [Letter.IsAllowedBlock]

private theorem x_left_of_allowed_blocks {m n : ℕ}
    (L : Fin m → Fin n → Letter) (hm : 2 ≤ m)
    (halpha : IsThetaXMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    (i : Fin m) {j l : Fin n} (hjl : j < l) (hil : L i l = .x) :
    L i j = .x := by
  obtain ⟨k, hki⟩ := exists_fin_ne hm i
  rcases lt_or_gt_of_ne hki with hki | hik
  · exact allowed_theta_x_bottom_left_x_of_bottom_right_x
      (halpha k j) (halpha k l) (halpha i j) (halpha i l)
      (hblocks k i j l hki hjl) hil
  · exact allowed_theta_x_top_left_x_of_top_right_x
      (halpha i j) (halpha i l) (halpha k j) (halpha k l)
      (hblocks i k j l hik hjl) hil

private theorem theta_right_of_allowed_blocks {m n : ℕ}
    (L : Fin m → Fin n → Letter) (hm : 2 ≤ m)
    (halpha : IsThetaXMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    (i : Fin m) {j l : Fin n} (hjl : j < l) (hij : L i j = .theta) :
    L i l = .theta := by
  rcases halpha i l with hil | hil
  · exact hil
  · exact Letter.noConfusion
      (hij.symm.trans (x_left_of_allowed_blocks L hm halpha hblocks i hjl hil))

private theorem x_below_of_allowed_blocks {m n : ℕ}
    (L : Fin m → Fin n → Letter) (hn : 2 ≤ n)
    (halpha : IsThetaXMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    {i k : Fin m} (hik : i < k) (j : Fin n) (hij : L i j = .x) :
    L k j = .x := by
  obtain ⟨l, hlj⟩ := exists_fin_ne hn j
  rcases lt_or_gt_of_ne hlj with hlj | hjl
  · exact allowed_theta_x_bottom_right_x_of_top_right_x
      (halpha i l) (halpha i j) (halpha k l) (halpha k j)
      (hblocks i k l j hik hlj) hij
  · exact allowed_theta_x_bottom_left_x_of_top_left_x
      (halpha i j) (halpha i l) (halpha k j) (halpha k l)
      (hblocks i k j l hik hjl) hij

private theorem exists_x_prefix_cut {n : ℕ} (f : Fin n → Letter)
    (halpha : ∀ j, f j = .theta ∨ f j = .x)
    (hxleft : ∀ {j l}, j < l → f l = .x → f j = .x) :
    ∃ c, c ≤ n ∧ ∀ j, f j = .x ↔ j.1 < c := by
  classical
  let thetaCols : Finset (Fin n) := Finset.univ.filter fun j ↦ f j = .theta
  by_cases hempty : thetaCols = ∅
  · refine ⟨n, le_rfl, fun j ↦ ⟨fun _ ↦ j.2, fun _ ↦ ?_⟩⟩
    rcases halpha j with hj | hj
    · have hjmem : j ∈ thetaCols := by
        simpa only [thetaCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hempty] at hjmem
      simp at hjmem
    · exact hj
  · have hnonempty : thetaCols.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let c : Fin n := thetaCols.min' hnonempty
    have hc_mem : c ∈ thetaCols := Finset.min'_mem thetaCols hnonempty
    have hc_theta : f c = .theta := by
      simpa only [thetaCols, Finset.mem_filter, Finset.mem_univ, true_and] using hc_mem
    refine ⟨c.1, c.2.le, fun j ↦ ⟨?_, ?_⟩⟩
    · intro hjx
      by_contra hnot
      have hcj : c ≤ j := by simpa using Nat.le_of_not_gt hnot
      rcases hcj.eq_or_lt with hcj_eq | hcj_lt
      · subst j
        exact Letter.noConfusion (hc_theta.symm.trans hjx)
      · exact Letter.noConfusion (hc_theta.symm.trans (hxleft hcj_lt hjx))
    · intro hjc
      rcases halpha j with hj | hj
      · have hcj : c ≤ j := Finset.min'_le thetaCols j (by
          simpa only [thetaCols, Finset.mem_filter, Finset.mem_univ, true_and])
        exact False.elim ((not_le_of_gt (by simpa using hjc)) hcj)
      · exact hj

private theorem exists_x_suffix_cut {m : ℕ} (f : Fin m → Letter)
    (hxbelow : ∀ {i k}, i < k → f i = .x → f k = .x) :
    ∃ r, r ≤ m ∧ ∀ i, f i = .x ↔ r ≤ i.1 := by
  classical
  let xRows : Finset (Fin m) := Finset.univ.filter fun i ↦ f i = .x
  by_cases hempty : xRows = ∅
  · refine ⟨m, le_rfl, fun i ↦ ⟨?_, ?_⟩⟩
    · intro hix
      have himem : i ∈ xRows := by
        simpa only [xRows, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hempty] at himem
      simp at himem
    · intro him
      exact False.elim ((not_le_of_gt i.2) him)
  · have hnonempty : xRows.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let r : Fin m := xRows.min' hnonempty
    have hr_mem : r ∈ xRows := Finset.min'_mem xRows hnonempty
    have hr_x : f r = .x := by
      simpa only [xRows, Finset.mem_filter, Finset.mem_univ, true_and] using hr_mem
    refine ⟨r.1, r.2.le, fun i ↦ ⟨?_, ?_⟩⟩
    · intro hix
      simpa using Finset.min'_le xRows i (by
        simpa only [xRows, Finset.mem_filter, Finset.mem_univ, true_and])
    · intro hri
      have hri' : r ≤ i := by simpa using hri
      rcases hri'.eq_or_lt with rfl | hri_lt
      · exact hr_x
      · exact hxbelow hri_lt hr_x

private theorem row_eq_of_mixed_row {m n : ℕ}
    (L : Fin m → Fin n → Letter) (hm : 2 ≤ m)
    (halpha : IsThetaXMatrix L)
    (hblocks : ∀ i k j l, i < k → j < l →
      (L i j).IsAllowedBlock (L i l) (L k j) (L k l))
    {a : Fin m} {u v : Fin n} (huv : u < v)
    (hau : L a u = .x) (hav : L a v = .theta) (i : Fin m) (j : Fin n) :
    L i j = L a j := by
  by_cases hia : i = a
  · subst i
    rfl
  rcases lt_or_gt_of_ne hia with hia | hai
  · have hmixed := allowed_theta_x_top_of_bottom_mixed
      (halpha i u) (halpha i v) (halpha a u) (halpha a v)
      (hblocks i a u v hia huv) hau hav
    have hiu : L i u = .x := hmixed.1
    have hiv : L i v = .theta := hmixed.2
    rcases le_total j u with hju | huj
    · rcases hju.eq_or_lt with rfl | hju_lt
      · exact hiu.trans hau.symm
      · exact (x_left_of_allowed_blocks L hm halpha hblocks i hju_lt hiu).trans
          (x_left_of_allowed_blocks L hm halpha hblocks a hju_lt hau).symm
    · rcases le_total v j with hvj | hjv
      · rcases hvj.eq_or_lt with rfl | hvj_lt
        · exact hiv.trans hav.symm
        · exact (theta_right_of_allowed_blocks L hm halpha hblocks i hvj_lt hiv).trans
            (theta_right_of_allowed_blocks L hm halpha hblocks a hvj_lt hav).symm
      · rcases huj.eq_or_lt with huj_eq | huj_lt
        · subst j
          exact hiu.trans hau.symm
        · exact allowed_theta_x_right_eq_of_left_x
            (halpha i u) (halpha i j) (halpha a u) (halpha a j)
            (hblocks i a u j hia huj_lt) hiu hau
  · have hmixed := allowed_theta_x_bottom_of_top_mixed
      (halpha a u) (halpha a v) (halpha i u) (halpha i v)
      (hblocks a i u v hai huv) hau hav
    have hiu : L i u = .x := hmixed.1
    have hiv : L i v = .theta := hmixed.2
    rcases le_total j u with hju | huj
    · rcases hju.eq_or_lt with rfl | hju_lt
      · exact hiu.trans hau.symm
      · exact (x_left_of_allowed_blocks L hm halpha hblocks i hju_lt hiu).trans
          (x_left_of_allowed_blocks L hm halpha hblocks a hju_lt hau).symm
    · rcases le_total v j with hvj | hjv
      · rcases hvj.eq_or_lt with rfl | hvj_lt
        · exact hiv.trans hav.symm
        · exact (theta_right_of_allowed_blocks L hm halpha hblocks i hvj_lt hiv).trans
            (theta_right_of_allowed_blocks L hm halpha hblocks a hvj_lt hav).symm
      · rcases huj.eq_or_lt with huj_eq | huj_lt
        · subst j
          exact hiu.trans hau.symm
        · exact (allowed_theta_x_right_eq_of_left_x
            (halpha a u) (halpha a j) (halpha i u) (halpha i j)
            (hblocks a i u j hai huj_lt) hau hiu).symm

/-- For matrices with at least two rows and columns over `{θ, X}`, ordered-PF
preservation is equivalent to having either identical threshold rows or
identical threshold columns. -/
theorem preservesOrderedPF_theta_x_iff_rowCut_or_columnCut
    {m n : ℕ} (L : Fin m → Fin n → Letter)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (halpha : IsThetaXMatrix L) :
    PreservesOrderedPF (fun i j ↦ (L i j).linearMap) ↔
      XsFormLeftColumns L ∨ XsFormBottomRows L := by
  classical
  rw [preservesOrderedPF_letters_iff L hm hn]
  constructor
  · intro hblocks
    have hxleft : ∀ i, ∀ {j l : Fin n}, j < l → L i l = .x → L i j = .x :=
      fun i j l hjl ↦ x_left_of_allowed_blocks L hm halpha hblocks i hjl
    have hxbelow : ∀ j, ∀ {i k : Fin m}, i < k → L i j = .x → L k j = .x :=
      fun j i k hik ↦ x_below_of_allowed_blocks L hn halpha hblocks hik j
    by_cases hmixed : ∃ a u v, u < v ∧ L a u = .x ∧ L a v = .theta
    · obtain ⟨a, u, v, huv, hau, hav⟩ := hmixed
      obtain ⟨c, hc, hcut⟩ := exists_x_prefix_cut (L a) (halpha a) (hxleft a)
      left
      refine ⟨c, hc, fun i j ↦ ?_⟩
      rw [row_eq_of_mixed_row L hm halpha hblocks huv hau hav i j]
      exact hcut j
    · let z : Fin n := ⟨0, by lia⟩
      have hrowConstant : ∀ i j, L i j = L i z := by
        intro i j
        by_cases hjz : j = z
        · subst j
          rfl
        have hzj : z < j := by
          apply Fin.mk_lt_mk.mpr
          exact Nat.pos_of_ne_zero fun hj0 ↦ hjz (Fin.ext hj0)
        rcases halpha i z with hiz | hiz
        · rcases halpha i j with hij | hij
          · exact hij.trans hiz.symm
          · exact Letter.noConfusion (hiz.symm.trans (hxleft i hzj hij))
        · rcases halpha i j with hij | hij
          · exact (hmixed ⟨i, z, j, hzj, hiz, hij⟩).elim
          · exact hij.trans hiz.symm
      obtain ⟨r, hr, hcut⟩ := exists_x_suffix_cut (fun i ↦ L i z)
        (fun hik hix ↦ hxbelow z hik hix)
      right
      refine ⟨r, hr, fun i j ↦ ?_⟩
      rw [hrowConstant i j]
      exact hcut i
  · rintro (hcolumns | hrows)
    · obtain ⟨c, hc, hcut⟩ := hcolumns
      intro i k j l hik hjl
      have hij := hcut i j
      have hil := hcut i l
      have hkj := hcut k j
      have hkl := hcut k l
      have ha_alpha := halpha i j
      have hb_alpha := halpha i l
      have hc_alpha := halpha k j
      have hd_alpha := halpha k l
      clear hcut halpha
      rcases ha_alpha with ha | ha <;> rcases hb_alpha with hb | hb <;>
        rcases hc_alpha with hcc | hcc <;> rcases hd_alpha with hd | hd <;>
        simp only [ha, hb, hcc, hd, Letter.IsAllowedBlock] <;> grind
    · obtain ⟨r, hr, hcut⟩ := hrows
      intro i k j l hik hjl
      have hij := hcut i j
      have hil := hcut i l
      have hkj := hcut k j
      have hkl := hcut k l
      have ha_alpha := halpha i j
      have hb_alpha := halpha i l
      have hc_alpha := halpha k j
      have hd_alpha := halpha k l
      clear hcut halpha
      rcases ha_alpha with ha | ha <;> rcases hb_alpha with hb | hb <;>
        rcases hc_alpha with hcc | hcc <;> rcases hd_alpha with hd | hd <;>
        simp only [ha, hb, hcc, hd, Letter.IsAllowedBlock] <;> grind

end RealRooted.OperatorMatrix
