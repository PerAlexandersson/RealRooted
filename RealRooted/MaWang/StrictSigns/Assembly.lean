import RealRooted.MaWang.StrictSigns.RootSigns

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Strict interval-root construction: if a polynomial has strictly opposite
signs at each consecutive pair in a sorted real list `rs`, then it has a root
strictly between each consecutive pair. The constructed root list is strictly
sorted. -/
theorem exists_strictSignInterleaving {F : ℝ[X]} :
    ∀ (rs : List ℝ),
      rs.Pairwise (· ≤ ·) →
      (∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) →
      ∃ us : List ℝ, us.length = rs.length - 1 ∧
        ListInterlaces us rs ∧
        (∀ u ∈ us, F.IsRoot u) ∧
        us.Pairwise (· < ·)
  | [], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩ <;> simp [ListInterlaces]
  | [_], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩ <;> simp [ListInterlaces]
  | r₁ :: r₂ :: rest, hrs_sorted, hsign => by
      have hr₁r₂ : r₁ < r₂ := by
        have hprod : F.eval r₁ * F.eval r₂ < 0 := by simpa using hsign [] rfl
        have hr₁r₂_le : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs_sorted (by simp)
        by_contra hEq
        have : F.eval r₁ * F.eval r₂ = (F.eval r₁) ^ 2 := by grind
        nlinarith [sq_nonneg (F.eval r₁)]
      obtain ⟨u, hu₁, hu₂, hu_root⟩ :=
        exists_isRoot_between_of_eval_mul_neg hr₁r₂ (by simpa using hsign [] rfl)
      have htail_sorted : (r₂ :: rest).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrs_sorted).2
      obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
        exists_strictSignInterleaving (F := F) (r₂ :: rest) htail_sorted
          (fun pre {a b tail} hEq => by
            grind)
      have hu_lt_all : ∀ w ∈ us, u < w :=
        fun w hw => lt_of_lt_of_le hu₂ (listInterlaces_all_ge us rest r₂ hus_int w hw)
      refine ⟨u :: us, by simp [hus_len], ⟨hu₁.le, hu₂.le, hus_int⟩, ?_, ?_⟩ <;>
        simp_all

/-- Public strict wrapper around `exists_strictSignInterleaving`. -/
theorem exists_roots_strictly_interlacing_of_consecutive_signs {F : ℝ[X]} {rs : List ℝ}
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) :
    ∃ us : List ℝ, us.length = rs.length - 1 ∧
      ListInterlaces us rs ∧
      (∀ u ∈ us, F.IsRoot u) ∧
      us.Pairwise (· < ·) :=
  exists_strictSignInterleaving (F := F) rs hrs_sorted hsign

/-- If a nonzero polynomial has strictly alternating signs on consecutive
roots of a real-rooted polynomial and has smaller degree, then it is the
degree-one left interlacer. -/
theorem interlaces_of_consecutive_signs_of_natDegree_lt
    {f F : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0)
    (hdeg_lt : F.natDegree < f.natDegree)
    (hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) :
    Interlaces F f := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted (by grind)
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
      card_roots_of_splits hf_splits]
  have hus_sub : (↑us : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    simp_all
  have hus_card_le : us.length ≤ F.natDegree := by
    calc
      us.length = (↑us : Multiset ℝ).card := (Multiset.coe_card _).symm
      _ ≤ F.roots.card := Multiset.card_le_card hus_sub
      _ ≤ F.natDegree := card_roots' F
  have hus_len_f : us.length = f.natDegree - 1 := by lia
  have hdeg : F.natDegree + 1 = f.natDegree := by lia
  have hus_len_deg : us.length = F.natDegree := by lia
  have hus_eq : (↑us : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hus_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = us.length := hus_len_deg.symm
        _ = (↑us : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : F ≠ 0 ∧ F.Splits := by
    refine ⟨hF_ne, splits_of_card_roots ?_⟩
    rw [← hus_eq, Multiset.coe_card, hus_len_deg]
  exact
    ⟨⟨hf_ne, hf_splits⟩, hF, hdeg, rs, us, hrs_sorted,
      hus_pw.imp le_of_lt, hrs_eq, hus_eq, hus_int⟩

/-- If every element of the right-hand list is strictly above `a`, then so is
every element of the interlacing left-hand list. -/
lemma listInterlaces_all_gt_of_lowerBound :
    ∀ {us rs : List ℝ},
      ListInterlaces us rs →
      ∀ {a : ℝ}, (∀ r ∈ rs, a < r) → ∀ u ∈ us, a < u
  | [], [], hint, a, hlt, u, hu => by
      simp at hu
  | [], [_], hint, a, hlt, u, hu => by
      simp at hu
  | s :: ss, r₁ :: r₂ :: rs, hint, a, hlt, u, hu => by
      obtain ⟨hr₁s, _, htail⟩ := hint
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact lt_of_lt_of_le (hlt r₁ (by simp)) hr₁s
      · exact listInterlaces_all_gt_of_lowerBound htail
          (fun r hr => hlt r (by simp [hr])) u hu'
  | [], _ :: _ :: _, hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [_], hint, _, _, _, _ => by simp [ListInterlaces] at hint

/-- If every element of the right-hand list is strictly below `a`, then so is
every element of the interlacing left-hand list. -/
lemma listInterlaces_all_lt_of_upperBound :
    ∀ {us rs : List ℝ},
      ListInterlaces us rs →
      ∀ {a : ℝ}, (∀ r ∈ rs, r < a) → ∀ u ∈ us, u < a
  | [], [], hint, a, hlt, u, hu => by
      simp at hu
  | [], [_], hint, a, hlt, u, hu => by
      simp at hu
  | s :: ss, r₁ :: r₂ :: rs, hint, a, hlt, u, hu => by
      obtain ⟨_, hsr₂, htail⟩ := hint
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact lt_of_le_of_lt hsr₂ (hlt r₂ (by simp))
      · exact listInterlaces_all_lt_of_upperBound htail
          (fun r hr => hlt r (by simp [hr])) u hu'
  | [], _ :: _ :: _, hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [_], hint, _, _, _, _ => by simp [ListInterlaces] at hint

lemma eval_sign_of_interlaces_root
    {f g : ℝ[X]} {rs ss : List ℝ}
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hg_pos : HasPosLeadingCoeff g)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
      rs = pre ++ r :: rest →
      (Even rest.length → 0 < g.eval r) ∧ (Odd rest.length → g.eval r < 0) := by
  intro pre r rest hEq
  induction rest generalizing pre r with
  | nil =>
      have hrs_ne : rs ≠ [] := by simp_all
      have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
      have hroots_g_lt_r : ∀ t ∈ g.roots, t < r := by
        intro t ht
        have ht_ss : t ∈ ss := by
          rw [← hss_eq] at ht
          exact Multiset.mem_coe.mp ht
        have ht_le_last : t ≤ rs.getLast hrs_ne :=
          listInterlaces_all_le_getLast hrs_ne hrs_sorted hint t ht_ss
        have ht_le_r : t ≤ r := by simp_all
        have ht_root : g.IsRoot t := (mem_roots hg_ne).mp ht
        grind
      constructor
      · intro _
        exact eval_pos_of_all_roots_lt hg_ne hg_splits hg_pos hroots_g_lt_r
      · simp
  | cons r₂ rest ih =>
      have hEq_next : rs = (pre ++ [r]) ++ r₂ :: rest := by simp_all
      have hnext := ih (pre := pre ++ [r]) (r := r₂) hEq_next
      have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
      have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
      have hgg_nonpos : g.eval r * g.eval r₂ ≤ 0 :=
        eval_mul_eval_nonpos_of_interlacing_consecutive hg_splits hrs_sorted hss_eq hint hEq
      have hg_r_ne : g.eval r ≠ 0 := by simp_all
      have hg_r₂_ne : g.eval r₂ ≠ 0 := by simp_all
      have hgg_neg : g.eval r * g.eval r₂ < 0 :=
        lt_of_le_of_ne hgg_nonpos (mul_ne_zero hg_r_ne hg_r₂_ne)
      constructor
      · intro heven
        have hodd_rest : Odd rest.length := by grind
        have hg₂_neg : g.eval r₂ < 0 := hnext.2 hodd_rest
        nlinarith
      · intro hodd
        have heven_rest : Even rest.length := by grind
        have hg₂_pos : 0 < g.eval r₂ := hnext.1 heven_rest
        nlinarith

lemma mul_nonpos_of_mul_nonpos_of_mul_neg {a b c d : ℝ}
    (hab : a * b ≤ 0) (hcd : c * d ≤ 0) (hbd : b * d < 0) :
    a * c ≤ 0 := by
  have hb_ne : b ≠ 0 := by
    intro hb0
    simp [hb0] at hbd
  rcases lt_or_gt_of_ne hb_ne with hb | hb
  · have hd : 0 < d := by nlinarith
    have ha : 0 ≤ a := by nlinarith
    have hc : c ≤ 0 := by nlinarith
    nlinarith
  · have hd : d < 0 := by nlinarith
    have ha : a ≤ 0 := by nlinarith
    have hc : 0 ≤ c := by nlinarith
    nlinarith

lemma isRoot_of_eq_max_countP_le_of_sign
    {g F : ℝ[X]} {rs ts : List ℝ} {off : ℕ}
    {pre : List ℝ} {r : ℝ} {rest : List ℝ}
    (hF_splits : F.Splits) (hF_pos : HasPosLeadingCoeff F)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hoff : ts.length = rs.length + off)
    (hroot_nonpos : F.eval r * g.eval r ≤ 0)
    (hgsign_even : Even rest.length → 0 < g.eval r) (hgsign_odd : Odd rest.length → g.eval r < 0)
    (hEq : rs = pre ++ r :: rest)
    (hcount : ts.countP (· ≤ r) = pre.length + off + 1) :
    F.IsRoot r := by
  have hrs_len : rs.length = pre.length + rest.length + 1 := by grind
  have hcount_gt : ts.countP (r < ·) = rest.length := by
    have hsplit := countP_le_add_countP_gt_eq_length ts r
    lia
  rcases Nat.even_or_odd rest.length with heven | hodd
  · have hF_nonpos : F.eval r ≤ 0 := by
      have hg_pos' : 0 < g.eval r := hgsign_even heven
      nlinarith [hroot_nonpos, hg_pos']
    exact isRoot_of_eval_nonpos_of_even_countP_gt hF_splits hF_pos hts_eq hF_nonpos
      (by lia)
  · have hF_nonneg : 0 ≤ F.eval r := by
      have hg_neg' : g.eval r < 0 := hgsign_odd hodd
      nlinarith [hroot_nonpos, hg_neg']
    exact isRoot_of_eval_nonneg_of_odd_countP_gt hF_splits hF_pos hts_eq hF_nonneg
      (by lia)

lemma countP_le_of_eq_max_isRoot
    {F : ℝ[X]} {rs ts : List ℝ} {off : ℕ}
    (hF_ne : F ≠ 0)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hoff : ts.length = rs.length + off)
    (hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂)
    (hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + off + 1 →
        F.IsRoot r) :
    ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
      rs = pre ++ r :: rest →
      ts.countP (· ≤ r) ≤ pre.length + off + 1 := by
  intro pre r rest hEq
  induction rest generalizing pre r with
  | nil =>
      have hcount_le :
          ts.countP (· ≤ r) ≤ ts.length :=
        List.countP_le_length (p := fun x => decide (x ≤ r)) (l := ts)
      grind
  | cons r₂ rest ih =>
      have hEq_next : rs = (pre ++ [r]) ++ r₂ :: rest := by simp_all
      have hnext : ts.countP (· ≤ r₂) ≤ pre.length + off + 2 := by grind
      have hr_lt_r₂ : r < r₂ := hstrict pre hEq
      by_cases hsmall : ts.countP (· ≤ r₂) ≤ pre.length + off + 1
      · have hmono : ts.countP (· ≤ r) ≤ ts.countP (· ≤ r₂) :=
          List.countP_mono_left <| by
            grind
        lia
      · have heq : ts.countP (· ≤ r₂) = pre.length + off + 2 := by lia
        have hr₂_root : F.IsRoot r₂ := by grind
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          simp_all
        have hlt : ts.countP (· ≤ r) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · grind
          · exact hr₂_mem
          · simp [not_le_of_gt hr_lt_r₂]
          · simp
        lia

lemma countP_lt_of_eq_max_isRoot
    {F : ℝ[X]} {rs ts : List ℝ} {off : ℕ}
    (hF_ne : F ≠ 0)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + off + 1)
    (hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + off + 1 →
        F.IsRoot r) :
    ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
      rs = pre ++ r :: rest →
      ts.countP (· < r) ≤ pre.length + off := by
  intro pre r rest hEq
  have hle := hcount_le pre hEq
  by_cases hsmall : ts.countP (· ≤ r) ≤ pre.length + off
  · have hmono : ts.countP (· < r) ≤ ts.countP (· ≤ r) :=
      List.countP_mono_left <| by
        grind
    lia
  · have heq : ts.countP (· ≤ r) = pre.length + off + 1 := by lia
    have hr_root : F.IsRoot r := hroot_on_max pre hEq heq
    have hr_mem : r ∈ ts := by
      apply Multiset.mem_coe.mp
      simp_all
    have hlt : ts.countP (· < r) < ts.countP (· ≤ r) := by
      exact countP_lt_countP_of_exists (by grind) hr_mem (by simp) (by simp)
    lia

lemma mul_neg_of_mul_neg_of_mul_neg {a b c d : ℝ}
    (hab : a * b < 0) (hcd : c * d < 0) (hbd : b * d < 0) :
    a * c < 0 := by
  have hb_ne : b ≠ 0 := by
    intro hb0
    simp [hb0] at hab
  rcases lt_or_gt_of_ne hb_ne with hb | hb
  · have hd : 0 < d := by nlinarith
    have ha : 0 < a := by nlinarith
    have hc : c < 0 := by nlinarith
    nlinarith
  · have hd : d < 0 := by nlinarith
    have ha : a < 0 := by nlinarith
    have hc : 0 < c := by nlinarith
    nlinarith

/-- If `ss` interlaces a nonempty sorted list `rs`, then adjoining one extra
point `uR` to the right turns the tail of `rs` into a `ListInterlaces` witness
against `ss ++ [uR]`. -/
lemma listInterlaces_of_interlacing_append_right :
    ∀ {ss rs : List ℝ},
      rs ≠ [] →
      ListInterlaces ss rs →
      ∀ {s uR : ℝ},
        s ≤ rs.head! →
        (∀ r ∈ rs, r ≤ uR) →
        ListInterlaces rs (s :: ss ++ [uR])
  | [], [], hrs_ne, hint, s, uR, hs, hR => by
      lia
  | [], [r], _, hint, s, uR, hs, hR => by
      have hs' : s ≤ r := by simp_all
      simp [ListInterlaces, hs', hR r (by simp)]
  | [], _ :: _ :: _, _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | s₂ :: ss, [], hrs_ne, hint, s, uR, hs, hR => by
      lia
  | s₂ :: ss, [r], _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | s₂ :: ss, r₁ :: r₂ :: rs, _, hint, s, uR, hs, hR => by
      obtain ⟨hr₁s₂, hs₂r₂, htail⟩ := hint
      have htail_bound : ∀ r ∈ r₂ :: rs, r ≤ uR := by simp_all
      have htail_inter : ListInterlaces (r₂ :: rs) (s₂ :: ss ++ [uR]) :=
        listInterlaces_of_interlacing_append_right (rs := r₂ :: rs) (by lia)
          htail hs₂r₂ htail_bound
      exact ⟨hs, hr₁s₂, htail_inter⟩

/-- Same-degree assembly: strict sign changes on consecutive roots of `f`
produce inner roots of `F`; if one additional root of `F` lies strictly to the
right of all roots of `f`, then `f ≺ F` in the same-degree sense. -/
theorem prec_same_of_strict_signs_of_right_root
    {f F : ℝ[X]} {rs : List ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hright : ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR) :
    Prec f F := by
  obtain ⟨uR, huR_root, huR_lt⟩ := hright
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs (F := F) hrs_sorted hsign
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  have hrs_ne : rs ≠ [] := by grind
  obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
    cases rs with
    | nil => lia
    | cons r rs' => lia
  have hall_us_lt_uR : ∀ u ∈ us, u < uR :=
    listInterlaces_all_lt_of_upperBound hus_int huR_lt
  have hws_pw : (us ++ [uR]).Pairwise (· < ·) := by grind
  have hws_sub : (↑(us ++ [uR]) : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
    intro x hx
    rcases List.mem_append.mp (Multiset.mem_coe.mp hx) with hx_us | hx_uR <;> simp_all
  have hws_len : (us ++ [uR]).length = F.natDegree := by simp_all
  have hws_eq : (↑(us ++ [uR]) : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hws_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = (us ++ [uR]).length := hws_len.symm
        _ = (↑(us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : (F ≠ 0 ∧ F.Splits) := by
    refine ⟨hF_ne, splits_of_card_roots ?_⟩
    rw [← hws_eq, Multiset.coe_card, hws_len]
  have hws_sorted : (us ++ [uR]).Pairwise (· ≤ ·) := hws_pw.imp le_of_lt
  have hshape : ListAlternates (r :: rs') (us ++ [uR]) := by
    cases us with
    | nil =>
        have hrs_single : rs' = [] := by grind
        subst rs'
        simp [ListAlternates, ListInterlaces, le_of_lt (huR_lt r (by simp))]
    | cons s ss =>
        have hint' : ListInterlaces (s :: ss) (r :: rs') := by lia
        cases rs' with
        | nil =>
            simp [ListInterlaces] at hint'
        | cons r₂ rest =>
            obtain ⟨hrs, hs_r₂, htail⟩ := hint'
            have htail_bound : ∀ x ∈ r₂ :: rest, x ≤ uR := by grind
            exact ⟨hrs, listInterlaces_of_interlacing_append_right (rs := r₂ :: rest) (by lia)
              htail hs_r₂ htail_bound⟩
  have hlen_shape : (r :: rs').length = (us ++ [uR]).length := by lia
  exact ⟨⟨hf_ne, hf_splits⟩, hF, r :: rs', us ++ [uR], hrs_sorted, hws_sorted, hrs_eq, hws_eq,
    Or.inr ⟨hlen_shape, hshape⟩⟩

/-- Add one outer point on each side of a sorted interlacing layout. -/
lemma listInterlaces_with_outer :
    ∀ {us rs : List ℝ},
      rs ≠ [] →
      rs.Pairwise (· ≤ ·) →
      ListInterlaces us rs →
      ∀ {uL uR : ℝ},
        (∀ r ∈ rs, uL ≤ r) →
        (∀ r ∈ rs, r ≤ uR) →
        ListInterlaces rs (uL :: us ++ [uR])
  | [], [], hrs_ne, _, _, _, _, _, _ => by
      lia
  | [], [r], _, _, _, _, _, hL, hR => by
      simp [ListInterlaces, hL r (by simp), hR r (by simp)]
  | [], _ :: _ :: _, _, _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | _ :: _, [], hrs_ne, _, _, _, _, _, _ => by
      lia
  | _ :: _, [_], _, _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | s :: ss, r₁ :: r₂ :: rs, _, hrs, hint, uL, uR, hL, hR => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      have hrs_tail : (r₂ :: rs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hrs).2
      have hrs_tail_ne : (r₂ :: rs) ≠ [] := by lia
      have hL_tail : ∀ r ∈ r₂ :: rs, s ≤ r := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · lia
        · exact le_trans hsr₂ (List.Pairwise.rel_head hrs_tail (List.mem_cons_of_mem _ hr'))
      have hR_tail : ∀ r ∈ r₂ :: rs, r ≤ uR := by simp_all
      simp only [List.cons_append, ListInterlaces, hL r₁ (by simp), hr₁s, true_and]
      exact listInterlaces_with_outer hrs_tail_ne hrs_tail htail hL_tail hR_tail

/-- Assemble a differ-by-1 `Prec` statement from strict sign changes on a sorted
root list together with one strict outer root on each side. -/
theorem prec_of_strict_signs_of_strict_outer_roots
    {f F : ℝ[X]} {rs : List ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft : ∃ uL, F.IsRoot uL ∧ ∀ r ∈ rs, uL < r)
    (hright : ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR) :
    Prec f F := by
  obtain ⟨uL, huL_root, huL_lt⟩ := hleft
  obtain ⟨uR, huR_root, huR_lt⟩ := hright
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs (F := F) hrs_sorted hsign
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  have hrs_ne : rs ≠ [] := by grind
  obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
    cases rs with
    | nil => lia
    | cons r rs' => lia
  have hr_mem : r ∈ r :: rs' := by simp
  have huL_lt_uR : uL < uR := lt_trans (huL_lt r hr_mem) (huR_lt r hr_mem)
  have huL_lt_all_us : ∀ u ∈ us, uL < u :=
    listInterlaces_all_gt_of_lowerBound hus_int huL_lt
  have hall_us_lt_uR : ∀ u ∈ us, u < uR :=
    listInterlaces_all_lt_of_upperBound hus_int huR_lt
  have husuR_pw : (us ++ [uR]).Pairwise (· < ·) := by grind
  have hws_pw : (uL :: us ++ [uR]).Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, husuR_pw⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> simp_all
  have hws_sub : (↑(uL :: us ++ [uR]) : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
    intro x hx
    rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx'
    · simp_all
    rcases List.mem_append.mp hx' with hx_us | hx_uR <;> simp_all
  have hws_len : (uL :: us ++ [uR]).length = F.natDegree := by simp_all
  have hws_eq : (↑(uL :: us ++ [uR]) : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hws_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = (uL :: us ++ [uR]).length := hws_len.symm
        _ = (↑(uL :: us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : (F ≠ 0 ∧ F.Splits) := by
    refine ⟨hF_ne, splits_of_card_roots ?_⟩
    rw [← hws_eq, Multiset.coe_card, hws_len]
  have hws_sorted : (uL :: us ++ [uR]).Pairwise (· ≤ ·) := hws_pw.imp le_of_lt
  have hshape : ListInterlaces (r :: rs') (uL :: us ++ [uR]) :=
    listInterlaces_with_outer hrs_ne hrs_sorted hus_int
      (fun r hr => le_of_lt (huL_lt r hr))
      (fun r hr => le_of_lt (huR_lt r hr))
  have hlen_shape : (r :: rs').length + 1 = (uL :: us ++ [uR]).length := by lia
  exact ⟨⟨hf_ne, hf_splits⟩, hF, r :: rs', uL :: us ++ [uR], hrs_sorted, hws_sorted, hrs_eq, hws_eq,
    Or.inl ⟨hlen_shape, hshape⟩⟩

/-- Right-hand IVT bridge: if a polynomial is nonpositive at `r` and tends to
`+∞` at `+∞`, then it has a real root to the right of `r`. -/
lemma exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r ≤ 0) (ht : Tendsto (fun x => p.eval x) atTop atTop) :
    ∃ u ≥ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hneg
  · exact ⟨r, le_rfl, by simp_all⟩
  · have hpos : ∀ᶠ x in atTop, 0 < p.eval x :=
      ht.eventually (Ioi_mem_atTop 0)
    have hgt : ∀ᶠ x : ℝ in atTop, r < x := eventually_gt_atTop r
    obtain ⟨x, hx_gt_r, hx_pos⟩ := (hgt.and hpos).exists
    have h0 : (0 : ℝ) ∈ Set.Icc (p.eval r) (p.eval x) := ⟨hr, le_of_lt hx_pos⟩
    obtain ⟨u, hu, hu_root⟩ :=
      intermediate_value_Icc (le_of_lt hx_gt_r) p.continuous.continuousOn h0
    exact ⟨u, hu.1, hu_root⟩

/-- Right-hand wrapper for the `atTop → -∞` case with a nonnegative value at the
basepoint. -/
lemma exists_isRoot_ge_of_eval_nonneg_of_tendsto_atTop_atBot {p : ℝ[X]} {r : ℝ}
    (hr : 0 ≤ p.eval r) (ht : Tendsto (fun x => p.eval x) atTop atBot) :
    ∃ u ≥ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · exact ⟨r, le_rfl, by simpa [Polynomial.IsRoot.def] using hzero.symm⟩
  · have hneg : ∀ᶠ x in atTop, p.eval x < 0 :=
      ht.eventually (Iio_mem_atBot 0)
    have hgt : ∀ᶠ x : ℝ in atTop, r < x := eventually_gt_atTop r
    obtain ⟨x, hx_gt_r, hx_neg⟩ := (hgt.and hneg).exists
    have h0 : (0 : ℝ) ∈ Set.Icc (p.eval x) (p.eval r) :=
      ⟨le_of_lt hx_neg, le_of_lt hpos⟩
    obtain ⟨u, hu, hu_root⟩ :=
      intermediate_value_Icc' (le_of_lt hx_gt_r) p.continuous.continuousOn h0
    exact ⟨u, hu.1, hu_root⟩

/-- Left-hand wrapper for the `atBot → +∞` case with a nonpositive value at the
basepoint. -/
lemma exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r ≤ 0) (ht : Tendsto (fun x => p.eval x) atBot atTop) :
    ∃ u ≤ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hneg
  · exact ⟨r, le_rfl, by simp_all⟩
  · exact exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hneg ht

/-- Left-hand wrapper for the `atBot → -∞` case with a nonnegative value at the
basepoint. -/
lemma exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot {p : ℝ[X]} {r : ℝ}
    (hr : 0 ≤ p.eval r) (ht : Tendsto (fun x => p.eval x) atBot atBot) :
    ∃ u ≤ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · exact ⟨r, le_rfl, by simp_all⟩
  · exact exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hpos ht

/-- Even-left endpoint version of
`prec_of_strict_signs_of_strict_outer_roots`: if `f` has even degree, `F` has
positive leading coefficient and degree `deg(f)+1`, strictly alternates sign on
consecutive `f`-roots, is positive at the leftmost `f`-root, and negative at
the rightmost `f`-root, then `f ⊳ F`. -/
theorem prec_of_strict_signs_of_endSigns_even
    {f F : ℝ[X]} {rs : List ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hn : 1 ≤ rs.length)
    (hpar : Even f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft_sign : 0 < F.eval rs.head!)
    (hright_sign : F.eval (rs.getLast (by
      grind)) < 0) :
    Prec f F := by
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hrs_ne : rs ≠ [] := by lia
  have hF_natdeg_pos : 0 < F.natDegree := by lia
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp hF_natdeg_pos
  have hF_odd : Odd F.natDegree := by simp_all
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r ∈ rs, uL < r := by
    have ht : Tendsto (fun x => F.eval x) atBot atBot :=
      tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hF_pos hF_deg_pos hF_odd
    obtain ⟨uL, huL_le, huL_root⟩ :=
      exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hleft_sign ht
    have huL_lt_head : uL < rs.head! := by
      refine lt_of_le_of_ne huL_le ?_
      intro hEq
      simp_all
    refine ⟨uL, huL_root, ?_⟩
    intro r hr
    exact lt_of_lt_of_le huL_lt_head (hrs_sorted.head!_le hr)
  have hright :
      ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR := by
    have ht : Tendsto (fun x => F.eval x) atTop atTop :=
      F.tendsto_atTop_of_leadingCoeff_nonneg hF_deg_pos hF_pos.le
    obtain ⟨uR, huR_ge, huR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hright_sign) ht
    have hlast_lt_uR : rs.getLast hrs_ne < uR := by
      refine lt_of_le_of_ne huR_ge ?_
      intro hEq
      simp_all
    refine ⟨uR, huR_root, ?_⟩
    intro r hr
    exact lt_of_le_of_lt (hrs_sorted.rel_getLast hr) hlast_lt_uR
  exact prec_of_strict_signs_of_strict_outer_roots hf_ne hf_splits hF_ne hrs_sorted hrs_eq hdeg hn
    hsign hleft hright

/-- Odd-left endpoint version of
`prec_of_strict_signs_of_strict_outer_roots`: if `f` has odd degree, `F` has
positive leading coefficient and degree `deg(f)+1`, strictly alternates sign on
consecutive `f`-roots, and is negative at both extreme `f`-roots, then
`f ⊳ F`. -/
theorem prec_of_strict_signs_of_endSigns_odd
    {f F : ℝ[X]} {rs : List ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hn : 1 ≤ rs.length)
    (hpar : Odd f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft_sign : F.eval rs.head! < 0)
    (hright_sign : F.eval (rs.getLast (by
      grind)) < 0) :
    Prec f F := by
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hrs_ne : rs ≠ [] := by lia
  have hF_natdeg_pos : 0 < F.natDegree := by lia
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp hF_natdeg_pos
  have hF_even : Even F.natDegree := by simp_all
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r ∈ rs, uL < r := by
    have ht : Tendsto (fun x => F.eval x) atBot atTop :=
      tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hF_pos hF_deg_pos hF_even
    obtain ⟨uL, huL_le, huL_root⟩ :=
      exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hleft_sign ht
    have huL_lt_head : uL < rs.head! := by
      refine lt_of_le_of_ne huL_le ?_
      intro hEq
      simp_all
    refine ⟨uL, huL_root, ?_⟩
    intro r hr
    exact lt_of_lt_of_le huL_lt_head (hrs_sorted.head!_le hr)
  have hright :
      ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR := by
    have ht : Tendsto (fun x => F.eval x) atTop atTop :=
      F.tendsto_atTop_of_leadingCoeff_nonneg hF_deg_pos hF_pos.le
    obtain ⟨uR, huR_ge, huR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hright_sign) ht
    have hlast_lt_uR : rs.getLast hrs_ne < uR := by
      refine lt_of_le_of_ne huR_ge ?_
      intro hEq
      simp_all
    refine ⟨uR, huR_root, ?_⟩
    intro r hr
    exact lt_of_le_of_lt (hrs_sorted.rel_getLast hr) hlast_lt_uR
  exact prec_of_strict_signs_of_strict_outer_roots hf_ne hf_splits hF_ne hrs_sorted hrs_eq hdeg hn
    hsign hleft hright

end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (exists_roots_strictly_interlacing_of_consecutive_signs
    interlaces_of_consecutive_signs_of_natDegree_lt
    mul_neg_of_mul_neg_of_mul_neg
    prec_same_of_strict_signs_of_right_root
    prec_of_strict_signs_of_strict_outer_roots
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
    exists_isRoot_ge_of_eval_nonneg_of_tendsto_atTop_atBot
    exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop
    exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot
    prec_of_strict_signs_of_endSigns_even
    prec_of_strict_signs_of_endSigns_odd)

end RealRooted
