import RealRooted.MaWang

/-!
# Sign-based root assembly tactics

This module packages root-count arguments after the caller has supplied the
mathematical sign certificate. The first frontend handles a target whose degree
is two larger than a split source polynomial: consecutive sign changes give
the interior roots, while a left witness and the two end signs give three
additional roots.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

private lemma lt_of_le_of_eval_ne {p : ℝ[X]} {x y : ℝ}
    (hxy : x ≤ y) (hne : p.eval x ≠ p.eval y) :
    x < y :=
  lt_of_le_of_ne hxy fun h => hne (congrArg p.eval h)

private theorem isRealRooted_of_two_left_roots_of_strict_signs
    {F : ℝ[X]} {rs : List ℝ} {uLL uL : ℝ}
    (hF_pos : HasPosLeadingCoeff F)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hdeg : F.natDegree = rs.length + 2)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hright : F.eval (rs.getLast (by grind)) < 0)
    (huLL_root : F.IsRoot uLL)
    (huL_root : F.IsRoot uL)
    (huLL_lt_uL : uLL < uL)
    (huL_lt_head : uL < rs.head!) :
    F ≠ 0 ∧ F.Splits := by
  have hrs_ne : rs ≠ [] := by grind
  have hF_natDegree_pos : 0 < F.natDegree := by lia
  have hF_degree_pos : 0 < F.degree :=
    natDegree_pos_iff_degree_pos.mp hF_natDegree_pos
  obtain ⟨us, hus_len, hus_interlaces, hus_roots, hus_strict⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted hsign
  have htop : Tendsto (fun x => F.eval x) atTop atTop :=
    F.tendsto_atTop_of_leadingCoeff_nonneg hF_degree_pos hF_pos.le
  obtain ⟨uR, hlast_le_uR, huR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hright) htop
  have hlast_lt_uR : rs.getLast hrs_ne < uR := by
    apply lt_of_le_of_eval_ne hlast_le_uR
    rw [huR_root]
    linarith
  have hhead_le_us : ∀ u ∈ us, rs.head! ≤ u := by
    obtain ⟨r, rest, rfl⟩ : ∃ r rest, rs = r :: rest := by
      cases rs with
      | nil => contradiction
      | cons r rest => exact ⟨r, rest, rfl⟩
    exact listInterlaces_all_ge us rest r hus_interlaces
  have hus_le_last : ∀ u ∈ us, u ≤ rs.getLast hrs_ne :=
    listInterlaces_all_le_getLast hrs_ne hrs_sorted hus_interlaces
  have huL_lt_us : ∀ u ∈ us, uL < u := by
    intro u hu
    exact lt_of_lt_of_le huL_lt_head (hhead_le_us u hu)
  have hus_lt_uR : ∀ u ∈ us, u < uR := by
    intro u hu
    exact lt_of_le_of_lt (hus_le_last u hu) hlast_lt_uR
  have huL_lt_uR : uL < uR :=
    lt_trans huL_lt_head
      (lt_of_le_of_lt
        (hrs_sorted.head!_le (List.getLast_mem hrs_ne)) hlast_lt_uR)
  have hus_uR_strict : (us ++ [uR]).Pairwise (· < ·) := by grind
  have huL_us_uR_strict : (uL :: (us ++ [uR])).Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, hus_uR_strict⟩
    intro u hu
    rcases List.mem_append.mp hu with hu | hu <;> simp_all
  have hroots_strict :
      (uLL :: (uL :: (us ++ [uR]))).Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, huL_us_uR_strict⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact huLL_lt_uL
    · exact lt_trans huLL_lt_uL
        ((List.pairwise_cons.mp huL_us_uR_strict).1 u hu)
  have hroots_sub :
      (↑(uLL :: (uL :: (us ++ [uR]))) : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset
      (Multiset.coe_nodup.mpr (hroots_strict.imp ne_of_lt))]
    intro x hx
    rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
    · exact (mem_roots hF_pos.ne_zero).mpr huLL_root
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (mem_roots hF_pos.ne_zero).mpr huL_root
    rcases List.mem_append.mp hx with hx | hx
    · exact (mem_roots hF_pos.ne_zero).mpr (hus_roots x hx)
    · have hx_eq : x = uR := by simpa using hx
      subst x
      exact (mem_roots hF_pos.ne_zero).mpr huR_root
  have hroots_len :
      (uLL :: (uL :: (us ++ [uR]))).length = F.natDegree := by
    simp [hus_len]
    lia
  have hlower :
      (uLL :: (uL :: (us ++ [uR]))).length ≤ F.roots.card := by
    rw [← Multiset.coe_card]
    exact Multiset.card_le_card hroots_sub
  have hupper : F.roots.card ≤ F.natDegree := card_roots' F
  refine ⟨hF_pos.ne_zero, splits_of_card_roots ?_⟩
  lia

/-- Strict sign changes on a nonempty sorted list, together with a positive
left witness and negative values at both extremes, force a positive-leading
odd-degree target of degree `rs.length + 2` to be nonzero and split.

Both extreme signs remain explicit certificates, matching the adjacent
Ma--Wang assembly APIs. -/
theorem isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two
    {F : ℝ[X]} {rs : List ℝ} {a : ℝ}
    (hF_pos : HasPosLeadingCoeff F)
    (hF_odd : Odd F.natDegree)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hdeg : F.natDegree = rs.length + 2)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft : F.eval rs.head! < 0)
    (hright : F.eval (rs.getLast (by grind)) < 0)
    (ha_lt : a < rs.head!)
    (ha_pos : 0 < F.eval a) :
    F ≠ 0 ∧ F.Splits := by
  have hF_natDegree_pos : 0 < F.natDegree := by lia
  have hF_degree_pos : 0 < F.degree :=
    natDegree_pos_iff_degree_pos.mp hF_natDegree_pos
  have hbot : Tendsto (fun x => F.eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd
      hF_pos hF_degree_pos hF_odd
  obtain ⟨uLL, huLL_le, huLL_root⟩ :=
    exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot ha_pos hbot
  have huLL_lt_a : uLL < a := by
    apply lt_of_le_of_eval_ne huLL_le
    rw [huLL_root]
    linarith
  obtain ⟨uL, ha_uL, huL_head, huL_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg ha_lt (by nlinarith)
  exact isRealRooted_of_two_left_roots_of_strict_signs
    hF_pos hrs_sorted hdeg hn hsign hright huLL_root huL_root
      (lt_trans huLL_lt_a ha_uL) huL_head

/-- Polynomial-source wrapper for
`isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two`. -/
theorem isRealRooted_of_strict_signs_of_natDegree_eq_add_two
    {f F : ℝ[X]} {rs : List ℝ} {a : ℝ}
    (hf_splits : f.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hF_odd : Odd F.natDegree)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 2)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft : F.eval rs.head! < 0)
    (hright : F.eval (rs.getLast (by grind)) < 0)
    (ha_lt : a < rs.head!)
    (ha_pos : 0 < F.eval a) :
    F ≠ 0 ∧ F.Splits := by
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  apply isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two
    hF_pos hF_odd hrs_sorted (by lia) hn hsign hleft hright ha_lt ha_pos

/-- Even-degree counterpart of
`isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two`.

The positive-leading target tends to `+∞` at both ends. A negative far-left
witness and a positive value at the first listed root give two roots on the
left; a negative value at the last listed root gives one root on the right.
The `_even` suffix refers to the target degree. Both extreme signs remain
explicit certificates, matching the adjacent Ma--Wang assembly APIs. -/
theorem isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two_even
    {F : ℝ[X]} {rs : List ℝ} {a : ℝ}
    (hF_pos : HasPosLeadingCoeff F)
    (hF_even : Even F.natDegree)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hdeg : F.natDegree = rs.length + 2)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft : 0 < F.eval rs.head!)
    (hright : F.eval (rs.getLast (by grind)) < 0)
    (ha_lt : a < rs.head!)
    (ha_neg : F.eval a < 0) :
    F ≠ 0 ∧ F.Splits := by
  have hF_natDegree_pos : 0 < F.natDegree := by lia
  have hF_degree_pos : 0 < F.degree :=
    natDegree_pos_iff_degree_pos.mp hF_natDegree_pos
  have hbot : Tendsto (fun x => F.eval x) atBot atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even
      hF_pos hF_degree_pos hF_even
  obtain ⟨uLL, huLL_le, huLL_root⟩ :=
    exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop ha_neg hbot
  have huLL_lt_a : uLL < a := by
    apply lt_of_le_of_eval_ne huLL_le
    rw [huLL_root]
    linarith
  obtain ⟨uL, ha_uL, huL_head, huL_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg ha_lt (by nlinarith)
  exact isRealRooted_of_two_left_roots_of_strict_signs
    hF_pos hrs_sorted hdeg hn hsign hright huLL_root huL_root
      (lt_trans huLL_lt_a ha_uL) huL_head

/-- Polynomial-source wrapper for
`isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two_even`. -/
theorem isRealRooted_of_strict_signs_of_natDegree_eq_add_two_even
    {f F : ℝ[X]} {rs : List ℝ} {a : ℝ}
    (hf_splits : f.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hF_even : Even F.natDegree)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 2)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest → F.eval r₁ * F.eval r₂ < 0)
    (hleft : 0 < F.eval rs.head!)
    (hright : F.eval (rs.getLast (by grind)) < 0)
    (ha_lt : a < rs.head!)
    (ha_neg : F.eval a < 0) :
    F ≠ 0 ∧ F.Splits := by
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  apply isRealRooted_of_strict_signs_of_natDegree_eq_length_add_two_even
    hF_pos hF_even hrs_sorted (by lia) hn hsign hleft hright ha_lt ha_neg

syntax (name := rr_sign_assembly_gap_two_named)
  "rr_sign_assembly_gap_two" " using "
    "source_splits" ":=" term ","
    "target_pos" ":=" term ","
    "target_odd" ":=" term ","
    "roots_sorted" ":=" term ","
    "roots_eq" ":=" term ","
    "degree_gap" ":=" term ","
    "roots_nonempty" ":=" term ","
    "consecutive_signs" ":=" term ","
    "left_sign" ":=" term ","
    "right_sign" ":=" term ","
    "witness_lt" ":=" term ","
    "witness_sign" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_sign_assembly_gap_two using
        source_splits := $hf:term,
        target_pos := $hFpos:term,
        target_odd := $hFodd:term,
        roots_sorted := $hsorted:term,
        roots_eq := $hroots:term,
        degree_gap := $hdeg:term,
        roots_nonempty := $hn:term,
        consecutive_signs := $hsign:term,
        left_sign := $hleft:term,
        right_sign := $hright:term,
        witness_lt := $ha_lt:term,
        witness_sign := $ha_pos:term) =>
      `(tactic|
        first
        | exact RealRooted.isRealRooted_of_strict_signs_of_natDegree_eq_add_two
            $hf $hFpos $hFodd $hsorted $hroots $hdeg $hn $hsign
            $hleft $hright $ha_lt $ha_pos
        | exact
            (RealRooted.isRealRooted_of_strict_signs_of_natDegree_eq_add_two
              $hf $hFpos $hFodd $hsorted $hroots $hdeg $hn $hsign
              $hleft $hright $ha_lt $ha_pos).2
        | exact
            (RealRooted.isRealRooted_of_strict_signs_of_natDegree_eq_add_two
              $hf $hFpos $hFodd $hsorted $hroots $hdeg $hn $hsign
              $hleft $hright $ha_lt $ha_pos).1)

syntax (name := rr_sign_assembly_gap_two_even_named)
  "rr_sign_assembly_gap_two_even" " using "
    "source_splits" ":=" term ","
    "target_pos" ":=" term ","
    "target_even" ":=" term ","
    "roots_sorted" ":=" term ","
    "roots_eq" ":=" term ","
    "degree_gap" ":=" term ","
    "roots_nonempty" ":=" term ","
    "consecutive_signs" ":=" term ","
    "left_sign" ":=" term ","
    "right_sign" ":=" term ","
    "witness_lt" ":=" term ","
    "witness_sign" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_sign_assembly_gap_two_even using
        source_splits := $hf:term,
        target_pos := $hFpos:term,
        target_even := $hFeven:term,
        roots_sorted := $hsorted:term,
        roots_eq := $hroots:term,
        degree_gap := $hdeg:term,
        roots_nonempty := $hn:term,
        consecutive_signs := $hsign:term,
        left_sign := $hleft:term,
        right_sign := $hright:term,
        witness_lt := $ha_lt:term,
        witness_sign := $ha_neg:term) =>
      `(tactic|
        first
        | exact RealRooted.isRealRooted_of_strict_signs_of_natDegree_eq_add_two_even
            $hf $hFpos $hFeven $hsorted $hroots $hdeg $hn $hsign
            $hleft $hright $ha_lt $ha_neg
        | exact
            (RealRooted.isRealRooted_of_strict_signs_of_natDegree_eq_add_two_even
              $hf $hFpos $hFeven $hsorted $hroots $hdeg $hn $hsign
              $hleft $hright $ha_lt $ha_neg).2
        | exact
            (RealRooted.isRealRooted_of_strict_signs_of_natDegree_eq_add_two_even
              $hf $hFpos $hFeven $hsorted $hroots $hdeg $hn $hsign
              $hleft $hright $ha_lt $ha_neg).1)

end RealRooted
