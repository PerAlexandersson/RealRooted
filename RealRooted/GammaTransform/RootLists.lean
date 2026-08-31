import RealRooted.GammaTransform.RootMap

/-!
# Gamma-transform ordered roots

The ordered-root and reciprocal-center completion of the Hoster--Stump root
map.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

/-! ## Ordered root completion for Hoster--Stump Proposition 2.5

The following private helpers formalize the two cases after equation (2.2).
Preferred roots lie in `(-1, 0)`; their reciprocal roots lie below `-1`, and
the replicated center block records the multiplicity of `-1`.
-/

namespace GammaTransformInternal

/-- The reciprocal and central-root completion used within the gamma-transform package. -/
noncomputable def reciprocalCenterRoots (m : ℕ) (s : List ℝ) : List ℝ :=
  (s.map fun x => x⁻¹).reverse ++ (List.replicate m (-1) ++ s)

end GammaTransformInternal

open GammaTransformInternal

private lemma map_interleave (f : α → β) : ∀ l₁ l₂ : List α,
    (l₁.interleave l₂).map f = (l₁.map f).interleave (l₂.map f)
  | _, [] => by simp
  | l₁, b :: l₂ => by
      simp only [List.interleave_cons, List.map_cons]
      rw [map_interleave f l₂ l₁]
termination_by l₁ l₂ => l₁.length + l₂.length

private lemma mem_interleave_of_lengths {x : α} : ∀ l₁ l₂ : List α,
    (l₁.length = l₂.length ∨ l₁.length + 1 = l₂.length) →
      x ∈ l₁.interleave l₂ → x ∈ l₁ ∨ x ∈ l₂
  | _, [], _, hx => by simp at hx
  | l₁, b :: l₂, hlen, hx => by
      rw [List.interleave_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (by simp)
      · have htail : l₂.length = l₁.length ∨ l₂.length + 1 = l₁.length := by
          simp only [List.length_cons] at hlen
          lia
        rcases mem_interleave_of_lengths l₂ l₁ htail hx with hx | hx
        · exact Or.inr (by simp [hx])
        · exact Or.inl hx
termination_by l₁ l₂ => l₁.length + l₂.length

private lemma interleave_replicate_succ (m : ℕ) (a : α) :
    (List.replicate m a).interleave (List.replicate (m + 1) a) =
      List.replicate (2 * m + 1) a := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ (n := m)]
      rw [List.replicate_succ (n := m + 1)]
      rw [List.interleave_cons, List.interleave_cons]
      rw [ih]
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by lia]
      rfl

private lemma isChain_reverse_inv_center_iff
    {l : List ℝ} (m : ℕ)
    (hlmem : ∀ x ∈ l, x ∈ Set.Ioo (-1 : ℝ) 0) :
    ((l.reverse.map fun x => x⁻¹) ++
        (List.replicate (2 * m + 1) (-1) ++ l)).IsChain (· ≤ ·) ↔
      l.IsChain (· ≤ ·) := by
  let a := l.reverse.map fun x => x⁻¹
  let c := List.replicate (2 * m + 1) (-1 : ℝ)
  constructor
  · intro h
    have hp := h.pairwise
    rw [List.pairwise_append, List.pairwise_append] at hp
    exact hp.2.1.2.1.isChain
  · intro hl
    have ha : a.Pairwise (· ≤ ·) := by
      dsimp [a]
      rw [List.pairwise_map, List.pairwise_reverse]
      exact hl.pairwise.imp_of_mem fun hx hy hxy =>
        inv_antitoneOn_Iio (hlmem _ hx).2 (hlmem _ hy).2 hxy
    have hc : c.Pairwise (· ≤ ·) := by simp [c]
    have hac : (a ++ c).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨ha, hc, ?_⟩
      intro x hx y hy
      dsimp [a] at hx
      rw [List.mem_map] at hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzmem : z ∈ l := List.mem_reverse.mp hz
      have hzlt : z⁻¹ < -1 := by
        rw [inv_eq_one_div]
        exact (div_lt_iff_of_neg (hlmem z hzmem).2).2
          (by nlinarith [(hlmem z hzmem).1])
      have hy' : y = -1 := by simpa [c] using hy
      linarith
    have hacl : ((a ++ c) ++ l).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨hac, hl.pairwise, ?_⟩
      intro x hx y hy
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · dsimp [a] at hx
        rw [List.mem_map] at hx
        rcases hx with ⟨z, hz, rfl⟩
        have hzmem : z ∈ l := List.mem_reverse.mp hz
        have hzlt : z⁻¹ < -1 := by
          rw [inv_eq_one_div]
          exact (div_lt_iff_of_neg (hlmem z hzmem).2).2
            (by nlinarith [(hlmem z hzmem).1])
        linarith [(hlmem y hy).1]
      · have hx' : x = -1 := by simpa [c] using hx
        linarith [(hlmem y hy).1]
    simpa [a, c, List.append_assoc] using hacl.isChain

private lemma interleave_reciprocalCenterRoots_same
    {ss rs : List ℝ} (m : ℕ) (hlen : ss.length = rs.length) :
    (reciprocalCenterRoots m ss).interleave
        (reciprocalCenterRoots (m + 1) rs) =
      ((rs.interleave ss).reverse.map fun x => x⁻¹) ++
        (List.replicate (2 * m + 1) (-1) ++ rs.interleave ss) := by
  unfold reciprocalCenterRoots
  rw [List.interleave_append_append_of_length_eq_length]
  · rw [List.interleave_append_append_of_length_add_one_eq_length]
    · rw [interleave_replicate_succ]
      congr 1
      simpa only [map_interleave, List.map_reverse] using
        (List.reverse_interleave_of_length_eq_length
          (l₁ := rs.map fun x => x⁻¹) (l₂ := ss.map fun x => x⁻¹)
          (by simpa only [List.length_map] using hlen.symm)).symm
    · simp
  · simp [hlen]

private lemma interleave_reciprocalCenterRoots_succ
    {ss rs : List ℝ} (m : ℕ) (hlen : ss.length + 1 = rs.length) :
    (reciprocalCenterRoots (m + 1) ss).interleave
        (reciprocalCenterRoots m rs) =
      ((ss.interleave rs).reverse.map fun x => x⁻¹) ++
        (List.replicate (2 * m + 1) (-1) ++ ss.interleave rs) := by
  unfold reciprocalCenterRoots
  rw [List.interleave_append_append_of_length_add_one_eq_length]
  · rw [List.interleave_append_append_of_length_add_one_eq_length]
    · rw [interleave_replicate_succ]
      congr 1
      simpa only [map_interleave, List.map_reverse] using
        (List.reverse_interleave_of_length_add_one_eq_length
          (l₁ := ss.map fun x => x⁻¹) (l₂ := rs.map fun x => x⁻¹)
          (by simpa only [List.length_map] using hlen)).symm
    · simp
  · simp [hlen]

/-- Equal gamma degrees give one additional central root on the right transform.
This is the first backward case in Hoster--Stump, Proposition 2.5. -/
lemma GammaTransformInternal.listInterlaces_reciprocalCenterRoots_same_iff
    {ss rs : List ℝ} (m : ℕ)
    (hss : ∀ x ∈ ss, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hrs : ∀ x ∈ rs, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hlen : ss.length = rs.length) :
    ListInterlaces (reciprocalCenterRoots m ss)
        (reciprocalCenterRoots (m + 1) rs) ↔
      ListAlternates ss rs := by
  have hfull_len :
      (reciprocalCenterRoots m ss).length + 1 =
        (reciprocalCenterRoots (m + 1) rs).length := by
    simp [reciprocalCenterRoots, hlen]
    lia
  rw [listInterlaces_iff_interleaves_of_length hfull_len]
  constructor
  · intro h
    have hc := ((List.interleaves_iff_length_isChain_interleave).1 h).2
    rw [interleave_reciprocalCenterRoots_same m hlen,
      isChain_reverse_inv_center_iff m] at hc
    · apply (listAlternates_iff_interleaves_of_length hlen).2
      apply (List.interleaves_iff_length_isChain_interleave).2
      exact ⟨Or.inl hlen.symm, hc⟩
    · intro x hx
      rcases mem_interleave_of_lengths rs ss (Or.inl hlen.symm) hx with hx | hx
      · exact hrs x hx
      · exact hss x hx
  · intro h
    have hi := (listAlternates_iff_interleaves_of_length hlen).1 h
    apply (List.interleaves_iff_length_isChain_interleave).2
    refine ⟨Or.inr hfull_len, ?_⟩
    rw [interleave_reciprocalCenterRoots_same m hlen,
      isChain_reverse_inv_center_iff m]
    · exact ((List.interleaves_iff_length_isChain_interleave).1 hi).2
    · intro x hx
      rcases mem_interleave_of_lengths rs ss (Or.inl hlen.symm) hx with hx | hx
      · exact hrs x hx
      · exact hss x hx

/-- Successive gamma degrees remove one central root from the right transform.
This is the second backward case in Hoster--Stump, Proposition 2.5. -/
lemma GammaTransformInternal.listInterlaces_reciprocalCenterRoots_succ_iff
    {ss rs : List ℝ} (m : ℕ)
    (hss : ∀ x ∈ ss, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hrs : ∀ x ∈ rs, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hlen : ss.length + 1 = rs.length) :
    ListInterlaces (reciprocalCenterRoots (m + 1) ss)
        (reciprocalCenterRoots m rs) ↔
      ListInterlaces ss rs := by
  have hfull_len :
      (reciprocalCenterRoots (m + 1) ss).length + 1 =
        (reciprocalCenterRoots m rs).length := by
    simp [reciprocalCenterRoots]
    lia
  rw [listInterlaces_iff_interleaves_of_length hfull_len]
  constructor
  · intro h
    have hc := ((List.interleaves_iff_length_isChain_interleave).1 h).2
    rw [interleave_reciprocalCenterRoots_succ m hlen,
      isChain_reverse_inv_center_iff m] at hc
    · apply (listInterlaces_iff_interleaves_of_length hlen).2
      apply (List.interleaves_iff_length_isChain_interleave).2
      exact ⟨Or.inr hlen, hc⟩
    · intro x hx
      rcases mem_interleave_of_lengths ss rs (Or.inr hlen) hx with hx | hx
      · exact hss x hx
      · exact hrs x hx
  · intro h
    have hi := (listInterlaces_iff_interleaves_of_length hlen).1 h
    apply (List.interleaves_iff_length_isChain_interleave).2
    refine ⟨Or.inr hfull_len, ?_⟩
    rw [interleave_reciprocalCenterRoots_succ m hlen,
      isChain_reverse_inv_center_iff m]
    · exact ((List.interleaves_iff_length_isChain_interleave).1 hi).2
    · intro x hx
      rcases mem_interleave_of_lengths ss rs (Or.inr hlen) hx with hx | hx
      · exact hss x hx
      · exact hrs x hx

/-- Exact root-multiset form of Hoster--Stump, Proposition 2.5, equations
(2.1) and (2.2): the roots of the gamma transform consist of reciprocal
pairs, together with the exceptional roots at `-1` prescribed by the degree.
-/
theorem roots_gammaTransform_eq_reciprocal_add_neg_one_add
    {d : Nat} {γ : Real[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0)
    (hneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0) :
    (gammaTransform d γ).roots =
      ((gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : Real) 0)).map (fun x => x⁻¹) +
        Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) +
          (gammaTransform d γ).roots.filter
            (fun x => x ∈ Set.Ioo (-1 : Real) 0) := by
  classical
  let s := (gammaTransform d γ).roots.filter
    (fun x => x ∈ Set.Ioo (-1 : Real) 0)
  change (gammaTransform d γ).roots =
    s.map (fun x => x⁻¹) +
      Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s
  have hs_Ioo {x : Real} (hx : x ∈ s) : x ∈ Set.Ioo (-1 : Real) 0 := by
    change x ∈ (gammaTransform d γ).roots.filter
      (fun z => z ∈ Set.Ioo (-1 : Real) 0) at hx
    exact (Multiset.mem_filter.mp hx).2
  have hinv_Ioo {x : Real} (hx : x < -1) : x⁻¹ ∈ Set.Ioo (-1 : Real) 0 := by
    constructor
    · rw [inv_eq_one_div]
      exact (lt_div_iff_of_neg (by linarith)).2 (by nlinarith)
    · exact inv_lt_zero.mpr (by linarith)
  have hinv_lt_neg_one {x : Real} (hx : x ∈ Set.Ioo (-1 : Real) 0) :
      x⁻¹ < -1 := by
    rw [inv_eq_one_div]
    exact (div_lt_iff_of_neg hx.2).2 (by nlinarith [hx.1])
  refine Multiset.ext.mpr fun x => ?_
  by_cases hxlt : x < -1
  · have hx0 : x ≠ 0 := by linarith
    have hxi := hinv_Ioo hxlt
    have hcount_inv :
        (gammaTransform d γ).roots.count x =
          (s.map (fun z => z⁻¹)).count x := by
      calc
        (gammaTransform d γ).roots.count x =
            (gammaTransform d γ).rootMultiplicity x :=
          Polynomial.count_roots (gammaTransform d γ)
        _ = γ.rootMultiplicity (gammaRootMap x) :=
          rootMultiplicity_gammaTransform_of_neg hγdeg hγ
            (by linarith) (by linarith)
        _ = γ.rootMultiplicity (gammaRootMap x⁻¹) := by rw [gammaRootMap_inv hx0]
        _ = (gammaTransform d γ).rootMultiplicity x⁻¹ :=
          (rootMultiplicity_gammaTransform_of_neg hγdeg hγ hxi.2
            (ne_of_gt hxi.1)).symm
        _ = (gammaTransform d γ).roots.count x⁻¹ :=
          (Polynomial.count_roots (gammaTransform d γ)).symm
        _ = s.count x⁻¹ := by
          simpa [s] using
            (Multiset.count_filter_of_pos
              (s := (gammaTransform d γ).roots) (a := x⁻¹)
              (p := fun z : Real => z ∈ Set.Ioo (-1) 0) hxi).symm
        _ = (s.map (fun z => z⁻¹)).count x := by
          simpa using
            (Multiset.count_map_eq_count' (fun z : Real => z⁻¹) s
              inv_injective x⁻¹).symm
    have hs_zero : s.count x = 0 := by
      apply Multiset.count_filter_of_neg
      intro hxmem
      linarith [hxmem.1]
    have hrep_zero :
        (Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real)).count x = 0 := by
      rw [Multiset.count_replicate]
      simp [Ne.symm (ne_of_lt hxlt)]
    calc
      (gammaTransform d γ).roots.count x =
          (s.map (fun z => z⁻¹)).count x := hcount_inv
      _ = (s.map (fun z => z⁻¹) +
          Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count x := by
        simp [Multiset.count_add, hs_zero, hrep_zero]
  · by_cases hxeq : x = -1
    · subst x
      have hs_zero : s.count (-1) = 0 := by
        apply Multiset.count_filter_of_neg
        simp
      have hinv_zero : (s.map (fun z => z⁻¹)).count (-1) = 0 := by
        apply Multiset.count_eq_zero_of_notMem
        rw [Multiset.mem_map]
        rintro ⟨z, hzs, hz⟩
        have hzlt := hinv_lt_neg_one (hs_Ioo hzs)
        rw [hz] at hzlt
        linarith
      calc
        (gammaTransform d γ).roots.count (-1) =
            (gammaTransform d γ).rootMultiplicity (-1) :=
          Polynomial.count_roots (gammaTransform d γ)
        _ = d - 2 * γ.natDegree :=
          rootMultiplicity_neg_one_gammaTransform hγdeg hγ
        _ = (s.map (fun z => z⁻¹) +
            Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count (-1) := by
          simp [Multiset.count_add, hs_zero, hinv_zero]
    · by_cases hxneg : x < 0
      · have hxmem : x ∈ Set.Ioo (-1 : Real) 0 :=
          ⟨lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm hxeq), hxneg⟩
        have hinv_zero : (s.map (fun z => z⁻¹)).count x = 0 := by
          apply Multiset.count_eq_zero_of_notMem
          rw [Multiset.mem_map]
          rintro ⟨z, hzs, hz⟩
          have hzlt := hinv_lt_neg_one (hs_Ioo hzs)
          rw [hz] at hzlt
          linarith [hxmem.1]
        have hs_count :
            (gammaTransform d γ).roots.count x = s.count x := by
          simpa [s] using
            (Multiset.count_filter_of_pos
              (s := (gammaTransform d γ).roots) (a := x)
              (p := fun z : Real => z ∈ Set.Ioo (-1) 0) hxmem).symm
        have hrep_zero :
            (Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real)).count x = 0 := by
          rw [Multiset.count_replicate]
          simp [Ne.symm hxeq]
        calc
          (gammaTransform d γ).roots.count x = s.count x := hs_count
          _ = (s.map (fun z => z⁻¹) +
              Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count x := by
            simp [Multiset.count_add, hinv_zero, hrep_zero]
      · have hx_not_mem : x ∉ (gammaTransform d γ).roots := by
          intro hxroot
          exact hxneg (hneg x hxroot)
        have hs_zero : s.count x = 0 := by
          apply Multiset.count_filter_of_neg
          intro hxmem
          exact hxneg hxmem.2
        have hinv_zero : (s.map (fun z => z⁻¹)).count x = 0 := by
          apply Multiset.count_eq_zero_of_notMem
          rw [Multiset.mem_map]
          rintro ⟨z, hzs, hz⟩
          have hzlt := hinv_lt_neg_one (hs_Ioo hzs)
          rw [hz] at hzlt
          linarith
        have hrep_zero :
            (Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real)).count x = 0 := by
          rw [Multiset.count_replicate]
          simp [Ne.symm hxeq]
        calc
          (gammaTransform d γ).roots.count x = 0 :=
            Multiset.count_eq_zero_of_notMem hx_not_mem
          _ = (s.map (fun z => z⁻¹) +
              Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count x := by
            simp [Multiset.count_add, hs_zero, hinv_zero, hrep_zero]

/-- Exact root-multiset form of Hoster--Stump, Proposition 2.5, equation
(2.1): the negative gamma roots are the images of the transform roots on the
preferred reciprocal branch `(-1, 0)`, with multiplicity. -/
theorem roots_eq_map_filter_roots_gammaTransform
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2) (hγ : γ ≠ 0)
    (hγneg : ∀ y ∈ γ.roots, y < 0) :
    γ.roots =
      ((gammaTransform d γ).roots.filter
        (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).map gammaRootMap := by
  classical
  let s := (gammaTransform d γ).roots.filter
    (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)
  have hs_Ioo {x : ℝ} (hx : x ∈ s) : x ∈ Set.Ioo (-1 : ℝ) 0 := by
    change x ∈ (gammaTransform d γ).roots.filter
      (fun z => z ∈ Set.Ioo (-1 : ℝ) 0) at hx
    exact (Multiset.mem_filter.mp hx).2
  refine Multiset.ext.mpr fun y => ?_
  by_cases hy : y < 0
  · obtain ⟨x, hx, hxy⟩ := exists_mem_Ioo_gammaRootMap_eq hy
    have hcount_map : (s.map gammaRootMap).count y = s.count x := by
      rw [← hxy]
      calc
        (s.map gammaRootMap).count (gammaRootMap x) =
            (s.filter
              (fun z => gammaRootMap x = gammaRootMap z)).card :=
          Multiset.count_map gammaRootMap s (gammaRootMap x)
        _ = (s.filter (fun z => x = z)).card := by
          exact congrArg Multiset.card <|
            Multiset.filter_congr fun z hz =>
              strictMonoOn_gammaRootMap.injOn.eq_iff hx (hs_Ioo hz)
        _ = s.count x :=
          (Multiset.count_eq_card_filter_eq s x).symm
    calc
      γ.roots.count y = γ.rootMultiplicity y :=
        Polynomial.count_roots γ
      _ = γ.rootMultiplicity (gammaRootMap x) := by rw [hxy]
      _ = (gammaTransform d γ).rootMultiplicity x :=
        (rootMultiplicity_gammaTransform_of_mem_Ioo hγdeg hγ hx).symm
      _ = (gammaTransform d γ).roots.count x :=
        (Polynomial.count_roots (gammaTransform d γ)).symm
      _ = s.count x := by
        simpa [s] using
          (Multiset.count_filter_of_pos
            (s := (gammaTransform d γ).roots) (a := x)
            (p := fun z : ℝ => z ∈ Set.Ioo (-1) 0) hx).symm
      _ = (s.map gammaRootMap).count y := hcount_map.symm
      _ = (((gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).map gammaRootMap).count y := by
        rfl
  · have hy_not_mem : y ∉ γ.roots := by
      intro hyroot
      exact hy (hγneg y hyroot)
    have hy_not_map : y ∉ s.map gammaRootMap := by
      rw [Multiset.mem_map]
      rintro ⟨x, hxs, hxy⟩
      apply hy
      rw [← hxy]
      unfold gammaRootMap
      exact div_neg_of_neg_of_pos (hs_Ioo hxs).2
        (sq_pos_of_pos (by linarith [(hs_Ioo hxs).1]))
    calc
      γ.roots.count y = 0 :=
        Multiset.count_eq_zero_of_notMem hy_not_mem
      _ = (s.map gammaRootMap).count y :=
        (Multiset.count_eq_zero_of_notMem hy_not_map).symm
      _ = (((gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).map gammaRootMap).count y := by
        rfl



end RealRooted
