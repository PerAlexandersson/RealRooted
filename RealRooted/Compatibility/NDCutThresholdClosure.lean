import RealRooted.Compatibility.NDCutStaircase

/-!
# Marker-one closure for structural N/D cut outputs

The selected thresholds for a structural cut are increasing: they consist of
`0, ..., m - 1`, skip `m`, and continue with `m + 1, ..., 2 * m`.  Therefore
the marker-one threshold theorem applies directly and gives the zero-aware
interlacing package on the ordered successor cut outputs.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The selected structural cut thresholds are weakly increasing. -/
theorem pairwise_ndCutThresholds (m : ℕ) :
    (ndCutThresholds m).Pairwise (· ≤ ·) := by
  unfold ndCutThresholds
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_reverse, List.pairwise_ofFn]
    intro i j hij
    lia
  · rw [List.pairwise_ofFn]
    intro i j hij
    lia
  · intro a ha b hb
    rw [List.mem_reverse, List.mem_ofFn] at ha
    rw [List.mem_ofFn] at hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    lia

/-- Every selected structural cut row has the nonnegative marker `1`. -/
theorem ndCutThresholdRows_marker_nonneg {m : ℕ} :
    ∀ p ∈ ndCutThresholdRows m, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases List.mem_map.mp hp with ⟨t, _, rfl⟩
  exact hasNonnegCoeffs_one

/-- The selected structural cut rows are weakly ordered by threshold. -/
theorem pairwise_ndCutThresholdRows (m : ℕ) :
    (ndCutThresholdRows m).Pairwise (fun a b ↦ a.1 ≤ b.1) := by
  rw [ndCutThresholdRows, List.pairwise_map]
  exact pairwise_ndCutThresholds m

/-- The selected structural cut rows satisfy the marker-one entry condition
at every matrix width. -/
theorem ndCutThresholdRows_has2x2 {m q : ℕ} :
    ∀ (i₁ i₂ : Fin (ndCutThresholdRows m).length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry ((ndCutThresholdRows m).get i₁).1
          ((ndCutThresholdRows m).get i₁).2 j₁.val)
        (thresholdEntry ((ndCutThresholdRows m).get i₁).1
          ((ndCutThresholdRows m).get i₁).2 j₂.val)
        (thresholdEntry ((ndCutThresholdRows m).get i₂).1
          ((ndCutThresholdRows m).get i₂).2 j₁.val)
        (thresholdEntry ((ndCutThresholdRows m).get i₂).1
          ((ndCutThresholdRows m).get i₂).2 j₂.val) := by
  intro i₁ i₂ j₁ j₂ hi hj
  have ht := (pairwise_ndCutThresholdRows m).rel_get_of_le hi
  have hone : ∀ i : Fin (ndCutThresholdRows m).length,
      ((ndCutThresholdRows m).get i).2 = 1 := by
    intro i
    change ((List.map (fun t => (t, 1)) (ndCutThresholds m)).get
      ⟨i.1, by simpa [ndCutThresholdRows] using i.2⟩).2 = 1
    simp
  rw [hone i₁, hone i₂]
  exact has2x2_thresholdEntry_one ht hj

/-- The selected marker-one structural cut matrix preserves a zero-aware
nonnegative interlacing family and real-rootedness of every nonzero output. -/
theorem ndCutThresholdMatrix_preserves_interlacing_weak
    (m : ℕ) (fs : List ℝ[X])
    (hfs : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted
      (matPolyAction (thresholdMatrix fs.length (ndCutThresholdRows m)) fs) := by
  exact thresholdMatrix_preserves_interlacing_seq0_of_entry_weak
    (ndCutThresholdRows m) ndCutThresholdRows_marker_nonneg
      ndCutThresholdRows_has2x2 fs rfl hfs.1 hfs.2

/-- A structural N/D invariant sends its state-order field to the exact
zero-aware interlacing package on `reverse P' ++ Q'`. -/
theorem OrderedNDCutCompatible.cutOutputs_stateInterlacing
    {m : ℕ} {N D : Fin m → ℝ[X]} (h : OrderedNDCutCompatible N D) :
    IsInterlacingSeq0NonnegRealRooted
      ((List.ofFn
          (cutTransformP (ndCutP N D) (ndCutQ N D))).reverse ++
        List.ofFn (cutTransformQ (ndCutP N D) (ndCutQ N D))) := by
  rw [← matPolyAction_ndCutThresholdRows]
  exact ndCutThresholdMatrix_preserves_interlacing_weak
    m (ndCutStateOrder N D) h.stateInterlacing

private theorem prec_of_prec0_of_pos {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hfg : Interl f g) : StrictInterl f g := by
  rcases hfg with rfl | rfl | hfg
  · exact False.elim (hf.ne_zero rfl)
  · exact False.elim (hg.ne_zero rfl)
  · exact hfg

private theorem compatible_X_left_of_prec_nonneg {f g : ℝ[X]}
    (hfg : StrictInterl f g) (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) :
    Compatible (X * f) g :=
  (Compatible.of_strictInterl (strictInterl_mul_X_of_strictInterl_of_nonneg hfg hf hg)).comm

/-- A zero-aware interlacing package on `reverse P ++ Q`, together with
positive leading coefficients, supplies every field of the ordered cut
interface. -/
theorem orderedCutCompatible_of_stateInterlacing
    {m : ℕ} {P Q : Fin m → ℝ[X]}
    (hP_pos : ∀ i, HasPosLeadingCoeff (P i))
    (hQ_pos : ∀ i, HasPosLeadingCoeff (Q i))
    (hstate : IsInterlacingSeq0NonnegRealRooted
      ((List.ofFn P).reverse ++ List.ofFn Q)) :
    OrderedCutCompatible P Q := by
  have hpair := isInterlacingSeq0_iff_pairwise.mp hstate.interlacingSeq0
  have hparts := List.pairwise_append.mp hpair
  have hPP0 := hparts.1
  rw [List.pairwise_reverse, List.pairwise_ofFn] at hPP0
  have hQQ0 := hparts.2.1
  rw [List.pairwise_ofFn] at hQQ0
  have hP_mem : ∀ i, P i ∈ (List.ofFn P).reverse ++ List.ofFn Q := by
    intro i
    apply List.mem_append_left
    rw [List.mem_reverse]
    simp
  have hQ_mem : ∀ i, Q i ∈ (List.ofFn P).reverse ++ List.ofFn Q := by
    intro i
    apply List.mem_append_right
    simp
  have hP_nonneg : ∀ i, HasNonnegCoeffs (P i) :=
    fun i ↦ hstate.nonnegCoeffs (P i) (hP_mem i)
  have hQ_nonneg : ∀ i, HasNonnegCoeffs (Q i) :=
    fun i ↦ hstate.nonnegCoeffs (Q i) (hQ_mem i)
  have hP_real : ∀ i, P i ≠ 0 ∧ (P i).Splits :=
    fun i ↦ hstate.realRooted (P i) (hP_mem i) (hP_pos i).ne_zero
  have hQ_real : ∀ i, Q i ≠ 0 ∧ (Q i).Splits :=
    fun i ↦ hstate.realRooted (Q i) (hQ_mem i) (hQ_pos i).ne_zero
  have hPP : ∀ ⦃i j⦄, i ≤ j → StrictInterl (P j) (P i) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with hij | hij
    · subst j
      exact StrictInterl.refl (hP_real i).1 (hP_real i).2
    · exact prec_of_prec0_of_pos (hP_pos j) (hP_pos i) (hPP0 hij)
  have hQQ : ∀ ⦃i j⦄, i ≤ j → StrictInterl (Q i) (Q j) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with hij | hij
    · subst j
      exact StrictInterl.refl (hQ_real i).1 (hQ_real i).2
    · exact prec_of_prec0_of_pos (hQ_pos i) (hQ_pos j) (hQQ0 hij)
  have hPQ : ∀ i j, StrictInterl (P i) (Q j) := by
    intro i j
    apply prec_of_prec0_of_pos (hP_pos i) (hQ_pos j)
    exact hparts.2.2 (P i) (by rw [List.mem_reverse]; simp) (Q j) (by simp)
  exact
    { p_pos := hP_pos
      p_nonneg := hP_nonneg
      q_pos := hQ_pos
      q_nonneg := hQ_nonneg
      pp_reverse := by
        intro i j hij
        exact Compatible.of_strictInterl (hPP hij)
      xpp_reverse := by
        intro i j hij
        exact compatible_X_left_of_prec_nonneg
          (hPP hij) (hP_nonneg j) (hP_nonneg i)
      pq := fun i j ↦ Compatible.of_strictInterl (hPQ i j)
      xpq := fun i j ↦
        compatible_X_left_of_prec_nonneg (hPQ i j) (hP_nonneg i) (hQ_nonneg j)
      qq_forward := by
        intro i j hij
        exact Compatible.of_strictInterl (hQQ hij)
      xqq_forward := by
        intro i j hij
        exact compatible_X_left_of_prec_nonneg
          (hQQ hij) (hQ_nonneg i) (hQ_nonneg j) }

/-- The structural state-order field and the exact threshold representation
produce the complete ordered cut package on the successor `P/Q` outputs. -/
theorem OrderedNDCutCompatible.cutOutputs_orderedCutCompatible
    {m : ℕ} {N D : Fin m → ℝ[X]} (h : OrderedNDCutCompatible N D) :
    OrderedCutCompatible
      (cutTransformP (ndCutP N D) (ndCutQ N D))
      (cutTransformQ (ndCutP N D) (ndCutQ N D)) := by
  apply orderedCutCompatible_of_stateInterlacing
  · exact h.cutCompatible.cutTransformP_pos
  · exact h.cutCompatible.cutTransformQ_pos
  · exact h.cutOutputs_stateInterlacing

end RealRooted
