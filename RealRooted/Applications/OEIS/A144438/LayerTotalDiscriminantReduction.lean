import RealRooted.Applications.OEIS.A144438.LayerTotalWronskianRecurrence

/-!
# Two-rank discriminant reduction for the Deco layer total

The affine base and slope are simultaneous positive-coordinate renamings of
the two-rank Wronskian companion and preceding normal core.  This file moves
the old-coordinate affine discriminants to that lower coordinate system and
packages the resulting exact companion data.  It does not assert that the
data is preserved at every rank.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The companion uses only the ordinary labels `1, ..., n+1`. -/
theorem vars_decoBottomTotalWronskianCompanion_subset_Icc (n : Nat) :
    (decoBottomTotalWronskianCompanion n).vars ⊆
      Finset.Icc 1 (n + 1) := by
  classical
  intro x hx
  unfold decoBottomTotalWronskianCompanion at hx
  have hxadd := MvPolynomial.vars_add_subset _ _ hx
  rcases Finset.mem_union.mp hxadd with htotal | hproduct
  · exact vars_decoBottomTotal_subset_Icc (n + 1) htotal
  · have hmul := MvPolynomial.vars_mul _ _ hproduct
    rcases Finset.mem_union.mp hmul with hX | hrename
    · rw [MvPolynomial.vars_X] at hX
      simp only [Finset.mem_singleton] at hX
      subst x
      exact Finset.mem_Icc.mpr ⟨le_rfl, by lia⟩
    · obtain ⟨i, hi, hix⟩ := MvPolynomial.mem_vars_rename
        (fun i : Nat => i + 1) (decoBottomTotal n) hrename
      have hibounds := vars_decoBottomTotal_subset_Icc n hi
      rw [Finset.mem_Icc] at hibounds ⊢
      rw [← hix]
      constructor <;> lia

/-- Coordinate `0` is absent from the two-rank companion. -/
theorem zero_notMem_vars_decoBottomTotalWronskianCompanion (n : Nat) :
    0 ∉ (decoBottomTotalWronskianCompanion n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalWronskianCompanion_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Coordinate `0` is absent from the preceding normal core. -/
theorem zero_notMem_vars_decoBottomTotalWronskianCore (n : Nat) :
    0 ∉ (decoNormalBottomCore (n + 1)
      (decoBottomTotal (n + 1))).vars := by
  intro h
  have hbounds := vars_decoNormalBottomCore_subset_Icc
    (vars_decoBottomTotal_subset_Icc (n + 1)) h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Coordinate `0` is absent from the shifted affine base. -/
theorem zero_notMem_vars_decoBottomTotalAffineBase (n : Nat) :
    0 ∉ (decoBottomTotalAffineBase n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalAffineBase_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Coordinate `0` is absent from the shifted affine slope. -/
theorem zero_notMem_vars_decoBottomTotalAffineSlope (n : Nat) :
    0 ∉ (decoBottomTotalAffineSlope n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalAffineSlope_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Every positive-coordinate affine discriminant is the shifted
discriminant of the lower companion/core pair. -/
theorem affineRayleighDiscriminant_affineBase_slope_succ
    (n i j : Nat) :
    MvPolynomial.affineRayleighDiscriminant
        (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n)
        (i + 1) (j + 1) =
      MvPolynomial.rename (fun k : Nat => k + 1)
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))) i j) := by
  rw [decoBottomTotalAffineBase_eq_rename_wronskianCompanion]
  unfold decoBottomTotalAffineSlope
  exact MvPolynomial.affineRayleighDiscriminant_rename
    (fun k : Nat => k + 1) (by intro a b h; lia) _ _ i j

/-- Evaluation of a positive-coordinate affine discriminant is evaluation
of the lower companion/core discriminant after shifting the assignment. -/
theorem eval_affineRayleighDiscriminant_affineBase_slope_succ
    (n i j : Nat) (x : Nat → Real) :
    MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n)
          (i + 1) (j + 1)) =
      MvPolynomial.eval (fun k => x (k + 1))
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))) i j) := by
  rw [affineRayleighDiscriminant_affineBase_slope_succ,
    MvPolynomial.eval_rename]
  rfl

/-- Nonpositivity of every old-coordinate affine discriminant is exactly
nonpositivity of every lower companion/core discriminant.  The unused
coordinate `0` vanishes on both sides. -/
theorem eval_affineRayleighDiscriminant_nonpos_iff_companion (n : Nat) :
    (∀ i j x, i ≠ 1 → j ≠ 1 → MvPolynomial.eval x
      (MvPolynomial.affineRayleighDiscriminant
        (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n) i j) ≤ 0) ↔
      ∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))) i j) ≤ 0 := by
  constructor
  · intro h i j x
    by_cases hi : i = 0
    · subst i
      rw [MvPolynomial.affineRayleighDiscriminant_eq_zero_of_notMem_vars
        _ _ 0 j
        (zero_notMem_vars_decoBottomTotalWronskianCompanion n)
        (zero_notMem_vars_decoBottomTotalWronskianCore n)]
      simp
    · by_cases hj : j = 0
      · subst j
        rw [MvPolynomial.affineRayleighDiscriminant_comm_coord]
        rw [MvPolynomial.affineRayleighDiscriminant_eq_zero_of_notMem_vars
          _ _ 0 i
          (zero_notMem_vars_decoBottomTotalWronskianCompanion n)
          (zero_notMem_vars_decoBottomTotalWronskianCore n)]
        simp
      · let y : Nat → Real := fun k => match k with
          | 0 => 0
          | l + 1 => x l
        have hshift := h (i + 1) (j + 1) y (by lia) (by lia)
        rw [eval_affineRayleighDiscriminant_affineBase_slope_succ] at hshift
        simpa [y] using hshift
  · intro h i j x hi hj
    by_cases hi0 : i = 0
    · subst i
      rw [MvPolynomial.affineRayleighDiscriminant_eq_zero_of_notMem_vars
        _ _ 0 j (zero_notMem_vars_decoBottomTotalAffineBase n)
        (zero_notMem_vars_decoBottomTotalAffineSlope n)]
      simp
    · by_cases hj0 : j = 0
      · subst j
        rw [MvPolynomial.affineRayleighDiscriminant_comm_coord]
        rw [MvPolynomial.affineRayleighDiscriminant_eq_zero_of_notMem_vars
          _ _ 0 i (zero_notMem_vars_decoBottomTotalAffineBase n)
          (zero_notMem_vars_decoBottomTotalAffineSlope n)]
        simp
      · have hi2 : 2 ≤ i := by lia
        have hj2 : 2 ≤ j := by lia
        obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi2
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hj2
        have hlower := h (a + 1) (b + 1) (fun k => x (k + 1))
        rw [← eval_affineRayleighDiscriminant_affineBase_slope_succ
          n (a + 1) (b + 1) x] at hlower
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlower

/-- The exact lower two-rank data appearing in one affine Rayleigh step.
This is a bundle of proof obligations, not an all-rank preservation claim. -/
structure DecoBottomTotalCompanionRayleighData (n : Nat) : Prop where
  companion_isRayleigh : MvPolynomial.IsRayleigh
    (decoBottomTotalWronskianCompanion n)
  coordinateWronskian_nonneg : ∀ i x, 0 ≤ MvPolynomial.eval x
    (MvPolynomial.coordinateWronskian
      (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
      (decoBottomTotalWronskianCompanion n) i)
  affineDiscriminant_nonpos : ∀ i j x, MvPolynomial.eval x
    (MvPolynomial.affineRayleighDiscriminant
      (decoBottomTotalWronskianCompanion n)
      (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))) i j) ≤ 0

end

end RealRooted.Applications.OEIS
