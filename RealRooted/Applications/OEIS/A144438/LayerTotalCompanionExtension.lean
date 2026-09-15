import RealRooted.Applications.OEIS.A144438.LayerTotalWronskianRecurrence

/-!
# Affine extensions underlying the Deco two-rank companion

This file gives the companion and the next bottom total a common unshifted
coordinate system.  Both arise by adjoining the fresh coordinate `0` to the
same companion base, with slopes given respectively by the preceding normal
core and that core plus the preceding total.  These are algebraic recurrence
interfaces; no all-rank stability claim is made here.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The normal core paired with the two-rank Wronskian companion. -/
def decoBottomTotalCompanionCore (n : Nat) : MvPolynomial Nat Real :=
  decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))

/-- The slope in the unshifted affine extension producing the next
companion. -/
def decoBottomTotalCompanionSlope (n : Nat) : MvPolynomial Nat Real :=
  decoBottomTotal (n + 1) + decoBottomTotalCompanionCore n

/-- The unshifted affine extension whose positive-coordinate rename is the
next bottom total. -/
def decoBottomTotalCompanionTotalExtension (n : Nat) :
    MvPolynomial Nat Real :=
  decoBottomTotalWronskianCompanion n + MvPolynomial.X 0 *
    decoBottomTotalCompanionCore n

/-- The unshifted affine extension whose positive-coordinate rename is the
next two-rank companion. -/
def decoBottomTotalCompanionSuccessorExtension (n : Nat) :
    MvPolynomial Nat Real :=
  decoBottomTotalWronskianCompanion n + MvPolynomial.X 0 *
    decoBottomTotalCompanionSlope n

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

/-- The companion core uses only the ordinary labels `1, ..., n+1`. -/
theorem vars_decoBottomTotalCompanionCore_subset_Icc (n : Nat) :
    (decoBottomTotalCompanionCore n).vars ⊆ Finset.Icc 1 (n + 1) := by
  unfold decoBottomTotalCompanionCore
  exact vars_decoNormalBottomCore_subset_Icc
    (vars_decoBottomTotal_subset_Icc (n + 1))

/-- The companion slope uses only the ordinary labels `1, ..., n+1`. -/
theorem vars_decoBottomTotalCompanionSlope_subset_Icc (n : Nat) :
    (decoBottomTotalCompanionSlope n).vars ⊆ Finset.Icc 1 (n + 1) := by
  intro x hx
  have hxadd := MvPolynomial.vars_add_subset _ _ hx
  rcases Finset.mem_union.mp hxadd with htotal | hcore
  · exact vars_decoBottomTotal_subset_Icc (n + 1) htotal
  · exact vars_decoBottomTotalCompanionCore_subset_Icc n hcore

/-- Coordinate `1` is absent from a positive-coordinate shift of the prior
bottom total. -/
theorem one_notMem_vars_rename_succ_decoBottomTotal (n : Nat) :
    1 ∉ (MvPolynomial.rename (fun i : Nat => i + 1)
      (decoBottomTotal n)).vars := by
  intro h
  obtain ⟨i, hi, hix⟩ := MvPolynomial.mem_vars_rename
    (fun i : Nat => i + 1) (decoBottomTotal n) h
  have hibounds := vars_decoBottomTotal_subset_Icc n hi
  rw [Finset.mem_Icc] at hibounds
  lia

/-- Coordinate `0` is absent from the two-rank companion. -/
theorem zero_notMem_vars_decoBottomTotalWronskianCompanion (n : Nat) :
    0 ∉ (decoBottomTotalWronskianCompanion n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalWronskianCompanion_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Coordinate `0` is absent from the companion core. -/
theorem zero_notMem_vars_decoBottomTotalCompanionCore (n : Nat) :
    0 ∉ (decoBottomTotalCompanionCore n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalCompanionCore_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Coordinate `0` is absent from the companion slope. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSlope (n : Nat) :
    0 ∉ (decoBottomTotalCompanionSlope n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalCompanionSlope_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- The two-rank companion is multiaffine. -/
theorem decoBottomTotalWronskianCompanion_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalWronskianCompanion n) := by
  have hrename := (decoBottomTotal_isMultiaffine n).rename
    (f := fun i : Nat => i + 1) (by intro i j h; lia)
  unfold decoBottomTotalWronskianCompanion
  exact (decoBottomTotal_isMultiaffine (n + 1)).add
    (hrename.X_mul_of_notMem_vars
      (one_notMem_vars_rename_succ_decoBottomTotal n))

/-- The companion core is multiaffine. -/
theorem decoBottomTotalCompanionCore_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionCore
  exact decoNormalBottomCore_isMultiaffine
    (decoBottomTotal_isMultiaffine (n + 1))

/-- The companion slope is multiaffine. -/
theorem decoBottomTotalCompanionSlope_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalCompanionSlope n) := by
  unfold decoBottomTotalCompanionSlope
  exact (decoBottomTotal_isMultiaffine (n + 1)).add
    (decoBottomTotalCompanionCore_isMultiaffine n)

/-- The coordinate-`1` zero-section of the companion is the zero-section of
the latest bottom total. -/
theorem specializeZero_one_decoBottomTotalWronskianCompanion (n : Nat) :
    MvPolynomial.specializeZero 1
        (decoBottomTotalWronskianCompanion n) =
      MvPolynomial.specializeZero 1 (decoBottomTotal (n + 1)) := by
  unfold decoBottomTotalWronskianCompanion
  rw [MvPolynomial.specializeZero_add, MvPolynomial.specializeZero_mul,
    MvPolynomial.specializeZero_X_self]
  simp

/-- The coordinate-`1` slope of the companion is the latest slope plus the
shifted preceding total. -/
theorem pderiv_one_decoBottomTotalWronskianCompanion (n : Nat) :
    MvPolynomial.pderiv 1 (decoBottomTotalWronskianCompanion n) =
      MvPolynomial.pderiv 1 (decoBottomTotal (n + 1)) +
        MvPolynomial.rename (fun i : Nat => i + 1)
          (decoBottomTotal n) := by
  unfold decoBottomTotalWronskianCompanion
  rw [map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (one_notMem_vars_rename_succ_decoBottomTotal n)]
  ring

/-- The value-one section of the companion is the corresponding section of
the latest total plus the shifted preceding total. -/
theorem specializeAt_one_decoBottomTotalWronskianCompanion (n : Nat) :
    MvPolynomial.specializeAt 1 1
        (decoBottomTotalWronskianCompanion n) =
      MvPolynomial.specializeAt 1 1 (decoBottomTotal (n + 1)) +
        MvPolynomial.rename (fun i : Nat => i + 1)
          (decoBottomTotal n) := by
  rw [MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
      (decoBottomTotalWronskianCompanion_isMultiaffine n) 1,
    MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
      (decoBottomTotal_isMultiaffine (n + 1)) 1,
    specializeZero_one_decoBottomTotalWronskianCompanion,
    pderiv_one_decoBottomTotalWronskianCompanion]
  ring

/-- Zero-specializing the companion slope distributes over its two summands. -/
theorem specializeZero_one_decoBottomTotalCompanionSlope (n : Nat) :
    MvPolynomial.specializeZero 1 (decoBottomTotalCompanionSlope n) =
      MvPolynomial.specializeZero 1 (decoBottomTotal (n + 1)) +
        MvPolynomial.specializeZero 1
          (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionSlope
  rw [MvPolynomial.specializeZero_add]

/-- Differentiating the companion slope distributes over its two summands. -/
theorem pderiv_one_decoBottomTotalCompanionSlope (n : Nat) :
    MvPolynomial.pderiv 1 (decoBottomTotalCompanionSlope n) =
      MvPolynomial.pderiv 1 (decoBottomTotal (n + 1)) +
        MvPolynomial.pderiv 1 (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionSlope
  rw [map_add]

/-- The unshifted extension producing the next bottom total is
multiaffine. -/
theorem decoBottomTotalCompanionTotalExtension_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine
      (decoBottomTotalCompanionTotalExtension n) := by
  unfold decoBottomTotalCompanionTotalExtension
  exact (decoBottomTotalWronskianCompanion_isMultiaffine n).add
    ((decoBottomTotalCompanionCore_isMultiaffine n).X_mul_of_notMem_vars
      (zero_notMem_vars_decoBottomTotalCompanionCore n))

/-- The unshifted extension producing the next companion is multiaffine. -/
theorem decoBottomTotalCompanionSuccessorExtension_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine
      (decoBottomTotalCompanionSuccessorExtension n) := by
  unfold decoBottomTotalCompanionSuccessorExtension
  exact (decoBottomTotalWronskianCompanion_isMultiaffine n).add
    ((decoBottomTotalCompanionSlope_isMultiaffine n).X_mul_of_notMem_vars
      (zero_notMem_vars_decoBottomTotalCompanionSlope n))

/-- A positive-coordinate value-one section of the total extension splits
over its companion base and fresh-coordinate core term. -/
theorem specializeAt_one_decoBottomTotalCompanionTotalExtension_add_one
    (n i : Nat) :
    MvPolynomial.specializeAt (i + 1) 1
        (decoBottomTotalCompanionTotalExtension n) =
      MvPolynomial.specializeAt (i + 1) 1
          (decoBottomTotalWronskianCompanion n) +
        MvPolynomial.X 0 *
          MvPolynomial.specializeAt (i + 1) 1
            (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionTotalExtension
  simp

/-- A positive-coordinate derivative of the total extension splits over its
companion base and fresh-coordinate core term. -/
theorem pderiv_decoBottomTotalCompanionTotalExtension_add_one
    (n i : Nat) :
    MvPolynomial.pderiv (i + 1)
        (decoBottomTotalCompanionTotalExtension n) =
      MvPolynomial.pderiv (i + 1)
          (decoBottomTotalWronskianCompanion n) +
        MvPolynomial.X 0 *
          MvPolynomial.pderiv (i + 1)
            (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionTotalExtension
  simp

/-- Specializing the normal affine step at its fresh coordinate to one gives
the positive-coordinate rename of the companion successor slope. -/
theorem specializeAt_one_decoBottomTotalAffineNormal_eq_companionSlope
    (n : Nat) :
    MvPolynomial.specializeAt 1 1
        (decoBottomTotalAffineNormalBase n + MvPolynomial.X 1 *
          decoBottomTotalAffineSlope n) =
      MvPolynomial.rename (fun i : Nat => i + 1)
        (decoBottomTotalCompanionSlope n) := by
  rw [MvPolynomial.specializeAt_add,
    MvPolynomial.specializeAt_eq_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineNormalBase n),
    MvPolynomial.specializeAt_mul, MvPolynomial.specializeAt_X,
    MvPolynomial.specializeAt_eq_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineSlope n)]
  simp only [ite_true]
  unfold decoBottomTotalAffineNormalBase decoBottomTotalAffineSlope
    decoBottomTotalCompanionSlope decoBottomTotalCompanionCore
  simp only [map_add, map_one, one_mul]

/-- The next bottom total is the positive-coordinate rename of the unshifted
companion/core affine extension. -/
theorem decoBottomTotal_add_two_eq_rename_companionTotalExtension (n : Nat) :
    decoBottomTotal (n + 2) =
      MvPolynomial.rename (fun i : Nat => i + 1)
        (decoBottomTotalCompanionTotalExtension n) := by
  rw [decoBottomTotal_recurrence_affine,
    decoBottomTotalAffineBase_eq_rename_wronskianCompanion]
  unfold decoBottomTotalAffineSlope decoBottomTotalCompanionTotalExtension
    decoBottomTotalCompanionCore
  simp only [map_add, map_mul, MvPolynomial.rename_X]

/-- The next two-rank companion is the positive-coordinate rename of a fresh
affine extension of the current companion. -/
theorem decoBottomTotalWronskianCompanion_succ_eq_rename_extension (n : Nat) :
    decoBottomTotalWronskianCompanion (n + 1) =
      MvPolynomial.rename (fun i : Nat => i + 1)
        (decoBottomTotalCompanionSuccessorExtension n) := by
  have hrename :
      MvPolynomial.rename (fun i : Nat => i + 1)
          (MvPolynomial.rename (fun i : Nat => i + 1) (decoBottomTotal n)) =
        MvPolynomial.rename (fun i : Nat => i + 2) (decoBottomTotal n) := by
    rw [MvPolynomial.rename_rename]
    congr 1
  rw [decoBottomTotalWronskianCompanion_succ]
  unfold decoBottomTotalCompanionSuccessorExtension
    decoBottomTotalCompanionSlope decoBottomTotalCompanionCore
    decoBottomTotalWronskianCompanion
  simp only [map_add, map_mul, MvPolynomial.rename_X, hrename]
  ring

/-- Every noninitial value-one section of the next companion is the shifted
section of its unshifted affine extension. -/
theorem specializeAt_one_decoBottomTotalWronskianCompanion_succ_add_two
    (n i : Nat) :
    MvPolynomial.specializeAt (i + 2) 1
        (decoBottomTotalWronskianCompanion (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.specializeAt (i + 1) 1
          (decoBottomTotalCompanionSuccessorExtension n)) := by
  rw [decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  simpa only [Nat.add_assoc] using
    MvPolynomial.specializeAt_rename (fun j : Nat => j + 1)
      (by intro j k h; lia) (i + 1) 1
        (decoBottomTotalCompanionSuccessorExtension n)

/-- Every noninitial derivative of the next companion is the shifted
derivative of its unshifted affine extension. -/
theorem pderiv_decoBottomTotalWronskianCompanion_succ_add_two
    (n i : Nat) :
    MvPolynomial.pderiv (i + 2)
        (decoBottomTotalWronskianCompanion (n + 1)) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.pderiv (i + 1)
          (decoBottomTotalCompanionSuccessorExtension n)) := by
  rw [decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  simpa only [Nat.add_assoc] using
    MvPolynomial.pderiv_rename (R := Real)
      (f := fun j : Nat => j + 1) (by intro j k h; lia) (i + 1)
        (decoBottomTotalCompanionSuccessorExtension n)

/-- Rayleighness of the next bottom total is exactly Rayleighness of its
unshifted companion/core affine extension. -/
theorem decoBottomTotal_add_two_isRayleigh_iff_companionTotalExtension
    (n : Nat) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) ↔
      MvPolynomial.IsRayleigh (decoBottomTotalCompanionTotalExtension n) := by
  rw [decoBottomTotal_add_two_eq_rename_companionTotalExtension]
  exact MvPolynomial.isRayleigh_rename_iff (by intro i j h; lia)

/-- Rayleighness of the next companion is exactly Rayleighness of its
unshifted fresh-coordinate affine extension. -/
theorem decoBottomTotalWronskianCompanion_succ_isRayleigh_iff_extension
    (n : Nat) :
    MvPolynomial.IsRayleigh (decoBottomTotalWronskianCompanion (n + 1)) ↔
      MvPolynomial.IsRayleigh
        (decoBottomTotalCompanionSuccessorExtension n) := by
  rw [decoBottomTotalWronskianCompanion_succ_eq_rename_extension]
  exact MvPolynomial.isRayleigh_rename_iff (by intro i j h; lia)

/-- Exact affine criterion for Rayleighness of the next two-rank companion. -/
theorem decoBottomTotalWronskianCompanion_succ_isRayleigh_iff_affine
    (n : Nat) :
    MvPolynomial.IsRayleigh (decoBottomTotalWronskianCompanion (n + 1)) ↔
      MvPolynomial.IsRayleigh (decoBottomTotalWronskianCompanion n) ∧
      MvPolynomial.IsRayleigh (decoBottomTotalCompanionSlope n) ∧
      (∀ i x, 0 ≤ MvPolynomial.eval x
        (MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionSlope n)
          (decoBottomTotalWronskianCompanion n) i)) ∧
      (∀ i j x, MvPolynomial.eval x
        (MvPolynomial.affineRayleighDiscriminant
          (decoBottomTotalWronskianCompanion n)
          (decoBottomTotalCompanionSlope n) i j) ≤ 0) := by
  rw [decoBottomTotalWronskianCompanion_succ_isRayleigh_iff_extension]
  unfold decoBottomTotalCompanionSuccessorExtension
  exact MvPolynomial.isRayleigh_add_X_mul_iff_of_fresh_all_discriminants
    (decoBottomTotalWronskianCompanion_isMultiaffine n)
    (decoBottomTotalCompanionSlope_isMultiaffine n)
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n)
    (zero_notMem_vars_decoBottomTotalCompanionSlope n)

end

end RealRooted.Applications.OEIS
