import RealRooted.Applications.OEIS.A144438.LayerTotalStructure
import RealRooted.Multiaffine.AffineCoordinateExtension

/-!
# Affine-coordinate recurrence for the Deco layer total

The ordinary-coordinate recurrence introduces label `1` freshly. This file
separates its constant and linear parts in that coordinate and specializes the
generic affine-coordinate Rayleigh criterion to one Deco recurrence step.

No all-rank stability claim is made here: the remaining hypotheses are exact
Rayleigh, Wronskian, and discriminant invariants for the two recurrence parts.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The constant-in-`1` part contributed by the normal recurrence branch. -/
def decoBottomTotalAffineNormalBase (n : Nat) : MvPolynomial Nat Real :=
  MvPolynomial.rename (fun i : Nat => i + 1) (decoBottomTotal (n + 1))

/-- The constant-in-`1` part contributed by the exceptional recurrence
branch. -/
def decoBottomTotalAffineExceptionalBase (n : Nat) : MvPolynomial Nat Real :=
  decoExceptionalBottomStep (decoBottomTotal n)

/-- The part of the rank-`n+2` recurrence independent of its new coordinate
`1`. -/
def decoBottomTotalAffineBase (n : Nat) : MvPolynomial Nat Real :=
  decoBottomTotalAffineNormalBase n + decoBottomTotalAffineExceptionalBase n

/-- The coefficient of the new coordinate `1` in the rank-`n+2`
recurrence. -/
def decoBottomTotalAffineSlope (n : Nat) : MvPolynomial Nat Real :=
  MvPolynomial.rename (fun i : Nat => i + 1)
    (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))

/-- The normal core's coordinate Wronskian is an affine-weighted row of
Rayleigh differences. This is the exact first-order invariant contributed by
the normal branch before relabeling. -/
theorem coordinateWronskian_decoNormalBottomCore
    {R : Type*} [CommRing R] (n : Nat) (Q : MvPolynomial Nat R) (i : Fin n) :
    MvPolynomial.coordinateWronskian (decoNormalBottomCore n Q) Q
        (decoLayerBottomEmbedding n i) =
      Q * MvPolynomial.pderiv (decoLayerBottomEmbedding n i) Q +
        ∑ j : Fin n,
          (1 - MvPolynomial.X (decoLayerBottomEmbedding n j)) *
            MvPolynomial.rayleighDifference Q
              (decoLayerBottomEmbedding n i)
              (decoLayerBottomEmbedding n j) := by
  classical
  have hderiv := MvPolynomial.coordinateWronskian_sum_pderiv_left
    (decoLayerBottomEmbedding n) (fun _ : Fin n => (1 : R)) Q
      (decoLayerBottomEmbedding n i)
  simp only [map_one, one_mul] at hderiv
  have heuler := MvPolynomial.coordinateWronskian_sum_X_mul_pderiv_left
    (decoLayerBottomEmbedding n) (decoLayerBottomEmbedding n).injective Q i
  have hsum :
      (∑ j : Fin n,
          (1 - MvPolynomial.X (decoLayerBottomEmbedding n j)) *
            MvPolynomial.rayleighDifference Q
              (decoLayerBottomEmbedding n i)
              (decoLayerBottomEmbedding n j)) =
        (∑ j : Fin n,
          MvPolynomial.rayleighDifference Q
            (decoLayerBottomEmbedding n i)
            (decoLayerBottomEmbedding n j)) -
          ∑ j : Fin n,
            MvPolynomial.X (decoLayerBottomEmbedding n j) *
              MvPolynomial.rayleighDifference Q
                (decoLayerBottomEmbedding n i)
                (decoLayerBottomEmbedding n j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold decoNormalBottomCore
  rw [MvPolynomial.coordinateWronskian_add_left,
    MvPolynomial.coordinateWronskian_sub_left,
    MvPolynomial.coordinateWronskian_C_mul_left,
    MvPolynomial.coordinateWronskian_self, mul_zero, zero_sub,
    heuler, hderiv, hsum]
  ring

/-- Relabeling transports the normal core Wronskian to the corresponding
normal affine base and slope. -/
theorem coordinateWronskian_affineSlope_normalBase (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n)
        (decoBottomTotalAffineNormalBase n) (i + 1) =
      MvPolynomial.rename (fun j : Nat => j + 1)
        (MvPolynomial.coordinateWronskian
          (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
          (decoBottomTotal (n + 1)) i) := by
  unfold decoBottomTotalAffineSlope decoBottomTotalAffineNormalBase
  exact MvPolynomial.coordinateWronskian_rename (fun j : Nat => j + 1)
    (by intro j k h; lia) _ _ i

/-- The affine base Wronskian splits exactly into its normal contribution and
the remaining exceptional cross term. -/
theorem coordinateWronskian_affineSlope_base (n i : Nat) :
    MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n) (decoBottomTotalAffineBase n) (i + 1) =
      MvPolynomial.rename (fun j : Nat => j + 1)
          (MvPolynomial.coordinateWronskian
            (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))
            (decoBottomTotal (n + 1)) i) +
        MvPolynomial.coordinateWronskian
          (decoBottomTotalAffineSlope n)
          (decoBottomTotalAffineExceptionalBase n) (i + 1) := by
  rw [decoBottomTotalAffineBase,
    MvPolynomial.coordinateWronskian_add_right,
    coordinateWronskian_affineSlope_normalBase]

/-- The normal recurrence branch is itself the affine extension formed by the
normal base and slope. -/
theorem decoNormalBottomStep_total_eq_affine (n : Nat) :
    decoNormalBottomStep (n + 1) (decoBottomTotal (n + 1)) =
      decoBottomTotalAffineNormalBase n + MvPolynomial.X 1 *
        decoBottomTotalAffineSlope n := by
  simp only [decoNormalBottomStep, decoBottomTotalAffineNormalBase,
    decoBottomTotalAffineSlope]

/-- The defining two-step recurrence, collected as an affine extension in its
fresh coordinate `1`. -/
theorem decoBottomTotal_recurrence_affine (n : Nat) :
    decoBottomTotal (n + 2) =
      decoBottomTotalAffineBase n + MvPolynomial.X 1 *
        decoBottomTotalAffineSlope n := by
  rw [decoBottomTotal_recurrence]
  simp only [decoNormalBottomStep, decoBottomTotalAffineBase,
    decoBottomTotalAffineNormalBase, decoBottomTotalAffineExceptionalBase,
    decoBottomTotalAffineSlope]
  ring

/-- The affine base uses only the old labels `2, ..., n+2`. -/
theorem vars_decoBottomTotalAffineBase_subset_Icc (n : Nat) :
    (decoBottomTotalAffineBase n).vars ⊆ Finset.Icc 2 (n + 2) := by
  classical
  intro x hx
  unfold decoBottomTotalAffineBase decoBottomTotalAffineNormalBase
    decoBottomTotalAffineExceptionalBase at hx
  have hxadd := MvPolynomial.vars_add_subset _ _ hx
  rcases Finset.mem_union.mp hxadd with hxnormal | hxexceptional
  · obtain ⟨y, hy, hyx⟩ := MvPolynomial.mem_vars_rename
      (fun i : Nat => i + 1) (decoBottomTotal (n + 1)) hxnormal
    have hybounds := vars_decoBottomTotal_subset_Icc (n + 1) hy
    rw [Finset.mem_Icc] at hybounds ⊢
    rw [← hyx]
    constructor <;> lia
  · unfold decoExceptionalBottomStep at hxexceptional
    have hxmul := MvPolynomial.vars_mul _ _ hxexceptional
    rcases Finset.mem_union.mp hxmul with hxX | hxrename
    · rw [MvPolynomial.vars_X] at hxX
      simp only [Finset.mem_singleton] at hxX
      subst x
      exact Finset.mem_Icc.mpr ⟨le_rfl, by lia⟩
    · obtain ⟨y, hy, hyx⟩ := MvPolynomial.mem_vars_rename
        (fun i : Nat => i + 2) (decoBottomTotal n) hxrename
      have hybounds := vars_decoBottomTotal_subset_Icc n hy
      rw [Finset.mem_Icc] at hybounds ⊢
      rw [← hyx]
      constructor <;> lia

/-- The affine slope uses only the old labels `2, ..., n+2`. -/
theorem vars_decoBottomTotalAffineSlope_subset_Icc (n : Nat) :
    (decoBottomTotalAffineSlope n).vars ⊆ Finset.Icc 2 (n + 2) := by
  intro x hx
  unfold decoBottomTotalAffineSlope at hx
  obtain ⟨y, hy, hyx⟩ := MvPolynomial.mem_vars_rename
    (fun i : Nat => i + 1)
    (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1))) hx
  have hybounds := vars_decoNormalBottomCore_subset_Icc
    (vars_decoBottomTotal_subset_Icc (n + 1)) hy
  rw [Finset.mem_Icc] at hybounds ⊢
  rw [← hyx]
  constructor <;> lia

/-- The new coordinate does not occur in the normal affine base. -/
theorem one_notMem_vars_decoBottomTotalAffineNormalBase (n : Nat) :
    1 ∉ (decoBottomTotalAffineNormalBase n).vars := by
  intro h
  unfold decoBottomTotalAffineNormalBase at h
  obtain ⟨i, hi, hone⟩ := MvPolynomial.mem_vars_rename
    (fun i : Nat => i + 1) (decoBottomTotal (n + 1)) h
  have hibounds := vars_decoBottomTotal_subset_Icc (n + 1) hi
  rw [Finset.mem_Icc] at hibounds
  lia

/-- The new coordinate does not occur in the exceptional affine base. -/
theorem one_notMem_vars_decoBottomTotalAffineExceptionalBase (n : Nat) :
    1 ∉ (decoBottomTotalAffineExceptionalBase n).vars := by
  intro h
  unfold decoBottomTotalAffineExceptionalBase decoExceptionalBottomStep at h
  have hmul := MvPolynomial.vars_mul _ _ h
  rcases Finset.mem_union.mp hmul with hX | hrename
  · rw [MvPolynomial.vars_X] at hX
    simp at hX
  · obtain ⟨i, hi, hone⟩ := MvPolynomial.mem_vars_rename
      (fun i : Nat => i + 2) (decoBottomTotal n) hrename
    lia

/-- The new coordinate does not occur in the affine base. -/
theorem one_notMem_vars_decoBottomTotalAffineBase (n : Nat) :
    1 ∉ (decoBottomTotalAffineBase n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalAffineBase_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- The new coordinate does not occur in the affine slope. -/
theorem one_notMem_vars_decoBottomTotalAffineSlope (n : Nat) :
    1 ∉ (decoBottomTotalAffineSlope n).vars := by
  intro h
  have hbounds := vars_decoBottomTotalAffineSlope_subset_Icc n h
  rw [Finset.mem_Icc] at hbounds
  lia

/-- Zero-specializing the new coordinate in the normal affine branch leaves
its normal base. -/
theorem specializeZero_one_decoNormalBottomStep_total (n : Nat) :
    MvPolynomial.specializeZero 1
        (decoNormalBottomStep (n + 1) (decoBottomTotal (n + 1))) =
      decoBottomTotalAffineNormalBase n := by
  rw [decoNormalBottomStep_total_eq_affine,
    MvPolynomial.specializeZero_add, MvPolynomial.specializeZero_mul,
    MvPolynomial.specializeZero_eq_self_of_notMem_vars _ _
      (one_notMem_vars_decoBottomTotalAffineNormalBase n),
    MvPolynomial.specializeZero_X_self]
  simp

/-- Differentiating the normal affine branch in its new coordinate returns
its slope. -/
theorem pderiv_one_decoNormalBottomStep_total (n : Nat) :
    MvPolynomial.pderiv 1
        (decoNormalBottomStep (n + 1) (decoBottomTotal (n + 1))) =
      decoBottomTotalAffineSlope n := by
  rw [decoNormalBottomStep_total_eq_affine]
  simp only [map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineNormalBase n),
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineSlope n),
    zero_add, one_mul, mul_zero, add_zero]

/-- The affine base is canonically the zero-specialization of the next total
in its new coordinate. -/
theorem specializeZero_one_decoBottomTotal_add_two (n : Nat) :
    MvPolynomial.specializeZero 1 (decoBottomTotal (n + 2)) =
      decoBottomTotalAffineBase n := by
  rw [decoBottomTotal_recurrence_affine, MvPolynomial.specializeZero_add,
    MvPolynomial.specializeZero_mul,
    MvPolynomial.specializeZero_eq_self_of_notMem_vars _ _
      (one_notMem_vars_decoBottomTotalAffineBase n),
    MvPolynomial.specializeZero_X_self]
  simp

/-- The affine slope is canonically the partial derivative of the next total
in its new coordinate. -/
theorem pderiv_one_decoBottomTotal_add_two (n : Nat) :
    MvPolynomial.pderiv 1 (decoBottomTotal (n + 2)) =
      decoBottomTotalAffineSlope n := by
  rw [decoBottomTotal_recurrence_affine]
  simp only [map_add, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineBase n),
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (one_notMem_vars_decoBottomTotalAffineSlope n),
    zero_add, one_mul, mul_zero, add_zero]

/-- The affine normal base is multiaffine. -/
theorem decoBottomTotalAffineNormalBase_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalAffineNormalBase n) := by
  have hsucc : Function.Injective (fun i : Nat => i + 1) := by
    intro i j h
    lia
  unfold decoBottomTotalAffineNormalBase
  exact (decoBottomTotal_isMultiaffine (n + 1)).rename hsucc

/-- The affine exceptional base is multiaffine. -/
theorem decoBottomTotalAffineExceptionalBase_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalAffineExceptionalBase n) := by
  have haddTwo : Function.Injective (fun i : Nat => i + 2) := by
    intro i j h
    lia
  have hrename := (decoBottomTotal_isMultiaffine n).rename haddTwo
  have hfresh : 2 ∉
      (MvPolynomial.rename (fun i : Nat => i + 2)
        (decoBottomTotal n)).vars := by
    intro h
    obtain ⟨i, hi, htwo⟩ := MvPolynomial.mem_vars_rename
      (fun i : Nat => i + 2) (decoBottomTotal n) h
    have hibounds := vars_decoBottomTotal_subset_Icc n hi
    rw [Finset.mem_Icc] at hibounds
    lia
  unfold decoBottomTotalAffineExceptionalBase decoExceptionalBottomStep
  exact hrename.X_mul_of_notMem_vars hfresh

/-- The affine base is multiaffine. -/
theorem decoBottomTotalAffineBase_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalAffineBase n) := by
  unfold decoBottomTotalAffineBase
  exact (decoBottomTotalAffineNormalBase_isMultiaffine n).add
    (decoBottomTotalAffineExceptionalBase_isMultiaffine n)

/-- The affine slope is multiaffine. -/
theorem decoBottomTotalAffineSlope_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalAffineSlope n) := by
  unfold decoBottomTotalAffineSlope
  apply MvPolynomial.IsMultiaffine.rename
  · exact decoNormalBottomCore_isMultiaffine
      (decoBottomTotal_isMultiaffine (n + 1))
  · intro i j h
    lia

/-- One Deco recurrence step is Rayleigh once its exact affine-coordinate
endpoint, Wronskian, and discriminant conditions are established. -/
theorem decoBottomTotal_add_two_isRayleigh_of_affine
    (n : Nat)
    (hbase : MvPolynomial.IsRayleigh (decoBottomTotalAffineBase n))
    (hslope : MvPolynomial.IsRayleigh (decoBottomTotalAffineSlope n))
    (hcross : ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoBottomTotalAffineSlope n) (decoBottomTotalAffineBase n) i))
    (hdisc : ∀ i j x, i ≠ 1 → j ≠ 1 → MvPolynomial.eval x
      (MvPolynomial.affineRayleighDiscriminant
        (decoBottomTotalAffineBase n) (decoBottomTotalAffineSlope n) i j) ≤ 0) :
    MvPolynomial.IsRayleigh (decoBottomTotal (n + 2)) := by
  rw [decoBottomTotal_recurrence_affine]
  exact hbase.add_X_mul_of_fresh hslope
    (decoBottomTotalAffineBase_isMultiaffine n)
    (decoBottomTotalAffineSlope_isMultiaffine n)
    (one_notMem_vars_decoBottomTotalAffineBase n)
    (one_notMem_vars_decoBottomTotalAffineSlope n) hcross hdisc

end

end RealRooted.Applications.OEIS
