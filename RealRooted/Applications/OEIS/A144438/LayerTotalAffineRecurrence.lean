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

/-- The part of the rank-`n+2` recurrence independent of its new coordinate
`1`. -/
def decoBottomTotalAffineBase (n : Nat) : MvPolynomial Nat Real :=
  MvPolynomial.rename (fun i : Nat => i + 1) (decoBottomTotal (n + 1)) +
    decoExceptionalBottomStep (decoBottomTotal n)

/-- The coefficient of the new coordinate `1` in the rank-`n+2`
recurrence. -/
def decoBottomTotalAffineSlope (n : Nat) : MvPolynomial Nat Real :=
  MvPolynomial.rename (fun i : Nat => i + 1)
    (decoNormalBottomCore (n + 1) (decoBottomTotal (n + 1)))

/-- The defining two-step recurrence, collected as an affine extension in its
fresh coordinate `1`. -/
theorem decoBottomTotal_recurrence_affine (n : Nat) :
    decoBottomTotal (n + 2) =
      decoBottomTotalAffineBase n + MvPolynomial.X 1 *
        decoBottomTotalAffineSlope n := by
  rw [decoBottomTotal_recurrence]
  simp only [decoNormalBottomStep, decoBottomTotalAffineBase,
    decoBottomTotalAffineSlope]
  ring

/-- The affine base uses only the old labels `2, ..., n+2`. -/
theorem vars_decoBottomTotalAffineBase_subset_Icc (n : Nat) :
    (decoBottomTotalAffineBase n).vars ⊆ Finset.Icc 2 (n + 2) := by
  classical
  intro x hx
  unfold decoBottomTotalAffineBase at hx
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

/-- The affine base is multiaffine. -/
theorem decoBottomTotalAffineBase_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotalAffineBase n) := by
  have hsucc : Function.Injective (fun i : Nat => i + 1) := by
    intro i j h
    lia
  have haddTwo : Function.Injective (fun i : Nat => i + 2) := by
    intro i j h
    lia
  have hnormal := (decoBottomTotal_isMultiaffine (n + 1)).rename hsucc
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
  unfold decoBottomTotalAffineBase decoExceptionalBottomStep
  exact hnormal.add (hrename.X_mul_of_notMem_vars hfresh)

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
      (decoBottomTotalAffineSlope n *
          MvPolynomial.pderiv i (decoBottomTotalAffineBase n) -
        decoBottomTotalAffineBase n *
          MvPolynomial.pderiv i (decoBottomTotalAffineSlope n)))
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
