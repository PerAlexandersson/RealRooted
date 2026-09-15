import RealRooted.Applications.OEIS.A144438.LayerTotalCompanionCoreRecurrence
import RealRooted.Mathlib.Algebra.QuadraticDiscriminant
import RealRooted.Multiaffine.AffineLineRestriction

/-!
# Fresh-coordinate quadratic for the Deco companion core rows

This file decomposes the finite successor core rows along their remaining
fresh coordinate.  The three resulting endpoint Wronskian coefficients and
their discriminant are exact algebraic data; no sign claim is made here.
-/

namespace RealRooted.Applications.OEIS

noncomputable section

/-- The zero-section of the companion extension core in its fresh coordinate. -/
def decoBottomTotalCompanionExtensionCoreZero (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.specializeZero 0
    (decoBottomTotalCompanionExtensionCore n)

/-- The slope of the companion extension core in its fresh coordinate. -/
def decoBottomTotalCompanionExtensionCoreSlope (n : Nat) :
    MvPolynomial Nat Real :=
  MvPolynomial.pderiv 0 (decoBottomTotalCompanionExtensionCore n)

/-- The fresh-coordinate derivative of the total extension is its companion
core. -/
theorem pderiv_zero_decoBottomTotalCompanionTotalExtension (n : Nat) :
    MvPolynomial.pderiv 0
        (decoBottomTotalCompanionTotalExtension n) =
      decoBottomTotalCompanionCore n := by
  unfold decoBottomTotalCompanionTotalExtension
  rw [map_add, MvPolynomial.pderiv_eq_zero_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n),
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars
      (zero_notMem_vars_decoBottomTotalCompanionCore n)]
  ring

/-- The fresh-coordinate slope of the extension core is the affine Euler core
of the preceding companion core, with coefficient lowered by one. -/
theorem decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore
    (n : Nat) :
    decoBottomTotalCompanionExtensionCoreSlope n =
      MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
          (decoBottomTotalCompanionCore n) := by
  unfold decoBottomTotalCompanionExtensionCoreSlope
    decoBottomTotalCompanionExtensionCore
  let i : Fin (n + 2) := ⟨0, by lia⟩
  have hderiv : MvPolynomial.pderiv 0
        (MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
            (decoBottomTotalCompanionTotalExtension n)) =
      MvPolynomial.affineEulerCore
        (Fin.valEmbedding : Fin (n + 2) ↪ Nat) ((n + 3 : Real) - 1)
          (MvPolynomial.pderiv 0
            (decoBottomTotalCompanionTotalExtension n)) := by
    simpa [i] using MvPolynomial.pderiv_affineEulerCore
      (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
        (n + 3 : Real) (decoBottomTotalCompanionTotalExtension n) i
  rw [hderiv, pderiv_zero_decoBottomTotalCompanionTotalExtension]
  congr 2
  ring

/-- The extension core splits into the affine Euler core of the companion,
the preceding companion core, and the fresh-coordinate slope. -/
theorem decoBottomTotalCompanionExtensionCore_eq_base_add_X_mul_slope
    (n : Nat) :
    decoBottomTotalCompanionExtensionCore n =
      MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
          (decoBottomTotalWronskianCompanion n) +
        decoBottomTotalCompanionCore n +
        MvPolynomial.X 0 *
          decoBottomTotalCompanionExtensionCoreSlope n := by
  rw [decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore]
  unfold decoBottomTotalCompanionExtensionCore
    decoBottomTotalCompanionTotalExtension
  let i : Fin (n + 2) := ⟨0, by lia⟩
  have h := MvPolynomial.affineEulerCore_add_X_mul
    (Fin.valEmbedding : Fin (n + 2) ↪ Nat) Fin.valEmbedding.injective
      (n + 3 : Real) (decoBottomTotalWronskianCompanion n)
        (decoBottomTotalCompanionCore n) i
  have hc : (n + 3 : Real) - 1 = (n + 2 : Real) := by ring
  rw [hc] at h
  simpa [i] using h

/-- The constant coefficient of a successor core row in the fresh
coordinate. -/
def decoBottomTotalCompanionSuccessorCoreRowConstant
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionExtensionCoreZero n)
    (decoBottomTotalWronskianCompanion n) (i + 1 : Nat)

/-- The linear coefficient of a successor core row in the fresh coordinate. -/
def decoBottomTotalCompanionSuccessorCoreRowLinear
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionExtensionCoreZero n)
      (decoBottomTotalCompanionSlope n) (i + 1 : Nat) +
    MvPolynomial.coordinateWronskian
      (decoBottomTotalCompanionExtensionCoreSlope n)
      (decoBottomTotalWronskianCompanion n) (i + 1 : Nat)

/-- The quadratic coefficient of a successor core row in the fresh
coordinate. -/
def decoBottomTotalCompanionSuccessorCoreRowQuadratic
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  MvPolynomial.coordinateWronskian
    (decoBottomTotalCompanionExtensionCoreSlope n)
    (decoBottomTotalCompanionSlope n) (i + 1 : Nat)

/-- The polynomial discriminant of the fresh-coordinate successor core row. -/
def decoBottomTotalCompanionSuccessorCoreRowDiscriminant
    (n : Nat) (i : Fin (n + 1)) : MvPolynomial Nat Real :=
  decoBottomTotalCompanionSuccessorCoreRowLinear n i ^ 2 -
    MvPolynomial.C 4 *
      decoBottomTotalCompanionSuccessorCoreRowQuadratic n i *
        decoBottomTotalCompanionSuccessorCoreRowConstant n i

/-- The companion extension core is affine in coordinate `0`, with the named
zero-section and slope. -/
theorem decoBottomTotalCompanionExtensionCore_eq_zero_add_X_mul_slope
    (n : Nat) :
    decoBottomTotalCompanionExtensionCore n =
      decoBottomTotalCompanionExtensionCoreZero n +
        MvPolynomial.X 0 *
          decoBottomTotalCompanionExtensionCoreSlope n := by
  exact MvPolynomial.IsMultiaffine.eq_specializeZero_add_X_mul_pderiv
    (decoBottomTotalCompanionExtensionCore_isMultiaffine n) 0

/-- The zero-section of the extension core is the companion affine Euler
core plus the preceding companion core. -/
theorem decoBottomTotalCompanionExtensionCoreZero_eq_affineEulerCore_add
    (n : Nat) :
    decoBottomTotalCompanionExtensionCoreZero n =
      MvPolynomial.affineEulerCore
          (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
          (decoBottomTotalWronskianCompanion n) +
        decoBottomTotalCompanionCore n := by
  have h :=
    decoBottomTotalCompanionExtensionCore_eq_zero_add_X_mul_slope n
  rw [decoBottomTotalCompanionExtensionCore_eq_base_add_X_mul_slope] at h
  exact (add_right_cancel h).symm

/-- The constant row coefficient splits into an affine Euler row of the
companion and the current companion-data Wronskian. -/
theorem decoBottomTotalCompanionSuccessorCoreRowConstant_eq_add
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowConstant n i =
      MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 3 : Real)
            (decoBottomTotalWronskianCompanion n))
          (decoBottomTotalWronskianCompanion n) (i + 1 : Nat) +
        MvPolynomial.coordinateWronskian
          (decoBottomTotalCompanionCore n)
          (decoBottomTotalWronskianCompanion n) (i + 1 : Nat) := by
  unfold decoBottomTotalCompanionSuccessorCoreRowConstant
  rw [decoBottomTotalCompanionExtensionCoreZero_eq_affineEulerCore_add,
    MvPolynomial.coordinateWronskian_add_left]

/-- The quadratic row coefficient splits into a mixed core/total row and an
affine Euler row of the preceding companion core. -/
theorem decoBottomTotalCompanionSuccessorCoreRowQuadratic_eq_add
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRowQuadratic n i =
      MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
            (decoBottomTotalCompanionCore n))
          (decoBottomTotal (n + 1)) (i + 1 : Nat) +
        MvPolynomial.coordinateWronskian
          (MvPolynomial.affineEulerCore
            (Fin.valEmbedding : Fin (n + 2) ↪ Nat) (n + 2 : Real)
            (decoBottomTotalCompanionCore n))
          (decoBottomTotalCompanionCore n) (i + 1 : Nat) := by
  unfold decoBottomTotalCompanionSuccessorCoreRowQuadratic
    decoBottomTotalCompanionSlope
  rw [decoBottomTotalCompanionExtensionCoreSlope_eq_affineEulerCore,
    MvPolynomial.coordinateWronskian_add_right]

/-- Each successor core row is exactly quadratic in the remaining fresh
coordinate, with the three named endpoint-Wronskian coefficients. -/
theorem decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic
    (n : Nat) (i : Fin (n + 1)) :
    decoBottomTotalCompanionSuccessorCoreRow n i =
      decoBottomTotalCompanionSuccessorCoreRowConstant n i +
        MvPolynomial.X 0 *
          decoBottomTotalCompanionSuccessorCoreRowLinear n i +
        MvPolynomial.X 0 ^ 2 *
          decoBottomTotalCompanionSuccessorCoreRowQuadratic n i := by
  rw [← coordinateWronskian_companionExtensionCore_successorExtension,
    decoBottomTotalCompanionExtensionCore_eq_zero_add_X_mul_slope]
  unfold decoBottomTotalCompanionSuccessorExtension
    decoBottomTotalCompanionSuccessorCoreRowConstant
    decoBottomTotalCompanionSuccessorCoreRowLinear
    decoBottomTotalCompanionSuccessorCoreRowQuadratic
  exact MvPolynomial.coordinateWronskian_add_X_mul_add_X_mul_of_ne
    _ _ _ _ (i + 1 : Nat) 0 (by lia)

/-- Evaluation of a successor core row is the corresponding scalar quadratic
in the fresh coordinate. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic
    (n : Nat) (i : Fin (n + 1)) (x : Nat → Real) :
    MvPolynomial.eval x (decoBottomTotalCompanionSuccessorCoreRow n i) =
      MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowConstant n i) +
        x 0 * MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowLinear n i) +
        x 0 ^ 2 * MvPolynomial.eval x
          (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i) := by
  rw [decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, map_pow]

/-- The core zero-section is independent of its specialized coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionExtensionCoreZero
    (n : Nat) :
    0 ∉ (decoBottomTotalCompanionExtensionCoreZero n).vars := by
  intro h
  have herase := MvPolynomial.vars_specializeZero_subset_erase
    (decoBottomTotalCompanionExtensionCore n) 0 h
  exact (Finset.mem_erase.mp herase).1 rfl

/-- The core slope is independent of its differentiated coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionExtensionCoreSlope
    (n : Nat) :
    0 ∉ (decoBottomTotalCompanionExtensionCoreSlope n).vars := by
  exact MvPolynomial.IsMultiaffine.notMem_vars_pderiv_self
    (decoBottomTotalCompanionExtensionCore_isMultiaffine n) 0

/-- The constant row coefficient is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowConstant n i).vars := by
  unfold decoBottomTotalCompanionSuccessorCoreRowConstant
  exact MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreZero n)
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n) (i + 1 : Nat)

/-- The linear row coefficient is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowLinear n i).vars := by
  have hleft := MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreZero n)
    (zero_notMem_vars_decoBottomTotalCompanionSlope n) (i + 1 : Nat)
  have hright := MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreSlope n)
    (zero_notMem_vars_decoBottomTotalWronskianCompanion n) (i + 1 : Nat)
  intro h
  exact (Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ h)).elim
    hleft hright

/-- The quadratic row coefficient is independent of the fresh coordinate. -/
theorem zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic
    (n : Nat) (i : Fin (n + 1)) :
    0 ∉ (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i).vars := by
  unfold decoBottomTotalCompanionSuccessorCoreRowQuadratic
  exact MvPolynomial.notMem_vars_coordinateWronskian_of_notMem_vars
    (zero_notMem_vars_decoBottomTotalCompanionExtensionCoreSlope n)
    (zero_notMem_vars_decoBottomTotalCompanionSlope n) (i + 1 : Nat)

/-- Global nonnegativity of a successor core row is exactly nonnegativity of
its leading and constant coefficients together with nonpositivity of its
fresh-coordinate discriminant. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
    (n : Nat) (i : Fin (n + 1)) :
    (∀ x, 0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      (∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)) ∧
      (∀ x, 0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowConstant n i)) ∧
      ∀ x, MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0 := by
  have hconstant :=
    zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowConstant n i
  have hlinear :=
    zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowLinear n i
  have hquadratic :=
    zero_notMem_vars_decoBottomTotalCompanionSuccessorCoreRowQuadratic n i
  constructor
  · intro h
    have hscalar (x : Nat → Real) : ∀ t : Real,
        0 ≤ MvPolynomial.eval x
              (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i) *
            (t * t) +
          MvPolynomial.eval x
              (decoBottomTotalCompanionSuccessorCoreRowLinear n i) * t +
          MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowConstant n i) := by
      intro t
      have ht := h (Function.update x 0 t)
      rw [eval_decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic,
        MvPolynomial.eval_update_eq_of_notMem_vars hconstant,
        MvPolynomial.eval_update_eq_of_notMem_vars hlinear,
        MvPolynomial.eval_update_eq_of_notMem_vars hquadratic] at ht
      simp only [Function.update, dite_true] at ht
      simpa only [pow_two, mul_comm,
        add_comm, add_left_comm, add_assoc] using ht
    refine ⟨fun x => quadratic_leadingCoeff_nonneg (hscalar x), ?_, ?_⟩
    · intro x
      simpa using hscalar x 0
    · intro x
      have hdisc := discrim_le_zero (hscalar x)
      simpa [decoBottomTotalCompanionSuccessorCoreRowDiscriminant,
        discrim] using hdisc
  · rintro ⟨hquadraticNonneg, hconstantNonneg, hdisc⟩ x
    have hdiscEval :
        discrim
          (MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i))
          (MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowLinear n i))
          (MvPolynomial.eval x
            (decoBottomTotalCompanionSuccessorCoreRowConstant n i)) ≤ 0 := by
      simpa [decoBottomTotalCompanionSuccessorCoreRowDiscriminant,
        discrim] using hdisc x
    have hnonneg := quadratic_nonneg_of_nonneg_of_discrim_nonpos
      (hquadraticNonneg x) (hconstantNonneg x) hdiscEval (x 0)
    rw [eval_decoBottomTotalCompanionSuccessorCoreRow_eq_quadratic]
    simpa only [pow_two, mul_comm, add_comm, add_left_comm, add_assoc]
      using hnonneg

/-- The exact finite coefficient conditions for nonnegativity of every
successor core row.  This packages proof obligations and does not assert that
they hold. -/
structure DecoBottomTotalCompanionSuccessorCoreQuadraticData
    (n : Nat) : Prop where
  quadratic_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowQuadratic n i)
  constant_nonneg : ∀ i : Fin (n + 1), ∀ x,
    0 ≤ MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowConstant n i)
  discriminant_nonpos : ∀ i : Fin (n + 1), ∀ x,
    MvPolynomial.eval x
      (decoBottomTotalCompanionSuccessorCoreRowDiscriminant n i) ≤ 0

/-- The finite successor core rows are nonnegative exactly when their bundled
quadratic coefficient data holds. -/
theorem eval_decoBottomTotalCompanionSuccessorCoreRows_nonneg_iff
    (n : Nat) :
    (∀ i : Fin (n + 1), ∀ x,
      0 ≤ MvPolynomial.eval x
        (decoBottomTotalCompanionSuccessorCoreRow n i)) ↔
      DecoBottomTotalCompanionSuccessorCoreQuadraticData n := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
        n i).mp (h i) |>.1
    · intro i
      exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
        n i).mp (h i) |>.2.1
    · intro i
      exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
        n i).mp (h i) |>.2.2
  · intro h i
    exact (eval_decoBottomTotalCompanionSuccessorCoreRow_nonneg_iff
      n i).mpr ⟨h.quadratic_nonneg i, h.constant_nonneg i,
        h.discriminant_nonpos i⟩

end

end RealRooted.Applications.OEIS
