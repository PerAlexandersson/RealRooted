import RealRooted.HomogeneousStability
import RealRooted.Applications.OEIS.A144438.ExceptionalHistory

/-!
# Exact stable layers for the deco construction

This file defines the polynomial attached to one fixed exceptional history.
The normal one-step operator is the nonnegative directional-derivative pencil,
followed by multiplication by the homogenizing variable.  The exceptional
two-step operator only shifts the old variables and multiplies by `s * u₂`.

Every operator-defined layer is homogeneous and multivariate real stable, as
is its specialization at `s = 1`.  No conclusion is drawn about the sum of
different exceptional layers.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- Coordinates for a height-`n+2` exact layer: `none` represents `s`, and
`some i` represents `u_(i+1)`. -/
abbrev DecoLayerCoord (n : ℕ) := Option (Fin n)

/-- Embed the ordinary coordinate `u_(i+1)` into its positive integer label. -/
def decoLayerBottomEmbedding (n : Nat) : Fin n ↪ Nat where
  toFun i := i.1 + 1
  inj' := by
    intro i j hij
    apply Fin.ext
    lia

@[simp] theorem decoLayerBottomEmbedding_apply {n : Nat} (i : Fin n) :
    decoLayerBottomEmbedding n i = i.1 + 1 := rfl

@[simp] theorem decoLayerBottomEmbedding_succ {n : Nat} (i : Fin n) :
    decoLayerBottomEmbedding (n + 1) i.succ =
      decoLayerBottomEmbedding n i + 1 := by
  rfl

@[simp] theorem decoLayerBottomEmbedding_succ_succ {n : Nat} (i : Fin n) :
    decoLayerBottomEmbedding (n + 2) i.succ.succ =
      decoLayerBottomEmbedding n i + 2 := by
  rfl

/-- Relabel the old bottom variables upward by one in a normal step. -/
def decoNormalRename {n : ℕ} : DecoLayerCoord n → DecoLayerCoord (n + 1)
  | none => none
  | some i => some i.succ

/-- Relabel the old bottom variables upward by two in an exceptional step. -/
def decoExceptionalRename {n : ℕ} :
    DecoLayerCoord n → DecoLayerCoord (n + 2)
  | none => none
  | some i => some i.succ.succ

/-- The normal-step relabeling does not identify old coordinates. -/
theorem decoNormalRename_injective {n : ℕ} :
    Function.Injective (decoNormalRename : DecoLayerCoord n →
      DecoLayerCoord (n + 1)) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => simp [decoNormalRename] at hij
  | some i =>
      cases j with
      | none => simp [decoNormalRename] at hij
      | some j =>
          simp only [decoNormalRename, Option.some.injEq, Fin.succ_inj] at hij
          simp [hij]

/-- The exceptional-step relabeling does not identify old coordinates. -/
theorem decoExceptionalRename_injective {n : ℕ} :
    Function.Injective (decoExceptionalRename : DecoLayerCoord n →
      DecoLayerCoord (n + 2)) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j => simp [decoExceptionalRename] at hij
  | some i =>
      cases j with
      | none => simp [decoExceptionalRename] at hij
      | some j =>
          simp only [decoExceptionalRename, Option.some.injEq, Fin.succ_inj] at hij
          simp [hij]

/-- The normal one-step operator `f ↦ s (f + u₁ Df)`, where `D` is the
sum of the partial derivatives in all old coordinates. -/
def decoNormalLayerStep {R : Type*} [CommSemiring R] {n : ℕ}
    (P : MvPolynomial (DecoLayerCoord n) R) :
    MvPolynomial (DecoLayerCoord (n + 1)) R :=
  MvPolynomial.X none *
    (MvPolynomial.rename decoNormalRename P + MvPolynomial.X (some 0) *
      MvPolynomial.rename decoNormalRename
        (∑ i : DecoLayerCoord n, MvPolynomial.pderiv i P))

/-- The exceptional two-step operator `f ↦ s u₂ f` after shifting the
old bottom-variable indices by two. -/
def decoExceptionalLayerStep {R : Type*} [CommSemiring R] {n : ℕ}
    (P : MvPolynomial (DecoLayerCoord n) R) :
    MvPolynomial (DecoLayerCoord (n + 2)) R :=
  MvPolynomial.X none * MvPolynomial.X (some 1) *
    MvPolynomial.rename decoExceptionalRename P

/-- Dehomogenizing the normal layer step gives the ordinary-variable Euler
derivative recurrence. -/
theorem dehomogenize_decoNormalLayerStep {R : Type*} [CommRing R] {n : Nat}
    {P : MvPolynomial (DecoLayerCoord n) R}
    (hP : P.IsHomogeneous (n + 1)) :
    MvPolynomial.dehomogenize (decoNormalLayerStep P) =
      MvPolynomial.rename Fin.succ (MvPolynomial.dehomogenize P) +
        MvPolynomial.X 0 * MvPolynomial.rename Fin.succ
          (MvPolynomial.C (n + 1 : R) * MvPolynomial.dehomogenize P -
            MvPolynomial.eulerOperator (MvPolynomial.dehomogenize P) +
            ∑ i : Fin n,
              MvPolynomial.pderiv i (MvPolynomial.dehomogenize P)) := by
  have hnormal :
      (decoNormalRename : DecoLayerCoord n → DecoLayerCoord (n + 1)) =
        Option.map Fin.succ := by
    funext i
    cases i <;> rfl
  rw [decoNormalLayerStep, map_mul, MvPolynomial.dehomogenize_X_none,
    one_mul, map_add, map_mul, MvPolynomial.dehomogenize_X_some,
    hnormal, MvPolynomial.dehomogenize_rename_option_map, map_sum,
    Fintype.sum_option, map_add]
  simp_rw [MvPolynomial.dehomogenize_rename_option_map]
  rw [hP.dehomogenize_pderiv_none, map_sum]
  simp_rw [MvPolynomial.dehomogenize_rename_option_map,
    MvPolynomial.dehomogenize_pderiv_some]
  simp

/-- Dehomogenizing the exceptional layer step shifts the old ordinary
variables by two and adjoins the new bottom variable `u₂`. -/
theorem dehomogenize_decoExceptionalLayerStep {R : Type*} [CommSemiring R]
    {n : Nat} (P : MvPolynomial (DecoLayerCoord n) R) :
    MvPolynomial.dehomogenize (decoExceptionalLayerStep P) =
      MvPolynomial.X 1 *
        MvPolynomial.rename (fun i => i.succ.succ)
          (MvPolynomial.dehomogenize P) := by
  have hexceptional :
      (decoExceptionalRename : DecoLayerCoord n → DecoLayerCoord (n + 2)) =
        Option.map (fun i => i.succ.succ) := by
    funext i
    cases i <;> rfl
  rw [decoExceptionalLayerStep, map_mul, map_mul,
    MvPolynomial.dehomogenize_X_none, one_mul,
    MvPolynomial.dehomogenize_X_some, hexceptional,
    MvPolynomial.dehomogenize_rename_option_map]

/-- Embedding ordinary layer coordinates into positive natural labels
commutes with an exceptional step. -/
theorem rename_decoLayerBottomEmbedding_dehomogenize_exceptional
    {R : Type*} [CommSemiring R] {n : Nat}
    (P : MvPolynomial (DecoLayerCoord n) R) :
    MvPolynomial.rename (decoLayerBottomEmbedding (n + 2))
        (MvPolynomial.dehomogenize (decoExceptionalLayerStep P)) =
      MvPolynomial.X 2 *
        MvPolynomial.rename (fun i : Nat => i + 2)
          (MvPolynomial.rename (decoLayerBottomEmbedding n)
            (MvPolynomial.dehomogenize P)) := by
  rw [dehomogenize_decoExceptionalLayerStep, map_mul,
    MvPolynomial.rename_X, MvPolynomial.rename_rename,
    MvPolynomial.rename_rename]
  congr 1

/-- A normal step raises the homogeneous degree by one. -/
theorem decoNormalLayerStep_isHomogeneous {R : Type*}
    [CommSemiring R] {n : ℕ} {P : MvPolynomial (DecoLayerCoord n) R}
    (hP : P.IsHomogeneous (n + 1)) :
    (decoNormalLayerStep P).IsHomogeneous (n + 2) := by
  have hderiv :
      (∑ i : DecoLayerCoord n, MvPolynomial.pderiv i P).IsHomogeneous n := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa using hP.pderiv (i := i)
  have hpencil :
      (MvPolynomial.rename decoNormalRename P + MvPolynomial.X (some 0) *
        MvPolynomial.rename decoNormalRename
          (∑ i : DecoLayerCoord n, MvPolynomial.pderiv i P)).IsHomogeneous
            (n + 1) := by
    apply hP.rename_isHomogeneous.add
    simpa [Nat.add_comm] using
      (MvPolynomial.isHomogeneous_X R (some 0)).mul
        hderiv.rename_isHomogeneous
  change (MvPolynomial.X none *
    (MvPolynomial.rename decoNormalRename P + MvPolynomial.X (some 0) *
      MvPolynomial.rename decoNormalRename
        (∑ i : DecoLayerCoord n, MvPolynomial.pderiv i P))).IsHomogeneous
          (n + 2)
  have hproduct := (MvPolynomial.isHomogeneous_X R none).mul hpencil
  simpa only [show 1 + (n + 1) = n + 2 by lia] using hproduct

/-- An exceptional step raises the homogeneous degree by two. -/
theorem decoExceptionalLayerStep_isHomogeneous {R : Type*}
    [CommSemiring R] {n : ℕ} {P : MvPolynomial (DecoLayerCoord n) R}
    (hP : P.IsHomogeneous (n + 1)) :
    (decoExceptionalLayerStep P).IsHomogeneous (n + 3) := by
  have hrename :
      (MvPolynomial.rename decoExceptionalRename P).IsHomogeneous (n + 1) :=
    hP.rename_isHomogeneous
  change (MvPolynomial.X none * MvPolynomial.X (some 1) *
    MvPolynomial.rename decoExceptionalRename P).IsHomogeneous (n + 3)
  have hproduct := ((MvPolynomial.isHomogeneous_X R none).mul
    (MvPolynomial.isHomogeneous_X R (some 1))).mul hrename
  simpa only [show 1 + 1 + (n + 1) = n + 3 by lia] using hproduct

/-- The normal exact-layer operator preserves multivariate real stability. -/
theorem decoNormalLayerStep_mvRealStable {n : ℕ}
    {P : MvPolynomial (DecoLayerCoord n) ℝ} (hP : MvRealStable P) :
    MvRealStable (decoNormalLayerStep P) := by
  apply (MvRealStable.X none).mul
  exact hP.sum_pderiv_pencil_rename decoNormalRename (some 0)

/-- The exceptional exact-layer operator preserves multivariate real
stability. -/
theorem decoExceptionalLayerStep_mvRealStable {n : ℕ}
    {P : MvPolynomial (DecoLayerCoord n) ℝ} (hP : MvRealStable P) :
    MvRealStable (decoExceptionalLayerStep P) := by
  exact ((MvRealStable.X none).mul (MvRealStable.X (some 1))).mul
    (hP.rename decoExceptionalRename)

/-- Exact layer generated by a proposed set of exceptional starts.  At the
last available start, membership selects the exceptional two-step; otherwise
the recursion takes the normal one-step. -/
def decoExactLayerFromStarts :
    (n : ℕ) → Finset ℕ → MvPolynomial (DecoLayerCoord n) ℝ
  | 0, _ => MvPolynomial.X none
  | 1, _ => decoNormalLayerStep (MvPolynomial.X none)
  | n + 2, R =>
      if n + 3 ∈ R then
        decoExceptionalLayerStep
          (decoExactLayerFromStarts n (R.erase (n + 3)))
      else
        decoNormalLayerStep (decoExactLayerFromStarts (n + 1) R)
termination_by n => n

/-- The operator-defined exact layer for a height-`n+2` history. -/
def decoExactLayer {n : ℕ} (H : DecoExceptionalHistory (n + 2)) :
    MvPolynomial (DecoLayerCoord n) ℝ :=
  decoExactLayerFromStarts n H.starts

@[simp] theorem decoExactLayer_seed :
    decoExactLayer DecoExceptionalHistory.seed =
      (MvPolynomial.X none : MvPolynomial (DecoLayerCoord 0) ℝ) := by
  simp [decoExactLayer, decoExactLayerFromStarts]

/-- The exact layer of a normal extension is the normal operator applied to
the old exact layer. -/
@[simp] theorem decoExactLayer_normal {n : ℕ}
    (H : DecoExceptionalHistory (n + 2)) :
    decoExactLayer (n := n + 1) (DecoExceptionalHistory.normal H) =
      decoNormalLayerStep (decoExactLayer H) := by
  cases n with
  | zero => simp [decoExactLayer, decoExactLayerFromStarts]
  | succ n =>
      have hlast : n + 3 ∉ H.starts := by
        intro hmem
        have := (DecoExceptionalHistory.mem_bounds H hmem).2
        lia
      change decoExactLayerFromStarts (n + 2) H.starts =
        decoNormalLayerStep (decoExactLayerFromStarts (n + 1) H.starts)
      rw [decoExactLayerFromStarts, if_neg hlast]

/-- The exact layer of an exceptional extension is the exceptional operator
applied to the old exact layer. -/
@[simp] theorem decoExactLayer_exceptional {n : ℕ}
    (H : DecoExceptionalHistory (n + 2)) :
    decoExactLayer (n := n + 2) (DecoExceptionalHistory.exceptional H) =
      decoExceptionalLayerStep (decoExactLayer H) := by
  change decoExactLayerFromStarts (n + 2) (insert (n + 3) H.starts) =
    decoExceptionalLayerStep (decoExactLayerFromStarts n H.starts)
  rw [decoExactLayerFromStarts, if_pos (Finset.mem_insert_self _ _),
    Finset.erase_insert]
  intro hmem
  have := (DecoExceptionalHistory.mem_bounds H hmem).2
  lia

/-- Every proposed exceptional-start set generates a homogeneous layer of
the expected degree. -/
theorem decoExactLayerFromStarts_isHomogeneous (n : ℕ) (R : Finset ℕ) :
    (decoExactLayerFromStarts n R).IsHomogeneous (n + 1) := by
  induction n using Nat.twoStepInduction generalizing R with
  | zero => simpa [decoExactLayerFromStarts] using
      (MvPolynomial.isHomogeneous_X ℝ (none : DecoLayerCoord 0))
  | one =>
      simpa [decoExactLayerFromStarts] using
        decoNormalLayerStep_isHomogeneous
          (MvPolynomial.isHomogeneous_X ℝ (none : DecoLayerCoord 0))
  | more n ih0 ih1 =>
      rw [decoExactLayerFromStarts]
      split
      · exact decoExceptionalLayerStep_isHomogeneous (ih0 _)
      · exact decoNormalLayerStep_isHomogeneous (ih1 _)

/-- Every proposed exceptional-start set generates a multivariate real-stable
layer. -/
theorem decoExactLayerFromStarts_mvRealStable (n : ℕ) (R : Finset ℕ) :
    MvRealStable (decoExactLayerFromStarts n R) := by
  induction n using Nat.twoStepInduction generalizing R with
  | zero => simpa [decoExactLayerFromStarts] using
      (MvRealStable.X (none : DecoLayerCoord 0))
  | one =>
      simpa [decoExactLayerFromStarts] using
        decoNormalLayerStep_mvRealStable
          (MvRealStable.X (none : DecoLayerCoord 0))
  | more n ih0 ih1 =>
      rw [decoExactLayerFromStarts]
      split
      · exact decoExceptionalLayerStep_mvRealStable (ih0 _)
      · exact decoNormalLayerStep_mvRealStable (ih1 _)

/-- Every history-indexed exact layer has homogeneous degree `n+1`. -/
theorem decoExactLayer_isHomogeneous {n : ℕ}
    (H : DecoExceptionalHistory (n + 2)) :
    (decoExactLayer H).IsHomogeneous (n + 1) :=
  decoExactLayerFromStarts_isHomogeneous n H.starts

/-- Every history-indexed exact layer is multivariate real stable. -/
theorem decoExactLayer_mvRealStable {n : ℕ}
    (H : DecoExceptionalHistory (n + 2)) :
    MvRealStable (decoExactLayer H) :=
  decoExactLayerFromStarts_mvRealStable n H.starts

/-- Set the homogenizing coordinate `s` to one and remove it from the
coordinate type. -/
def decoExactLayerDehomogenized {n : ℕ}
    (H : DecoExceptionalHistory (n + 2)) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.dehomogenize (decoExactLayer H)

/-- Every dehomogenized exact layer is multivariate real stable. -/
theorem decoExactLayerDehomogenized_mvRealStable {n : ℕ}
    (H : DecoExceptionalHistory (n + 2)) :
    MvRealStable (decoExactLayerDehomogenized H) := by
  exact (decoExactLayer_mvRealStable H).dehomogenize
    (decoExactLayer_isHomogeneous H)

end


end RealRooted.Applications.OEIS
