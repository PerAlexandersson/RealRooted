import RealRooted.HomogeneousOre

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Homogeneous Ore certificate examples

This module contains sequence-agnostic smoke tests for the homogeneous Ore
certificate interface.  The examples are deliberately generic and do not add a
tactic frontend.
-/

/-- Smoke test: a global real-rootedness preserver can be used as a
pencil-local preserver in one transport step. -/
theorem allComboRealRooted_step_of_global_preserver_example
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g f' g' : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hT : PreservesRealRootedOrZero T)
    (hf' : f' = T f) (hg' : g' = T g) :
    AllComboRealRooted f' g' :=
  allComboRealRooted_step_of_pencil hall
    (preservesRealRootedOnPencil_of_preservesRealRootedOrZero hT f g)
    hf' hg'

/-- Smoke test: pointwise global preservers feed the sequence transport
through the pencil-local adapter. -/
theorem allComboRealRooted_sequence_of_global_preserver_example
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : ∀ j : ℕ, PreservesRealRootedOrZero (T j))
    (hP : ∀ j : ℕ, P (j + 1) = T j (P j))
    (hQ : ∀ j : ℕ, Q (j + 1) = T j (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) :=
  allComboRealRooted_sequence_of_pencil hbase
    (preservesRealRootedOnPencilsAlong_of_preservesRealRootedOrZero hT) hP hQ

/-- A trivial normalized row certificate stream for
`T_j = id`, `ell_j = 0`, `m_j = 0`, and `k_j = 1`.

This is a sequence-agnostic smoke test for generated row certificates: it
checks that the homogeneous induced-cone backend can consume a concrete
`HomogeneousInducedConeRowsAlong` witness. -/
def homogeneousInducedConeRowsAlong_zero_id
    (P Q : ℕ → ℝ[X]) :
    HomogeneousInducedConeRowsAlong
      (fun _ => LinearMap.id) (fun _ => 0) (fun _ => 0) (fun _ => 1) P Q := by
  simpa using
    homogeneousInducedConeRowsAlong_scalar_id (fun _ : ℕ => 0)
      (fun _ : ℕ => 1) P Q

/-- Smoke test showing that the named homogeneous induced-cone backend consumes
the trivial row certificate stream. -/
theorem homogeneous_induced_two_coordinate_cone_backend_zero_id
    {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap 0 0 (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap 1 (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) :=
  homogeneous_induced_two_coordinate_cone_backend_scalar_id
    (r := fun _ : ℕ => 0) (s := fun _ : ℕ => 1) hbase
    (by simpa using hQstate) (by simpa using hQnext)

/-- Direct step-preserver for the scalar unit triangular row
`P_{j+1} = P_j + Q_j`, `Q_{j+1} = Q_j`. -/
theorem homogeneous_induced_cone_step_preservers_scalar_unit
    (P Q : ℕ → ℝ[X]) :
    HomogeneousInducedConeStepPreserversAlong
      (fun _ : ℕ => C (1 : ℝ)) (fun _ : ℕ => 0)
      (fun _ : ℕ => C (1 : ℝ)) P Q := by
  intro j hall
  exact AllComboRealRooted.linear_recombination hall
    (f := P j) (g := Q j)
    (a := 1) (b := 1) (c := 0) (d := 1)
    (by simp [oreAffineDerivativeLinearMap_apply])
    (by simp [polynomialMulLinearMap_apply])

/-- Smoke test showing that the normalized backend can consume a direct
triangular step-preserver hypothesis.  Here the scalar row
`P_{j+1} = P_j + Q_j`, `Q_{j+1} = Q_j` is supplied by the generic
all-combo linear-recombination lemma. -/
theorem homogeneous_induced_cone_step_preserver_scalar_unit_example
    {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (1 : ℝ)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (1 : ℝ)) (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) :=
  homogeneous_induced_two_coordinate_cone_backend_of_step_preservers
    hbase (homogeneous_induced_cone_step_preservers_scalar_unit P Q)
    hQstate hQnext

/-- Smoke test for the direct step-preserver closed-form `Splits` exit. -/
theorem homogeneous_induced_cone_splits_eq_combo_step_preserver_example
    {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (1 : ℝ)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (1 : ℝ)) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j) :
    ∀ j : ℕ, (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo_of_step_preservers
    hbase (homogeneous_induced_cone_step_preservers_scalar_unit P Q)
    hQstate hQnext hR

/-- Smoke test for the direct step-preserver closed-form nonzero
real-rootedness exit. -/
theorem homogeneous_induced_cone_ne_zero_splits_step_preserver_example
    {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (1 : ℝ)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (1 : ℝ)) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j)
    (hR0 : ∀ j : ℕ, R j ≠ 0) :
    ∀ j : ℕ, R j ≠ 0 ∧ (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo_of_step_preservers
    hbase (homogeneous_induced_cone_step_preservers_scalar_unit P Q)
    hQstate hQnext hR hR0

/-- Smoke test for the scalar-identity closed-form `Splits` exit. -/
theorem homogeneous_induced_cone_splits_eq_combo_scalar_id_example
    {r s u v : ℕ → ℝ} {P Q R : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (r j)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (s j)) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j) :
    ∀ j : ℕ, (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo_scalar_id
    hbase hQstate hQnext hR

/-- Smoke test for the scalar-identity closed-form nonzero real-rootedness
exit. -/
theorem homogeneous_induced_cone_ne_zero_splits_scalar_id_example
    {r s u v : ℕ → ℝ} {P Q R : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (r j)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (s j)) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j)
    (hR0 : ∀ j : ℕ, R j ≠ 0) :
    ∀ j : ℕ, R j ≠ 0 ∧ (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo_scalar_id
    hbase hQstate hQnext hR hR0

end RealRooted
