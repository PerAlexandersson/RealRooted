import RealRooted.OperatorPreservesInterlacing

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Homogeneous Ore pencil transport

This module contains the first transport layer for homogeneous Ore-cone
backends.  The statements are deliberately generic: a sequence of linear maps
acts on the current two-coordinate pencil, and the backend supplies a
pencil-local real-rootedness-preservation hypothesis for each step.

The same linear map must produce both endpoints of a step.  This is the
load-bearing condition that lets `allComboRealRooted_map_of_pencil` turn
preservation on the current pencil into preservation of all combinations at
the next state.

The normalized homogeneous Ore state transition is triangular:
`P_{j+1} = A_j P_j + Q_j` and `Q_{j+1} = k_j Q_j`.  Thus this module is a
transport layer for single-operator image steps and triangular rows that can
be identified with such image steps.  Instantiating the Ore rows themselves
still requires Ore-specific endpoint identities and pencil-local preservation
proofs.

The `_splits` consequences below are `Splits`-only statements; they do not
assert nonvanishing.  Use the `*_ne_zero_and_splits*` wrappers when the target
also needs a nonzero proof.
-/

/-- A linear map preserves real-rootedness on the pencil spanned by `f` and
`g`, with zero images allowed. -/
abbrev PreservesRealRootedOnPencil
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (f g : ℝ[X]) : Prop :=
  ∀ α β : ℝ,
    (C α * f + C β * g ≠ 0 ∧ (C α * f + C β * g).Splits) →
      T (C α * f + C β * g) = 0 ∨
        (T (C α * f + C β * g)).Splits

/-- A sequence of linear maps preserves real-rootedness on each current
two-coordinate pencil.

The hypothesis consumes the current `AllComboRealRooted` fact, since later
Ore-specialized root-window lemmas may use the current pencil data when proving
real-rootedness preservation for one step. -/
abbrev PreservesRealRootedOnPencilsAlong
    (T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]) (P Q : ℕ → ℝ[X]) : Prop :=
  ∀ j : ℕ, AllComboRealRooted (P j) (Q j) →
    PreservesRealRootedOnPencil (T j) (P j) (Q j)

/-- The identity map preserves real-rootedness on any pencil. -/
theorem preservesRealRootedOnPencil_id (f g : ℝ[X]) :
    PreservesRealRootedOnPencil LinearMap.id f g := by
  intro α β hrr
  exact Or.inr (by simpa using hrr.2)

/-- The identity map preserves real-rootedness along any sequence of pencils. -/
theorem preservesRealRootedOnPencilsAlong_id (P Q : ℕ → ℝ[X]) :
    PreservesRealRootedOnPencilsAlong (fun _ => LinearMap.id) P Q :=
  fun j _ => preservesRealRootedOnPencil_id (P j) (Q j)

/-- A global real-rootedness preserver is a preserver on every fixed pencil. -/
theorem preservesRealRootedOnPencil_of_preservesRealRootedOrZero
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : PreservesRealRootedOrZero T) (f g : ℝ[X]) :
    PreservesRealRootedOnPencil T f g :=
  fun _ _ hrr => hT _ hrr

/-- Pointwise global real-rootedness preservers preserve every sequence of
pencils along the homogeneous transport chain. -/
theorem preservesRealRootedOnPencilsAlong_of_preservesRealRootedOrZero
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hT : ∀ j : ℕ, PreservesRealRootedOrZero (T j)) :
    PreservesRealRootedOnPencilsAlong T P Q :=
  fun j _ => preservesRealRootedOnPencil_of_preservesRealRootedOrZero
    (hT j) (P j) (Q j)

/-- Multiplication by a fixed polynomial, viewed as an `ℝ`-linear map. -/
def polynomialMulLinearMap (k : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := k * p
  map_add' p q := by simp [mul_add]
  map_smul' a p := by simp [Polynomial.smul_eq_C_mul, mul_assoc, mul_comm]

@[simp]
theorem polynomialMulLinearMap_apply (k p : ℝ[X]) :
    polynomialMulLinearMap k p = k * p :=
  rfl

/-- The normalized Ore operator `ell + m * D`, viewed as an `ℝ`-linear map. -/
def oreAffineDerivativeLinearMap (ell m : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  polynomialMulLinearMap ell + (polynomialMulLinearMap m).comp Polynomial.derivative

@[simp]
theorem oreAffineDerivativeLinearMap_apply (ell m p : ℝ[X]) :
    oreAffineDerivativeLinearMap ell m p = ell * p + m * p.derivative :=
  rfl

/-- Single-step pencil transport with free endpoint names.

This is the reusable wrapper around `allComboRealRooted_map_of_pencil`: callers
may prove the endpoint identities by recurrence normalization before applying
the step. -/
theorem allComboRealRooted_step_of_pencil
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g f' g' : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hT : PreservesRealRootedOnPencil T f g)
    (hf' : f' = T f) (hg' : g' = T g) :
    AllComboRealRooted f' g' := by
  rw [hf', hg']
  exact allComboRealRooted_map_of_pencil hall hT

/-- Single-step pencil transport followed by a two-coordinate linear change.

This is the algebraic layer needed by homogeneous Ore rows whose normalized
state is obtained from a real-rootedness-preserving image pencil and then
rewritten by a triangular coordinate change. -/
theorem allComboRealRooted_step_linear_change_of_pencil
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g p q : ℝ[X]} {a b c d : ℝ}
    (hall : AllComboRealRooted f g)
    (hT : PreservesRealRootedOnPencil T f g)
    (hp : p = C a * T f + C b * T g)
    (hq : q = C c * T f + C d * T g) :
    AllComboRealRooted p q := by
  exact allComboRealRooted_linear_recombination hp hq
    (allComboRealRooted_map_of_pencil hall hT)

/-- Single triangular Ore-shaped step through a pencil-local image operator.

The row backend must prove the two endpoint identities into the image pencil;
this theorem only performs the all-combinations transport. -/
theorem allComboRealRooted_triangular_step_of_pencil
    {T A K : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]} {a b c d : ℝ}
    (hall : AllComboRealRooted f g)
    (hT : PreservesRealRootedOnPencil T f g)
    (hP : A f + g = C a * T f + C b * T g)
    (hQ : K g = C c * T f + C d * T g) :
    AllComboRealRooted (A f + g) (K g) :=
  allComboRealRooted_step_linear_change_of_pencil hall hT hP hQ

/-- Backend certificate for one triangular homogeneous Ore-shaped row.

The row backend supplies an image operator `T`, the row operators `A` and `K`,
the real two-coordinate recombination coefficients, pencil-local preservation
for `T`, and the two endpoint identities into the image pencil. -/
structure HomogeneousOreTriangularStepCertificate
    (T A K : ℝ[X] →ₗ[ℝ] ℝ[X]) (f g : ℝ[X]) where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  preserves : PreservesRealRootedOnPencil T f g
  p_image :
    A f + g = Polynomial.C a * (T f) + Polynomial.C b * (T g)
  q_image :
    K g = Polynomial.C c * (T f) + Polynomial.C d * (T g)

/-- Consume a triangular row certificate to transport all-combinations
real-rootedness across one state row. -/
theorem allComboRealRooted_triangular_step_of_certificate
    {T A K : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hrow : HomogeneousOreTriangularStepCertificate T A K f g) :
    AllComboRealRooted (A f + g) (K g) :=
  allComboRealRooted_triangular_step_of_pencil hall hrow.preserves
    hrow.p_image hrow.q_image

/-- Row certificates along a triangular homogeneous Ore-shaped state chain.

The certificate may use the current all-combinations induction hypothesis when
proving its pencil-local preservation field. -/
abbrev HomogeneousOreTriangularRowsAlong
    (T A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]) (P Q : ℕ → ℝ[X]) : Type :=
  ∀ j : ℕ, AllComboRealRooted (P j) (Q j) →
    HomogeneousOreTriangularStepCertificate (T j) (A j) (K j) (P j) (Q j)

/-- Direct all-combinations preservation for one triangular state step.

This is the fallback insertion point when a row proof proves the full
triangular step directly, rather than factoring both endpoints through one
image pencil. -/
abbrev HomogeneousOreTriangularStepPreserver
    (A K : ℝ[X] →ₗ[ℝ] ℝ[X]) (f g : ℝ[X]) : Prop :=
  AllComboRealRooted f g → AllComboRealRooted (A f + g) (K g)

/-- Direct all-combinations preservation along a triangular state chain. -/
abbrev HomogeneousOreTriangularStepPreserversAlong
    (A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]) (P Q : ℕ → ℝ[X]) : Prop :=
  ∀ j : ℕ, HomogeneousOreTriangularStepPreserver (A j) (K j) (P j) (Q j)

/-- Certificate stream specialized to the normalized homogeneous Ore state
operators `ell + m * D` and multiplication by `k`. -/
abbrev HomogeneousInducedConeRowsAlong
    (T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]) (ell m k : ℕ → ℝ[X])
    (P Q : ℕ → ℝ[X]) : Type :=
  HomogeneousOreTriangularRowsAlong T
    (fun j => oreAffineDerivativeLinearMap (ell j) (m j))
    (fun j => polynomialMulLinearMap (k j)) P Q

/-- Direct triangular step preservation specialized to the normalized
homogeneous Ore operators. -/
abbrev HomogeneousInducedConeStepPreserversAlong
    (ell m k : ℕ → ℝ[X]) (P Q : ℕ → ℝ[X]) : Prop :=
  HomogeneousOreTriangularStepPreserversAlong
    (fun j => oreAffineDerivativeLinearMap (ell j) (m j))
    (fun j => polynomialMulLinearMap (k j)) P Q

/-- Build normalized homogeneous Ore row certificates from separated
pencil-local preservation and endpoint identities.

This is the generated-row-facing constructor: row proof bodies may provide the
preserver `T_j`, the scalar two-coordinate row, and the two endpoint identities
without constructing `HomogeneousOreTriangularStepCertificate` by hand. -/
def homogeneousInducedConeRowsAlong_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q : ℕ → ℝ[X]} {a b c d : ℕ → ℝ}
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hPimage : ∀ j : ℕ,
      oreAffineDerivativeLinearMap (ell j) (m j) (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      polynomialMulLinearMap (k j) (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j)) :
    HomogeneousInducedConeRowsAlong T ell m k P Q :=
  fun j hall =>
    { a := a j
      b := b j
      c := c j
      d := d j
      preserves := hT j hall
      p_image := hPimage j
      q_image := hQimage j }

/-- Scalar triangular normalized row certificates with identity preserver.

This is a sequence-agnostic generated-row pattern:
`T_j = id`, `ell_j = C (r j)`, `m_j = 0`, and `k_j = C (s j)`. -/
def homogeneousInducedConeRowsAlong_scalar_id
    (r s : ℕ → ℝ) (P Q : ℕ → ℝ[X]) :
    HomogeneousInducedConeRowsAlong
      (fun _ => LinearMap.id) (fun j => C (r j)) (fun _ => 0)
      (fun j => C (s j)) P Q :=
  homogeneousInducedConeRowsAlong_of_pencil
    (a := r) (b := fun _ : ℕ => 1) (c := fun _ : ℕ => 0) (d := s)
    (preservesRealRootedOnPencilsAlong_id P Q)
    (by intro j; simp)
    (by intro j; simp)

/-- Transport `AllComboRealRooted` along a sequence of pencil-local preserving
linear maps. -/
theorem allComboRealRooted_sequence_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hP : ∀ j : ℕ, P (j + 1) = T j (P j))
    (hQ : ∀ j : ℕ, Q (j + 1) = T j (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  intro j
  induction j with
  | zero =>
      exact hbase
  | succ j ih =>
      exact allComboRealRooted_step_of_pencil ih (hT j ih) (hP j) (hQ j)

/-- Transport `AllComboRealRooted` along a sequence of pencil-local preserving
linear maps, allowing a real two-coordinate change after each map. -/
theorem allComboRealRooted_sequence_linear_change_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    {a b c d : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hP : ∀ j : ℕ,
      P (j + 1) = C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQ : ∀ j : ℕ,
      Q (j + 1) = C (c j) * T j (P j) + C (d j) * T j (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  intro j
  induction j with
  | zero =>
      exact hbase
  | succ j ih =>
      exact allComboRealRooted_step_linear_change_of_pencil ih (hT j ih)
        (hP j) (hQ j)

/-- Transport `AllComboRealRooted` along triangular Ore-shaped state rows.

Each row has the state form `P_{j+1} = A_j P_j + Q_j` and
`Q_{j+1} = K_j Q_j`, but the row backend supplies identities placing these
endpoints in a pencil-local image of the previous state. -/
theorem allComboRealRooted_triangular_sequence_of_pencil
    {T A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    {a b c d : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hP : ∀ j : ℕ, P (j + 1) = A j (P j) + Q j)
    (hQ : ∀ j : ℕ, Q (j + 1) = K j (Q j))
    (hPimage : ∀ j : ℕ,
      A j (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      K j (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  intro j
  induction j with
  | zero =>
      exact hbase
  | succ j ih =>
      have hPstep :
          P (j + 1) =
            C (a j) * T j (P j) + C (b j) * T j (Q j) := by
        rw [hP j, hPimage j]
      have hQstep :
          Q (j + 1) =
            C (c j) * T j (P j) + C (d j) * T j (Q j) := by
        rw [hQ j, hQimage j]
      exact allComboRealRooted_step_linear_change_of_pencil ih (hT j ih)
        hPstep hQstep

/-- Transport `AllComboRealRooted` along triangular state rows supplied by
row certificates. -/
theorem allComboRealRooted_triangular_sequence_of_certificates
    {T A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hrow : HomogeneousOreTriangularRowsAlong T A K P Q)
    (hP : ∀ j : ℕ, P (j + 1) = A j (P j) + Q j)
    (hQ : ∀ j : ℕ, Q (j + 1) = K j (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  intro j
  induction j with
  | zero =>
      exact hbase
  | succ j ih =>
      have row := hrow j ih
      have hstep :
          AllComboRealRooted (A j (P j) + Q j) (K j (Q j)) :=
        allComboRealRooted_triangular_step_of_certificate (T := T j) ih row
      simpa [hP j, hQ j] using hstep

/-- Transport `AllComboRealRooted` along triangular rows whose full
all-combinations step is supplied directly.

This theorem does not assert any operator-preserver criterion.  It only runs
the induction once each row has provided the complete triangular all-combo
step. -/
theorem allComboRealRooted_triangular_sequence_of_step_preservers
    {A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hstep : HomogeneousOreTriangularStepPreserversAlong A K P Q)
    (hP : ∀ j : ℕ, P (j + 1) = A j (P j) + Q j)
    (hQ : ∀ j : ℕ, Q (j + 1) = K j (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  intro j
  induction j with
  | zero =>
      exact hbase
  | succ j ih =>
      simpa [hP j, hQ j] using hstep j ih

/-- Named homogeneous induced two-coordinate cone backend for normalized Ore
states.

The statement is generic: generated row proofs must still supply the row
certificate stream, including the pencil-local preservation and endpoint
identities. -/
theorem homogeneous_induced_two_coordinate_cone_backend
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hrow : HomogeneousInducedConeRowsAlong T ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  refine allComboRealRooted_triangular_sequence_of_certificates
    hbase hrow ?_ hQnext
  intro j
  rw [hQstate j]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Named homogeneous induced-cone backend whose row invariant is supplied as a
direct triangular all-combinations step. -/
theorem homogeneous_induced_two_coordinate_cone_backend_of_step_preservers
    {ell m k : ℕ → ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hstep : HomogeneousInducedConeStepPreserversAlong ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) := by
  refine allComboRealRooted_triangular_sequence_of_step_preservers
    hbase hstep ?_ hQnext
  intro j
  rw [hQstate j]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Endpoint `Splits` consequence of
`homogeneous_induced_two_coordinate_cone_backend`. -/
theorem homogeneous_induced_two_coordinate_cone_backend_splits
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hrow : HomogeneousInducedConeRowsAlong T ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j)) :
    ∀ j : ℕ, (P j).Splits := fun j => by
  simpa using
    (homogeneous_induced_two_coordinate_cone_backend
      hbase hrow hQstate hQnext j 1 0)

/-- Endpoint `Splits` consequence of
`homogeneous_induced_two_coordinate_cone_backend_of_step_preservers`. -/
theorem homogeneous_induced_two_coordinate_cone_backend_splits_of_step_preservers
    {ell m k : ℕ → ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hstep : HomogeneousInducedConeStepPreserversAlong ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j)) :
    ∀ j : ℕ, (P j).Splits := fun j => by
  simpa using
    (homogeneous_induced_two_coordinate_cone_backend_of_step_preservers
      hbase hstep hQstate hQnext j 1 0)

/-- Closed-form `Splits` exit from the direct step-preserver homogeneous
induced-cone backend. -/
theorem
  homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo_of_step_preservers
    {ell m k : ℕ → ℝ[X]} {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hstep : HomogeneousInducedConeStepPreserversAlong ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j) :
    ∀ j : ℕ, (R j).Splits :=
  AllComboRealRooted.splits_sequence_of_eq_combo
    (homogeneous_induced_two_coordinate_cone_backend_of_step_preservers
      hbase hstep hQstate hQnext) hR

/-- Nonzero real-rootedness package for a closed-form exit from the direct
step-preserver homogeneous induced-cone backend. -/
theorem
  homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo_of_step_preservers
    {ell m k : ℕ → ℝ[X]} {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hstep : HomogeneousInducedConeStepPreserversAlong ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j)
    (hR0 : ∀ j : ℕ, R j ≠ 0) :
    ∀ j : ℕ, R j ≠ 0 ∧ (R j).Splits :=
  AllComboRealRooted.ne_zero_and_splits_sequence_of_eq_combo
    (homogeneous_induced_two_coordinate_cone_backend_of_step_preservers
      hbase hstep hQstate hQnext) hR hR0

/-- Closed-form `Splits` exit from the homogeneous induced-cone backend.

The target family may be any pointwise real linear combination of the carried
state `(P j, Q j)`. -/
theorem homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hrow : HomogeneousInducedConeRowsAlong T ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j) :
    ∀ j : ℕ, (R j).Splits :=
  AllComboRealRooted.splits_sequence_of_eq_combo
    (homogeneous_induced_two_coordinate_cone_backend
      hbase hrow hQstate hQnext) hR

/-- Nonzero real-rootedness package for a closed-form exit from the homogeneous
induced-cone backend. -/
theorem homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hrow : HomogeneousInducedConeRowsAlong T ell m k P Q)
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j)
    (hR0 : ∀ j : ℕ, R j ≠ 0) :
    ∀ j : ℕ, R j ≠ 0 ∧ (R j).Splits :=
  AllComboRealRooted.ne_zero_and_splits_sequence_of_eq_combo
    (homogeneous_induced_two_coordinate_cone_backend
      hbase hrow hQstate hQnext) hR hR0

/-- Named homogeneous induced-cone backend with row certificates constructed
from generated-row-facing pencil data. -/
theorem homogeneous_induced_two_coordinate_cone_backend_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q : ℕ → ℝ[X]} {a b c d : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hPimage : ∀ j : ℕ,
      oreAffineDerivativeLinearMap (ell j) (m j) (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      polynomialMulLinearMap (k j) (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) :=
  homogeneous_induced_two_coordinate_cone_backend hbase
    (homogeneousInducedConeRowsAlong_of_pencil
      (a := a) (b := b) (c := c) (d := d) hT hPimage hQimage)
    hQstate hQnext

/-- The named homogeneous induced-cone backend specialized to scalar
triangular rows with the identity preserver. -/
theorem homogeneous_induced_two_coordinate_cone_backend_scalar_id
    {r s : ℕ → ℝ} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (r j)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (s j)) (Q j)) :
    ∀ j : ℕ, AllComboRealRooted (P j) (Q j) :=
  homogeneous_induced_two_coordinate_cone_backend hbase
    (homogeneousInducedConeRowsAlong_scalar_id r s P Q) hQstate hQnext

/-- Endpoint `Splits` consequence of
`homogeneous_induced_two_coordinate_cone_backend_of_pencil`. -/
theorem homogeneous_induced_two_coordinate_cone_backend_splits_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q : ℕ → ℝ[X]} {a b c d : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hPimage : ∀ j : ℕ,
      oreAffineDerivativeLinearMap (ell j) (m j) (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      polynomialMulLinearMap (k j) (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j)) :
    ∀ j : ℕ, (P j).Splits := fun j => by
  simpa using
    (homogeneous_induced_two_coordinate_cone_backend_of_pencil
      (a := a) (b := b) (c := c) (d := d)
      hbase hT hPimage hQimage hQstate hQnext j 1 0)

/-- Closed-form `Splits` exit from generated-row-facing pencil data. -/
theorem homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q R : ℕ → ℝ[X]} {a b c d u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hPimage : ∀ j : ℕ,
      oreAffineDerivativeLinearMap (ell j) (m j) (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      polynomialMulLinearMap (k j) (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j) :
    ∀ j : ℕ, (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo
    hbase
    (homogeneousInducedConeRowsAlong_of_pencil
      (a := a) (b := b) (c := c) (d := d) hT hPimage hQimage)
    hQstate hQnext hR

/-- Nonzero real-rootedness package for a closed-form exit from
generated-row-facing pencil data. -/
theorem homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {ell m k : ℕ → ℝ[X]}
    {P Q R : ℕ → ℝ[X]} {a b c d u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hPimage : ∀ j : ℕ,
      oreAffineDerivativeLinearMap (ell j) (m j) (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      polynomialMulLinearMap (k j) (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) - oreAffineDerivativeLinearMap (ell j) (m j) (P j))
    (hQnext : ∀ j : ℕ, Q (j + 1) = polynomialMulLinearMap (k j) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j)
    (hR0 : ∀ j : ℕ, R j ≠ 0) :
    ∀ j : ℕ, R j ≠ 0 ∧ (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo
    hbase
    (homogeneousInducedConeRowsAlong_of_pencil
      (a := a) (b := b) (c := c) (d := d) hT hPimage hQimage)
    hQstate hQnext hR hR0

/-- Closed-form `Splits` exit for scalar triangular rows with the
identity preserver. -/
theorem homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo_scalar_id
    {r s : ℕ → ℝ} {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (r j)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (s j)) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j) :
    ∀ j : ℕ, (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_splits_of_eq_combo
    hbase (homogeneousInducedConeRowsAlong_scalar_id r s P Q)
    hQstate hQnext hR

/-- Nonzero real-rootedness package for a closed-form exit from scalar
triangular rows with the identity preserver. -/
theorem homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo_scalar_id
    {r s : ℕ → ℝ} {P Q R : ℕ → ℝ[X]} {u v : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hQstate : ∀ j : ℕ,
      Q j = P (j + 1) -
        oreAffineDerivativeLinearMap (C (r j)) 0 (P j))
    (hQnext : ∀ j : ℕ,
      Q (j + 1) = polynomialMulLinearMap (C (s j)) (Q j))
    (hR : ∀ j : ℕ, R j = C (u j) * P j + C (v j) * Q j)
    (hR0 : ∀ j : ℕ, R j ≠ 0) :
    ∀ j : ℕ, R j ≠ 0 ∧ (R j).Splits :=
  homogeneous_induced_two_coordinate_cone_backend_ne_zero_and_splits_of_eq_combo
    hbase (homogeneousInducedConeRowsAlong_scalar_id r s P Q)
    hQstate hQnext hR hR0

/-- Unoriented `Prec0` consequence of sequence-level pencil transport.

The conclusion is intentionally orientation-free.  Homogeneous Ore row chains
will need a later degree and leading-coefficient layer to choose a branch. -/
theorem prec0_or_revPrec0_sequence_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hP : ∀ j : ℕ, P (j + 1) = T j (P j))
    (hQ : ∀ j : ℕ, Q (j + 1) = T j (Q j)) :
    ∀ j : ℕ, Prec0 (P j) (Q j) ∨ Prec0 (Q j) (P j) := fun j =>
  prec0_or_revPrec0_of_allComboRealRooted
    (allComboRealRooted_sequence_of_pencil hbase hT hP hQ j)

/-- Unoriented `Prec0` consequence of sequence-level pencil transport with a
post-map two-coordinate linear change at each step. -/
theorem prec0_or_revPrec0_sequence_linear_change_of_pencil
    {T : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    {a b c d : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hP : ∀ j : ℕ,
      P (j + 1) = C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQ : ∀ j : ℕ,
      Q (j + 1) = C (c j) * T j (P j) + C (d j) * T j (Q j)) :
    ∀ j : ℕ, Prec0 (P j) (Q j) ∨ Prec0 (Q j) (P j) := fun j =>
  prec0_or_revPrec0_of_allComboRealRooted
    (allComboRealRooted_sequence_linear_change_of_pencil hbase hT hP hQ j)

/-- Unoriented `Prec0` consequence of triangular Ore-shaped state transport. -/
theorem prec0_or_revPrec0_triangular_sequence_of_pencil
    {T A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    {a b c d : ℕ → ℝ}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hT : PreservesRealRootedOnPencilsAlong T P Q)
    (hP : ∀ j : ℕ, P (j + 1) = A j (P j) + Q j)
    (hQ : ∀ j : ℕ, Q (j + 1) = K j (Q j))
    (hPimage : ∀ j : ℕ,
      A j (P j) + Q j =
        C (a j) * T j (P j) + C (b j) * T j (Q j))
    (hQimage : ∀ j : ℕ,
      K j (Q j) =
        C (c j) * T j (P j) + C (d j) * T j (Q j)) :
    ∀ j : ℕ, Prec0 (P j) (Q j) ∨ Prec0 (Q j) (P j) := fun j =>
  prec0_or_revPrec0_of_allComboRealRooted
    (allComboRealRooted_triangular_sequence_of_pencil
      hbase hT hP hQ hPimage hQimage j)

/-- Unoriented `Prec0` consequence of triangular row-certificate transport. -/
theorem prec0_or_revPrec0_triangular_sequence_of_certificates
    {T A K : ℕ → ℝ[X] →ₗ[ℝ] ℝ[X]} {P Q : ℕ → ℝ[X]}
    (hbase : AllComboRealRooted (P 0) (Q 0))
    (hrow : HomogeneousOreTriangularRowsAlong T A K P Q)
    (hP : ∀ j : ℕ, P (j + 1) = A j (P j) + Q j)
    (hQ : ∀ j : ℕ, Q (j + 1) = K j (Q j)) :
    ∀ j : ℕ, Prec0 (P j) (Q j) ∨ Prec0 (Q j) (P j) := fun j =>
  prec0_or_revPrec0_of_allComboRealRooted
    (allComboRealRooted_triangular_sequence_of_certificates
      hbase hrow hP hQ j)

end RealRooted
