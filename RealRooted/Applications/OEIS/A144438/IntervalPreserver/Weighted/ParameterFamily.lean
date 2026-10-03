import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.FirstContactAlgebra

/-!
# Unequal input-root parameters for the weighted A144438 transform

We package products of affine input factors, their weighted transform and
companion, coordinate replacement, and the generic strict insertion step.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- A monic input with labeled roots `-a i`, restricted to a finite set of
labels. -/
def weightedDecoParameterInput {I : Type*} (s : Finset I) (a : I → ℝ) : ℝ[X] :=
  ∏ i ∈ s, (X + C (a i))

/-- The weighted transform of a labeled affine-factor product. -/
def weightedDecoParameterImage {I : Type*}
    (w : ℝ) (s : Finset I) (a : I → ℝ) : ℝ[X] :=
  weightedDecoTransform w (weightedDecoParameterInput s a)

/-- The companion transform of a labeled affine-factor product. -/
def weightedDecoParameterCompanion {I : Type*}
    (w : ℝ) (s : Finset I) (a : I → ℝ) : ℝ[X] :=
  weightedDecoCompanionTransform w (weightedDecoParameterInput s a)

theorem weightedDecoParameterInput_monic {I : Type*}
    (s : Finset I) (a : I → ℝ) :
    (weightedDecoParameterInput s a).Monic := by
  unfold weightedDecoParameterInput
  exact monic_prod_of_monic s (fun i ↦ X + C (a i))
    (fun i _ ↦ monic_X_add_C (a i))

@[simp]
theorem weightedDecoParameterInput_natDegree {I : Type*}
    (s : Finset I) (a : I → ℝ) :
    (weightedDecoParameterInput s a).natDegree = s.card := by
  unfold weightedDecoParameterInput
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · exact fun i _ ↦ monic_X_add_C (a i)

theorem weightedDecoTransform_natDegree_of_monic
    {w : ℝ} {p : ℝ[X]} (hp : p.Monic) :
    (weightedDecoTransform w p).natDegree = p.natDegree := by
  have hle : (weightedDecoTransform w p).natDegree ≤ p.natDegree := by
    exact Polynomial.basisTransform_natDegree_le_of_natDegree_le
      (fun n ↦ (weightedDecoEulerian_natDegree w n).le) p
  have hcoeff : (weightedDecoTransform w p).coeff p.natDegree = 1 := by
    simpa only [weightedDecoTransform] using
      Polynomial.coeff_basisTransform_natDegree_eq_one_of_monic
        (weightedDecoEulerian_natDegree w) (weightedDecoEulerian_monic w) hp
  exact natDegree_eq_of_le_of_coeff_ne_zero hle (by norm_num [hcoeff])

@[simp]
theorem weightedDecoParameterImage_natDegree {I : Type*}
    (w : ℝ) (s : Finset I) (a : I → ℝ) :
    (weightedDecoParameterImage w s a).natDegree = s.card := by
  rw [weightedDecoParameterImage,
    weightedDecoTransform_natDegree_of_monic
      (weightedDecoParameterInput_monic s a),
    weightedDecoParameterInput_natDegree]

theorem weightedDecoParameterImage_monic {I : Type*}
    (w : ℝ) (s : Finset I) (a : I → ℝ) :
    (weightedDecoParameterImage w s a).Monic :=
  weightedDecoTransform_monic w (weightedDecoParameterInput_monic s a)

theorem weightedDecoParameterInput_eq_mul_erase {I : Type*} [DecidableEq I]
    {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) :
    weightedDecoParameterInput s a =
      (X + C (a j)) * weightedDecoParameterInput (s.erase j) a := by
  unfold weightedDecoParameterInput
  rw [← Finset.prod_erase_mul (s := s) (f := fun i ↦ X + C (a i)) hj]
  ring

/-- Replace one affine factor while retaining all other labeled factors. -/
def weightedDecoParameterInputAt {I : Type*} [DecidableEq I]
    (s : Finset I) (a : I → ℝ) (j : I) (b : ℝ) : ℝ[X] :=
  (X + C b) * weightedDecoParameterInput (s.erase j) a

def weightedDecoParameterImageAt {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) (b : ℝ) : ℝ[X] :=
  weightedDecoTransform w (weightedDecoParameterInputAt s a j b)

def weightedDecoParameterCompanionAt {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) (b : ℝ) : ℝ[X] :=
  weightedDecoCompanionTransform w (weightedDecoParameterInputAt s a j b)

theorem weightedDecoParameterInput_update {I : Type*} [DecidableEq I]
    {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) (b : ℝ) :
    weightedDecoParameterInput s (Function.update a j b) =
      weightedDecoParameterInputAt s a j b := by
  rw [weightedDecoParameterInput_eq_mul_erase hj]
  unfold weightedDecoParameterInputAt weightedDecoParameterInput
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem weightedDecoParameterImage_update {I : Type*} [DecidableEq I]
    {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) (b : ℝ) :
    weightedDecoParameterImage w s (Function.update a j b) =
      weightedDecoParameterImageAt w s a j b := by
  unfold weightedDecoParameterImage weightedDecoParameterImageAt
  rw [weightedDecoParameterInput_update hj]

theorem weightedDecoParameterCompanion_update {I : Type*} [DecidableEq I]
    {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) (b : ℝ) :
    weightedDecoParameterCompanion w s (Function.update a j b) =
      weightedDecoParameterCompanionAt w s a j b := by
  unfold weightedDecoParameterCompanion weightedDecoParameterCompanionAt
  rw [weightedDecoParameterInput_update hj]

theorem weightedDecoParameterInputAt_self {I : Type*} [DecidableEq I]
    {s : Finset I} {a : I → ℝ} {j : I} (hj : j ∈ s) :
    weightedDecoParameterInputAt s a j (a j) =
      weightedDecoParameterInput s a := by
  exact (weightedDecoParameterInput_eq_mul_erase hj).symm

theorem weightedDecoParameterImageAt_insertion {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) (b : ℝ) :
    weightedDecoParameterImageAt w s a j b =
      (1 + X + C b) * weightedDecoParameterImage w (s.erase j) a +
        X * weightedDecoParameterCompanion w (s.erase j) a := by
  exact weightedDecoTransform_mul_X_add_C w b
    (weightedDecoParameterInput (s.erase j) a)

/-- The transformed coordinate family is affine, with slope equal to the
transform of the product with that factor deleted. -/
theorem weightedDecoParameterImageAt_sub {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) (b c : ℝ) :
    weightedDecoParameterImageAt w s a j b -
        weightedDecoParameterImageAt w s a j c =
      C (b - c) * weightedDecoParameterImage w (s.erase j) a := by
  rw [weightedDecoParameterImageAt_insertion,
    weightedDecoParameterImageAt_insertion]
  simp only [map_sub]
  ring

/-- The companion coordinate family is affine, with slope equal to the
companion of the product with that factor deleted. -/
theorem weightedDecoParameterCompanionAt_sub {I : Type*} [DecidableEq I]
    (w : ℝ) (s : Finset I) (a : I → ℝ) (j : I) (b c : ℝ) :
    weightedDecoParameterCompanionAt w s a j b -
        weightedDecoParameterCompanionAt w s a j c =
      C (b - c) * weightedDecoParameterCompanion w (s.erase j) a := by
  unfold weightedDecoParameterCompanionAt weightedDecoParameterInputAt
  have hinput :
      (X + C b) * weightedDecoParameterInput (s.erase j) a -
          (X + C c) * weightedDecoParameterInput (s.erase j) a =
        C (b - c) * weightedDecoParameterInput (s.erase j) a := by
    simp only [map_sub]
    ring
  have hneg (p : ℝ[X]) :
      weightedDecoCompanionTransform w (-p) =
        -weightedDecoCompanionTransform w p := by
    change Polynomial.basisTransform (weightedDecoCompanionBasis w) (-p) =
      -Polynomial.basisTransform (weightedDecoCompanionBasis w) p
    rw [show -p = (-1 : ℝ) • p by simp,
      Polynomial.basisTransform_smul]
    simp
  change
    weightedDecoCompanionTransform w
          ((X + C b) * weightedDecoParameterInput (s.erase j) a) -
        weightedDecoCompanionTransform w
          ((X + C c) * weightedDecoParameterInput (s.erase j) a) =
      C (b - c) * weightedDecoCompanionTransform w
        (weightedDecoParameterInput (s.erase j) a)
  calc
    _ = weightedDecoCompanionTransform w
        ((X + C b) * weightedDecoParameterInput (s.erase j) a -
          (X + C c) * weightedDecoParameterInput (s.erase j) a) := by
      symm
      rw [sub_eq_add_neg, weightedDecoCompanionTransform_add, hneg]
      rfl
    _ = weightedDecoCompanionTransform w
        (C (b - c) * weightedDecoParameterInput (s.erase j) a) := by
      rw [hinput]
    _ = _ := weightedDecoCompanionTransform_C_mul w (b - c)
      (weightedDecoParameterInput (s.erase j) a)

/-- Positive companion residues propagate simple negative roots through one
arbitrary affine-factor insertion. -/
theorem weightedDecoTransform_mul_X_add_C_root_step
    {w a : ℝ} (ha : 0 ≤ a) {g : ℝ[X]} (hg : g.Monic)
    (hdegree : 1 ≤ g.natDegree)
    (hsplits : (weightedDecoTransform w g).Splits)
    (hresidue : ∀ r, (weightedDecoTransform w g).IsRoot r →
      0 < (weightedDecoCompanionTransform w g).eval r /
        (weightedDecoTransform w g).derivative.eval r)
    (hneg : ∀ r, (weightedDecoTransform w g).IsRoot r → r < 0)
    (hone : 0 < g.eval 1) :
    let p := weightedDecoTransform w g
    let q := weightedDecoTransform w ((X + C a) * g)
    StrictInterl p q ∧ HasSimpleRoots q ∧
      (∀ r, q.IsRoot r → r < 0) ∧
      (∀ r, p.IsRoot r → ¬ q.IsRoot r) := by
  dsimp only
  let p := weightedDecoTransform w g
  let h := weightedDecoCompanionTransform w g
  let q := weightedDecoTransform w ((X + C a) * g)
  have hpPos : HasPosLeadingCoeff p :=
    hasPosLeadingCoeff_of_monic (weightedDecoTransform_monic w hg)
  have hinputMonic : ((X + C a) * g).Monic := (monic_X_add_C a).mul hg
  have hqPos : HasPosLeadingCoeff q :=
    hasPosLeadingCoeff_of_monic (weightedDecoTransform_monic w hinputMonic)
  have hpdeg : 1 ≤ p.natDegree := by
    dsimp only [p]
    rw [weightedDecoTransform_natDegree_of_monic hg]
    exact hdegree
  have hqdeg : q.natDegree = p.natDegree + 1 := by
    dsimp only [q, p]
    rw [weightedDecoTransform_natDegree_of_monic hinputMonic,
      weightedDecoTransform_natDegree_of_monic hg,
      (monic_X_add_C a).natDegree_mul hg, natDegree_X_add_C]
    exact Nat.add_comm 1 g.natDegree
  have hsign : ∀ r, p.IsRoot r → 0 < h.eval r * p.derivative.eval r := by
    intro r hr
    have hres := hresidue r hr
    have hderivative : p.derivative.eval r ≠ 0 := by
      intro hzero
      rw [hzero, div_zero] at hres
      exact (lt_irrefl 0) hres
    have heq : h.eval r * p.derivative.eval r =
        (h.eval r / p.derivative.eval r) * (p.derivative.eval r) ^ 2 := by
      field_simp [hderivative]
    rw [heq]
    exact mul_pos hres (sq_pos_of_ne_zero hderivative)
  have hXneg : ∀ r, p.IsRoot r → X.eval r < 0 := by
    intro r hr
    simpa using hneg r hr
  have hrec : q = (1 + X + C a) * p + X * h :=
    weightedDecoTransform_mul_X_add_C w a g
  have hstep := strictInterl_and_hasSimpleRoots_of_auxiliary_sign_succ
    hsplits hpPos hqPos hpdeg hqdeg hrec hsign hXneg
  have hno : ∀ r, p.IsRoot r → ¬ q.IsRoot r :=
    noCommonRoot_of_auxiliary_sign hrec hsign hXneg
  have hinter : Interlaces p q := hstep.1.toInterlaces (by rw [hqdeg])
  have hqzero : 0 < q.eval 0 := by
    dsimp only [q]
    rw [weightedDecoTransform_eval_zero]
    simp only [eval_mul, eval_add, eval_X, eval_C]
    exact mul_pos (by linarith) hone
  have hqneg : ∀ r, q.IsRoot r → r < 0 :=
    roots_neg_of_interlaces_of_eval_zero_pos hinter hqPos hqzero hneg
  exact ⟨hstep.1, hstep.2, hqneg, hno⟩

end RealRooted.Applications.OEIS
