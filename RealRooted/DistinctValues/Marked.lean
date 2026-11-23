module

public import RealRooted.DistinctValues.Reciprocal
public import RealRooted.Multiaffine.AffineEulerCore
import RealRooted.MultivariateStability.AffineEulerCore
import Mathlib.Algebra.MvPolynomial.Variables
import RealRooted.Multiaffine.AffineLineRestriction

/-!
# Marked distinct-value polynomials

The step for a column of height `h` and null weight `a` is
`a F + ∑ i < h, z_i F|z_i=1`. Iteration marks each distinct positive code
value once. We index these values from zero: `X i` marks code value `i + 1`.
A zero choice in a column has weight `a`.

For weakly increasing heights and nonnegative weights, these are the marked
`s`-inversion distinct-value polynomials, the independent-Bernoulli moments
`E ∏ (a_j + X_{h_j})`, and the relative-rook polynomials on augmented Ferrers
boards. Chordal elimination codes give the chromatic-exponent specializations.
The combinatorial descriptions motivate the recurrence; no model identity is
assumed in the stability proof. Source: unpublished manuscript, ferrers-dist,
Sections 2 and 4, and chordal-dist, Section 1; RealRooted issue #2640.

The proof uses positive reciprocation: marking becomes specialization at one,
whose sum is the affine Euler core. The checked homogenization theorem and
directional-derivative pencil prove stability of this core.
-/

@[expose] public section

open scoped BigOperators

namespace RealRooted.DistinctValues

noncomputable section

/-- A marked column step when all ambient coordinates are available. -/
def fullStep {σ : Type*} [Fintype σ] (a : ℝ) (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  MvPolynomial.C a * P + ∑ i, MvPolynomial.X i * MvPolynomial.specializeAt i 1 P

/-- A full column step preserves multiaffineness. -/
theorem fullStep_isMultiaffine {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hP : P.IsMultiaffine) (a : ℝ) :
    (fullStep a P).IsMultiaffine :=
  (hP.C_mul a).add (MvPolynomial.IsMultiaffine.sum fun i _ => mark_isMultiaffine hP i)

/-- Summing the value-one sections of a multiaffine polynomial is its affine Euler core. -/
theorem sum_specializeAt_one {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hP : P.IsMultiaffine) :
    (∑ i : σ, MvPolynomial.specializeAt i 1 P) =
      MvPolynomial.affineEulerCore id (Fintype.card σ : ℝ) P := by
  classical
  have hsection (i : σ) : MvPolynomial.specializeAt i 1 P =
      P - MvPolynomial.X i * MvPolynomial.pderiv i P + MvPolynomial.pderiv i P := by
    rw [RealRooted.MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
      hP i]
    have h := hP.eq_specializeZero_add_X_mul_pderiv i
    linear_combination -h
  simp_rw [hsection]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, MvPolynomial.affineEulerCore, id_eq]
  simp

/-- Positive reciprocation conjugates the marked step to an affine Euler core. -/
theorem reciprocal_fullStep {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hP : P.IsMultiaffine) (a : ℝ) :
    reciprocal (fullStep a P) = MvPolynomial.C a * reciprocal P +
      MvPolynomial.affineEulerCore id (Fintype.card σ : ℝ) (reciprocal P) := by
  classical
  rw [fullStep, reciprocal_add, reciprocal_C_mul, reciprocal_sum]
  simp_rw [reciprocal_mark hP]
  rw [sum_specializeAt_one (reciprocal_isMultiaffine P)]

/-- A full column step preserves zero-aware real stability for multiaffine
polynomials with nonnegative coefficients. The stability conclusion even allows
arbitrary real null weight; nonnegativity of the output requires a nonnegative weight. -/
theorem fullStep_mvRealStableOrZero {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hP : MvRealStableOrZero P)
    (hma : P.IsMultiaffine) (hnn : P.HasNonnegCoeffs) (a : ℝ) :
    MvRealStableOrZero (fullStep a P) := by
  classical
  rcases hP with hzero | hstable
  · subst P
    left
    simp [fullStep]
  · have hQ := reciprocal_mvRealStable hstable hma
    have hcombo := hQ.allCombo_affineEulerCore (reciprocal_hasNonnegCoeffs hnn)
      (totalDegree_le_card (reciprocal_isMultiaffine P)) a 1
    rw [map_one, one_mul, ← reciprocal_fullStep hma a] at hcombo
    rcases hcombo with hzero | hstable
    · left
      have h := congrArg reciprocal hzero
      rwa [reciprocal_reciprocal (fullStep_isMultiaffine hma a), reciprocal_zero] at h
    · right
      have h := reciprocal_mvRealStable hstable (reciprocal_isMultiaffine (fullStep a P))
      rwa [reciprocal_reciprocal (fullStep_isMultiaffine hma a)] at h

/-- A value-one section of a multiaffine nonnegative polynomial has nonnegative coefficients. -/
theorem specializeAt_one_hasNonnegCoeffs {σ : Type*} {P : MvPolynomial σ ℝ}
    (hma : P.IsMultiaffine) (hnn : P.HasNonnegCoeffs) (i : σ) :
    (MvPolynomial.specializeAt i 1 P).HasNonnegCoeffs := by
  rw [RealRooted.MvPolynomial.IsMultiaffine.specializeAt_one_eq_specializeZero_add_pderiv
    hma i]
  apply MvPolynomial.HasNonnegCoeffs.add _ (hnn.pderiv i)
  intro d
  rw [MvPolynomial.coeff_specializeZero]
  split
  · exact hnn d
  · exact le_rfl

/-- A nonnegative full step preserves nonnegative coefficients. -/
theorem fullStep_hasNonnegCoeffs {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ ℝ} (hma : P.IsMultiaffine) (hnn : P.HasNonnegCoeffs)
    {a : ℝ} (ha : 0 ≤ a) : (fullStep a P).HasNonnegCoeffs :=
  ((MvPolynomial.HasNonnegCoeffs.C ha).mul hnn).add
    (MvPolynomial.HasNonnegCoeffs.sum fun i _ =>
      (MvPolynomial.HasNonnegCoeffs.X i).mul (specializeAt_one_hasNonnegCoeffs hma hnn i))

/-- The column step of height `h`; coordinate `i` marks positive code value `i + 1`. -/
def step (h : ℕ) (a : ℝ) (P : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  MvPolynomial.C a * P +
    ∑ i : Fin h, MvPolynomial.X (i : ℕ) * MvPolynomial.specializeAt (i : ℕ) 1 P

/-- A finite-height step preserves multiaffineness. -/
theorem step_isMultiaffine {P : MvPolynomial ℕ ℝ} (hP : P.IsMultiaffine)
    (h : ℕ) (a : ℝ) : (step h a P).IsMultiaffine :=
  (hP.C_mul a).add (MvPolynomial.IsMultiaffine.sum fun i _ => mark_isMultiaffine hP i)

/-- A finite-height step with nonnegative weight preserves coefficient nonnegativity. -/
theorem step_hasNonnegCoeffs {P : MvPolynomial ℕ ℝ}
    (hma : P.IsMultiaffine) (hnn : P.HasNonnegCoeffs) (h : ℕ)
    {a : ℝ} (ha : 0 ≤ a) : (step h a P).HasNonnegCoeffs :=
  ((MvPolynomial.HasNonnegCoeffs.C ha).mul hnn).add
    (MvPolynomial.HasNonnegCoeffs.sum fun i _ =>
      (MvPolynomial.HasNonnegCoeffs.X (i : ℕ)).mul
        (specializeAt_one_hasNonnegCoeffs hma hnn (i : ℕ)))

/-- The finite-height step agrees with the full step on its supported coordinate type. -/
theorem step_rename (h : ℕ) (a : ℝ) (P : MvPolynomial (Fin h) ℝ) :
    step h a (MvPolynomial.rename Fin.val P) =
      MvPolynomial.rename Fin.val (fullStep a P) := by
  classical
  simp only [step, fullStep, map_add, map_mul, map_sum, MvPolynomial.rename_C,
    MvPolynomial.rename_X, MvPolynomial.specializeAt_rename _ Fin.val_injective]

/-- Restrict a supported polynomial to the finite coordinate type of its height. -/
private theorem exists_fin_rename {P : MvPolynomial ℕ ℝ} {h : ℕ}
    (hvars : P.vars ⊆ Finset.range h) :
    ∃ Q : MvPolynomial (Fin h) ℝ, MvPolynomial.rename Fin.val Q = P := by
  apply MvPolynomial.exists_rename_eq_of_vars_subset_range P Fin.val Fin.val_injective
  intro i hi
  exact ⟨⟨i, Finset.mem_range.mp (hvars hi)⟩, rfl⟩

/-- A step introduces only values below its height when its input uses those values. -/
theorem vars_step_subset {P : MvPolynomial ℕ ℝ} {h : ℕ}
    (hvars : P.vars ⊆ Finset.range h) (a : ℝ) :
    (step h a P).vars ⊆ Finset.range h := by
  obtain ⟨Q, rfl⟩ := exists_fin_rename hvars
  rw [step_rename]
  intro i hi
  obtain ⟨j, _, rfl⟩ := MvPolynomial.mem_vars_rename Fin.val (fullStep a Q) hi
  exact Finset.mem_range.mpr j.isLt

/-- A supported column step preserves zero-aware real stability. -/
theorem step_mvRealStableOrZero {P : MvPolynomial ℕ ℝ} {h : ℕ}
    (hP : MvRealStableOrZero P) (hma : P.IsMultiaffine) (hnn : P.HasNonnegCoeffs)
    (hvars : P.vars ⊆ Finset.range h) (a : ℝ) :
    MvRealStableOrZero (step h a P) := by
  obtain ⟨Q, rfl⟩ := exists_fin_rename hvars
  rw [step_rename]
  apply MvRealStableOrZero.rename
  apply fullStep_mvRealStableOrZero (hP.of_rename Fin.val_injective)
    (hma.of_rename Fin.val_injective)
  intro d
  rw [← MvPolynomial.coeff_rename_mapDomain Fin.val Fin.val_injective Q d]
  exact hnn _

/-- Process columns from left to right, marking each distinct positive value once.
Weakly increasing heights are the natural hypothesis of the stability theorem. -/
def markedPolynomial (columns : List (ℕ × ℝ)) : MvPolynomial ℕ ℝ :=
  columns.foldl (fun P c => step c.1 c.2 P) 1

/-- The empty board has marked polynomial one. -/
@[simp] theorem markedPolynomial_nil : markedPolynomial [] = 1 := rfl

/-- Appending a column applies its marked step. -/
@[simp] theorem markedPolynomial_append_singleton (columns : List (ℕ × ℝ)) (c : ℕ × ℝ) :
    markedPolynomial (columns ++ [c]) = step c.1 c.2 (markedPolynomial columns) := by
  simp [markedPolynomial, List.foldl_append]

/-- Increasing-height columns with nonnegative null weights have multiaffine,
nonnegative, weakly real-stable marked polynomials, supported below every height bound. -/
theorem markedPolynomial_properties (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) :
    (markedPolynomial columns).IsMultiaffine ∧
      (markedPolynomial columns).HasNonnegCoeffs ∧
      MvRealStableOrZero (markedPolynomial columns) ∧
      ∀ H, (∀ c ∈ columns, c.1 ≤ H) →
        (markedPolynomial columns).vars ⊆ Finset.range H := by
  induction columns using List.reverseRecOn with
  | nil =>
      refine ⟨?_, MvPolynomial.HasNonnegCoeffs.one, MvRealStable.one.orZero, ?_⟩
      · simpa using MvPolynomial.IsMultiaffine.C (σ := ℕ) (1 : ℝ)
      · intro H hH
        simp
  | append_singleton columns c ih =>
      have hsort := List.pairwise_append.mp hsorted
      have hprev : ∀ d ∈ columns, 0 ≤ d.2 := fun d hd => ha d (List.mem_append_left _ hd)
      obtain ⟨hma, hnn, hstable, hvars⟩ := ih hsort.1 hprev
      have hbound : ∀ d ∈ columns, d.1 ≤ c.1 := fun d hd => hsort.2.2 d hd c (by simp)
      have hc : 0 ≤ c.2 := ha c (by simp)
      rw [markedPolynomial_append_singleton]
      refine ⟨step_isMultiaffine hma _ _, step_hasNonnegCoeffs hma hnn _ hc,
        step_mvRealStableOrZero hstable hma hnn (hvars c.1 hbound) c.2, ?_⟩
      intro H hH
      exact (vars_step_subset (hvars c.1 hbound) c.2).trans
        (Finset.range_mono (hH c (by simp)))

/-- The main stability theorem for marked distinct-value polynomials. -/
theorem markedPolynomial_mvRealStableOrZero (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2) :
    MvRealStableOrZero (markedPolynomial columns) :=
  (markedPolynomial_properties columns hsorted ha).2.2.1

/-- At all-one markers, a column step multiplies the total weight by `a + h`. -/
theorem eval_one_step (h : ℕ) (a : ℝ) (P : MvPolynomial ℕ ℝ) :
    MvPolynomial.eval (fun _ => 1) (step h a P) =
      (a + h) * MvPolynomial.eval (fun _ => 1) P := by
  classical
  have hupdate (i : ℕ) : Function.update (fun _ : ℕ => (1 : ℝ)) i 1 = (fun _ => 1) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  simp only [step, map_add, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, MvPolynomial.eval_specializeAt, hupdate, one_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The total weight of a marked board is the product of its column weights. -/
theorem eval_one_markedPolynomial (columns : List (ℕ × ℝ)) :
    MvPolynomial.eval (fun _ => 1) (markedPolynomial columns) =
      (columns.map fun c => c.2 + (c.1 : ℝ)).prod := by
  induction columns using List.reverseRecOn with
  | nil => simp
  | append_singleton columns c ih =>
      rw [markedPolynomial_append_singleton, eval_one_step, ih]
      simp [mul_comm]

/-- The marked polynomial is nonzero if every column has nonzero total weight. -/
theorem markedPolynomial_ne_zero (columns : List (ℕ × ℝ))
    (h : ∀ c ∈ columns, c.2 + (c.1 : ℝ) ≠ 0) : markedPolynomial columns ≠ 0 := by
  intro hzero
  have hprod := eval_one_markedPolynomial columns
  rw [hzero, map_zero] at hprod
  have hn : (columns.map fun c => c.2 + (c.1 : ℝ)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hx
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp hx
    exact h c hc heq
  exact hn hprod.symm

/-- Null weight one gives a genuinely real-stable polynomial for every increasing list of bounds. -/
theorem markedPolynomial_one_mvRealStable (heights : List ℕ)
    (hsorted : heights.Pairwise (· ≤ ·)) :
    MvRealStable (markedPolynomial (heights.map fun h => (h, 1))) := by
  have hs : (heights.map fun h => (h, (1 : ℝ))).Pairwise (fun c d => c.1 ≤ d.1) := by
    simpa only [List.pairwise_map] using hsorted
  have ha : ∀ c ∈ heights.map (fun h => (h, (1 : ℝ))), 0 ≤ c.2 := by
    intro c hc
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hc
    exact zero_le_one
  rcases markedPolynomial_mvRealStableOrZero _ hs ha with hzero | hstable
  · exfalso
    apply markedPolynomial_ne_zero _ _ hzero
    intro c hc
    obtain ⟨h, _, rfl⟩ := List.mem_map.mp hc
    positivity
  · exact hstable

/-- Positive total weights remove the zero alternative from the marked stability theorem. -/
theorem markedPolynomial_mvRealStable (columns : List (ℕ × ℝ))
    (hsorted : columns.Pairwise (fun c d => c.1 ≤ d.1))
    (ha : ∀ c ∈ columns, 0 ≤ c.2)
    (hne : ∀ c ∈ columns, c.2 + (c.1 : ℝ) ≠ 0) :
    MvRealStable (markedPolynomial columns) :=
  (markedPolynomial_mvRealStableOrZero columns hsorted ha).resolve_left
    (markedPolynomial_ne_zero columns hne)

end

end RealRooted.DistinctValues
