module

import Mathlib.Data.Fin.Tuple.Sort
import RealRooted.Mathlib.Algebra.MvPolynomial.PDerivProd
import RealRooted.Mathlib.Algebra.MvPolynomial.SpecializeList
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Permanent
public import RealRooted.Permanent.Basic
public import RealRooted.Multiaffine
public import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize

/-!
# Ferrers matrices and their permanent polynomial

The definitions follow Section 3 of P. Brändén, J. Haglund, M. Visontai,
and D. G. Wagner, *Proof of the monotone column permanent conjecture*,
arXiv:1010.2565v2.
-/

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- Every entry of a real matrix is zero or one. -/
def IsZeroOne {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- Every row is weakly increasing as the column index increases. -/
def HasWeaklyIncreasingRows {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j k, j ≤ k → A i j ≤ A i k

/-- A Ferrers matrix has zero-one entries, decreasing columns, and increasing
rows. -/
def IsFerrers {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsZeroOne A ∧ HasWeaklyDecreasingColumns A ∧
    HasWeaklyIncreasingRows A

/-- Delete the last row and last column of a nonempty square matrix. -/
def deleteLast {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i.castSucc j.castSucc

/-- Deleting the last row and column preserves the Ferrers conditions. -/
theorem IsFerrers.deleteLast {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsFerrers A) : IsFerrers (deleteLast A) := by
  rcases hA with ⟨hzeroOne, hcols, hrows⟩
  exact ⟨fun i j => hzeroOne i.castSucc j.castSucc,
    fun j i k hik => hcols j.castSucc i.castSucc k.castSucc (by simpa using hik),
    fun i j k hjk => hrows i.castSucc j.castSucc k.castSucc (by simpa using hjk)⟩

end Matrix

namespace RealRooted
namespace Permanent

noncomputable section

/-- The two-alphabet polynomial `per B(A)`, where
`B(A)_ij = a_ij y_j + (1-a_ij) x_i`. -/
def ferrersPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Sum (Fin n) (Fin n)) ℝ :=
  Matrix.permanent fun i j =>
    MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) +
      MvPolynomial.C (1 - A i j) * MvPolynomial.X (Sum.inl i)

/-- The row-specialized Ferrers polynomial obtained by setting every `x_i`
equal to one. -/
def ferrersColumnPolynomial {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  Matrix.permanent fun i j =>
    MvPolynomial.C (A i j) * MvPolynomial.X j +
      MvPolynomial.C (1 - A i j)

/-- Set every row variable of a two-alphabet polynomial equal to one and keep
the column variables. -/
def specializeFerrersRows {n : ℕ}
    (P : MvPolynomial (Sum (Fin n) (Fin n)) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval
    (Sum.elim (fun _ => 1) fun j => MvPolynomial.X j) P

/-- Row specialization sends `per B(A)` to its one-alphabet Ferrers
polynomial. -/
theorem specializeFerrersRows_ferrersPermanent {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    specializeFerrersRows (ferrersPermanent A) =
      ferrersColumnPolynomial A := by
  classical
  simp [specializeFerrersRows, ferrersPermanent, ferrersColumnPolynomial,
    Matrix.permanent]

/-- The Ferrers dual `J - Aᵀ`. -/
def ferrersDual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => 1 - A j i

/-- Complement-transpose preserves the Ferrers conditions. -/
theorem isFerrers_ferrersDual {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : Matrix.IsFerrers A) :
    Matrix.IsFerrers (ferrersDual A) := by
  rcases hA with ⟨hzeroOne, hcols, hrows⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rcases hzeroOne j i with hzero | hone <;> simp [ferrersDual, *]
  · intro j i k hik
    dsimp only [ferrersDual]
    linarith [hrows j i k hik]
  · intro i j k hjk
    dsimp only [ferrersDual]
    linarith [hcols i j k hjk]

/-- Exchange the row and column alphabets. -/
def swapFerrersVariable {n : ℕ} :
    Sum (Fin n) (Fin n) → Sum (Fin n) (Fin n)
  | Sum.inl i => Sum.inr i
  | Sum.inr j => Sum.inl j

/-- Ferrers duality transposes the matrix of linear forms and exchanges the
two alphabets. -/
theorem rename_ferrersPermanent_dual {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial.rename (swapFerrersVariable (n := n))
        (ferrersPermanent (ferrersDual A)) =
      ferrersPermanent A := by
  classical
  unfold ferrersPermanent ferrersDual
  rw [rename_permanent (swapFerrersVariable (n := n))
    (fun i j : Fin n =>
      MvPolynomial.C (1 - A j i) * MvPolynomial.X (Sum.inr j) +
        MvPolynomial.C (1 - (1 - A j i)) *
          MvPolynomial.X (Sum.inl i))]
  let M : Matrix (Fin n) (Fin n)
      (MvPolynomial (Sum (Fin n) (Fin n)) ℝ) :=
    fun i j =>
      MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) +
        MvPolynomial.C (1 - A i j) * MvPolynomial.X (Sum.inl i)
  have hmatrix :
      (fun i j =>
        MvPolynomial.rename (swapFerrersVariable (n := n))
          (MvPolynomial.C (1 - A j i) *
              MvPolynomial.X (Sum.inr j) +
            MvPolynomial.C (1 - (1 - A j i)) *
              MvPolynomial.X (Sum.inl i))) = M.transpose := by
    funext i j
    change _ = M j i
    simp [M, swapFerrersVariable]; ring
  rw [hmatrix, Matrix.permanent_transpose]

/-- Embed the two alphabets of an `n` by `n` deletion into the corresponding
alphabets of size `n+1`. -/
def embedSmallVariable {n : ℕ} :
    Sum (Fin n) (Fin n) → Sum (Fin (n + 1)) (Fin (n + 1))
  | Sum.inl i => Sum.inl i.castSucc
  | Sum.inr j => Sum.inr j.castSucc

/-- Direction weights occurring in the Ferrers deletion recurrence. -/
def ferrersActiveWeight {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Sum (Fin n) (Fin n) → ℝ
  | Sum.inl i => A i.castSucc (Fin.last n)
  | Sum.inr _ => 1

/-- The coefficient of the undeleted polynomial in the Ferrers recurrence.
For a Ferrers matrix with zero bottom-right entry, this is the number of zeros
in its last column. -/
def ferrersZeroWeight {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  1 + ∑ i : Fin n, (1 - A i.castSucc (Fin.last n))

/-- The active derivative direction is nonnegative for a zero-one matrix. -/
theorem ferrersActiveWeight_nonneg {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsZeroOne A) :
    ∀ u, 0 ≤ ferrersActiveWeight A u := by
  rintro (i | j)
  · rcases hA i.castSucc (Fin.last n) with h | h <;> simp [ferrersActiveWeight, h]
  · simp [ferrersActiveWeight]

/-- The zero count in the last column is positive for a zero-one matrix. -/
theorem ferrersZeroWeight_pos {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsZeroOne A) : 0 < ferrersZeroWeight A := by
  unfold ferrersZeroWeight
  have hnonneg :
      0 ≤ ∑ i : Fin n, (1 - A i.castSucc (Fin.last n)) := by
    refine Finset.sum_nonneg fun i _ => ?_
    rcases hA i.castSucc (Fin.last n) with hzero | hone <;> simp [*]
  linarith

/-- The right-hand side of the Ferrers deletion recurrence. -/
def ferrersRecurrenceRhs {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    MvPolynomial (Sum (Fin (n + 1)) (Fin (n + 1))) ℝ :=
  let P := ferrersPermanent (Matrix.deleteLast A)
  MvPolynomial.X (Sum.inl (Fin.last n)) *
    (MvPolynomial.C (ferrersZeroWeight A) *
        MvPolynomial.rename embedSmallVariable P +
      MvPolynomial.X (Sum.inr (Fin.last n)) *
        MvPolynomial.rename embedSmallVariable
          (directionalPDeriv (ferrersActiveWeight A) P))

/-- The permanent summand indexed by one permutation. -/
def ferrersPermutationTerm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) :
    MvPolynomial (Sum (Fin n) (Fin n)) ℝ :=
  ∏ j, (MvPolynomial.C (A (π j) j) * MvPolynomial.X (Sum.inr j) +
    MvPolynomial.C (1 - A (π j) j) * MvPolynomial.X (Sum.inl (π j)))

/-- Terms whose last-column entry is zero. -/
def ferrersLastZeroContribution {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    MvPolynomial (Sum (Fin (n + 1)) (Fin (n + 1))) ℝ :=
  ∑ π ∈ Finset.univ.filter
      (fun π : Equiv.Perm (Fin (n + 1)) => A (π (Fin.last n)) (Fin.last n) = 0),
    ferrersPermutationTerm A π

/-- Terms whose last-column entry is one. -/
def ferrersLastOneContribution {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    MvPolynomial (Sum (Fin (n + 1)) (Fin (n + 1))) ℝ :=
  ∑ π ∈ Finset.univ.filter
      (fun π : Equiv.Perm (Fin (n + 1)) => A (π (Fin.last n)) (Fin.last n) = 1),
    ferrersPermutationTerm A π

/-- For a zero-one matrix, the permanent splits into the terms using zero
and one, respectively, in the last column. -/
theorem ferrersPermanent_eq_lastZeroContribution_add_lastOneContribution
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hzeroOne : Matrix.IsZeroOne A) :
    ferrersPermanent A =
      ferrersLastZeroContribution A + ferrersLastOneContribution A := by
  classical
  unfold ferrersPermanent ferrersLastZeroContribution
    ferrersLastOneContribution ferrersPermutationTerm Matrix.permanent
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun π : Equiv.Perm (Fin (n + 1)) =>
      A (π (Fin.last n)) (Fin.last n) = 0)]
  congr 1
  have hfilter :
      Finset.univ.filter
          (fun π : Equiv.Perm (Fin (n + 1)) =>
            ¬A (π (Fin.last n)) (Fin.last n) = 0) =
        Finset.univ.filter
          (fun π : Equiv.Perm (Fin (n + 1)) =>
            A (π (Fin.last n)) (Fin.last n) = 1) := by
    apply Finset.filter_congr; intro π _
    rcases hzeroOne (π (Fin.last n)) (Fin.last n) with h | h <;> simp [h]
  rw [hfilter]

end

end Permanent
end RealRooted

namespace RealRooted
namespace Permanent

noncomputable section

private def ferrersEntry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial (Sum (Fin n) (Fin n)) ℝ :=
  MvPolynomial.C (A i j) * MvPolynomial.X (Sum.inr j) +
    MvPolynomial.C (1 - A i j) * MvPolynomial.X (Sum.inl i)

private theorem ferrersPermutationTerm_eq_prod_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) :
    ferrersPermutationTerm A π = ∏ j, ferrersEntry A (π j) j := rfl

private theorem ferrersEntry_eq_X_of_zero {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A) {i : Fin (n + 1)}
    (hi : A i (Fin.last n) = 0) (j : Fin (n + 1)) :
    ferrersEntry A i j = MvPolynomial.X (Sum.inl i) := by
  have hij : A i j = 0 := by
    rcases hA with ⟨h01, -, hrows⟩
    rcases h01 i j with h | h
    · exact h
    · linarith [hrows i j (Fin.last n) (Fin.le_last j)]
  simp [ferrersEntry, hij]

private theorem ferrersPermutationTerm_swap_last_zero {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0)
    {r : Fin (n + 1)} (hr : A r (Fin.last n) = 0)
    (π : Equiv.Perm (Fin (n + 1))) :
    ferrersPermutationTerm A (Equiv.swap r (Fin.last n) * π) =
      ferrersPermutationTerm A π := by
  rw [ferrersPermutationTerm_eq_prod_entry,
    ferrersPermutationTerm_eq_prod_entry]
  have key : ∀ ρ : Equiv.Perm (Fin (n + 1)),
      ∏ j, ferrersEntry A (ρ j) j =
        ∏ i, ferrersEntry A i (ρ⁻¹ i) := by
    intro ρ; rw [← Equiv.prod_comp ρ (fun i => ferrersEntry A i (ρ⁻¹ i))]
    simp
  rw [key, key]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : A i (Fin.last n) = 0
  · rw [ferrersEntry_eq_X_of_zero hA hi,
      ferrersEntry_eq_X_of_zero hA hi]
  · have h1 : i ≠ r := fun h => hi (h ▸ hr)
    have h2 : i ≠ Fin.last n := fun h => hi (h ▸ hcorner)
    congr 1
    rw [mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_inv,
      Equiv.swap_apply_of_ne_of_ne h1 h2]

private def extendLast {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans ((Equiv.optionCongr σ).trans finSuccEquivLast.symm)

@[simp] private theorem extendLast_last {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    extendLast σ (Fin.last n) = Fin.last n := by simp [extendLast]

@[simp] private theorem extendLast_castSucc {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendLast σ i.castSucc = (σ i).castSucc := by simp [extendLast]

private theorem ferrersPermutationTerm_extendLast {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hcorner : A (Fin.last n) (Fin.last n) = 0)
    (σ : Equiv.Perm (Fin n)) :
    ferrersPermutationTerm A (extendLast σ) =
      MvPolynomial.X (Sum.inl (Fin.last n)) *
        MvPolynomial.rename embedSmallVariable
          (ferrersPermutationTerm (Matrix.deleteLast A) σ) := by
  rw [ferrersPermutationTerm_eq_prod_entry,
    ferrersPermutationTerm_eq_prod_entry, Fin.prod_univ_castSucc,
    map_prod, mul_comm]
  congr 1
  · simp [ferrersEntry, hcorner]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [ferrersEntry, Matrix.deleteLast, embedSmallVariable]

private theorem sum_ferrersPermutationTerm_fixing_last {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ∑ π ∈ Finset.univ.filter
        (fun π : Equiv.Perm (Fin (n + 1)) =>
          π (Fin.last n) = Fin.last n),
      ferrersPermutationTerm A π =
      MvPolynomial.X (Sum.inl (Fin.last n)) *
        MvPolynomial.rename embedSmallVariable
          (ferrersPermanent (Matrix.deleteLast A)) := by
  rw [show ferrersPermanent (Matrix.deleteLast A) =
      ∑ π, ferrersPermutationTerm (Matrix.deleteLast A) π from rfl,
    map_sum, Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun σ _ => extendLast σ) ?_ ?_ ?_ ?_
  · intro σ _
    simp
  · intro σ _ τ _ h
    ext i
    have heq := congrArg
      (fun π : Equiv.Perm (Fin (n + 1)) => π i.castSucc) h
    exact congrArg _ (by simpa using heq)
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    have hne : ∀ i : Fin n, π i.castSucc ≠ Fin.last n := by
      intro i h; rw [← hπ] at h
      exact (Fin.castSucc_lt_last i).ne (π.injective h)
    let f : Fin n → Fin n :=
      fun i => (π i.castSucc).castPred (hne i)
    have hf : Function.Injective f := by
      intro i j h
      have heq := congrArg Fin.castSucc h
      simp only [f, Fin.castSucc_castPred] at heq
      exact Fin.castSucc_injective _ (π.injective heq)
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf),
      Finset.mem_univ _, ?_⟩
    ext i
    induction i using Fin.lastCases with
    | last => simp [hπ]
    | cast i => simp [f]
  · intro σ _
    rw [ferrersPermutationTerm_extendLast hcorner]

private theorem ferrersLastZeroContribution_eq_card_mul {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ferrersLastZeroContribution A =
      (Finset.univ.filter
        (fun i => A i (Fin.last n) = 0)).card •
        ∑ π ∈ Finset.univ.filter
          (fun π : Equiv.Perm (Fin (n + 1)) =>
            π (Fin.last n) = Fin.last n),
          ferrersPermutationTerm A π := by
  set Z := Finset.univ.filter (fun i => A i (Fin.last n) = 0)
  set T := Finset.univ.filter
    (fun π : Equiv.Perm (Fin (n + 1)) =>
      π (Fin.last n) = Fin.last n)
  have hproduct :
      ∑ p ∈ Z ×ˢ T, ferrersPermutationTerm A p.2 =
        Z.card • ∑ π ∈ T, ferrersPermutationTerm A π := by
    simp only [Finset.sum_product, Finset.sum_const]
  rw [← hproduct, ferrersLastZeroContribution]
  refine Finset.sum_nbij'
    (fun π =>
      (π (Fin.last n),
        Equiv.swap (π (Fin.last n)) (Fin.last n) * π))
    (fun p => Equiv.swap p.1 (Fin.last n) * p.2) ?_ ?_ ?_ ?_ ?_
  · intro π hπ
    simpa [Z, T, Finset.mem_product] using hπ
  · rintro ⟨r, σ⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and, Z, T] at hp
    simp [hp.1, hp.2]
  · intro π _
    simp
  · rintro ⟨r, σ⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and, Z, T] at hp
    simp [hp.2]
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    exact (ferrersPermutationTerm_swap_last_zero
      hA hcorner hπ π).symm

private theorem ferrersZeroWeight_eq_card {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ferrersZeroWeight A =
      ((Finset.univ.filter
        (fun i => A i (Fin.last n) = 0)).card : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum, Fin.sum_univ_castSucc,
    ferrersZeroWeight, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rcases hA.1 i.castSucc (Fin.last n) with h | h <;> simp [h]
  · simp [hcorner]

/-- The zero terms in the last column form the scalar half of the Ferrers
deletion recurrence. Its formal permutation bijection
was contributed by Aristotle and independently checked with AXLE. -/
theorem ferrersLastZeroContribution_eq {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ferrersLastZeroContribution A =
      MvPolynomial.X (Sum.inl (Fin.last n)) *
        (MvPolynomial.C (ferrersZeroWeight A) *
          MvPolynomial.rename embedSmallVariable
            (ferrersPermanent (Matrix.deleteLast A))) := by
  rw [ferrersLastZeroContribution_eq_card_mul hA hcorner,
    sum_ferrersPermutationTerm_fixing_last hcorner,
    ferrersZeroWeight_eq_card hA hcorner, nsmul_eq_mul,
    ← map_natCast MvPolynomial.C]
  ring

private theorem active_weighted_pderiv_entry {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A) (s t : Fin n) :
    ∑ u, MvPolynomial.C (ferrersActiveWeight A u) *
        MvPolynomial.pderiv u
          (MvPolynomial.C (A s.castSucc t.castSucc) *
              MvPolynomial.X (Sum.inr t) +
            MvPolynomial.C (1 - A s.castSucc t.castSucc) *
              MvPolynomial.X (Sum.inl s) :
            MvPolynomial (Sum (Fin n) (Fin n)) ℝ) =
      MvPolynomial.C (A s.castSucc (Fin.last n)) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [ferrersActiveWeight, MvPolynomial.C_1, map_add,
    Derivation.leibniz,
    MvPolynomial.pderiv_X, ne_eq, reduceCtorEq, not_false_eq_true,
    Pi.single_eq_of_ne, smul_eq_mul, mul_zero,
    MvPolynomial.derivation_C, add_zero, Pi.single_apply,
    Sum.inl.injEq, mul_ite, mul_one, map_sub,
    Derivation.map_one_eq_zero, sub_self, zero_add,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Sum.inr.injEq,
    one_mul]
  rw [← MvPolynomial.C_1, ← map_sub, ← map_mul, ← map_add]
  congr 1
  rcases hA.1 s.castSucc t.castSucc with h | h
  · simp [h]
  · have hlast : A s.castSucc (Fin.last n) = 1 := by
      rcases hA.1 s.castSucc (Fin.last n) with h' | h'
      · linarith [hA.2.2 s.castSucc t.castSucc (Fin.last n) (Fin.le_last _)]
      · exact h'
    simp [h, hlast]

private theorem directionalPDeriv_ferrersPermanent {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A) :
    directionalPDeriv (ferrersActiveWeight A)
        (ferrersPermanent (Matrix.deleteLast A)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ t : Fin n,
        MvPolynomial.C (A (σ t).castSucc (Fin.last n)) *
          ∏ j ∈ Finset.univ.erase t,
            (MvPolynomial.C (A (σ j).castSucc j.castSucc) *
                MvPolynomial.X (Sum.inr j) +
              MvPolynomial.C (1 - A (σ j).castSucc j.castSucc) *
                MvPolynomial.X (Sum.inl (σ j))) := by
  classical
  unfold directionalPDeriv ferrersPermanent Matrix.permanent
    Matrix.deleteLast
  simp_rw [map_sum, MvPolynomial.pderiv_finsetProd, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← active_weighted_pderiv_entry hA (σ t) t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

private theorem ferrersLastOneContribution_eq_expansion {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ferrersLastOneContribution A =
      MvPolynomial.X (Sum.inl (Fin.last n)) *
        MvPolynomial.X (Sum.inr (Fin.last n)) *
          ∑ σ : Equiv.Perm (Fin n), ∑ t : Fin n,
            MvPolynomial.C (A (σ t).castSucc (Fin.last n)) *
              ∏ j ∈ Finset.univ.erase t,
                (MvPolynomial.C (A (σ j).castSucc j.castSucc) *
                    MvPolynomial.X (Sum.inr j.castSucc) +
                  MvPolynomial.C
                      (1 - A (σ j).castSucc j.castSucc) *
                    MvPolynomial.X (Sum.inl (σ j).castSucc)) := by
  classical
  have h1 : ferrersLastOneContribution A =
      ∑ π : Equiv.Perm (Fin (n + 1)),
        MvPolynomial.C (A (π (Fin.last n)) (Fin.last n)) *
          ferrersPermutationTerm A π := by
    unfold ferrersLastOneContribution
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun π _ => ?_
    rcases hA.1 (π (Fin.last n)) (Fin.last n) with h | h <;>
      simp [h]
  rw [h1, ← ((Equiv.permCongr finSuccEquivLast).trans
    Equiv.Perm.decomposeOption).symm.sum_comp, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_option]
  set e := (finSuccEquivLast.permCongr.trans
    (Equiv.Perm.decomposeOption (α := Fin n))).symm with he
  have he_last : ∀ p,
      e (p, σ) (Fin.last n) = finSuccEquivLast.symm p := by
    intro p; simp [he]
  have he_cs : ∀ p x,
      e (p, σ) x.castSucc =
        finSuccEquivLast.symm (Equiv.swap none p (some (σ x))) := by
    intro p x; simp [he]
  have hF1 : ∀ j, A (Fin.last n) j = 0 := by
    intro j
    have hle := hA.2.2 (Fin.last n) j (Fin.last n) (Fin.le_last _)
    rcases hA.1 (Fin.last n) j with h | h
    · exact h
    · linarith
  rw [he_last, finSuccEquivLast_symm_none, hcorner, map_zero,
    zero_mul, zero_add, ← (Equiv.sum_comp σ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [he_last, finSuccEquivLast_symm_some]
  unfold ferrersPermutationTerm
  rw [Fin.prod_univ_castSucc, he_last, finSuccEquivLast_symm_some,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  rw [he_cs, Equiv.swap_apply_right, finSuccEquivLast_symm_none, hF1]
  rw [Finset.prod_congr rfl (g := fun j =>
    MvPolynomial.C (A (σ j).castSucc j.castSucc) *
        MvPolynomial.X (Sum.inr j.castSucc) +
      MvPolynomial.C (1 - A (σ j).castSucc j.castSucc) *
        MvPolynomial.X (Sum.inl (σ j).castSucc)) ?_]
  · rcases hA.1 (σ q).castSucc (Fin.last n) with h | h <;>
      simp [h]
    ring
  · intro x hx
    have hxq : σ x ≠ σ q := by
      intro h; simp [σ.injective h] at hx
    rw [he_cs, Equiv.swap_apply_of_ne_of_ne (by simp)
      (by simpa using hxq), finSuccEquivLast_symm_some]

/-- The one terms in the last column form the marked-derivative half of the
Ferrers deletion recurrence. Its formal permutation
bijection was contributed by Aristotle and independently checked with AXLE. -/
theorem ferrersLastOneContribution_eq_directionalPDeriv {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ferrersLastOneContribution A =
      MvPolynomial.X (Sum.inl (Fin.last n)) *
        (MvPolynomial.X (Sum.inr (Fin.last n)) *
          MvPolynomial.rename embedSmallVariable
            (directionalPDeriv (ferrersActiveWeight A)
              (ferrersPermanent (Matrix.deleteLast A)))) := by
  rw [ferrersLastOneContribution_eq_expansion hA hcorner,
    directionalPDeriv_ferrersPermanent hA, mul_assoc]
  congr 2
  simp [map_sum, map_prod, embedSmallVariable]

/-- Splitting the permanent sum by its last-column entry gives the Ferrers
deletion recurrence, Lemma 3.2 of Brändén--Haglund--Visontai--Wagner. -/
theorem ferrersPermanent_eq_recurrenceRhs {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : Matrix.IsFerrers A)
    (hcorner : A (Fin.last n) (Fin.last n) = 0) :
    ferrersPermanent A = ferrersRecurrenceRhs A := by
  rw [ferrersPermanent_eq_lastZeroContribution_add_lastOneContribution
    hA.1, ferrersLastZeroContribution_eq hA hcorner,
    ferrersLastOneContribution_eq_directionalPDeriv hA hcorner]
  unfold ferrersRecurrenceRhs; ring

end

end Permanent
end RealRooted

namespace RealRooted
namespace Permanent

noncomputable section

/-- A vector indexed from top to bottom is weakly decreasing. -/
def IsWeaklyDecreasingVector {n : ℕ} (v : Fin n → ℝ) : Prop :=
  ∀ i k, i ≤ k → v k ≤ v i

/-- The zero-one vector supported on the prefix ending at `r`. -/
def prefixIndicator {n : ℕ} (r : Fin n) (i : Fin (n + 1)) : ℝ :=
  if i ≤ r.castSucc then 1 else 0

/-- A prefix indicator has only zero-one entries. -/
theorem prefixIndicator_zero_or_one {n : ℕ} (r : Fin n)
    (i : Fin (n + 1)) :
    prefixIndicator r i = 0 ∨ prefixIndicator r i = 1 := by
  unfold prefixIndicator; split_ifs <;> simp

/-- Every prefix indicator is weakly decreasing. -/
theorem prefixIndicator_isWeaklyDecreasingVector {n : ℕ} (r : Fin n) :
    IsWeaklyDecreasingVector (prefixIndicator r) := by
  intro i k hik
  by_cases hi : i ≤ r.castSucc
  · by_cases hk : k ≤ r.castSucc <;> simp [prefixIndicator, hi, hk]
  · have hk : ¬k ≤ r.castSucc := fun hkr => hi (hik.trans hkr)
    simp [prefixIndicator, hi, hk]

/-- Adjacent differences of a weakly decreasing vector are nonnegative. -/
theorem adjacentDifference_nonneg {n : ℕ} {v : Fin (n + 1) → ℝ}
    (hv : IsWeaklyDecreasingVector v) (r : Fin n) :
    0 ≤ v r.castSucc - v r.succ :=
  sub_nonneg.mpr (hv r.castSucc r.succ Fin.castSucc_lt_succ.le)

/-- The prefix decomposition of a decreasing column. -/
def monotonePrefixCombination {n : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  max (v (Fin.last n)) 0 - max (-v (Fin.last n)) 0 +
    ∑ r : Fin n,
      (v r.castSucc - v r.succ) * prefixIndicator r i

private theorem prefix_telescope_eq :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)),
      v (Fin.last n) +
          ∑ r : Fin n,
            (v r.castSucc - v r.succ) * prefixIndicator r i =
        v i := by
  intro n
  induction n with
  | zero =>
      intro v i; simp [Fin.fin_one_eq_zero i]
  | succ n ih =>
      intro v i; rw [Fin.sum_univ_succ]
      have key := fun j => ih (fun k => v k.succ) j
      have hcs : ∀ r : Fin n, r.succ.castSucc = r.castSucc.succ :=
        fun r => rfl
      refine Fin.cases ?_ (fun j => ?_) i
      · have h0 := key 0
        simp only [prefixIndicator, Fin.zero_le, ite_true, mul_one] at h0 ⊢
        simp only [Fin.succ_last, Fin.castSucc_zero,
          Fin.succ_zero_eq_one] at h0 ⊢
        simp only [hcs]
        linarith
      · have hj := key j
        have e1 : ¬(j.succ ≤ (0 : Fin (n + 1)).castSucc) := by simp
        have e2 : ∀ r : Fin n,
            (j.succ ≤ r.succ.castSucc ↔ j ≤ r.castSucc) := by
          intro r
          simp
        simp only [prefixIndicator, e1, ite_false, mul_zero] at hj ⊢
        simp only [e2, Fin.succ_last] at hj ⊢
        simp only [hcs]
        linarith

/-- Every decreasing vector is its signed constant part plus a nonnegative
combination of prefix indicators. Its formal proof was
contributed by Aristotle and independently checked with AXLE. -/
theorem monotonePrefixCombination_eq {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    monotonePrefixCombination v i = v i := by
  have h := prefix_telescope_eq n v i
  have hm :
      max (v (Fin.last n)) 0 - max (-v (Fin.last n)) 0 =
        v (Fin.last n) := by
    rcases le_total 0 (v (Fin.last n)) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
  rw [monotonePrefixCombination, hm, h]

/-- The matrix column condition is exactly the decreasing-vector condition
on each column. -/
theorem hasWeaklyDecreasingColumns_iff_columns {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.HasWeaklyDecreasingColumns A ↔
      ∀ j, IsWeaklyDecreasingVector (fun i => A i j) := Iff.rfl

/-- Specializing every row variable to one gives the renamed one-alphabet
Ferrers polynomial. Its formal proof was contributed
by Aristotle and independently checked with AXLE. -/
theorem specializeAtList_one_ferrersPermanent_eq_rename {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial.specializeAtList (fun _ => (1 : ℝ))
        (List.ofFn fun i : Fin n => Sum.inl i) (ferrersPermanent A) =
      MvPolynomial.rename Sum.inr (ferrersColumnPolynomial A) := by
  classical
  rw [MvPolynomial.specializeAtList_eq_aeval]
  unfold ferrersPermanent ferrersColumnPolynomial Matrix.permanent
  simp only [map_sum, map_prod, map_add, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    MvPolynomial.rename_C, MvPolynomial.rename_X,
    MvPolynomial.algebraMap_eq]
  simp

private def columnHeight {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun r => A r j = 1).card

private theorem entry_eq_one_of_columnHeight_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hzeroOne : Matrix.IsZeroOne A)
    (hcols : Matrix.HasWeaklyDecreasingColumns A) {i j k : Fin n}
    (hjk : columnHeight A j ≤ columnHeight A k) (hij : A i j = 1) :
    A i k = 1 := by
  by_contra hik
  have hik0 : A i k = 0 := (hzeroOne i k).resolve_right hik
  have hsub :
      (Finset.univ.filter fun r => A r k = 1) ⊂
        (Finset.univ.filter fun r => A r j = 1) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hij], by simp [hik0]⟩
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rcases le_or_gt i r with h | h
      · have hle := hcols k i r h
        linarith
      · have hle := hcols j r i h.le
        rcases hzeroOne r j with h0 | h1
        · linarith
        · exact h1
  have hcard := Finset.card_lt_card hsub
  unfold columnHeight at hjk; lia

/-- Permuting decreasing zero-one columns by their heights produces a Ferrers
matrix. Its formal proof was contributed by Aristotle
and independently checked with AXLE. -/
theorem exists_columnPermutation_isFerrers {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hzeroOne : Matrix.IsZeroOne A)
    (hcols : Matrix.HasWeaklyDecreasingColumns A) :
    ∃ τ : Equiv.Perm (Fin n), Matrix.IsFerrers (A.submatrix id τ) := by
  refine ⟨Tuple.sort (columnHeight A), ?_, ?_, ?_⟩
  · intro i j
    exact hzeroOne _ _
  · intro j i k hik
    exact hcols _ _ _ hik
  · intro i j k hjk
    have hmono := Tuple.monotone_sort (columnHeight A) hjk
    simp only [Function.comp_apply] at hmono
    simp only [Matrix.submatrix_apply, id]
    rcases hzeroOne i (Tuple.sort (columnHeight A) j) with h0 | h1
    · rcases hzeroOne i (Tuple.sort (columnHeight A) k) with h0' | h1'
      · simp [h0, h0']
      · simp [h0, h1']
    · simp [h1, entry_eq_one_of_columnHeight_le hzeroOne hcols hmono h1]

end

end Permanent
end RealRooted
