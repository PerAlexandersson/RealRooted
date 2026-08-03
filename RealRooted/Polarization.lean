import Mathlib.Algebra.MvPolynomial.Equiv
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.DegreeBox
import Mathlib.RingTheory.Polynomial.Vieta
import RealRooted.GraceHalfPlane
import RealRooted.Multiaffine
import RealRooted.MultivariateStability

/-!
# Polarization and upper-half-plane stability

This file defines the polarization of a degree-bounded univariate complex
polynomial and proves the exact-degree stability theorem used in
Gribinski--Marcus, Theorem 2.6. The proof derives the Grace--Walsh--Szego
coincidence step from the project's checked upper/lower-half-plane form of
Grace's apolarity theorem.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

/-- Polarization of a reduced coefficient sequence. Its diagonal
specialization is `binomialLift n f`. -/
def reducedPolarization (n : ℕ) (f : ℂ[X]) : MvPolynomial (Fin n) ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    MvPolynomial.C (f.coeff k) * MvPolynomial.esymm (Fin n) ℂ k

/-- Divide degree-`n` polynomial coefficients by their binomial weights. -/
def binomialUnlift (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.monomial k (p.coeff k / (n.choose k : ℂ))

/-- The binomial unlift is a right inverse on polynomials of degree at most
`n`. -/
theorem binomialLift_binomialUnlift {n : ℕ} {p : ℂ[X]}
    (hp : p.natDegree ≤ n) :
    binomialLift n (binomialUnlift n p) = p := by
  ext k
  rw [coeff_binomialLift]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    unfold binomialUnlift
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · simp only [Polynomial.coeff_monomial_same]
      rw [mul_div_cancel₀ _ (Nat.cast_choose_ne_zero (R := ℂ) hk)]
    · intro j hj hjk
      simp [Polynomial.coeff_monomial, hjk]
    · intro hknot
      exact (hknot (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk)).elim
  · rw [if_neg hk]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt hp (Nat.lt_of_not_ge hk))).symm

/-- The degree-`n` polarization of `p`: the coefficient of the `k`th
elementary symmetric polynomial is `p.coeff k / choose n k`. -/
def polarization (n : ℕ) (p : ℂ[X]) : MvPolynomial (Fin n) ℂ :=
  reducedPolarization n (binomialUnlift n p)

theorem isMultiaffine_reducedPolarization (n : ℕ) (p : ℂ[X]) :
    MvPolynomial.IsMultiaffine (reducedPolarization n p) := by
  unfold reducedPolarization
  apply MvPolynomial.IsMultiaffine.sum
  intro k hk
  exact (MvPolynomial.IsMultiaffine.esymm k).C_mul _

/-- A polarization is multiaffine. -/
theorem isMultiaffine_polarization (n : ℕ) (p : ℂ[X]) :
    MvPolynomial.IsMultiaffine (polarization n p) :=
  isMultiaffine_reducedPolarization n (binomialUnlift n p)

/-- The monic polynomial whose roots are the entries of `z`. -/
def polarizationRootPolynomial {n : ℕ} (z : Fin n → ℂ) : ℂ[X] :=
  (((Finset.univ.val.map z).map fun w => X - C w).prod)

/-- Evaluation of a reduced polarization in elementary symmetric functions. -/
theorem eval_reducedPolarization (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) :
    MvPolynomial.eval z (reducedPolarization n f) =
      ∑ k ∈ Finset.range (n + 1),
        f.coeff k * (Finset.univ.val.map z).esymm k := by
  simp only [reducedPolarization, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℂ k z

/-- The elementary symmetric function of `n` equal entries. -/
theorem esymm_const_fin (n k : ℕ) (w : ℂ) :
    (Finset.univ.val.map (fun _ : Fin n => w)).esymm k =
      (n.choose k : ℂ) * w ^ k := by
  rw [Finset.esymm_map_val]
  calc
    ∑ t ∈ Finset.univ.powersetCard k, ∏ _i ∈ t, w =
        ∑ _t ∈ Finset.univ.powersetCard k, w ^ k := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
    _ = (n.choose k : ℂ) * w ^ k := by
      simp [Finset.card_powersetCard, nsmul_eq_mul]

/-- The diagonal specialization of a reduced polarization is its binomial
lift. -/
theorem eval_reducedPolarization_const (n : ℕ) (f : ℂ[X]) (w : ℂ) :
    MvPolynomial.eval (fun _ : Fin n => w) (reducedPolarization n f) =
      (binomialLift n f).eval w := by
  rw [eval_reducedPolarization, eval_binomialLift]
  simp only [esymm_const_fin, apolarEval]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The diagonal specialization of `polarization n p` is `p`. -/
theorem eval_polarization_const {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n)
    (w : ℂ) :
    MvPolynomial.eval (fun _ : Fin n => w) (polarization n p) = p.eval w := by
  unfold polarization
  rw [eval_reducedPolarization_const, binomialLift_binomialUnlift hp]

/-- Renaming every polarization variable to the unique variable reconstructs
the original univariate polynomial. This is the diagonal identity for
polarization. -/
theorem rename_polarization_const {n : ℕ} {p : ℂ[X]}
    (hp : p.natDegree ≤ n) :
    MvPolynomial.rename (fun _ : Fin n ↦ (0 : Fin 1)) (polarization n p) =
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p := by
  apply (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Polynomial.funext
  intro w
  change Polynomial.eval₂ (RingHom.id ℂ) w
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
      (MvPolynomial.rename (fun _ : Fin n ↦ (0 : Fin 1))
        (polarization n p))) = p.eval w
  rw [MvPolynomial.eval₂_const_uniqueAlgEquiv]
  rw [MvPolynomial.eval₂_rename]
  change MvPolynomial.eval (fun _ : Fin n ↦ w) (polarization n p) = p.eval w
  exact eval_polarization_const hp w

/-- Package polarization as the multiaffine source polynomial
`Π↑ₙ p` in the all-ones degree box. -/
noncomputable def polarizationDegreeBox (n : ℕ) (p : ℂ[X]) :
    MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1) :=
  ⟨polarization n p,
    (MvPolynomial.mem_degreeOfLE_iff_degreeOf (polarization n p)).2
      (isMultiaffine_polarization n p)⟩

@[simp]
theorem coe_polarizationDegreeBox (n : ℕ) (p : ℂ[X]) :
    (polarizationDegreeBox n p : MvPolynomial (Fin n) ℂ) = polarization n p := rfl

/-- Evaluation of a polarization in elementary symmetric functions. -/
theorem eval_polarization (n : ℕ) (p : ℂ[X]) (z : Fin n → ℂ) :
    MvPolynomial.eval z (polarization n p) =
      ∑ k ∈ Finset.range (n + 1),
        p.coeff k / (n.choose k : ℂ) *
          (Finset.univ.val.map z).esymm k := by
  rw [polarization, eval_reducedPolarization]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  unfold binomialUnlift
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, hjk]
  · simp [hkn]

/-- The top elementary symmetric function is the product of all entries. -/
theorem esymm_card_eq_prod {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm s.card = s.prod := by
  simp [Multiset.esymm]

/-- The root polynomial of an `n`-tuple has degree `n`. -/
theorem natDegree_polarizationRootPolynomial {n : ℕ} (z : Fin n → ℂ) :
    (polarizationRootPolynomial z).natDegree = n := by
  unfold polarizationRootPolynomial
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  simp

/-- Every root of the root polynomial is one of the tuple entries. -/
theorem exists_eq_of_isRoot_polarizationRootPolynomial
    {n : ℕ} {z : Fin n → ℂ} {w : ℂ}
    (hw : (polarizationRootPolynomial z).IsRoot w) :
    ∃ i : Fin n, w = z i := by
  simpa only [Polynomial.IsRoot, polarizationRootPolynomial,
    Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Multiset.prod_eq_zero_iff, Multiset.mem_map, Finset.mem_val,
    Finset.mem_univ, true_and, sub_eq_zero] using hw

/-- Evaluating a reduced polarization is an apolar pairing against any
binomial unlift of the corresponding root polynomial. -/
theorem eval_reducedPolarization_eq_apolarPairing_of_binomialLift_eq_rootPolynomial
    {n : ℕ} (f g : ℂ[X]) (z : Fin n → ℂ)
    (hg : binomialLift n g = polarizationRootPolynomial z) :
    MvPolynomial.eval z (reducedPolarization n f) = apolarPairing n f g := by
  rw [eval_reducedPolarization]
  unfold apolarPairing
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hsub : n - k ≤ n := Nat.sub_le n k
  have hback : n - (n - k) = k := Nat.sub_sub_self hkn
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (n - k)) hg
  rw [coeff_binomialLift, if_pos hsub] at hcoeff
  have hrootCoeff :
      (polarizationRootPolynomial z).coeff (n - k) =
        (-1 : ℂ) ^ k * (Finset.univ.val.map z).esymm k := by
    unfold polarizationRootPolynomial
    rw [Multiset.prod_X_sub_C_coeff]
    · simp [hback]
    · simp
  rw [hrootCoeff, Nat.choose_symm hkn] at hcoeff
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    f.coeff k * (Finset.univ.val.map z).esymm k =
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * f.coeff k *
          (Finset.univ.val.map z).esymm k := by rw [hsign, one_mul]
    _ = (-1 : ℂ) ^ k * f.coeff k *
          ((-1 : ℂ) ^ k * (Finset.univ.val.map z).esymm k) := by ring
    _ = (-1 : ℂ) ^ k * f.coeff k *
          ((n.choose k : ℂ) * g.coeff (n - k)) := by rw [hcoeff]
    _ = (-1 : ℂ) ^ k * (n.choose k : ℂ) * f.coeff k *
          g.coeff (n - k) := by ring

/-- Grace--Walsh--Szego for reduced coefficients: exact-degree
upper-half-plane stability is preserved by polarization. -/
theorem mvUpperHalfPlaneStable_reducedPolarization {n : ℕ} {f : ℂ[X]}
    (hdeg : (binomialLift n f).natDegree = n)
    (hstable : ∀ w : ℂ, 0 < w.im → (binomialLift n f).eval w ≠ 0) :
    MvUpperHalfPlaneStable (reducedPolarization n f) := by
  intro z hz hzero
  obtain ⟨g, hg⟩ := exists_binomialLift_eq (polarizationRootPolynomial z)
    (natDegree_polarizationRootPolynomial z).le
  have hgdeg : (binomialLift n g).natDegree = n := by
    rw [hg, natDegree_polarizationRootPolynomial]
  have hap : AreApolar n f g := by
    rw [AreApolar,
      ← eval_reducedPolarization_eq_apolarPairing_of_binomialLift_eq_rootPolynomial
      f g z hg, hzero]
  have hroots : (binomialLift n f).RootsIn (lowerHalf 0) := by
    intro w hw
    exact not_lt.mp (fun hwpos => hstable w hwpos hw)
  obtain ⟨w, hwroot, hwlower⟩ :=
    grace_apolarity_lowerHalf hdeg hgdeg hap hroots
  obtain ⟨i, hwi⟩ :=
    exists_eq_of_isRoot_polarizationRootPolynomial (hg ▸ hwroot)
  rw [hwi] at hwlower
  exact (not_le_of_gt (hz i)) (by simpa [lowerHalf] using hwlower)

/-- Exact-degree upper-half-plane stability is preserved by univariate
polarization. -/
theorem mvUpperHalfPlaneStable_polarization {n : ℕ} {p : ℂ[X]}
    (hdeg : p.natDegree = n)
    (hstable : ∀ w : ℂ, 0 < w.im → p.eval w ≠ 0) :
    MvUpperHalfPlaneStable (polarization n p) := by
  unfold polarization
  apply mvUpperHalfPlaneStable_reducedPolarization
  · rw [binomialLift_binomialUnlift hdeg.le, hdeg]
  · simpa [binomialLift_binomialUnlift hdeg.le] using hstable

end

end RealRooted
