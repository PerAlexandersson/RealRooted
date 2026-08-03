import RealRooted.Mathlib.Algebra.MvPolynomial.Degrees
import RealRooted.Mathlib.Algebra.MvPolynomial.Equiv
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.DegreeBox
import Mathlib.RingTheory.Polynomial.Vieta
import RealRooted.GraceHalfPlane
import RealRooted.PartialSymmetrization
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

private theorem binomialUnlift_add (n : ℕ) (p q : ℂ[X]) :
    binomialUnlift n (p + q) =
      binomialUnlift n p + binomialUnlift n q := by
  unfold binomialUnlift
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.coeff_add, add_div, map_add]

private theorem binomialUnlift_smul (n : ℕ) (c : ℂ) (p : ℂ[X]) :
    binomialUnlift n (c • p) = c • binomialUnlift n p := by
  unfold binomialUnlift
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Polynomial.coeff_smul, div_eq_mul_inv]
  change (Polynomial.monomial k)
    (c * p.coeff k * (n.choose k : ℂ)⁻¹) =
      c • (Polynomial.monomial k)
        (p.coeff k * (n.choose k : ℂ)⁻¹)
  rw [mul_assoc]
  exact (Polynomial.smul_monomial c k
    (p.coeff k * (n.choose k : ℂ)⁻¹)).symm

private theorem reducedPolarization_add (n : ℕ) (p q : ℂ[X]) :
    reducedPolarization n (p + q) =
      reducedPolarization n p + reducedPolarization n q := by
  unfold reducedPolarization
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp [add_mul]

private theorem reducedPolarization_smul (n : ℕ) (c : ℂ) (p : ℂ[X]) :
    reducedPolarization n (c • p) = c • reducedPolarization n p := by
  unfold reducedPolarization
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- Polarization as a complex-linear map on univariate polynomials. -/
noncomputable def polarizationLinearMap (n : ℕ) :
    ℂ[X] →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun := polarization n
  map_add' p q := by
    change polarization n (p + q) = polarization n p + polarization n q
    simp only [polarization, binomialUnlift_add, reducedPolarization_add]
  map_smul' c p := by
    change polarization n (c • p) = c • polarization n p
    simp only [polarization, binomialUnlift_smul, reducedPolarization_smul]

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

/-- Source polarization `Π↑ₙ` as a linear map from the one-variable degree-`n`
box to the multiaffine all-ones box. -/
noncomputable def polarizationDegreeBoxLinearMap (n : ℕ) :
    MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1) :=
  LinearMap.codRestrict (MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1))
    ((polarizationLinearMap n).comp
      ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toLinearMap.domRestrict
        (MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n))))
    (fun q =>
      (MvPolynomial.mem_degreeOfLE_iff_degreeOf _).2
        (isMultiaffine_polarization n
          (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1)))

/-- The diagonal projection `Π↓ₙ`, obtained by identifying every polarization
variable with the unique univariate variable. -/
noncomputable def diagonalProjection (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₗ[ℂ] ℂ[X] where
  toFun q :=
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
      (MvPolynomial.rename (fun _ : Fin n => (0 : Fin 1)) q)
  map_add' q r := by simp
  map_smul' c q := by
    simp [MvPolynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]

/-- Diagonal projection of an all-ones degree-box polynomial has degree at
most the size of its polarization block. -/
theorem natDegree_diagonalProjection_le {n : ℕ}
    (q : MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1)) :
    (diagonalProjection n q).natDegree ≤ n := by
  have hdeg : ∀ i, q.1.degreeOf i ≤ 1 :=
    (MvPolynomial.mem_degreeOfLE_iff_degreeOf q.1).mp q.2
  change (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
    (MvPolynomial.rename (fun _ : Fin n => (0 : Fin 1)) q.1)).natDegree ≤ n
  calc
    _ ≤ (MvPolynomial.rename (fun _ : Fin n => (0 : Fin 1)) q.1).totalDegree :=
      MvPolynomial.natDegree_uniqueAlgEquiv_le_totalDegree _
    _ ≤ q.1.totalDegree := MvPolynomial.totalDegree_rename_le _ _
    _ ≤ ∑ i, q.1.degreeOf i := MvPolynomial.totalDegree_le_sum_degreeOf q.1
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ => hdeg i
    _ = n := by simp

/-- Diagonal projection as a linear map from the multiaffine source box to the
original one-variable degree box. This is the source-side map `Π↓ₙ`. -/
noncomputable def diagonalProjectionDegreeBox (n : ℕ) :
    MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) :=
  LinearMap.codRestrict (MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n))
    (((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.toLinearMap.comp
      (diagonalProjection n)).domRestrict
        (MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1)))
    (fun q => by
      apply (MvPolynomial.mem_degreeOfLE_iff_degreeOf _).2
      intro i
      change MvPolynomial.degreeOf i
        ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
          (diagonalProjection n q)) ≤ n
      rw [Unique.eq_default i,
        MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
      exact natDegree_diagonalProjection_le q)

/-- Equation (2.2) on the source side: diagonal projection is a left inverse
to polarization on polynomials of degree at most `n`. -/
theorem diagonalProjection_polarizationDegreeBox {n : ℕ} {p : ℂ[X]}
    (hp : p.natDegree ≤ n) :
    diagonalProjection n (polarizationDegreeBox n p) = p := by
  change MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
    (MvPolynomial.rename (fun _ : Fin n => (0 : Fin 1)) (polarization n p)) = p
  rw [rename_polarization_const hp]
  exact (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).apply_symm_apply p

/-- Degree-box form of the source reconstruction identity
`Π↓ₙ (Π↑ₙ p) = p`. -/
theorem coe_diagonalProjectionDegreeBox_polarizationDegreeBox
    {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) :
    (diagonalProjectionDegreeBox n (polarizationDegreeBox n p) :
      MvPolynomial (Fin 1) ℂ) =
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p := by
  change (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
    (diagonalProjection n (polarizationDegreeBox n p)) =
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm p
  rw [diagonalProjection_polarizationDegreeBox hp]

/-- Source-side equation (2.2): diagonal projection is a left inverse to the
linear polarization map on the one-variable degree box. -/
theorem diagonalProjectionDegreeBox_comp_polarizationDegreeBoxLinearMap
    {n : ℕ}
    (q : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n)) :
    diagonalProjectionDegreeBox n (polarizationDegreeBoxLinearMap n q) = q := by
  have hdeg : ∀ i, q.1.degreeOf i ≤ n :=
    (MvPolynomial.mem_degreeOfLE_iff_degreeOf q.1).mp q.2
  have hp : (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1).natDegree ≤ n := by
    calc
      (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1).natDegree =
          q.1.degreeOf default := by
        simpa only [AlgEquiv.symm_apply_apply] using
          (MvPolynomial.degreeOf_uniqueAlgEquiv_symm (σ := Fin 1)
            (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1)).symm
      _ ≤ n := hdeg default
  have hdiag :
      diagonalProjection n
        (polarization n (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1)) =
          MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1 :=
    diagonalProjection_polarizationDegreeBox hp
  apply Subtype.ext
  change (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
    (diagonalProjection n
      (polarization n (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1) q.1))) = q.1
  rw [hdiag]
  exact (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm_apply_apply q.1

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

/-- Diagonal projection sends a bounded multiaffine basis monomial to the
univariate monomial whose exponent is its total degree. -/
theorem diagonalProjection_basisDegreeOfLE {n : ℕ}
    (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    diagonalProjection n
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m) =
      Polynomial.X ^ m.1.degree := by
  change MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
      (MvPolynomial.rename (fun _ : Fin n => (0 : Fin 1))
        ((MvPolynomial.basisDegreeOfLE (R := ℂ)
          (fun _ : Fin n => 1) m :
            MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1)) :
          MvPolynomial (Fin n) ℂ)) =
    Polynomial.X ^ m.1.degree
  rw [MvPolynomial.coe_basisDegreeOfLE]
  rw [MvPolynomial.rename_monomial, MvPolynomial.uniqueAlgEquiv_monomial]
  rw [Polynomial.X_pow_eq_monomial]
  apply congrArg (fun k : ℕ => Polynomial.monomial k (1 : ℂ))
  calc
    (Finsupp.mapDomain (fun _ : Fin n => (0 : Fin 1)) m.1) default =
        m.1.sum (fun _ e => e) := by
      simp [Finsupp.mapDomain, Finsupp.sum_apply]
    _ = m.1.degree := by
      rw [Finsupp.degree_apply]
      rfl

private theorem degree_le_fin_card_of_le_one {n : ℕ}
    (m : Fin n →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
    m.degree ≤ n := by
  rw [Finsupp.degree_apply]
  calc
    ∑ i ∈ m.support, m i ≤ ∑ i ∈ m.support, 1 :=
      Finset.sum_le_sum fun i hi => hm i
    _ = m.support.card := by simp
    _ ≤ Fintype.card (Fin n) := Finset.card_le_univ m.support
    _ = n := Fintype.card_fin n

/-- The one-variable degree-box index obtained by diagonalizing a bounded
multiaffine exponent vector. -/
noncomputable def diagonalDegreeBoxIndex {n : ℕ}
    (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    {d : Fin 1 →₀ ℕ // ∀ i, d i ≤ n} :=
  ⟨Finsupp.single default m.1.degree, fun i => by
    rw [Subsingleton.elim i default, Finsupp.single_eq_same]
    exact degree_le_fin_card_of_le_one m.1 m.2⟩

/-- Diagonal projection on degree boxes sends a multiaffine basis monomial to
the one-variable basis monomial indexed by its total degree. -/
theorem diagonalProjectionDegreeBox_basisDegreeOfLE {n : ℕ}
    (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    diagonalProjectionDegreeBox n
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m) =
      MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
        (diagonalDegreeBoxIndex m) := by
  apply Subtype.ext
  change (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
      (diagonalProjection n
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m)) =
    ((MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
      (diagonalDegreeBoxIndex m) :
        MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n)) :
      MvPolynomial (Fin 1) ℂ)
  apply (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).injective
  rw [AlgEquiv.apply_symm_apply, diagonalProjection_basisDegreeOfLE,
    MvPolynomial.coe_basisDegreeOfLE,
    MvPolynomial.uniqueAlgEquiv_monomial]
  simp [diagonalDegreeBoxIndex, Polynomial.X_pow_eq_monomial]

end RealRooted

namespace RealRooted

/-- Reduced polarization is symmetric in its polarized variables. -/
theorem isSymmetric_reducedPolarization (n : ℕ) (f : ℂ[X]) :
    MvPolynomial.IsSymmetric (reducedPolarization n f) := by
  classical
  intro e
  simp only [reducedPolarization, map_sum, map_mul,
    MvPolynomial.rename_C, MvPolynomial.rename_esymm]

/-- Polarization is symmetric in its polarized variables. -/
theorem isSymmetric_polarization (n : ℕ) (p : ℂ[X]) :
    MvPolynomial.IsSymmetric (polarization n p) := by
  unfold polarization
  exact isSymmetric_reducedPolarization n (binomialUnlift n p)

end RealRooted
