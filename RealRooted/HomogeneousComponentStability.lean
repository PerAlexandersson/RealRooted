module

public import RealRooted.AffineLineRestriction
public import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
public import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative
import RealRooted.Mathlib.RingTheory.MvPolynomial.Homogeneous
import RealRooted.RootContinuity
import RealRooted.MultivariateStability.JumpSystem

/-!
# Stability of the top homogeneous component

This file constructs a stable damping homotopy from a multivariate polynomial
toward its top homogeneous component. Root continuity will supply the endpoint.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace RealRooted

noncomputable section

/-- Dampen the degree-`k` homogeneous component by `δ ^ (totalDegree - k)`.
At positive `δ`, this is a nonzero scalar multiple of a positive coordinate
rescaling of the source polynomial. -/
def homogeneousTopApproximation {σ : Type*} (P : MvPolynomial σ ℝ)
    (δ : ℝ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.range (P.totalDegree + 1),
    MvPolynomial.C (δ ^ (P.totalDegree - k)) *
      MvPolynomial.homogeneousComponent k P

/-- Evaluating the damping homotopy is evaluation of ordinary homogenization
with the homogenizing coordinate specialized to the damping parameter. -/
theorem eval_homogeneousTopApproximation {σ : Type*}
    (P : MvPolynomial σ ℝ) (δ : ℝ) (z : σ → ℝ) :
    MvPolynomial.eval z (homogeneousTopApproximation P δ) =
      MvPolynomial.eval (fun o => Option.elim o δ z)
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) := by
  rw [MvPolynomial.eval_ordinaryHomogenization]
  simp [homogeneousTopApproximation]

/-- Complexification commutes with the damping homotopy term by term. -/
theorem complexifyMv_homogeneousTopApproximation {σ : Type*}
    (P : MvPolynomial σ ℝ) (δ : ℝ) :
    complexifyMv (homogeneousTopApproximation P δ) =
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        MvPolynomial.C ((δ : ℂ) ^ (P.totalDegree - k)) *
          MvPolynomial.homogeneousComponent k (complexifyMv P) := by
  unfold homogeneousTopApproximation complexifyMv
  simp [MvPolynomial.map_homogeneousComponent]

/-- At nonzero damping parameter, evaluation of the homotopy is a scalar
multiple of evaluation of the source at inversely rescaled coordinates. -/
theorem eval_complexifyMv_homogeneousTopApproximation {σ : Type*}
    (P : MvPolynomial σ ℝ) (δ : ℝ) (z : σ → ℂ) (hδ : δ ≠ 0) :
    MvPolynomial.eval z (complexifyMv (homogeneousTopApproximation P δ)) =
      (δ : ℂ) ^ P.totalDegree *
        MvPolynomial.eval (fun i => z i / (δ : ℂ)) (complexifyMv P) := by
  have htotal : (complexifyMv P).totalDegree = P.totalDegree := by
    unfold complexifyMv MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective _ Complex.ofRealHom.injective]
  rw [complexifyMv_homogeneousTopApproximation]
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [← MvPolynomial.eval_ordinaryHomogenization]
  rw [MvPolynomial.eval_ordinaryHomogenization_eq_pow_mul_eval_div
    (complexifyMv P) (by rw [htotal]) (by exact_mod_cast hδ)]

/-- Positive damping parameters preserve multivariate real stability. -/
theorem MvRealStable.homogeneousTopApproximation
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    {δ : ℝ} (hδ : 0 < δ) :
    MvRealStable (homogeneousTopApproximation P δ) := by
  intro z hz
  rw [eval_complexifyMv_homogeneousTopApproximation P δ z hδ.ne']
  apply mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hδ.ne'))
  apply hP
  intro i
  change 0 < (z i / (δ : ℂ)).im
  rw [Complex.div_ofReal_im]
  exact div_pos (hz i) hδ

/-- Affine-line restriction commutes with the finite damping sum. -/
theorem realAffineLineRestriction_homogeneousTopApproximation
    {σ : Type*} (P : MvPolynomial σ ℝ) (δ : ℝ) (a b : σ → ℝ) :
    realAffineLineRestriction a b (homogeneousTopApproximation P δ) =
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        Polynomial.C (δ ^ (P.totalDegree - k)) *
          realAffineLineRestriction a b
            (MvPolynomial.homogeneousComponent k P) := by
  unfold homogeneousTopApproximation realAffineLineRestriction
  simp

/-- Every damped affine restriction has the same top coefficient as the
restriction of the top homogeneous component. -/
theorem coeff_realAffineLineRestriction_homogeneousTopApproximation
    {σ : Type*} (P : MvPolynomial σ ℝ) (δ : ℝ) (a b : σ → ℝ) :
    (realAffineLineRestriction a b
      (homogeneousTopApproximation P δ)).coeff P.totalDegree =
      MvPolynomial.eval b
        (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  rw [realAffineLineRestriction_homogeneousTopApproximation,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single P.totalDegree]
  · simp only [Polynomial.coeff_C_mul, Nat.sub_self, pow_zero, one_mul]
    exact MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction
      (MvPolynomial.homogeneousComponent_isHomogeneous P.totalDegree P) a b
  · intro k hk hkd
    rw [Polynomial.coeff_C_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt]
    · simp
    · have hk_le : k ≤ P.totalDegree :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact (MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
        (MvPolynomial.homogeneousComponent_isHomogeneous k P) a b).trans_lt
          (lt_of_le_of_ne hk_le hkd)
  · simp

/-- Damping does not increase the degree of an affine-line restriction beyond
the total degree of the source polynomial. -/
theorem natDegree_realAffineLineRestriction_homogeneousTopApproximation_le
    {σ : Type*} (P : MvPolynomial σ ℝ) (δ : ℝ) (a b : σ → ℝ) :
    (realAffineLineRestriction a b
      (homogeneousTopApproximation P δ)).natDegree ≤ P.totalDegree := by
  rw [realAffineLineRestriction_homogeneousTopApproximation]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  exact (MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
    (MvPolynomial.homogeneousComponent_isHomogeneous k P) a b).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- Along any damping parameters tending to zero, every coefficient of an
affine-line restriction tends to the corresponding coefficient of the top
homogeneous component. -/
theorem tendsto_coeff_realAffineLineRestriction_homogeneousTopApproximation
    {σ ι : Type*} {l : Filter ι} (P : MvPolynomial σ ℝ)
    (δ : ι → ℝ) (hδ : Filter.Tendsto δ l (nhds 0))
    (a b : σ → ℝ) (i : ℕ) :
    Filter.Tendsto
      (fun n => (realAffineLineRestriction a b
        (homogeneousTopApproximation P (δ n))).coeff i) l
      (nhds ((realAffineLineRestriction a b
        (MvPolynomial.homogeneousComponent P.totalDegree P)).coeff i)) := by
  have hsum : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range (P.totalDegree + 1),
        (δ n) ^ (P.totalDegree - k) *
          (realAffineLineRestriction a b
            (MvPolynomial.homogeneousComponent k P)).coeff i) l
      (nhds (∑ k ∈ Finset.range (P.totalDegree + 1),
        0 ^ (P.totalDegree - k) *
          (realAffineLineRestriction a b
            (MvPolynomial.homogeneousComponent k P)).coeff i)) :=
    tendsto_finsetSum (Finset.range (P.totalDegree + 1)) fun k _ =>
      (hδ.pow (P.totalDegree - k)).mul tendsto_const_nhds
  have hlimit :
      (∑ k ∈ Finset.range (P.totalDegree + 1),
        0 ^ (P.totalDegree - k) *
          (realAffineLineRestriction a b
            (MvPolynomial.homogeneousComponent k P)).coeff i) =
        (realAffineLineRestriction a b
          (MvPolynomial.homogeneousComponent P.totalDegree P)).coeff i := by
    rw [Finset.sum_eq_single P.totalDegree]
    · simp
    · intro k hk hkd
      have hk_le : k ≤ P.totalDegree :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hsub : P.totalDegree - k ≠ 0 :=
        Nat.sub_ne_zero_iff_lt.mpr (lt_of_le_of_ne hk_le hkd)
      simp [hsub]
    · simp
  convert hsum using 1
  · funext n
    rw [realAffineLineRestriction_homogeneousTopApproximation,
      Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul]
  · rw [hlimit]

/-- The top homogeneous component of a nonzero real stable polynomial with
nonnegative coefficients is real stable. -/
theorem MvRealStable.homogeneousComponent_totalDegree
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (hnn : MvPolynomial.HasNonnegCoeffs P) (hP : P ≠ 0) :
    MvRealStable
      (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  apply mvRealStable_of_forall_realAffineLineRestriction
  intro a b hb
  let H := MvPolynomial.homogeneousComponent P.totalDegree P
  let L := MvPolynomial.eval b H
  let qLimit := realAffineLineRestriction a b H
  have hHhom : H.IsHomogeneous P.totalDegree :=
    MvPolynomial.homogeneousComponent_isHomogeneous P.totalDegree P
  have hHne : H ≠ 0 :=
    MvPolynomial.homogeneousComponent_totalDegree_ne_zero hP
  have hHnn : MvPolynomial.HasNonnegCoeffs H :=
    hnn.homogeneousComponent P.totalDegree
  have hLpos : 0 < L := hHnn.eval_pos hHne hb
  have hqlCoeff : qLimit.coeff P.totalDegree = L :=
    MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction
      hHhom a b
  have hqlDeg : qLimit.natDegree = P.totalDegree := by
    apply le_antisymm
    · exact MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
        hHhom a b
    · exact Polynomial.le_natDegree_of_ne_zero
        (hqlCoeff.trans_ne hLpos.ne')
  have hqlLead : qLimit.leadingCoeff = L := by
    rw [← Polynomial.coeff_natDegree, hqlDeg, hqlCoeff]
  let δseq : ℕ → ℝ := fun M => 1 / ((M : ℝ) + 1)
  have hδ : Filter.Tendsto δseq Filter.atTop (nhds 0) := by
    simpa [δseq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδpos (M : ℕ) : 0 < δseq M := by
    dsimp [δseq]
    positivity
  let qM : ℕ → ℝ[X] := fun M =>
    realAffineLineRestriction a b
      (RealRooted.homogeneousTopApproximation P (δseq M))
  have hqDegLe (M : ℕ) : (qM M).natDegree ≤ P.totalDegree := by
    simpa [qM] using
      natDegree_realAffineLineRestriction_homogeneousTopApproximation_le
        P (δseq M) a b
  have hqCoeffTop (M : ℕ) : (qM M).coeff P.totalDegree = L := by
    simpa [qM, L, H] using
      coeff_realAffineLineRestriction_homogeneousTopApproximation
        P (δseq M) a b
  have hqDeg (M : ℕ) : (qM M).natDegree = P.totalDegree :=
    le_antisymm (hqDegLe M)
      (Polynomial.le_natDegree_of_ne_zero
        ((hqCoeffTop M).trans_ne hLpos.ne'))
  have hqLead (M : ℕ) : (qM M).leadingCoeff = L := by
    rw [← Polynomial.coeff_natDegree, hqDeg M, hqCoeffTop M]
  have hqSplits (M : ℕ) : (qM M).Splits := by
    simpa [qM] using
      (MvRealStable.realAffineLineRestriction_splits_ne_zero
        (MvRealStable.homogeneousTopApproximation hst (hδpos M)) a b hb).1
  have hqCoeff (i : ℕ) :
      Filter.Tendsto (fun M => (qM M).coeff i) Filter.atTop
        (nhds (qLimit.coeff i)) := by
    simpa [qM, qLimit, H] using
      tendsto_coeff_realAffineLineRestriction_homogeneousTopApproximation
        P δseq hδ a b i
  let f : ℝ[X] := Polynomial.C L⁻¹ * qLimit
  let g : ℕ → ℝ[X] := fun M => Polynomial.C L⁻¹ * qM M
  have hLne : L ≠ 0 := hLpos.ne'
  have hfMonic : f.Monic := by
    dsimp [f]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hqlLead]
    simp [hLne]
  have hgMonic (M : ℕ) : (g M).Monic := by
    dsimp [g]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hqLead M]
    simp [hLne]
  have hgDegree (M : ℕ) : (g M).natDegree = f.natDegree := by
    dsimp [g, f]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hLne),
      Polynomial.natDegree_C_mul (inv_ne_zero hLne), hqDeg M, hqlDeg]
  have hgSplits (M : ℕ) : (g M).Splits :=
    (hqSplits M).C_mul L⁻¹
  have hgCoeff (i : ℕ) :
      Filter.Tendsto (fun M => (g M).coeff i) Filter.atTop
        (nhds (f.coeff i)) := by
    dsimp [g, f]
    simp only [Polynomial.coeff_C_mul]
    exact tendsto_const_nhds.mul (hqCoeff i)
  have hfSplits : f.Splits :=
    splits_of_monic_of_coeff_tendsto
      hfMonic hgMonic hgDegree hgSplits hgCoeff
  have hscaled := hfSplits.C_mul L
  rw [show Polynomial.C L * f = qLimit by
    dsimp [f]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hLne,
      Polynomial.C_1, one_mul]] at hscaled
  exact ⟨hscaled, Polynomial.leadingCoeff_ne_zero.mp
    (hqlLead.trans_ne hLne)⟩

private theorem weight_neg_one_eq_neg_degree {n : ℕ} (d : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ => (-1 : ℤ)) d = -(d.degree : ℤ) := by
  rw [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum]
  push_cast
  simp

/-- For finitely many variables, the top homogeneous component of a
real-stable polynomial is real stable, with no coefficient-sign hypothesis. -/
theorem MvRealStable.homogeneousComponent_totalDegree_fin
    {n : ℕ} {P : MvPolynomial (Fin n) ℝ} (hst : MvRealStable P) :
    MvRealStable
      (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  let w : Fin n → ℤ := fun _ => -1
  have hmin : ∀ d ∈ P.support,
      -(P.totalDegree : ℤ) ≤ Finsupp.weight w d := by
    intro d hd
    rw [show Finsupp.weight w d = -(d.degree : ℤ) by
      simpa [w] using weight_neg_one_eq_neg_degree d]
    apply neg_le_neg
    exact_mod_cast MvPolynomial.le_totalDegree hd
  obtain ⟨d, hd, hdegree⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hst.ne_zero) (fun e => e.degree)
  have htotal : P.totalDegree = d.degree := by
    have hfun :
        (fun e : Fin n →₀ ℕ => e.sum fun _ k => k) =
          fun e => e.degree := by
      funext e
      rw [Finsupp.degree_apply]
      rfl
    rw [MvPolynomial.totalDegree, hfun]
    exact hdegree
  have hex : ∃ d ∈ P.support,
      Finsupp.weight w d = -(P.totalDegree : ℤ) := by
    refine ⟨d, hd, ?_⟩
    rw [show Finsupp.weight w d = -(d.degree : ℤ) by
      simpa [w] using weight_neg_one_eq_neg_degree d, htotal]
  have hstable : JumpSystem.Stable
      (MvPolynomial.weightedHomogeneousComponent w
        (-(P.totalDegree : ℤ)) P) :=
    JumpSystem.Stable.weightedHomogeneousComponent hst w
      (-(P.totalDegree : ℤ)) hmin hex
  have heq :
      MvPolynomial.weightedHomogeneousComponent w
          (-(P.totalDegree : ℤ)) P =
        MvPolynomial.homogeneousComponent P.totalDegree P := by
    ext e
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_homogeneousComponent]
    rw [show Finsupp.weight w e = -(e.degree : ℤ) by
      simpa [w] using weight_neg_one_eq_neg_degree e]
    simp
  rw [heq] at hstable
  exact hstable

/-- The top homogeneous component of a finite-variable real-stable polynomial
does not vanish on a coordinatewise strictly positive real vector. -/
theorem MvRealStable.eval_homogeneousComponent_totalDegree_ne_zero
    {n : ℕ} {P : MvPolynomial (Fin n) ℝ} (hst : MvRealStable P)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    MvPolynomial.eval b
      (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
  let H := MvPolynomial.homogeneousComponent P.totalDegree P
  have hHstable : MvRealStable H := by
    simpa [H] using hst.homogeneousComponent_totalDegree_fin
  have hHhom : (complexifyMv H).IsHomogeneous P.totalDegree := by
    exact (MvPolynomial.homogeneousComponent_isHomogeneous
      P.totalDegree P).map Complex.ofRealHom
  intro heval
  have hevalH : MvPolynomial.eval b H = 0 := by
    simpa [H] using heval
  have hcomplexEval :
      MvPolynomial.eval (fun i => (b i : ℂ)) (complexifyMv H) = 0 := by
    change MvPolynomial.eval (Complex.ofRealHom ∘ b)
      (MvPolynomial.map Complex.ofRealHom H) = 0
    rw [← MvPolynomial.map_eval Complex.ofRealHom b H]
    simp [hevalH]
  have hnonzero := hHstable (fun i => Complex.I * (b i : ℂ)) fun i => by
    simpa using hb i
  apply hnonzero
  rw [hHhom.eval_smul, hcomplexEval, mul_zero]

end

end RealRooted
