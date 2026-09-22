import RealRooted.JacobiDeformation.Boundary
import RealRooted.JacobiDeformation.CriticalCases
import RealRooted.JacobiDeformation.CriticalSigns
import RealRooted.JacobiDeformation.ShiftPreservation
import RealRooted.PFPolynomial

/-!
# The strict Jacobi deformation theorem

For every positive rank and every increment `0 < δ < 1`, the derivative of
the delta-zero deformation strictly interlaces the positive-delta
deformation.  The latter has simple, strictly negative roots.  Rank one is
kept explicit: its critical-sign condition is vacuous, but the same strict
interlacing package applies to the constant derivative and the linear
deformation.
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The full strict-interlacing package for the open Jacobi increment. -/
theorem polynomial_strict_package {m : ℕ} (hm : 1 ≤ m) {δ c d U V : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    StrictInterl (polynomial m 0 c d U V).derivative
        (polynomial m δ c d U V) ∧
      Interlaces (polynomial m 0 c d U V).derivative
        (polynomial m δ c d U V) ∧
      (polynomial m δ c d U V).Splits ∧
      HasSimpleRoots (polynomial m 0 c d U V).derivative ∧
      HasSimpleRoots (polynomial m δ c d U V) ∧
      (∀ r, (polynomial m 0 c d U V).derivative.IsRoot r →
        ¬(polynomial m δ c d U V).IsRoot r) := by
  obtain ⟨t, htinj, ht, hnodes⟩ :=
    exists_shiftedJacobiMonic_interior_nodes m hc hd
  have hbase := polynomial_zero_eq_imageProduct m hc hd hU hV t ht hnodes
  obtain ⟨hder0, hderSplits, _, hderBound⟩ :=
    imageProduct_derivative_package hm hU hV t htinj ht
  have hhSplits : (polynomial m 0 c d U V).derivative.Splits := by
    rw [hbase]
    exact hderSplits
  have hhPos : HasPosLeadingCoeff (polynomial m 0 c d U V).derivative :=
    (hasPosLeadingCoeff_of_monic (monic_polynomial m 0 c d U V)).derivative
      (by rw [natDegree_polynomial]; lia)
  have hgPos : HasPosLeadingCoeff (polynomial m δ c d U V) :=
    hasPosLeadingCoeff_of_monic (monic_polynomial m δ c d U V)
  have hhDegree : (polynomial m 0 c d U V).derivative.natDegree = m - 1 := by
    rw [(polynomial m 0 c d U V).natDegree_derivative,
      natDegree_polynomial]
  have hgDegree : (polynomial m δ c d U V).natDegree = (m - 1) + 1 := by
    rw [natDegree_polynomial, Nat.sub_add_cancel hm]
  have hsign : ∀ r, (polynomial m 0 c d U V).derivative.IsRoot r →
      (polynomial m δ c d U V).eval r *
        (polynomial m 0 c d U V).derivative.derivative.eval r < 0 := by
    intro r hr
    by_cases hm2 : 2 ≤ m
    · have hrImage : (imageProduct U V t).derivative.IsRoot r := by
        simpa only [hbase] using hr
      have hrMem : r ∈ (imageProduct U V t).derivative.roots :=
        (Polynomial.mem_roots hder0).mpr hrImage
      have hrBound := hderBound r hrMem
      have hcritical := polynomial_eval_mul_imageProduct_secondDerivative_neg
        hm2 hc hd hU hV hδ hδ1 t htinj ht hnodes hrBound hrImage
      simpa only [hbase] using hcritical
    · have hmEq : m = 1 := by lia
      subst m
      simp [polynomial_one] at hr
  exact strictInterl_assembly_of_eval_mul_derivative_neg_succ
    hhSplits hhPos hgPos hhDegree hgDegree hsign

/-- In the open increment range, the deformation has exactly its degree many
simple real roots and every root is strictly negative. -/
theorem polynomial_strict_splits_simple_roots_neg
    {m : ℕ} (hm : 1 ≤ m) {δ c d U V : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    (polynomial m δ c d U V).Splits ∧
      HasSimpleRoots (polynomial m δ c d U V) ∧
      ∀ r ∈ (polynomial m δ c d U V).roots, r < 0 := by
  have hpackage := polynomial_strict_package hm hc hd hU hV hδ hδ1
  have hnonneg := hasNonnegCoeffs_polynomial_of_pos hm hδ.le hc hd hU hV
  have hne := (monic_polynomial m δ c d U V).ne_zero
  refine ⟨hpackage.2.2.1, hpackage.2.2.2.2.1, ?_⟩
  intro r hr
  have hrle : r ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hnonneg r hr
  have hrne : r ≠ 0 := by
    intro hrzero
    subst r
    have hroot : (polynomial m δ c d U V).IsRoot 0 :=
      (Polynomial.mem_roots hne).mp hr
    have hzero : (polynomial m δ c d U V).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hroot
    exact (ne_of_gt (coeff_zero_pos_of_pos hm hδ.le hc hd hU hV)) hzero
  exact lt_of_le_of_ne hrle hrne

/-- In the open increment range, the deformation has exactly `m` roots,
counted with multiplicity.  Together with
`polynomial_strict_splits_simple_roots_neg`, these roots are distinct and
strictly negative. -/
theorem roots_card_polynomial_strict
    {m : ℕ} (hm : 1 ≤ m) {δ c d U V : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    (polynomial m δ c d U V).roots.card = m := by
  rw [card_roots_of_splits
    (polynomial_strict_splits_simple_roots_neg hm hc hd hU hV hδ hδ1).1,
    natDegree_polynomial]

/-- The open-increment deformation is a Pólya-frequency polynomial. -/
theorem isPFPolynomial_polynomial_strict
    {m : ℕ} (hm : 1 ≤ m) {δ c d U V : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    IsPFPolynomial (polynomial m δ c d U V) := by
  have hpackage := polynomial_strict_splits_simple_roots_neg
    hm hc hd hU hV hδ hδ1
  exact IsPFPolynomial.of_realRooted_nonneg
    (hasNonnegCoeffs_polynomial_of_pos hm hδ.le hc hd hU hV) hpackage.1

/-- Every nonnegative increment gives a split deformation with strictly
negative roots.  The fractional part is supplied either by the delta-zero
image product or by the strict theorem, and equation (25) transports it
through the integral part. -/
theorem polynomial_nonneg_parameter_splits_roots_neg
    {m : ℕ} (hm : 1 ≤ m) {δ c d U V : ℝ} (hδ : 0 ≤ δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    (polynomial m δ c d U V).Splits ∧
      ∀ r ∈ (polynomial m δ c d U V).roots, r < 0 := by
  let n : ℕ := ⌊δ⌋₊
  let ε : ℝ := δ - n
  have hnle : (n : ℝ) ≤ δ := by
    exact Nat.floor_le hδ
  have hnlt : δ < (n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one δ
  have hε : 0 ≤ ε := by
    dsimp only [ε]
    linarith
  have hε1 : ε < 1 := by
    dsimp only [ε]
    linarith
  have hδeq : δ = ε + n := by
    dsimp only [ε]
    ring
  have hpε : IsPFPolynomial (polynomial m ε c d U V) := by
    by_cases hεzero : ε = 0
    · rw [hεzero]
      obtain ⟨t, _, ht, hnodes⟩ :=
        exists_shiftedJacobiMonic_interior_nodes m hc hd
      have hbase := polynomial_zero_eq_imageProduct m hc hd hU hV t ht hnodes
      apply IsPFPolynomial.of_realRooted_nonneg
        (hasNonnegCoeffs_polynomial_of_pos hm (by norm_num) hc hd hU hV)
      rw [hbase]
      exact imageProduct_splits U V t
    · exact isPFPolynomial_polynomial_strict hm hc hd hU hV
        (lt_of_le_of_ne hε (Ne.symm hεzero)) hε1
  have hshift := polynomial_nat_shift_splits_roots_neg
    hm hε hc hd hU hV hpε n
  simpa only [hδeq] using hshift

/-- The all-rank nonnegative-parameter theorem, including the constant rank
zero boundary. -/
theorem polynomial_all_rank_nonneg_parameter
    (m : ℕ) {δ c d U V : ℝ} (hδ : 0 ≤ δ)
    (hc : 0 < c) (hd : 0 < d) (hU : 0 < U) (hV : 0 < V) :
    (polynomial m δ c d U V).Splits ∧
      ∀ r ∈ (polynomial m δ c d U V).roots, r < 0 := by
  cases m with
  | zero =>
      refine ⟨(polynomial_zero_boundary δ c d U V).1, ?_⟩
      simp
  | succ m =>
      exact polynomial_nonneg_parameter_splits_roots_neg
        (Nat.succ_le_succ (Nat.zero_le m)) hδ hc hd hU hV

end RealRooted.JacobiDeformation
