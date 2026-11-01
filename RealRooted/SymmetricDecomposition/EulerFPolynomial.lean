module

public import RealRooted.SymmetricDecomposition.FPolynomialRecurrence
public import RealRooted.EulerOperator.Pencil
public import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Bernstein
import RealRooted.BernsteinCone
import RealRooted.BrandenLeite.ChainPolynomial
import RealRooted.MaWang.DerivativeStep
import RealRooted.Mathlib.Algebra.Polynomial.CayleyTransform.Algebra

/-!
# Euler shifts through the f-polynomial transform

This file conjugates affine Euler shifts through `fPolynomial` and applies the
identity to polynomials whose roots lie in `[-1, 0]`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The `fPolynomial` transform is the Bernstein expansion with the same
coefficient polynomial. -/
theorem fPolynomial_eq_bernsteinExpansion (n : ℕ) (p : ℝ[X]) :
    fPolynomial n p = Polynomial.bernsteinExpansion n p := by
  unfold fPolynomial Polynomial.bernsteinExpansion
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The real Cayley transform of an exact-degree split polynomial also splits
over the reals. -/
theorem cayleyTransform_splits_real {p : ℝ[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n) :
    (p.cayleyTransform n).Splits := by
  rw [Polynomial.cayleyTransform_eq_rootFactorProduct hp hdeg]
  apply (Polynomial.Splits.C _).mul
  apply Polynomial.Splits.multisetProd
  intro q hq
  obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hq
  exact Polynomial.Splits.of_natDegree_le_one (by compute_degree!)

/-- Every positive-leading exact-degree polynomial with roots in `[-1, 0]`
is an `fPolynomial` transform of a PF polynomial. -/
theorem exists_isPFPolynomial_fPolynomial_eq {p : ℝ[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n)
    (hpos : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) :
    ∃ q : ℝ[X], q.natDegree ≤ n ∧ IsPFPolynomial q ∧
      p = fPolynomial n q := by
  let q := p.cayleyTransform n
  have hqnn : HasNonnegCoeffs q :=
    hasNonnegCoeffs_cayleyTransform_of_roots_mem_Icc hp hdeg hpos.le hroots
  have hqs : q.Splits := cayleyTransform_splits_real hp hdeg
  have hqdeg : q.natDegree ≤ n := by
    dsimp [q]
    rw [Polynomial.cayleyTransform_eq_rootFactorProduct hp hdeg]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_multiset_prod_le _).trans ?_
    rw [Multiset.map_map]
    calc
      (p.roots.map (fun r => ((1 + C r) * X - C r).natDegree)).sum ≤
          (p.roots.map (fun _ => 1)).sum := by
            apply Multiset.sum_map_le_sum_map
            intro r hr
            compute_degree!
      _ = p.roots.card := by simp
      _ = n := by rw [← hp.natDegree_eq_card_roots, hdeg]
  refine ⟨q, hqdeg, IsPFPolynomial.of_realRooted_nonneg hqnn hqs, ?_⟩
  have hexp := bernsteinExpansion_cayleyTransform_of_roots_mem_Icc
    hp hdeg hpos.le hroots
  rw [fPolynomial_eq_bernsteinExpansion]
  exact hexp.1

/-- Conjugacy of an affine Euler shift through `fPolynomial`:
`F_n ((theta + a) p) = (a - nX) F_n(p) + X(1+X) F_n(p)'`. -/
theorem fPolynomial_theta_add_C_mul {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) (a : ℝ) :
    fPolynomial n (theta p + C a * p) =
      (C a - C (n : ℝ) * X) * fPolynomial n p +
        X * (1 + X) * (fPolynomial n p).derivative := by
  rcases n with _ | n
  · rw [Polynomial.eq_C_of_natDegree_le_zero hdeg]
    simp [fPolynomial, theta]
  · have hpder : p.derivative.natDegree ≤ n := by
      rw [Polynomial.natDegree_derivative]
      exact Nat.sub_le_iff_le_add.mpr hdeg
    have hpad : fPolynomial (n + 1) p.derivative =
        (X + 1) * fPolynomial n p.derivative :=
      fPolynomial_succ_of_natDegree_le hpder
    have hbase := fPolynomial_derivative hdeg
    have hX : (X + 1 : ℝ[X]) ≠ 0 := by
      simpa using Polynomial.X_add_C_ne_zero (1 : ℝ)
    have hder : (X + 1) * (fPolynomial (n + 1) p).derivative =
        C ((n + 1 : ℕ) : ℝ) * fPolynomial (n + 1) p +
          fPolynomial n p.derivative := by
      apply mul_left_cancel₀ hX
      rw [mul_add, ← mul_assoc, ← pow_two, hbase, hpad]
      ring
    rw [fPolynomial_add, fPolynomial_C_mul, theta, fPolynomial_X_mul_succ]
    linear_combination -X * hder

/-- Every real affine Euler shift of a PF polynomial splits over the reals. -/
theorem splits_theta_add_C_mul {p : ℝ[X]} (hp : IsPFPolynomial p) (a : ℝ) :
    (theta p + C a * p).Splits := by
  by_cases hp0 : p = 0
  · subst p
    simp [theta]
  by_cases hdeg : p.natDegree = 0
  · apply Polynomial.Splits.of_natDegree_le_one
    refine (Polynomial.natDegree_add_le_of_degree_le
      (natDegree_theta_le p) (Polynomial.natDegree_C_mul_le a p)).trans ?_
    lia
  · have hinter : StrictInterl p (theta p) :=
      strictInterl_self_theta_of_natDegree_ne_zero hp hdeg
    have hall : AllComboRealRooted p (theta p) :=
      allComboRealRooted_of_strictInterl hinter
    simpa [add_comm] using hall.splits a 1

private theorem natDegree_theta_add_C_mul_le {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n) (a : ℝ) :
    (theta p + C a * p).natDegree ≤ n := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (natDegree_theta_le p).trans hdeg
  · exact (Polynomial.natDegree_C_mul_le a p).trans hdeg

/-- The conjugated interval Euler operator is real-rooted for every real
parameter on every positive-leading polynomial rooted in `[-1, 0]`. -/
theorem intervalEulerOperator_splits {p : ℝ[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n)
    (hpos : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) (a : ℝ) :
    ((C a - C (n : ℝ) * X) * p + X * (1 + X) * p.derivative).Splits := by
  obtain ⟨q, hqdeg, hqpf, rfl⟩ :=
    exists_isPFPolynomial_fPolynomial_eq hp hdeg hpos hroots
  rw [← fPolynomial_theta_add_C_mul hqdeg]
  exact splits_fPolynomial (natDegree_theta_add_C_mul_le hqdeg a)
    (splits_theta_add_C_mul hqpf a)

private theorem hasNonnegCoeffs_theta_add_C_mul_of_nonneg
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (theta p + C a * p) :=
  hp.theta.add (hasNonnegCoeffs_C_mul ha hp)

private theorem hasNonnegCoeffs_neg_theta_add_C_mul_of_le_neg_nat
    {p : ℝ[X]} {n : ℕ} (hp : HasNonnegCoeffs p)
    (hdeg : p.natDegree ≤ n) {a : ℝ} (ha : a ≤ -(n : ℝ)) :
    HasNonnegCoeffs (-(theta p + C a * p)) := by
  intro k
  by_cases hk : k ≤ n
  · simp only [coeff_neg, coeff_add, coeff_theta, coeff_C_mul]
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith [hp k]
  · have hpk : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_not_ge hk))
    simp [coeff_theta, hpk]

/-- In the two sharp sufficient parameter ranges, every root of the
conjugated interval Euler output remains in `[-1, 0]`. -/
theorem intervalEulerOperator_roots_mem_Icc {p : ℝ[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n)
    (hpos : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0)
    {a : ℝ} (ha : 0 ≤ a ∨ a ≤ -(n : ℝ)) :
    ∀ r ∈ ((C a - C (n : ℝ) * X) * p +
      X * (1 + X) * p.derivative).roots, r ∈ Icc (-1 : ℝ) 0 := by
  obtain ⟨q, hqdeg, hqpf, rfl⟩ :=
    exists_isPFPolynomial_fPolynomial_eq hp hdeg hpos hroots
  let s := theta q + C a * q
  have hsdeg : s.natDegree ≤ n := natDegree_theta_add_C_mul_le hqdeg a
  have hss : s.Splits := splits_theta_add_C_mul hqpf a
  have hout :
      (C a - C (n : ℝ) * X) * fPolynomial n q +
          X * (1 + X) * (fPolynomial n q).derivative = fPolynomial n s := by
    simpa [s] using (fPolynomial_theta_add_C_mul hqdeg a).symm
  rw [hout]
  rcases ha with ha | ha
  · by_cases hs0 : s = 0
    · rw [hs0]
      simp
    · exact BrandenLeite.roots_fPolynomial_mem_Icc hsdeg hs0 hss
        (hasNonnegCoeffs_theta_add_C_mul_of_nonneg hqpf.hasNonnegCoeffs ha)
  · have hnegsnn : HasNonnegCoeffs (-s) :=
      hasNonnegCoeffs_neg_theta_add_C_mul_of_le_neg_nat
        hqpf.hasNonnegCoeffs hqdeg ha
    by_cases hs0 : s = 0
    · rw [hs0]
      simp
    · have hneg0 : -s ≠ 0 := neg_ne_zero.mpr hs0
      have hnegs : (-s).Splits := hss.neg
      have hnegdeg : (-s).natDegree ≤ n := by simpa using hsdeg
      have hr := BrandenLeite.roots_fPolynomial_mem_Icc
        hnegdeg hneg0 hnegs hnegsnn
      have heq : fPolynomial n (-s) = -(fPolynomial n s) := by
        simpa using fPolynomial_C_mul n (-1) s
      rw [heq, Polynomial.roots_neg] at hr
      exact hr

/-- For a positive parameter, the interval Euler output has the expected
degree and leading sign, and the input is in directed weak interlacing
position with the output. -/
theorem intervalEulerOperator_degree_pos_strictInterl
    {p : ℝ[X]} {n : ℕ}
    (hp : p.Splits) (hdeg : p.natDegree = n)
    (hpos : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0)
    {a : ℝ} (ha : 0 < a) :
    let F := (C a - C (n : ℝ) * X) * p +
      X * (1 + X) * p.derivative
    F.natDegree = n ∧ HasPosLeadingCoeff F ∧ StrictInterl p F := by
  dsimp only
  obtain ⟨q, hqdeg, hqpf, hpq⟩ :=
    exists_isPFPolynomial_fPolynomial_eq hp hdeg hpos hroots
  let s := theta q + C a * q
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, fPolynomial_zero] at hpq
    exact hpos.ne_zero hpq
  have hsnn : HasNonnegCoeffs s :=
    hasNonnegCoeffs_theta_add_C_mul_of_nonneg hqpf.hasNonnegCoeffs ha.le
  have hCa0 : C a * q ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr ha.ne') hq0
  have hs0 : s ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hqpf.hasNonnegCoeffs.theta
      (hasNonnegCoeffs_C_mul ha.le hqpf.hasNonnegCoeffs) hCa0
  have hsdeg : s.natDegree ≤ n := natDegree_theta_add_C_mul_le hqdeg a
  have hFdeg : (fPolynomial n s).natDegree = n :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hsdeg hsnn hs0
  have hFpos : HasPosLeadingCoeff (fPolynomial n s) := by
    rw [HasPosLeadingCoeff, leadingCoeff_fPolynomial_eq_eval_one hsdeg hsnn hs0]
    exact eval_one_pos_of_hasNonnegCoeffs hsnn hs0
  have hout :
      (C a - C (n : ℝ) * X) * p + X * (1 + X) * p.derivative =
        fPolynomial n s := by
    rw [hpq]
    simpa [s] using (fPolynomial_theta_add_C_mul hqdeg a).symm
  have hroot_lo : ∀ r, p.IsRoot r → -1 ≤ r := by
    intro r hr
    exact (hroots r ((Polynomial.mem_roots hpos.ne_zero).mpr hr)).1
  have hroot_hi : ∀ r, p.IsRoot r → r ≤ 0 := by
    intro r hr
    exact (hroots r ((Polynomial.mem_roots hpos.ne_zero).mpr hr)).2
  have hinter :=
    MaWang.strictInterl_derivative_X_mul_one_add_X_of_roots_in_Icc_of_splits
      (f := p) (u := C a - C (n : ℝ) * X) hp
      (by rw [hout, hFdeg, hdeg])
      (by rw [hout, hFdeg, hdeg]; exact Nat.le_succ n)
      (by rw [hout]; exact hFpos) hpos hroot_lo hroot_hi
  rw [hout]
  exact ⟨hFdeg, hFpos, by simpa only [hout] using hinter⟩

/-- Every parameter strictly between `-n` and `0` has an exact-degree
positive-leading input rooted in `[-1, 0]` whose interval Euler output has
the forbidden root `1`. -/
theorem exists_intervalEulerOperator_root_one
    {n : ℕ} (hn : 1 ≤ n) {a : ℝ}
    (ha_lo : -(n : ℝ) < a) (ha_hi : a < 0) :
    ∃ p : ℝ[X], p.Splits ∧ p.natDegree = n ∧
      HasPosLeadingCoeff p ∧
      (∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) ∧
      let F := (C a - C (n : ℝ) * X) * p +
        X * (1 + X) * p.derivative
      F ≠ 0 ∧ F.IsRoot 1 := by
  let c : ℝ := -((n : ℝ) + a) / (2 * a)
  have hna : 0 < (n : ℝ) + a := by linarith
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos hna) (by nlinarith)
  let q : ℝ[X] := (X + C c) ^ n
  have hqpf : IsPFPolynomial q := by
    exact (isPFPolynomial_X_add_C hc.le).pow n
  have hq0 : q ≠ 0 := pow_ne_zero n (Polynomial.X_add_C_ne_zero c)
  have hqdeg : q.natDegree = n := by
    dsimp [q]
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  let p := fPolynomial n q
  have hpdeg : p.natDegree = n := by
    exact fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero
      hqdeg.le hqpf.hasNonnegCoeffs hq0
  have hp0 : p ≠ 0 := by
    intro hzero
    rw [hzero] at hpdeg
    simp at hpdeg
    lia
  have hps : p.Splits :=
    splits_fPolynomial hqdeg.le (hqpf.ne_zero_and_splits hq0).2
  have hppos : HasPosLeadingCoeff p :=
    (hasNonnegCoeffs_fPolynomial hqpf.hasNonnegCoeffs).pos_leadingCoeff hp0
  have hproots : ∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0 :=
    BrandenLeite.roots_fPolynomial_mem_Icc
      hqdeg.le hq0 (hqpf.ne_zero_and_splits hq0).2 hqpf.hasNonnegCoeffs
  let s := theta q + C a * q
  have hsdeg : s.natDegree ≤ n := natDegree_theta_add_C_mul_le hqdeg.le a
  have hseval : s.eval (1 / 2 : ℝ) = 0 := by
    have hrel : (n : ℝ) / 2 + a * (1 / 2 + c) = 0 := by
      dsimp [c]
      field_simp [ha_hi.ne]
      ring
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
    change (X * ((X + C c) ^ (m + 1)).derivative +
      C a * (X + C c) ^ (m + 1)).eval (1 / 2) = 0
    rw [derivative_pow]
    simp only [derivative_add, derivative_X, derivative_C, add_zero,
      eval_add, eval_mul, eval_X, eval_C, eval_pow]
    rw [Nat.add_sub_cancel, pow_succ]
    norm_num
    calc
      _ = (1 / 2 + c) ^ m *
          (((m + 1 : ℕ) : ℝ) / 2 + a * (1 / 2 + c)) := by
            push_cast
            ring
      _ = 0 := by rw [hrel, mul_zero]
  have hs0 : s ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun f : ℝ[X] => f.coeff n) hzero
    have hqcoeff : q.coeff n = q.leadingCoeff := by rw [leadingCoeff, hqdeg]
    have hqlead : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
    have hqleadpos : 0 < q.leadingCoeff :=
      hqpf.hasNonnegCoeffs.pos_leadingCoeff hq0
    simp only [s, coeff_add, coeff_theta, coeff_C_mul, coeff_zero] at hcoeff
    rw [hqcoeff] at hcoeff
    apply hqlead
    nlinarith
  have hfp0 : fPolynomial n s ≠ 0 := by
    intro hzero
    have hmap := congrArg (Polynomial.cayleyTransform n) hzero
    rw [fPolynomial_eq_bernsteinExpansion,
      Polynomial.cayleyTransform_bernsteinExpansion hsdeg] at hmap
    exact hs0 (by simpa [Polynomial.cayleyTransform] using hmap)
  have hfproot : (fPolynomial n s).IsRoot 1 := by
    rw [Polynomial.IsRoot.def,
      eval_fPolynomial_eq_mul_eval_untransform hsdeg (by norm_num : (1 : ℝ) ≠ -1)]
    norm_num [untransformRoot, hseval]
  refine ⟨p, hps, hpdeg, hppos, hproots, ?_⟩
  dsimp only
  have hout :
      (C a - C (n : ℝ) * X) * p + X * (1 + X) * p.derivative =
        fPolynomial n s := by
    dsimp [p]
    simpa [s] using (fPolynomial_theta_add_C_mul hqdeg.le a).symm
  rw [hout]
  exact ⟨hfp0, hfproot⟩

/-- Sharp universal criterion for preservation of the closed root interval by
the degree-`n` conjugated Euler operator. -/
theorem forall_intervalEulerOperator_roots_mem_Icc_iff
    {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (∀ p : ℝ[X], p.Splits → p.natDegree = n →
      HasPosLeadingCoeff p →
      (∀ r ∈ p.roots, r ∈ Icc (-1 : ℝ) 0) →
      ∀ r ∈ ((C a - C (n : ℝ) * X) * p +
        X * (1 + X) * p.derivative).roots, r ∈ Icc (-1 : ℝ) 0) ↔
      0 ≤ a ∨ a ≤ -(n : ℝ) := by
  constructor
  · intro hall
    by_contra ha
    have ha0 : a < 0 := lt_of_not_ge (not_or.mp ha).1
    have han : -(n : ℝ) < a := lt_of_not_ge (not_or.mp ha).2
    obtain ⟨p, hps, hpdeg, hppos, hproots, hF0, hFroot⟩ :=
      exists_intervalEulerOperator_root_one hn han ha0
    have hmem : (1 : ℝ) ∈ ((C a - C (n : ℝ) * X) * p +
        X * (1 + X) * p.derivative).roots :=
      (Polynomial.mem_roots hF0).mpr hFroot
    have hbad := hall p hps hpdeg hppos hproots 1 hmem
    norm_num at hbad
  · intro ha p hps hpdeg hppos hproots
    exact intervalEulerOperator_roots_mem_Icc
      hps hpdeg hppos hproots ha

end RealRooted
