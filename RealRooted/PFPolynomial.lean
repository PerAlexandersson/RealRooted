import RealRooted.Derivative
import RealRooted.PosCombo
import RealRooted.WagnerX

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Polya-frequency polynomials

This file packages the polynomial-side Polya-frequency condition used by the
real-rootedness development: nonnegative coefficients and only real
nonpositive roots.  It also records small cone and reciprocal-shift operations
that are independent of any particular combinatorial family.
-/

/-- Polynomial-side Polya-frequency condition: nonnegative coefficients and
only real nonpositive roots.

This is zero-aware, unlike the strict local real-rootedness predicate
`p ≠ 0 ∧ p.Splits`.  The Toeplitz-minor side remains
`IsPolyaFreqSeq (fun n => p.coeff n)`.
-/
def IsPFPolynomial (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ (p = 0 ∨ p.Splits) ∧ ∀ r ∈ p.roots, r ≤ 0

namespace IsPFPolynomial

theorem hasNonnegCoeffs {p : ℝ[X]} (hp : IsPFPolynomial p) :
    HasNonnegCoeffs p :=
  hp.1

theorem eq_zero_or_splits {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p = 0 ∨ p.Splits :=
  hp.2.1

theorem roots_nonpos {p : ℝ[X]} (hp : IsPFPolynomial p) :
    ∀ r ∈ p.roots, r ≤ 0 :=
  hp.2.2

theorem ne_zero_and_splits {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hp0 : p ≠ 0) :
    p ≠ 0 ∧ p.Splits := by
  rcases hp.eq_zero_or_splits with hzero | hsplits
  · contradiction
  · exact ⟨hp0, hsplits⟩

theorem zero : IsPFPolynomial (0 : ℝ[X]) := by
  refine ⟨?_, Or.inl rfl, ?_⟩
  · intro n
    simp
  · intro r hr
    simp at hr

theorem of_realRooted_nonneg {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr : p ≠ 0 ∧ p.Splits) :
    IsPFPolynomial p :=
  ⟨hpnn, Or.inr hprr.2, roots_nonpos_of_nonneg_coeffs hprr.2 hpnn⟩

theorem const_mul {a : ℝ} (ha : 0 < a) {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (C a * p) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  · have hprr : p ≠ 0 ∧ p.Splits := hp.ne_zero_and_splits hp0
    refine ⟨nonnegCoeffs_C_mul ha.le hp.hasNonnegCoeffs, Or.inr ?_, ?_⟩
    · exact (isRealRooted_C_mul hprr ha.ne').2
    · intro r hr
      have hrp : r ∈ p.roots := by
        simpa [Polynomial.roots_C_mul _ ha.ne'] using hr
      exact hp.roots_nonpos r hrp

theorem X_mul {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (X * p) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  have hnn : HasNonnegCoeffs (X * p) := by
    intro n
    cases n with
    | zero =>
        simp
    | succ n =>
        rw [coeff_X_mul]
        exact hp.hasNonnegCoeffs n
  exact IsPFPolynomial.of_realRooted_nonneg
    hnn
    (isRealRooted_X_mul (hp.ne_zero_and_splits hp0))

theorem mul {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (p * q) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  by_cases hq0 : q = 0
  · subst q
    simpa using IsPFPolynomial.zero
  exact IsPFPolynomial.of_realRooted_nonneg
    (hp.hasNonnegCoeffs.mul hq.hasNonnegCoeffs)
    (isRealRooted_mul
      (hp.ne_zero_and_splits hp0)
      (hq.ne_zero_and_splits hq0))

theorem derivative {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial p.derivative := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  exact ⟨hp.hasNonnegCoeffs.derivative,
    eq_zero_or_splits_derivative hp.eq_zero_or_splits,
    roots_nonpos_derivative_of_roots_nonpos (hp.ne_zero_and_splits hp0)
      hp.roots_nonpos⟩

theorem of_sequence
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n => p.coeff n)) :
    IsPFPolynomial p := by
  have hpnn : HasNonnegCoeffs p :=
    hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff hpf
  exact ⟨hpnn, hASW hpnn hpf⟩

theorem to_sequence
    (hASWrev : aissenSchoenbergWhitneyReverseStatement)
    {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPolyaFreqSeq (fun n => p.coeff n) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPolyaFreqSeq_zero
  · exact hASWrev hp.hasNonnegCoeffs (hp.ne_zero_and_splits hp0).2
      hp.roots_nonpos

theorem prec0_self {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Prec0 p p := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  · exact Or.inr (Or.inr (prec_refl (hp.ne_zero_and_splits hp0).1 (hp.ne_zero_and_splits hp0).2))

theorem of_prec0_self {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hpp : Prec0 p p) :
    IsPFPolynomial p := by
  rcases hpp with hp0 | hp0 | hpp'
  · subst p
    exact IsPFPolynomial.zero
  · subst p
    exact IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg hpnn hpp'.1

end IsPFPolynomial

theorem isPFPolynomial_one : IsPFPolynomial (1 : ℝ[X]) :=
  IsPFPolynomial.of_realRooted_nonneg hasNonnegCoeffs_one (by simp)

theorem isPFPolynomial_X : IsPFPolynomial (X : ℝ[X]) := by
  simpa using isPFPolynomial_one.X_mul

theorem isPFPolynomial_X_pow (m : ℕ) :
    IsPFPolynomial ((X : ℝ[X]) ^ m) := by
  induction m with
  | zero =>
      simpa using isPFPolynomial_one
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul isPFPolynomial_X

theorem isPFPolynomial_X_add_C {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (X + C a : ℝ[X]) := by
  have hnn : HasNonnegCoeffs (X + C a : ℝ[X]) := by
    simpa [sub_eq_add_neg] using hasNonnegCoeffs_X_sub_C (r := -a) (by linarith)
  have hrr : ((X + C a : ℝ[X]) ≠ 0 ∧ (X + C a : ℝ[X]).Splits) := by
    simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-a)
  exact IsPFPolynomial.of_realRooted_nonneg hnn hrr

theorem reverse_X_sub_C_isPF {r : ℝ} (hr : r ≤ 0) :
    IsPFPolynomial ((X - C r : ℝ[X]).reverse) := by
  by_cases hr0 : r = 0
  · subst r
    rw [show (X - C (0 : ℝ) : ℝ[X]) = X by simp]
    rw [Polynomial.reverse, natDegree_X]
    simpa using isPFPolynomial_one
  · have hrlt : r < 0 := lt_of_le_of_ne hr hr0
    have hneg : 0 < -r := by linarith
    have hinvlt : r⁻¹ < 0 := inv_lt_zero'.mpr hrlt
    have hinv_nonneg : 0 ≤ -(r⁻¹) := by linarith
    have hbase : IsPFPolynomial (X + C (-(r⁻¹)) : ℝ[X]) :=
      isPFPolynomial_X_add_C hinv_nonneg
    have hscale : IsPFPolynomial (C (-r) * (X + C (-(r⁻¹)) : ℝ[X])) :=
      hbase.const_mul hneg
    have hrev_linear : (X - C r : ℝ[X]).reverse = 1 - C r * X := by
      ext n
      cases n with
      | zero =>
          simp [Polynomial.coeff_reverse, Polynomial.coeff_one, Polynomial.coeff_X]
      | succ n =>
          cases n with
          | zero =>
              simp [Polynomial.coeff_reverse, Polynomial.coeff_one, Polynomial.coeff_X]
          | succ n =>
              have hgt : 1 < Nat.succ (Nat.succ n) :=
                Nat.succ_lt_succ (Nat.zero_lt_succ n)
              simp [Polynomial.coeff_reverse, Polynomial.revAt_eq_self_of_lt hgt,
                Polynomial.coeff_one, Polynomial.coeff_X]
    have hscale_eq : C (-r) * (X + C (-(r⁻¹)) : ℝ[X]) = 1 - C r * X := by
      ext n
      cases n with
      | zero =>
          simp [Polynomial.coeff_one, Polynomial.coeff_X]
          field_simp [hr0]
      | succ n =>
          cases n with
          | zero =>
              simp [Polynomial.coeff_one, Polynomial.coeff_X]
          | succ n =>
              simp [Polynomial.coeff_one, Polynomial.coeff_X]
    simpa [hrev_linear, hscale_eq.symm] using hscale

theorem isPFPolynomial_reverse_prod_X_sub_C
    (s : Multiset ℝ) (hs : ∀ r ∈ s, r ≤ 0) :
    IsPFPolynomial ((s.map fun r => X - C r).prod.reverse) := by
  induction s using Multiset.induction_on with
  | empty =>
      change IsPFPolynomial ((1 : ℝ[X]).reverse)
      rw [Polynomial.reverse, natDegree_one]
      simpa using isPFPolynomial_one
  | cons r s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [Polynomial.reverse_mul_of_domain]
      exact
        (reverse_X_sub_C_isPF (hs r (by simp))).mul
          (ih (fun x hx => hs x (by simp [hx])))

theorem IsPFPolynomial.reverse {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial p.reverse := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  have hprr : p ≠ 0 ∧ p.Splits := hp.ne_zero_and_splits hp0
  have hp_eq : p = C p.leadingCoeff * (p.roots.map fun r => X - C r).prod := by
    exact (C_leadingCoeff_mul_prod_multiset_X_sub_C
      (card_roots_of_splits hprr.2)).symm
  rw [hp_eq]
  rw [Polynomial.reverse_mul_of_domain]
  have hlc_pos : 0 < p.leadingCoeff := hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have hlc_pf : IsPFPolynomial (C p.leadingCoeff).reverse := by
    simpa [Polynomial.reverse_C] using
      (IsPFPolynomial.const_mul (p := (1 : ℝ[X])) hlc_pos isPFPolynomial_one)
  exact hlc_pf.mul (isPFPolynomial_reverse_prod_X_sub_C p.roots hp.roots_nonpos)

theorem prec0_X_mul_both_of_pf {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Prec0 p q) :
    Prec0 (X * p) (X * q) := by
  rcases hpq with hp0 | hq0 | hpq'
  · subst p
    simpa using prec0_zero_left (X * q)
  · subst q
    simpa using prec0_zero_right (X * p)
  · exact (prec_mul_X_both_of_roots_nonpos hpq' hp.roots_nonpos hq.roots_nonpos).toPrec0

/-- Fixed-left cone closure in the two-summand form used downstream:
if a polynomial is a common left interleaver for two nonnegative-coefficient
summands, it is also a common left interleaver for their sum. -/
theorem prec0_add_right_of_common_left_of_nonneg {p q r : ℝ[X]}
    (hpq : Prec0 p q) (hpr : Prec0 p r)
    (hq : HasNonnegCoeffs q) (hr : HasNonnegCoeffs r) :
    Prec0 p (q + r) := by
  simpa using
    prec0_sum_left_of_common_left_of_nonneg [q, r] p
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with hs | hs
        · subst s
          exact hpq
        · subst s
          exact hpr)
      (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with hs | hs
        · subst s
          exact hq
        · subst s
          exact hr)

/-- Fixed-left cone closure for two nonnegative scalar multiples. -/
theorem prec0_nonneg_combo_right_of_common_left_of_nonneg {p q r : ℝ[X]}
    (hpq : Prec0 p q) (hpr : Prec0 p r)
    (hq : HasNonnegCoeffs q) (hr : HasNonnegCoeffs r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Prec0 p (C a * q + C b * r) := by
  have hpaq : Prec0 p (C a * q) := by
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp [prec0_zero_right]
    rcases hpq with hp0 | hq0 | hpq'
    · subst p
      exact prec0_zero_left (C a * q)
    · simp [hq0, prec0_zero_right]
    · exact (prec_C_mul_right hpq' ha_pos.ne').toPrec0
  have hpbr : Prec0 p (C b * r) := by
    rcases eq_or_lt_of_le hb with rfl | hb_pos
    · simp [prec0_zero_right]
    rcases hpr with hp0 | hr0 | hpr'
    · subst p
      exact prec0_zero_left (C b * r)
    · simp [hr0, prec0_zero_right]
    · exact (prec_C_mul_right hpr' hb_pos.ne').toPrec0
  exact prec0_add_right_of_common_left_of_nonneg hpaq hpbr
    (nonnegCoeffs_C_mul ha hq) (nonnegCoeffs_C_mul hb hr)

/-- Fixed-left cone closure in the polynomial PF notation. -/
theorem prec0_nonneg_combo_right_of_common_left_of_pf {p q r : ℝ[X]}
    (hpq : Prec0 p q) (hpr : Prec0 p r)
    (hq : IsPFPolynomial q) (hr : IsPFPolynomial r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Prec0 p (C a * q + C b * r) :=
  prec0_nonneg_combo_right_of_common_left_of_nonneg hpq hpr
    hq.hasNonnegCoeffs hr.hasNonnegCoeffs ha hb

/-- Shifted reciprocal `t^D p(1/t)`, represented by Mathlib's coefficient
reflection operator. -/
def reciprocalShift (D : ℕ) (p : ℝ[X]) : ℝ[X] :=
  p.reflect D

@[simp] theorem coeff_reciprocalShift (D : ℕ) (p : ℝ[X]) (n : ℕ) :
    (reciprocalShift D p).coeff n = p.coeff (Polynomial.revAt D n) := by
  simp [reciprocalShift, Polynomial.coeff_reflect]

theorem HasNonnegCoeffs.reciprocalShift {D : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (reciprocalShift D p) := by
  intro n
  simpa using hp (Polynomial.revAt D n)

/-- Standard reciprocal-polynomial input: shifted reciprocals preserve the PF
cone when the shift bounds the degree. -/
def reciprocalShiftPreservesPFStatement : Prop :=
  ∀ {D : ℕ} {p : ℝ[X]},
    IsPFPolynomial p →
    p.natDegree ≤ D →
    IsPFPolynomial (reciprocalShift D p)

theorem reciprocalShift_eq_X_pow_mul_reverse {D : ℕ} {p : ℝ[X]}
    (hdeg : p.natDegree ≤ D) :
    reciprocalShift D p = X ^ (D - p.natDegree) * p.reverse := by
  unfold reciprocalShift
  have hD : p.natDegree + (D - p.natDegree) = D := Nat.add_sub_of_le hdeg
  have hmul := Polynomial.reflect_mul (f := p) (g := (1 : ℝ[X]))
    (F := p.natDegree) (G := D - p.natDegree) le_rfl (by simp)
  rw [← hD]
  simpa [Polynomial.reverse, mul_comm] using hmul

theorem reciprocalShift_preserves_pf : reciprocalShiftPreservesPFStatement := by
  intro D p hp hdeg
  rw [reciprocalShift_eq_X_pow_mul_reverse hdeg]
  exact (isPFPolynomial_X_pow (D - p.natDegree)).mul hp.reverse

/-- Multiplication by `X + 1` preserves the polynomial PF cone. -/
theorem isPFPolynomial_mul_X_add_one {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial ((X + 1) * p) := by
  by_cases hp0 : p = 0
  · subst p
    simpa using IsPFPolynomial.zero
  have hX1rr : ((X + 1 : ℝ[X]) ≠ 0 ∧ (X + 1 : ℝ[X]).Splits) := by
    simpa using isRealRooted_X_sub_C (-1 : ℝ)
  have hX1nn : HasNonnegCoeffs (X + 1 : ℝ[X]) := by
    simpa using hasNonnegCoeffs_X_sub_C (r := -1) (by norm_num)
  have hrr : (((X + 1 : ℝ[X]) * p) ≠ 0 ∧
      ((X + 1 : ℝ[X]) * p).Splits) :=
    isRealRooted_mul hX1rr (hp.ne_zero_and_splits hp0)
  exact IsPFPolynomial.of_realRooted_nonneg
    (hX1nn.mul hp.hasNonnegCoeffs) hrr

end RealRooted
