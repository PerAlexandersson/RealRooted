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
  grind [IsPFPolynomial.eq_zero_or_splits]

theorem zero : IsPFPolynomial (0 : ℝ[X]) :=
  ⟨by simp [HasNonnegCoeffs], Or.inl rfl, by simp⟩

theorem of_realRooted_nonneg {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hprr_splits : p.Splits) :
    IsPFPolynomial p :=
  ⟨hpnn, Or.inr hprr_splits, roots_nonpos_of_nonneg_coeffs hprr_splits hpnn⟩

theorem one : IsPFPolynomial (1 : ℝ[X]) :=
  IsPFPolynomial.of_realRooted_nonneg hasNonnegCoeffs_one (by simp)

/-- Construct a PF polynomial from nonnegative coefficients and a
zero-or-splits certificate. -/
theorem of_nonnegCoeffs_eq_zero_or_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hp : p = 0 ∨ p.Splits) :
    IsPFPolynomial p := by
  rcases hp with rfl | hsplits
  · exact IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg hpnn hsplits

theorem const_mul {a : ℝ} (ha : 0 < a) {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (C a * p) := by
  by_cases hp0 : p = 0
  · simp_all
  · have hprr : p ≠ 0 ∧ p.Splits := hp.ne_zero_and_splits hp0
    refine ⟨nonnegCoeffs_C_mul ha.le hp.hasNonnegCoeffs, Or.inr ?_, ?_⟩
    · simp_all
    · intro r hr
      have hrp : r ∈ p.roots := by
        simpa [Polynomial.roots_C_mul _ ha.ne'] using hr
      exact hp.roots_nonpos r hrp

theorem of_C_nonneg {a : ℝ} (ha : 0 ≤ a) : IsPFPolynomial (Polynomial.C a) := by
  by_cases ha0 : a = 0
  · simpa [ha0] using IsPFPolynomial.zero
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simpa using IsPFPolynomial.one.const_mul ha_pos

theorem X_mul {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (X * p) := by
  by_cases hp0 : p = 0
  · simp_all
  have hprr := hp.ne_zero_and_splits hp0
  have hnn : HasNonnegCoeffs (X * p) := by
    rintro (_ | n)
    · simp
    · simpa [coeff_X_mul] using hp.hasNonnegCoeffs n
  have hXp_rr := isRealRooted_X_mul hprr.1 hprr.2
  exact IsPFPolynomial.of_realRooted_nonneg hnn hXp_rr.2

theorem mul {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    IsPFPolynomial (p * q) := by
  by_cases hp0 : p = 0
  · simp_all
  by_cases hq0 : q = 0
  · simp_all
  have hprr := hp.ne_zero_and_splits hp0
  have hqrr := hq.ne_zero_and_splits hq0
  have hpq_rr := isRealRooted_mul hprr.1 hprr.2 hqrr.1 hqrr.2
  exact IsPFPolynomial.of_realRooted_nonneg
    (hp.hasNonnegCoeffs.mul hq.hasNonnegCoeffs)
    hpq_rr.2

/-- If a PF polynomial is factored by a real linear factor, then the quotient
is again PF. -/
theorem of_X_sub_C_mul_factor {p q : ℝ[X]} {u : ℝ}
    (hp : IsPFPolynomial p) (hfactor : p = (X - C u) * q) :
    IsPFPolynomial q := by
  by_cases hq0 : q = 0
  · simpa [hq0] using IsPFPolynomial.zero
  have hp0 : p ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (X_sub_C_ne_zero u) hq0
  have hprr := hp.ne_zero_and_splits hp0
  have hq_dvd : q ∣ p := ⟨X - C u, by rw [hfactor]; ring⟩
  have hq_splits : q.Splits :=
    (isRealRooted_of_dvd hp0 hprr.2 hq0 hq_dvd).2
  have hp_pos : HasPosLeadingCoeff p := hp.hasNonnegCoeffs.pos_leadingCoeff hp0
  have hq_pos : HasPosLeadingCoeff q := by
    apply hasPosLeadingCoeff_of_X_sub_C_mul
    rwa [← hfactor]
  have hqnn : HasNonnegCoeffs q :=
    hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff hp0 hprr.2
      hp.hasNonnegCoeffs hq0 hq_splits hq_pos hq_dvd
  exact IsPFPolynomial.of_realRooted_nonneg hqnn hq_splits

/-- A positive-degree PF polynomial has a nonpositive linear root factor whose
quotient is again PF and has smaller degree. -/
theorem exists_X_sub_C_factor_of_pos_natDegree {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hdeg : 0 < p.natDegree) :
    ∃ u : ℝ, ∃ q : ℝ[X],
      u ≤ 0 ∧ p = (X - C u) * q ∧ IsPFPolynomial q ∧
        q.natDegree < p.natDegree := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hdeg
  have hpsplits : p.Splits := hp.ne_zero_and_splits hp0 |>.2
  have hroots_pos : 0 < p.roots.card := by
    rw [card_roots_of_splits hpsplits]
    exact hdeg
  rcases Multiset.card_pos_iff_exists_mem.mp hroots_pos with ⟨u, hu_mem⟩
  have hu_root : p.IsRoot u := (mem_roots hp0).mp hu_mem
  rcases (dvd_iff_isRoot).mpr hu_root with ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq, hq0, mul_zero] at hp0
    exact hp0 rfl
  have hqdeg : q.natDegree < p.natDegree := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero u) hq0, natDegree_X_sub_C]
    lia
  exact ⟨u, q, hp.roots_nonpos u hu_mem, hq,
    hp.of_X_sub_C_mul_factor hq, hqdeg⟩

theorem pow {p : ℝ[X]} (hp : IsPFPolynomial p) (n : ℕ) :
    IsPFPolynomial (p ^ n) := by
  induction n with
  | zero =>
      simpa using IsPFPolynomial.one
  | succ n ih =>
      simpa [pow_succ] using ih.mul hp

theorem derivative {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial p.derivative := by
  by_cases hp0 : p = 0
  · simp_all
  have hprr := hp.ne_zero_and_splits hp0
  exact ⟨hp.hasNonnegCoeffs.derivative,
    eq_zero_or_splits_derivative hp.eq_zero_or_splits,
    roots_nonpos_derivative_of_roots_nonpos hprr.2 hp.roots_nonpos⟩

theorem of_sequence
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n => p.coeff n)) :
    IsPFPolynomial p :=
  let hpnn := hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff hpf
  ⟨hpnn, hASW hpnn hpf⟩

/-- Construct a PF polynomial directly from its Pólya-frequency coefficient
sequence using the proved forward ASW theorem. -/
theorem of_polyaFreqSeq {p : ℝ[X]}
    (hpf : IsPolyaFreqSeq (fun n => p.coeff n)) :
    IsPFPolynomial p :=
  let hpnn := hasNonnegCoeffs_of_IsPolyaFreqSeq_coeff hpf
  ⟨hpnn, aissenSchoenbergWhitneyForwardOrZero hpnn hpf⟩

/-- Forward-ASW endpoint closure for positive affine coefficient limits. -/
theorem of_forall_pos_add_C_mul_of_forward
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → (p + C μ * q).Splits) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_sequence hASW <|
    IsPolyaFreqSeq.of_forall_pos_add_C_mul_splits hpnn hqnn hfamily

/-- Splitting form of `IsPFPolynomial.of_forall_pos_add_C_mul_of_forward`. -/
theorem splits_of_forall_pos_add_C_mul_of_forward
    (hASW : aissenSchoenbergWhitneyForwardOrZeroStatement)
    {p q : ℝ[X]}
    (hp0 : p ≠ 0)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → (p + C μ * q).Splits) :
    p.Splits :=
  (of_forall_pos_add_C_mul_of_forward hASW hpnn hqnn hfamily).ne_zero_and_splits hp0 |>.2

/-- PF endpoint closure for positive affine coefficient limits, using the
proved forward ASW theorem. -/
theorem of_forall_pos_add_C_mul
    {p q : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → (p + C μ * q).Splits) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_polyaFreqSeq <|
    IsPolyaFreqSeq.of_forall_pos_add_C_mul_splits hpnn hqnn hfamily

/-- Splitting form of `IsPFPolynomial.of_forall_pos_add_C_mul`. -/
theorem splits_of_forall_pos_add_C_mul
    {p q : ℝ[X]}
    (hp0 : p ≠ 0)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hfamily : ∀ {μ : ℝ}, 0 < μ → (p + C μ * q).Splits) :
    p.Splits :=
  (of_forall_pos_add_C_mul hpnn hqnn hfamily).ne_zero_and_splits hp0 |>.2

theorem to_sequence
    {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPolyaFreqSeq (fun n => p.coeff n) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using IsPolyaFreqSeq_zero
  · have hprr := hp.ne_zero_and_splits hp0
    exact aissenSchoenbergWhitney_reverse hp.hasNonnegCoeffs hprr.2 hp.roots_nonpos

theorem prec0_self {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Prec0 p p := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  · grind [Prec.toPrec0, prec_refl, IsPFPolynomial.ne_zero_and_splits]

theorem of_prec0_self {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hpp : Prec0 p p) :
    IsPFPolynomial p := by
  rcases hpp with rfl | rfl | hpp'
  · exact IsPFPolynomial.zero
  · exact IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg hpnn hpp'.1.2

end IsPFPolynomial

theorem isPFPolynomial_one : IsPFPolynomial (1 : ℝ[X]) :=
  IsPFPolynomial.one

theorem isPFPolynomial_X : IsPFPolynomial (X : ℝ[X]) := by
  simpa [mul_one] using IsPFPolynomial.one.X_mul

theorem isPFPolynomial_X_pow (m : ℕ) :
    IsPFPolynomial ((X : ℝ[X]) ^ m) :=
  isPFPolynomial_X.pow m

theorem isPFPolynomial_X_add_C {a : ℝ} (ha : 0 ≤ a) :
    IsPFPolynomial (X + C a : ℝ[X]) := by
  have hnn : HasNonnegCoeffs (X + C a : ℝ[X]) := by
    simpa [sub_eq_add_neg] using hasNonnegCoeffs_X_sub_C (r := -a) (by linarith)
  exact IsPFPolynomial.of_realRooted_nonneg hnn <| by
    simp

theorem isPFPolynomial_X_add_one : IsPFPolynomial (X + 1 : ℝ[X]) := by
  simpa using isPFPolynomial_X_add_C (a := 1) zero_le_one

namespace IsPFPolynomial

/-- A positive affine shift of a nonpositive linear root factor is PF. -/
theorem C_mul_X_add_C_sub_C {a d u : ℝ}
    (ha : 0 < a) (hd : 0 ≤ d) (hu : u ≤ 0) :
    IsPFPolynomial (C a * X + C d - C u : ℝ[X]) := by
  have hlin : (C a * X + C d - C u : ℝ[X]) = C a * X + C (d - u) := by
    rw [sub_eq_add_neg, add_assoc, ← Polynomial.C_neg, ← Polynomial.C_add]
    simp [sub_eq_add_neg]
  rw [hlin]
  have hfactor : (C a * X + C (d - u) : ℝ[X]) =
      C a * (X + C ((d - u) / a)) := by
    rw [mul_add, ← Polynomial.C_mul]
    congr 1
    field_simp [ha.ne']
  rw [hfactor]
  have hdsub : 0 ≤ d - u := by linarith
  exact (isPFPolynomial_X_add_C (div_nonneg hdsub ha.le)).const_mul ha

/-- PF polynomials are closed under positive affine substitution
`x ↦ a * x + d` with nonnegative constant term. -/
theorem comp_C_mul_X_add_C {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (p.comp (C a * X + C d)) := by
  induction hdeg : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp0 : p = 0
      · simpa [hp0] using IsPFPolynomial.zero
      by_cases hn0 : n = 0
      · have hpC : p = C (p.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero (by simpa [hdeg] using hn0)
        rw [hpC]
        have hcoeff_nonneg : 0 ≤ p.coeff 0 := hp.hasNonnegCoeffs 0
        simpa using IsPFPolynomial.of_C_nonneg hcoeff_nonneg
      · have hpos : 0 < p.natDegree := by
          rw [hdeg]
          exact Nat.pos_of_ne_zero hn0
        obtain ⟨u, q, hu, hfactor, hq, hqdeg⟩ :=
          hp.exists_X_sub_C_factor_of_pos_natDegree hpos
        rw [hfactor]
        simp only [Polynomial.comp, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        exact (C_mul_X_add_C_sub_C ha hd hu).mul
          (ih q.natDegree (by simpa [hdeg] using hqdeg) hq rfl)

end IsPFPolynomial

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
          simp
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
          simp_all
      | succ n =>
          cases n with
          | zero =>
              simp [Polynomial.coeff_one, Polynomial.coeff_X]
          | succ n =>
              simp [Polynomial.coeff_one, Polynomial.coeff_X]
    simp_all

theorem isPFPolynomial_reverse_prod_X_sub_C
    (s : Multiset ℝ) (hs : ∀ r ∈ s, r ≤ 0) :
    IsPFPolynomial ((s.map fun r => X - C r).prod.reverse) := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa [Polynomial.reverse, natDegree_one] using isPFPolynomial_one
  | cons r s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [Polynomial.reverse_mul_of_domain]
      exact
        (reverse_X_sub_C_isPF (hs r (by simp))).mul
          (ih (fun x hx => hs x (by simp [hx])))

theorem IsPFPolynomial.reverse {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial p.reverse := by
  by_cases hp0 : p = 0
  · simp_all
  have hprr : p ≠ 0 ∧ p.Splits := hp.ne_zero_and_splits hp0
  have hp_eq : p = C p.leadingCoeff * (p.roots.map fun r ↦ X - C r).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C
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
  · simpa [hp0] using prec0_zero_left (X * q)
  · simpa [hq0] using prec0_zero_right (X * p)
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
        simp_all)
      (by
        simp_all)

/-- Fixed-left cone closure for two nonnegative scalar multiples. -/
theorem prec0_nonneg_combo_right_of_common_left_of_nonneg {p q r : ℝ[X]}
    (hpq : Prec0 p q) (hpr : Prec0 p r)
    (hq : HasNonnegCoeffs q) (hr : HasNonnegCoeffs r)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Prec0 p (C a * q + C b * r) :=
  prec0_add_right_of_common_left_of_nonneg
    (prec0_C_mul_right_of_nonneg hpq ha)
    (prec0_C_mul_right_of_nonneg hpr hb)
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
    IsPFPolynomial ((X + 1) * p) :=
  isPFPolynomial_X_add_one.mul hp

end RealRooted
