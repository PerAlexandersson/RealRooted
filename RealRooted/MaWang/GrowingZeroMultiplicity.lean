module

public import RealRooted.PFPolynomial
public import RealRooted.MaWang.EndpointMultiplicity
public import RealRooted.SimpleRoots
import RealRooted.MaWang.DerivativeStep
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.Interlacing.Multiplicity

/-!
# Derivative steps with growing zero multiplicity

This file treats the differential operator
`f ↦ (a + bX)f + X(u - vX)f'`.  On a nonzero PF polynomial, its
nonnegative-coefficient threshold depends on the actual multiplicity at zero,
not just on the constant coefficient of the operator.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The derivative step `(a + bX)f + X(u - vX)f'`. -/
@[expose] def growingZeroStep (a b u v : ℝ) (f : ℝ[X]) : ℝ[X] :=
  (C u * X + C (-v) * X ^ 2) * f.derivative +
    (C a + C b * X) * f

/-- The coefficient recurrence for `growingZeroStep` above degree zero. -/
theorem growingZeroStep_coeff_succ (a b u v : ℝ) (f : ℝ[X]) (k : ℕ) :
    (growingZeroStep a b u v f).coeff (k + 1) =
      (a + u * (k + 1 : ℝ)) * f.coeff (k + 1) +
        (b - v * (k : ℝ)) * f.coeff k := by
  rw [growingZeroStep, Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  ring

/-- The constant coefficient of `growingZeroStep`. -/
@[simp] theorem growingZeroStep_coeff_zero (a b u v : ℝ) (f : ℝ[X]) :
    (growingZeroStep a b u v f).coeff 0 = a * f.coeff 0 := by
  simp [growingZeroStep]

/-- The degree and leading coefficient of a noncancelling `growingZeroStep`. -/
theorem growingZeroStep_natDegree_and_leadingCoeff
    {a b u v : ℝ} {f : ℝ[X]} (hf : f ≠ 0)
    (hraise : v * (f.natDegree : ℝ) < b) :
    (growingZeroStep a b u v f).natDegree = f.natDegree + 1 ∧
      (growingZeroStep a b u v f).leadingCoeff =
        (b - v * (f.natDegree : ℝ)) * f.leadingCoeff := by
  have htop :
      ((-v) * (f.natDegree : ℝ) + b) * f.leadingCoeff ≠ 0 := by
    exact mul_ne_zero (by linarith) (leadingCoeff_ne_zero.mpr hf)
  simpa [growingZeroStep, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using Polynomial.natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
      f 0 u (-v) a b (by simp) htop

/-- Below its zero multiplicity, every coefficient of `growingZeroStep` vanishes. -/
private lemma growingZeroStep_coeff_eq_zero_of_lt_rootMultiplicity
    {a b u v : ℝ} {f : ℝ[X]} (k : ℕ)
    (hk : k < f.rootMultiplicity 0) :
    (growingZeroStep a b u v f).coeff k = 0 := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree'] at hk
  cases k with
  | zero =>
      rw [growingZeroStep_coeff_zero]
      simp [coeff_eq_zero_of_lt_natTrailingDegree hk]
  | succ k =>
      rw [growingZeroStep_coeff_succ]
      have hk' : k < f.natTrailingDegree := lt_trans (Nat.lt_succ_self k) hk
      rw [coeff_eq_zero_of_lt_natTrailingDegree hk,
        coeff_eq_zero_of_lt_natTrailingDegree hk']
      ring

/-- The coefficient at the zero multiplicity is the effective constant
coefficient times the first nonzero coefficient of the input. -/
private lemma growingZeroStep_coeff_rootMultiplicity
    (a b u v : ℝ) (f : ℝ[X]) :
    (growingZeroStep a b u v f).coeff (f.rootMultiplicity 0) =
      (a + u * (f.rootMultiplicity 0 : ℝ)) *
        f.coeff (f.rootMultiplicity 0) := by
  cases hm : f.rootMultiplicity 0 with
  | zero => simp
  | succ m =>
      rw [growingZeroStep_coeff_succ]
      have hzero : f.coeff m = 0 := by
        apply coeff_eq_zero_of_lt_natTrailingDegree
        rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree', hm]
        exact Nat.lt_succ_self m
      rw [hzero, mul_zero, add_zero]
      norm_num

/-- A nonzero polynomial with nonnegative coefficients has a positive first
nonzero coefficient. -/
private lemma coeff_rootMultiplicity_pos {f : ℝ[X]}
    (hf : f ≠ 0) (hnonneg : HasNonnegCoeffs f) :
    0 < f.coeff (f.rootMultiplicity 0) := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  exact lt_of_le_of_ne (hnonneg f.natTrailingDegree)
    (Ne.symm (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hf))

/-- The exact zero multiplicity after a noncancelling derivative step. -/
theorem growingZeroStep_rootMultiplicity
    {a b u v : ℝ} {f : ℝ[X]} (hf : f ≠ 0)
    (hfnonneg : HasNonnegCoeffs f) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hraise : v * (f.natDegree : ℝ) < b) :
    (growingZeroStep a b u v f).rootMultiplicity 0 =
      if a + u * (f.rootMultiplicity 0 : ℝ) = 0
      then f.rootMultiplicity 0 + 1 else f.rootMultiplicity 0 := by
  simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  let m := f.natTrailingDegree
  change (growingZeroStep a b u v f).natTrailingDegree =
    if a + u * (m : ℝ) = 0 then m + 1 else m
  have hm_le : m ≤ f.natDegree := by
    exact f.natTrailingDegree_le_natDegree
  have hfm_pos : 0 < f.coeff m := by
    dsimp [m]
    rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree']
    exact coeff_rootMultiplicity_pos hf hfnonneg
  have hbelow : ∀ k < m, (growingZeroStep a b u v f).coeff k = 0 := by
    intro k hk
    apply growingZeroStep_coeff_eq_zero_of_lt_rootMultiplicity k
    rwa [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  split_ifs with heffective
  · apply le_antisymm
    · apply natTrailingDegree_le_of_ne_zero
      rw [growingZeroStep_coeff_succ]
      have hfactor : a + u * ((m : ℝ) + 1) = u := by
        linarith
      rw [hfactor]
      have hsecond : 0 < (b - v * (m : ℝ)) * f.coeff m := by
        apply mul_pos
        · have hm_cast : (m : ℝ) ≤ (f.natDegree : ℝ) := by exact_mod_cast hm_le
          nlinarith
        · exact hfm_pos
      exact ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg hu (hfnonneg (m + 1))) hsecond)
    · apply Polynomial.le_natTrailingDegree
      · apply leadingCoeff_ne_zero.mp
        rw [(growingZeroStep_natDegree_and_leadingCoeff hf hraise).2]
        exact mul_ne_zero (by linarith) (leadingCoeff_ne_zero.mpr hf)
      · intro k hk
        by_cases hkm : k < m
        · exact hbelow k hkm
        · have hkm_eq : k = m := by lia
          rw [hkm_eq, show m = f.rootMultiplicity 0 by
            simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree']; rfl,
            growingZeroStep_coeff_rootMultiplicity]
          rw [Polynomial.rootMultiplicity_eq_natTrailingDegree', heffective, zero_mul]
  · apply le_antisymm
    · apply natTrailingDegree_le_of_ne_zero
      rw [show m = f.rootMultiplicity 0 by
        simp only [Polynomial.rootMultiplicity_eq_natTrailingDegree']; rfl,
        growingZeroStep_coeff_rootMultiplicity]
      rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
      exact mul_ne_zero heffective hfm_pos.ne'
    · apply Polynomial.le_natTrailingDegree
      · apply leadingCoeff_ne_zero.mp
        rw [(growingZeroStep_natDegree_and_leadingCoeff hf hraise).2]
        exact mul_ne_zero (by linarith) (leadingCoeff_ne_zero.mpr hf)
      · exact hbelow

/-- The support-sensitive nonnegative-coefficient criterion for a derivative step. -/
theorem growingZeroStep_hasNonnegCoeffs_iff
    {a b u v : ℝ} {f : ℝ[X]} (hf : f ≠ 0)
    (hfnonneg : HasNonnegCoeffs f) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hraise : v * (f.natDegree : ℝ) < b) :
    HasNonnegCoeffs (growingZeroStep a b u v f) ↔
      0 ≤ a + u * (f.rootMultiplicity 0 : ℝ) := by
  constructor
  · intro hstep
    have hcoeff := hstep (f.rootMultiplicity 0)
    rw [growingZeroStep_coeff_rootMultiplicity] at hcoeff
    exact nonneg_of_mul_nonneg_left hcoeff (coeff_rootMultiplicity_pos hf hfnonneg)
  · intro heffective k
    cases k with
    | zero =>
        rw [growingZeroStep_coeff_zero]
        by_cases hm : f.rootMultiplicity 0 = 0
        · rw [hm] at heffective
          norm_num at heffective
          exact mul_nonneg heffective (hfnonneg 0)
        · have hcoeff : f.coeff 0 = 0 := by
            apply coeff_eq_zero_of_lt_natTrailingDegree
            rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree']
            exact Nat.pos_of_ne_zero hm
          rw [hcoeff, mul_zero]
    | succ k =>
        rw [growingZeroStep_coeff_succ]
        apply add_nonneg
        · by_cases hk : f.rootMultiplicity 0 ≤ k + 1
          · apply mul_nonneg
            · have hk_cast : (f.rootMultiplicity 0 : ℝ) ≤ (k + 1 : ℕ) := by
                exact_mod_cast hk
              norm_num at hk_cast
              nlinarith
            · exact hfnonneg (k + 1)
          · rw [coeff_eq_zero_of_lt_natTrailingDegree]
            · simp
            · rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree']
              exact Nat.lt_of_not_ge hk
        · by_cases hk : k ≤ f.natDegree
          · apply mul_nonneg
            · have hk_cast : (k : ℝ) ≤ (f.natDegree : ℝ) := by exact_mod_cast hk
              nlinarith
            · exact hfnonneg k
          · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hk), mul_zero]

/-- A noncancelling growing-zero step is in proper position above its PF input. -/
theorem growingZeroStep_strictInterl
    {a b u v : ℝ} {f : ℝ[X]} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hraise : v * (f.natDegree : ℝ) < b) :
    StrictInterl f (growingZeroStep a b u v f) := by
  have hsplit := (hf.ne_zero_and_splits hf0).2
  have hfpos := hf.hasNonnegCoeffs.pos_leadingCoeff hf0
  have hdegree := growingZeroStep_natDegree_and_leadingCoeff
    (a := a) (b := b) (u := u) (v := v) hf0 hraise
  let U := C a + C b * X
  let V := C u * X + C (-v) * X ^ 2
  have hform : U * f + V * f.derivative = growingZeroStep a b u v f := by
    simp [U, V, growingZeroStep, add_comm]
  have hdeg_lo : f.natDegree ≤ (U * f + V * f.derivative).natDegree := by
    rw [hform, hdegree.1]
    lia
  have hdeg_hi : (U * f + V * f.derivative).natDegree ≤ f.natDegree + 1 := by
    rw [hform, hdegree.1]
  have hstep_pos : HasPosLeadingCoeff (U * f + V * f.derivative) := by
    rw [hform, HasPosLeadingCoeff, hdegree.2]
    exact mul_pos (by linarith) hfpos
  have hV : ∀ r, f.IsRoot r → V.eval r ≤ 0 := by
    intro r hr
    have hr_nonpos := hf.roots_nonpos r ((mem_roots hf0).mpr hr)
    simp only [V, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    nlinarith
  have hinter := MaWang.strictInterl_derivative_of_nonpos_of_splits
    hsplit hdeg_lo hdeg_hi hstep_pos hfpos hV
  rwa [hform] at hinter

/-- A growing-zero derivative step is PF exactly when its effective constant
coefficient at the input's zero multiplicity is nonnegative. -/
theorem growingZeroStep_isPFPolynomial_iff
    {a b u v : ℝ} {f : ℝ[X]} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hraise : v * (f.natDegree : ℝ) < b) :
    IsPFPolynomial (growingZeroStep a b u v f) ↔
      0 ≤ a + u * (f.rootMultiplicity 0 : ℝ) := by
  rw [← growingZeroStep_hasNonnegCoeffs_iff hf0 hf.hasNonnegCoeffs hu hv hraise]
  constructor
  · exact IsPFPolynomial.hasNonnegCoeffs
  · intro hnonneg
    exact IsPFPolynomial.of_realRooted_nonneg hnonneg
      (growingZeroStep_strictInterl hf hf0 hu hv hraise).2.1.2

/-! ## The integer-parameter family -/

/-- The family starting at `1` and iterating the growing-zero derivative step
with affine coefficients in the row index. -/
@[expose] def growingZeroFamily (a r b c : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => growingZeroStep (a - n) (b * n + c) r r
      (growingZeroFamily a r b c n)

/-- The initial row of `growingZeroFamily`. -/
@[simp] theorem growingZeroFamily_zero (a r b c : ℝ) :
    growingZeroFamily a r b c 0 = 1 := by
  rfl

/-- The defining recurrence of `growingZeroFamily`. -/
@[simp] theorem growingZeroFamily_succ (a r b c : ℝ) (n : ℕ) :
    growingZeroFamily a r b c (n + 1) =
      growingZeroStep (a - n) (b * n + c) r r
        (growingZeroFamily a r b c n) := by
  rfl

/-- Ceiling division after a successor either stays fixed or increases by one. -/
private lemma ceilDiv_succ' (R k : ℕ) (hR : 0 < R) :
    (k + 1) ⌈/⌉ R =
      if k = R * (k ⌈/⌉ R) then k ⌈/⌉ R + 1 else k ⌈/⌉ R := by
  let m := k ⌈/⌉ R
  have hkm : k ≤ R * m := le_smul_ceilDiv hR
  split_ifs with heq
  · apply le_antisymm
    · rw [ceilDiv_le_iff_le_mul hR]
      nlinarith
    · rw [Nat.succ_le_iff, ← not_le, ceilDiv_le_iff_le_mul hR]
      nlinarith
  · have hlt : k < R * m := lt_of_le_of_ne hkm heq
    apply le_antisymm
    · rw [ceilDiv_le_iff_le_mul hR]
      lia
    · exact (gc_mul_ceilDiv hR).monotone_l (Nat.le_add_right k 1)

/-- The effective constant coefficient is nonnegative at the closed-form
multiplicity. -/
private lemma effectiveConstant_nonneg (A R n : ℕ) (hR : 0 < R) :
    0 ≤ (A : ℝ) - n + R * (MaWang.affineEndpointMultiplicity R A n : ℝ) := by
  by_cases hAn : A ≤ n
  · have hceil : n - A ≤ R * MaWang.affineEndpointMultiplicity R A n := by
      exact (ceilDiv_le_iff_le_mul hR).mp le_rfl
    have hcast : ((n - A : ℕ) : ℝ) = (n : ℝ) - A := Nat.cast_sub hAn
    have hceil' : (n : ℝ) - A ≤
        R * (MaWang.affineEndpointMultiplicity R A n : ℝ) := by
      rw [← hcast]
      exact_mod_cast hceil
    linarith
  · have hnA : (n : ℝ) < A := by exact_mod_cast Nat.lt_of_not_ge hAn
    positivity

/-- Vanishing of the effective constant coefficient is the divisibility
threshold at which the zero multiplicity grows. -/
private lemma effectiveConstant_eq_zero_iff (A R n : ℕ) (hR : 0 < R) :
    (A : ℝ) - n + R * (MaWang.affineEndpointMultiplicity R A n : ℝ) = 0 ↔
      A ≤ n ∧ n - A = R * MaWang.affineEndpointMultiplicity R A n := by
  constructor
  · intro heq
    have hAn : A ≤ n := by
      by_contra h
      have hnA : (n : ℝ) < A := by exact_mod_cast Nat.lt_of_not_ge h
      have hm : 0 ≤ (MaWang.affineEndpointMultiplicity R A n : ℝ) := by positivity
      have hR' : 0 < (R : ℝ) := by positivity
      nlinarith
    refine ⟨hAn, ?_⟩
    have hcast : ((n - A : ℕ) : ℝ) = (n : ℝ) - A := Nat.cast_sub hAn
    exact_mod_cast (show (n : ℝ) - A =
      R * (MaWang.affineEndpointMultiplicity R A n : ℝ) by linarith)
  · rintro ⟨hAn, heq⟩
    have hcast : ((n - A : ℕ) : ℝ) = (n : ℝ) - A := Nat.cast_sub hAn
    have heq' : (n : ℝ) - A =
        R * (MaWang.affineEndpointMultiplicity R A n : ℝ) := by
      rw [← hcast]
      exact_mod_cast heq
    linarith

/-- The closed-form zero multiplicity obeys the update dictated by the
effective constant coefficient. -/
private lemma affineEndpointMultiplicity_succ' (A R n : ℕ) (hR : 0 < R) :
    MaWang.affineEndpointMultiplicity R A (n + 1) =
      if (A : ℝ) - n + R * (MaWang.affineEndpointMultiplicity R A n : ℝ) = 0
      then MaWang.affineEndpointMultiplicity R A n + 1
      else MaWang.affineEndpointMultiplicity R A n := by
  by_cases hAn : A ≤ n
  · have hsub : n + 1 - A = (n - A) + 1 := by lia
    have hiff :
        ((A : ℝ) - n + R * (((n - A) ⌈/⌉ R : ℕ) : ℝ) = 0) ↔
          n - A = R * ((n - A) ⌈/⌉ R) := by
      simpa [MaWang.affineEndpointMultiplicity, hAn] using
        effectiveConstant_eq_zero_iff A R n hR
    rw [MaWang.affineEndpointMultiplicity, MaWang.affineEndpointMultiplicity, hsub,
      ceilDiv_succ' R (n - A) hR]
    simp only [hiff]
  · have hle : n + 1 ≤ A := by lia
    have hsub : n - A = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hAn))
    have hsub' : n + 1 - A = 0 := Nat.sub_eq_zero_of_le hle
    rw [MaWang.affineEndpointMultiplicity, hsub', zero_ceilDiv,
      MaWang.affineEndpointMultiplicity, hsub, zero_ceilDiv]
    have hnA : (n : ℝ) < (A : ℝ) := by exact_mod_cast (show n < A by lia)
    have hpos : 0 < (A : ℝ) - n := by linarith
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [ite_eq_right hpos.ne']

/-- For nonnegative integer `a` and positive integer `r`, the affine family is
PF in every row, has degree equal to its index, has the stated zero
multiplicity and leading coefficient, and consecutive rows interlace. -/
theorem growingZeroFamily_pf_degree_multiplicity_interlacing
    (A R : ℕ) {b c : ℝ} (hR : 0 < R) (hb : (R : ℝ) ≤ b) (hc : 0 < c) :
    ∀ n : ℕ,
      IsPFPolynomial (growingZeroFamily A R b c n) ∧
      (growingZeroFamily A R b c n).natDegree = n ∧
      (growingZeroFamily A R b c n).rootMultiplicity 0 =
        MaWang.affineEndpointMultiplicity R A n ∧
      StrictInterl (growingZeroFamily A R b c n)
        (growingZeroFamily A R b c (n + 1)) ∧
      (growingZeroFamily A R b c n).leadingCoeff =
        (Finset.range n).prod fun j => (b - R) * j + c := by
  intro n
  induction n with
  | zero =>
      refine ⟨IsPFPolynomial.one, by simp, ?_, ?_, by simp⟩
      · simp [MaWang.affineEndpointMultiplicity]
      · have hraise : (R : ℝ) * ((1 : ℝ[X]).natDegree : ℝ) < b * 0 + c := by
          simpa using hc
        simpa using growingZeroStep_strictInterl IsPFPolynomial.one one_ne_zero
          (by positivity : 0 ≤ (R : ℝ)) (by positivity : 0 ≤ (R : ℝ)) hraise
  | succ n ih =>
      have hrow0 : growingZeroFamily A R b c n ≠ 0 :=
        ih.2.2.2.1.1.1
      have hraise : (R : ℝ) *
          ((growingZeroFamily A R b c n).natDegree : ℝ) < b * n + c := by
        rw [ih.2.1]
        have hn : 0 ≤ (n : ℝ) := by positivity
        nlinarith
      have heffective : 0 ≤ (A : ℝ) - n +
          R * ((growingZeroFamily A R b c n).rootMultiplicity 0 : ℝ) := by
        rw [ih.2.2.1]
        exact effectiveConstant_nonneg A R n hR
      have hpf : IsPFPolynomial (growingZeroFamily A R b c (n + 1)) := by
        rw [growingZeroFamily_succ]
        exact (growingZeroStep_isPFPolynomial_iff ih.1 hrow0
          (by positivity) (by positivity) hraise).2 heffective
      have hdegree : (growingZeroFamily A R b c (n + 1)).natDegree = n + 1 := by
        rw [growingZeroFamily_succ,
          (growingZeroStep_natDegree_and_leadingCoeff hrow0 hraise).1, ih.2.1]
      have hmult : (growingZeroFamily A R b c (n + 1)).rootMultiplicity 0 =
          MaWang.affineEndpointMultiplicity R A (n + 1) := by
        rw [growingZeroFamily_succ,
          growingZeroStep_rootMultiplicity hrow0 ih.1.hasNonnegCoeffs
            (by positivity) (by positivity) hraise,
          ih.2.2.1]
        exact (affineEndpointMultiplicity_succ' A R n hR).symm
      have hnext0 : growingZeroFamily A R b c (n + 1) ≠ 0 := by
        intro hzero
        rw [hzero, natDegree_zero] at hdegree
        lia
      have hraise_next : (R : ℝ) *
          ((growingZeroFamily A R b c (n + 1)).natDegree : ℝ) <
            b * ((n + 1 : ℕ) : ℝ) + c := by
        rw [hdegree]
        have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
        have hterm : 0 ≤ (b - R) * ((n + 1 : ℕ) : ℝ) :=
          mul_nonneg (sub_nonneg.mpr hb) hn
        nlinarith
      have hinter : StrictInterl (growingZeroFamily A R b c (n + 1))
          (growingZeroFamily A R b c (n + 2)) := by
        change StrictInterl (growingZeroFamily A R b c (n + 1))
          (growingZeroStep (A - (n + 1 : ℕ)) (b * (n + 1 : ℕ) + c) R R
            (growingZeroFamily A R b c (n + 1)))
        exact growingZeroStep_strictInterl hpf hnext0
          (by positivity) (by positivity) hraise_next
      have hleading : (growingZeroFamily A R b c (n + 1)).leadingCoeff =
          (Finset.range (n + 1)).prod fun j => (b - R) * j + c := by
        calc
          (growingZeroFamily A R b c (n + 1)).leadingCoeff =
              (b * n + c - R * (n : ℝ)) *
                (growingZeroFamily A R b c n).leadingCoeff := by
            rw [growingZeroFamily_succ,
              (growingZeroStep_natDegree_and_leadingCoeff hrow0 hraise).2, ih.2.1]
          _ = ((b - R) * (n : ℝ) + c) *
                (Finset.range n).prod (fun j => (b - R) * j + c) := by
            rw [ih.2.2.2.2]
            ring
          _ = (Finset.range (n + 1)).prod fun j => (b - R) * j + c := by
            rw [Finset.prod_range_succ]
            ring
      exact ⟨hpf, hdegree, hmult, hinter, hleading⟩

/-- Constant coefficients in the affine family satisfy the falling-factorial
recurrence. -/
theorem growingZeroFamily_coeff_zero_succ (a r b c : ℝ) (n : ℕ) :
    (growingZeroFamily a r b c (n + 1)).coeff 0 =
      (a - n) * (growingZeroFamily a r b c n).coeff 0 := by
  rw [growingZeroFamily_succ, growingZeroStep_coeff_zero]

/-- Linear coefficients in the affine family satisfy the recurrence used in
the integrality classification. -/
theorem growingZeroFamily_coeff_one_succ (a r b c : ℝ) (n : ℕ) :
    (growingZeroFamily a r b c (n + 1)).coeff 1 =
      (a - n + r) * (growingZeroFamily a r b c n).coeff 1 +
        (b * n + c) * (growingZeroFamily a r b c n).coeff 0 := by
  rw [growingZeroFamily_succ, show 1 = 0 + 1 by rfl,
    growingZeroStep_coeff_succ]
  norm_num

/-- If all rows are PF, the initial parameter is a nonnegative integer. -/
private lemma exists_nat_eq_of_growingZeroFamily_pf
    {a r b c : ℝ} (hall : ∀ n, IsPFPolynomial (growingZeroFamily a r b c n)) :
    ∃ A : ℕ, a = A := by
  have ha : 0 ≤ a := by
    have h := (hall 1).hasNonnegCoeffs 0
    simpa [growingZeroFamily, growingZeroStep] using h
  let A := ⌊a⌋₊
  have hA_le : (A : ℝ) ≤ a := by
    exact Nat.floor_le ha
  by_cases haA : a = (A : ℝ)
  · exact ⟨A, haA⟩
  · have hA_lt : (A : ℝ) < a := lt_of_le_of_ne hA_le (Ne.symm haA)
    have hcoeff_pos : ∀ n, n ≤ A + 1 →
        0 < (growingZeroFamily a r b c n).coeff 0 := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
          rw [growingZeroFamily_coeff_zero_succ]
          apply mul_pos
          · have hnA : n ≤ A := by lia
            have hnA' : (n : ℝ) ≤ A := by exact_mod_cast hnA
            linarith
          · exact ih (by lia)
    have hnonneg := (hall (A + 2)).hasNonnegCoeffs 0
    rw [show A + 2 = (A + 1) + 1 by lia,
      growingZeroFamily_coeff_zero_succ] at hnonneg
    have ha_lt : a < (A : ℝ) + 1 := Nat.lt_floor_add_one a
    norm_num only [Nat.cast_add, Nat.cast_one] at hnonneg
    have hneg : a - ((A : ℝ) + 1) < 0 := sub_neg.mpr ha_lt
    have hprodneg := mul_neg_of_neg_of_pos hneg (hcoeff_pos (A + 1) le_rfl)
    exact False.elim ((not_lt_of_ge hnonneg) hprodneg)

/-- Once `a = A`, the constant coefficient is positive through row `A`. -/
private lemma growingZeroFamily_coeff_zero_pos_to_integer
    (A : ℕ) (r b c : ℝ) :
    ∀ n, n ≤ A → 0 < (growingZeroFamily A r b c n).coeff 0 := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
      rw [growingZeroFamily_coeff_zero_succ]
      apply mul_pos
      · have hnA : n < A := by lia
        exact sub_pos.mpr (by exact_mod_cast hnA)
      · exact ih (by lia)

/-- After row `A`, the constant coefficient vanishes permanently. -/
private lemma growingZeroFamily_coeff_zero_of_integer_le
    (A : ℕ) (r b c : ℝ) (n : ℕ) (hn : A + 1 ≤ n) :
    (growingZeroFamily A r b c n).coeff 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
      rw [growingZeroFamily_coeff_zero_succ]
      norm_num
  | succ k ih =>
      rw [show A + 1 + (k + 1) = (A + 1 + k) + 1 by lia,
        growingZeroFamily_coeff_zero_succ, ih (by lia), mul_zero]

/-- If all rows are PF and `a` is integral, positivity of `r` forces `r` to
be a positive integer. -/
private lemma exists_pos_nat_eq_of_growingZeroFamily_pf
    (A : ℕ) {r b c : ℝ} (hr : 0 < r) (hb : r ≤ b) (hc : 0 < c)
    (hall : ∀ n, IsPFPolynomial (growingZeroFamily A r b c n)) :
    ∃ R : ℕ, 0 < R ∧ r = R := by
  have hA0pos := growingZeroFamily_coeff_zero_pos_to_integer A r b c A le_rfl
  have hA1pos : 0 < (growingZeroFamily A r b c (A + 1)).coeff 1 := by
    rw [growingZeroFamily_coeff_one_succ]
    have hfirst : 0 ≤ r * (growingZeroFamily A r b c A).coeff 1 :=
      mul_nonneg hr.le ((hall A).hasNonnegCoeffs 1)
    have hfactor : 0 < b * (A : ℝ) + c := by
      have hb0 : 0 ≤ b := le_trans hr.le hb
      positivity
    norm_num
    nlinarith
  have hone_rec : ∀ n, A + 1 ≤ n →
      (growingZeroFamily A r b c (n + 1)).coeff 1 =
        ((A : ℝ) + r - n) * (growingZeroFamily A r b c n).coeff 1 := by
    intro n hn
    rw [growingZeroFamily_coeff_one_succ,
      growingZeroFamily_coeff_zero_of_integer_le A r b c n hn, mul_zero, add_zero]
    ring
  let R := ⌊r⌋₊
  have hR_le : (R : ℝ) ≤ r := Nat.floor_le hr.le
  by_cases hrR : r = (R : ℝ)
  · refine ⟨R, ?_, hrR⟩
    exact Nat.pos_of_ne_zero fun hzero => by
      rw [hzero] at hrR
      norm_num at hrR
      linarith
  · have hR_lt : (R : ℝ) < r := lt_of_le_of_ne hR_le (Ne.symm hrR)
    have hcoeff_pos : ∀ k, k ≤ R →
        0 < (growingZeroFamily A r b c (A + 1 + k)).coeff 1 := by
      intro k hk
      induction k with
      | zero => simpa using hA1pos
      | succ k ih =>
          rw [show A + 1 + (k + 1) = (A + 1 + k) + 1 by lia,
            hone_rec (A + 1 + k) (by lia)]
          apply mul_pos
          · have hkR : k + 1 ≤ R := hk
            have hkR' : ((k + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hkR
            have hkr : ((k + 1 : ℕ) : ℝ) < r := hkR'.trans_lt hR_lt
            have hfactor : (A : ℝ) + r - (A + 1 + k : ℕ) =
                r - (k + 1 : ℕ) := by
              push_cast
              ring
            rw [hfactor]
            exact sub_pos.mpr hkr
          · exact ih (by lia)
    have hnonneg := (hall (A + R + 2)).hasNonnegCoeffs 1
    rw [show A + R + 2 = (A + 1 + R) + 1 by lia,
      hone_rec (A + 1 + R) (by lia)] at hnonneg
    have hr_lt : r < (R : ℝ) + 1 := Nat.lt_floor_add_one r
    push_cast at hnonneg
    nlinarith [hcoeff_pos R le_rfl]

/-- All rows of the affine family are PF exactly for a nonnegative integer
initial parameter and a positive integer derivative parameter. -/
theorem growingZeroFamily_all_isPFPolynomial_iff
    {a r b c : ℝ} (hr : 0 < r) (hb : r ≤ b) (hc : 0 < c) :
    (∀ n, IsPFPolynomial (growingZeroFamily a r b c n)) ↔
      ∃ A R : ℕ, 0 < R ∧ a = A ∧ r = R := by
  constructor
  · intro hall
    obtain ⟨A, ha⟩ := exists_nat_eq_of_growingZeroFamily_pf hall
    subst a
    obtain ⟨R, hR, hrR⟩ :=
      exists_pos_nat_eq_of_growingZeroFamily_pf A hr hb hc hall
    exact ⟨A, R, hR, rfl, hrR⟩
  · rintro ⟨A, R, hR, rfl, rfl⟩
    exact fun n =>
      (growingZeroFamily_pf_degree_multiplicity_interlacing A R hR hb hc n).1

/-- A growing-zero step with positive derivative parameter preserves
simplicity away from zero and shares no negative root with its input. -/
theorem growingZeroStep_hasSimpleRootsExcept_zero_and_noCommon_neg
    {a b u v : ℝ} {f : ℝ[X]} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    (hF : IsPFPolynomial (growingZeroStep a b u v f))
    (hsimple : HasSimpleRootsExcept f 0) (hu : 0 < u) (hv : 0 ≤ v)
    (hraise : v * (f.natDegree : ℝ) < b) :
    HasSimpleRootsExcept (growingZeroStep a b u v f) 0 ∧
      ∀ x : ℝ, x < 0 →
        ¬(f.IsRoot x ∧ (growingZeroStep a b u v f).IsRoot x) := by
  have hinter := growingZeroStep_strictInterl
    (a := a) (b := b) (u := u) (v := v) hf hf0 hu.le hv hraise
  have hno : ∀ x : ℝ, x < 0 →
      ¬(f.IsRoot x ∧ (growingZeroStep a b u v f).IsRoot x) := by
    intro x hx hcommon
    have hder_ne : f.derivative.eval x ≠ 0 := by
      intro hder
      have hderroot : f.derivative.IsRoot x := by
        simpa [Polynomial.IsRoot.def] using hder
      have hmult : 1 < f.rootMultiplicity x :=
        (one_lt_rootMultiplicity_iff_isRoot hf0).2 ⟨hcommon.1, hderroot⟩
      have hsimple_x := hsimple x (ne_of_lt hx) hcommon.1
      lia
    have hFzero := hcommon.2
    have hfzero := hcommon.1
    rw [Polynomial.IsRoot.def, growingZeroStep] at hFzero
    rw [Polynomial.IsRoot.def] at hfzero
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow] at hFzero
    rw [hfzero, mul_zero, add_zero] at hFzero
    have hfactor : u * x + -v * x ^ 2 < 0 := by
      have hx2 : 0 < x ^ 2 := sq_pos_of_neg hx
      nlinarith
    rcases mul_eq_zero.mp hFzero with hfactor0 | hder0
    · exact hfactor.ne hfactor0
    · exact hder_ne hder0
  refine ⟨?_, hno⟩
  intro x hx0 hxroot
  have hpos : 0 < (growingZeroStep a b u v f).rootMultiplicity x :=
    (rootMultiplicity_pos hinter.2.1.1).2 hxroot
  have hle : (growingZeroStep a b u v f).rootMultiplicity x ≤ 1 := by
    by_contra h
    have hlarge : 1 < (growingZeroStep a b u v f).rootMultiplicity x := by lia
    have hfold : f.IsRoot x := hinter.isRoot_of_one_lt_rootMultiplicity hlarge
    have hx_nonpos := hF.roots_nonpos x ((mem_roots hinter.2.1.1).2 hxroot)
    exact hno x (lt_of_le_of_ne hx_nonpos hx0) ⟨hfold, hxroot⟩
  lia

/-- In the integer-parameter family every negative root is simple, and
consecutive rows have no common negative root. -/
theorem growingZeroFamily_negative_roots_simple_and_noCommon
    (A R : ℕ) {b c : ℝ} (hR : 0 < R) (hb : (R : ℝ) ≤ b) (hc : 0 < c) :
    ∀ n : ℕ,
      HasSimpleRootsExcept (growingZeroFamily A R b c n) 0 ∧
      ∀ x : ℝ, x < 0 →
        ¬((growingZeroFamily A R b c n).IsRoot x ∧
          (growingZeroFamily A R b c (n + 1)).IsRoot x) := by
  have hpackage := growingZeroFamily_pf_degree_multiplicity_interlacing A R hR hb hc
  have hsimple : ∀ n, HasSimpleRootsExcept (growingZeroFamily A R b c n) 0 := by
    intro n
    induction n with
    | zero =>
        intro x _ hx
        simp [Polynomial.IsRoot.def] at hx
    | succ n ih =>
        have hrow0 : growingZeroFamily A R b c n ≠ 0 :=
          (hpackage n).2.2.2.1.1.1
        have hraise : (R : ℝ) *
            ((growingZeroFamily A R b c n).natDegree : ℝ) < b * n + c := by
          rw [(hpackage n).2.1]
          have hn : 0 ≤ (n : ℝ) := by positivity
          nlinarith
        have hstep := growingZeroStep_hasSimpleRootsExcept_zero_and_noCommon_neg
          (hpackage n).1 hrow0 (by
            rw [← growingZeroFamily_succ]
            exact (hpackage (n + 1)).1) ih (by positivity) (by positivity) hraise
        rw [← growingZeroFamily_succ] at hstep
        exact hstep.1
  intro n
  have hrow0 : growingZeroFamily A R b c n ≠ 0 :=
    (hpackage n).2.2.2.1.1.1
  have hraise : (R : ℝ) *
      ((growingZeroFamily A R b c n).natDegree : ℝ) < b * n + c := by
    rw [(hpackage n).2.1]
    have hn : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hstep := growingZeroStep_hasSimpleRootsExcept_zero_and_noCommon_neg
    (hpackage n).1 hrow0 (by
      rw [← growingZeroFamily_succ]
      exact (hpackage (n + 1)).1) (hsimple n) (by positivity) (by positivity) hraise
  rw [← growingZeroFamily_succ] at hstep
  exact ⟨hsimple n, hstep.2⟩

end RealRooted
