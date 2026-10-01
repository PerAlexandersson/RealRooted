import RealRooted.BasisTransform
import RealRooted.Mathlib.Data.Nat.Choose.Nanjundiah

/-!
# Binary-run transformation: coefficient algebra

This file defines the normalized binary-run basis polynomial

`J n m = choose n m ⁻¹ * ∑ k≥1 choose (m-1) (k-1) choose (n+1-m) k X^k`

with `J n 0 = 1`, and the basis transform sending `X^m` to `J n m`.
The shifted coefficient formula is the finite identity used by the stable
pointing construction.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The normalized binary-run polynomial `J_{n,m}`. -/
def binaryRunPolynomial (n m : ℕ) : ℝ[X] :=
  if m = 0 then 1
  else
    ∑ k ∈ Finset.Icc 1 n,
      monomial k
        (((Nat.choose (m - 1) (k - 1) : ℝ) *
            (Nat.choose (n + 1 - m) k : ℝ)) /
          (Nat.choose n m : ℝ))

/-- The fixed-rank binary-run basis transform. -/
def binaryRunTransform (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  Polynomial.basisTransform (binaryRunPolynomial n) p

@[simp] theorem binaryRunPolynomial_zero (n : ℕ) :
    binaryRunPolynomial n 0 = 1 := by
  simp [binaryRunPolynomial]

@[simp] theorem binaryRunTransform_X_pow (n m : ℕ) :
    binaryRunTransform n (X ^ m) = binaryRunPolynomial n m := by
  simp [binaryRunTransform]

@[simp] theorem binaryRunTransform_zero (n : ℕ) :
    binaryRunTransform n 0 = 0 := by
  simp [binaryRunTransform]

theorem binaryRunTransform_add (n : ℕ) (p q : ℝ[X]) :
    binaryRunTransform n (p + q) =
      binaryRunTransform n p + binaryRunTransform n q := by
  simp [binaryRunTransform, Polynomial.basisTransform_add]

theorem binaryRunTransform_smul (n : ℕ) (a : ℝ) (p : ℝ[X]) :
    binaryRunTransform n (a • p) = C a * binaryRunTransform n p := by
  simp [binaryRunTransform, Polynomial.basisTransform_smul]

@[simp] theorem binaryRunTransform_one (n : ℕ) :
    binaryRunTransform n 1 = 1 := by
  simpa [binaryRunTransform] using
    (Polynomial.basisTransform_C (binaryRunPolynomial n) (1 : ℝ))

theorem hasNonnegCoeffs_binaryRunPolynomial (n m : ℕ) :
    HasNonnegCoeffs (binaryRunPolynomial n m) := by
  by_cases hm : m = 0
  · simpa [hm] using hasNonnegCoeffs_one
  rw [binaryRunPolynomial, ite_eq_right hm]
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg fun k _ => by
    rw [coeff_monomial]
    split <;> positivity

theorem HasNonnegCoeffs.binaryRunTransform {n : ℕ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (binaryRunTransform n p) :=
  hp.basisTransform (hasNonnegCoeffs_binaryRunPolynomial n)

/-- Fixed-range coefficient expansion of the binary-run transform. -/
theorem coeff_binaryRunTransform_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (k : ℕ) :
    (binaryRunTransform n p).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        p.coeff m * (binaryRunPolynomial n m).coeff k := by
  rw [binaryRunTransform, Polynomial.basisTransform, Polynomial.sum_def,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le <|
      (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hm)).trans hp
  · intro m hmrange hmsupport
    rw [Polynomial.notMem_support_iff.mp hmsupport]
    simp

/-- Away from the constant basis image, the coefficient of `X^k` in
`J_{n,m}` is the defining normalized binary-run count. -/
theorem coeff_binaryRunPolynomial_of_pos_formula (n m k : ℕ)
    (hm0 : 0 < m) (hk0 : 0 < k) :
    (binaryRunPolynomial n m).coeff k =
      ((Nat.choose (m - 1) (k - 1) : ℝ) *
          (Nat.choose (n + 1 - m) k : ℝ)) /
        (Nat.choose n m : ℝ) := by
  rw [binaryRunPolynomial, ite_eq_right (ne_of_gt hm0),
    Polynomial.finsetSum_coeff]
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [coeff_monomial, hbk]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨hk0, hkn⟩)).elim
  · have htop : n + 1 - m < k := by lia
    rw [Finset.sum_eq_zero]
    · simp [Nat.choose_eq_zero_of_lt htop]
    · intro b hb
      rw [coeff_monomial, ite_eq_right]
      intro hbk
      subst b
      exact hkn (Finset.mem_Icc.mp hb).2

/-- Every nonconstant binary-run basis image has zero constant term. -/
theorem coeff_zero_binaryRunPolynomial_of_pos (n m : ℕ) (hm0 : 0 < m) :
    (binaryRunPolynomial n m).coeff 0 = 0 := by
  rw [binaryRunPolynomial, ite_eq_right (ne_of_gt hm0),
    Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hk).1
  simp [coeff_monomial, hk0]

/-- A binary-run basis image has no terms above its input index. -/
theorem coeff_binaryRunPolynomial_eq_zero_of_lt
    {n m k : ℕ} (hmk : m < k) :
    (binaryRunPolynomial n m).coeff k = 0 := by
  have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le m) hmk
  by_cases hm0 : m = 0
  · subst m
    rw [binaryRunPolynomial_zero, Polynomial.coeff_one,
      ite_eq_right hk0.ne']
  rw [coeff_binaryRunPolynomial_of_pos_formula n m k
    (Nat.pos_of_ne_zero hm0) hk0]
  have hchoose : Nat.choose (m - 1) (k - 1) = 0 :=
    Nat.choose_eq_zero_of_lt (by lia)
  simp [hchoose]

/-- The diagonal coefficient of `J_{n,k}` is the normalized path-matching
number `choose (n+1-k) k / choose n k`. -/
theorem coeff_binaryRunPolynomial_self (n k : ℕ) (hk0 : 0 < k) :
    (binaryRunPolynomial n k).coeff k =
      (Nat.choose (n + 1 - k) k : ℝ) / (Nat.choose n k : ℝ) := by
  rw [coeff_binaryRunPolynomial_of_pos_formula n k k hk0 hk0]
  simp

theorem coeff_comp_binaryRunPolynomial (n m k : ℕ) (hm0 : 0 < m) :
    ((binaryRunPolynomial n m).comp (X + 1)).coeff k =
      ∑ r ∈ Finset.Icc 1 n,
        (((Nat.choose (m - 1) (r - 1) : ℝ) *
            (Nat.choose (n + 1 - m) r : ℝ)) /
          (Nat.choose n m : ℝ)) * (Nat.choose r k : ℝ) := by
  rw [binaryRunPolynomial, ite_eq_right (ne_of_gt hm0)]
  change ((Polynomial.compRingHom (X + 1))
    (∑ r ∈ Finset.Icc 1 n,
      monomial r
        (((Nat.choose (m - 1) (r - 1) : ℝ) *
            (Nat.choose (n + 1 - m) r : ℝ)) /
          (Nat.choose n m : ℝ)))).coeff k = _
  rw [map_sum]
  simp only [Polynomial.coe_compRingHom_apply,
    Polynomial.finsetSum_coeff, monomial_comp, coeff_C_mul,
    coeff_X_add_one_pow]

private theorem binaryRun_weighted_sum_pos (n m k : ℕ) (hm0 : 0 < m)
    (hm : m ≤ n) (hk : k ≤ m) (hkA : k ≤ n + 1 - m)
    (hk0 : 0 < k) :
    (∑ r ∈ Finset.Icc 1 n,
      Nat.choose r k * Nat.choose (m - 1) (r - 1) *
        Nat.choose (n + 1 - m) r) =
      Nat.choose (n + 1 - m) k * Nat.choose (n - k) (m - k) := by
  let f := fun r => Nat.choose r k * Nat.choose (m - 1) (r - 1) *
    Nat.choose (n + 1 - m) r
  have hrestrict :
      (∑ r ∈ Finset.Icc 1 n, f r) = ∑ r ∈ Finset.Icc 1 m, f r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans hm⟩
    · intro r hrn hrm
      have hmr : m < r := by
        have hr1 := (Finset.mem_Icc.mp hrn).1
        simp only [Finset.mem_Icc, hr1, true_and] at hrm
        lia
      have hlt : m - 1 < r - 1 := by lia
      dsimp [f]
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
  have hrange :
      (∑ r ∈ Finset.Icc 1 m, f r) = ∑ r ∈ Finset.range (m + 1), f r := by
    apply Finset.sum_subset
    · intro r hr
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hr).2
    · intro r hr hrnot
      have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      have hr0 : r = 0 := by
        by_contra h
        exact hrnot (Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr h, hrm⟩)
      subst r
      dsimp [f]
      rw [Nat.choose_eq_zero_of_lt hk0]
      simp
  rw [show (∑ r ∈ Finset.Icc 1 n,
      Nat.choose r k * Nat.choose (m - 1) (r - 1) *
        Nat.choose (n + 1 - m) r) = ∑ r ∈ Finset.Icc 1 n, f r by rfl,
    hrestrict, hrange]
  calc
    (∑ r ∈ Finset.range (m + 1), f r) =
        ∑ r ∈ Finset.range (m + 1),
          Nat.choose (n + 1 - m) r *
            Nat.choose (m - 1) (m - r) * Nat.choose r k := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      by_cases hr0 : r = 0
      · subst r
        dsimp [f]
        rw [Nat.choose_eq_zero_of_lt hk0]
        simp
      · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        have hidx : r - 1 ≤ m - 1 := by lia
        have hcomp : m - 1 - (r - 1) = m - r := by lia
        dsimp [f]
        rw [← Nat.choose_symm hidx, hcomp]
        ring
    _ = Nat.choose (n + 1 - m) k *
        Nat.choose (n + 1 - m - k + (m - 1)) (m - k) :=
      Nat.weighted_vandermonde (n + 1 - m) (m - 1) m k hk
    _ = Nat.choose (n + 1 - m) k *
        Nat.choose (n - k) (m - k) := by
      have htop : n + 1 - m - k + (m - 1) = n - k := by lia
      rw [htop]

private theorem binaryRun_weighted_sum_zero (n m : ℕ) (hm0 : 0 < m)
    (hm : m ≤ n) :
    (∑ r ∈ Finset.Icc 1 n,
      Nat.choose r 0 * Nat.choose (m - 1) (r - 1) *
        Nat.choose (n + 1 - m) r) = Nat.choose n m := by
  let f := fun r => Nat.choose r 0 * Nat.choose (m - 1) (r - 1) *
    Nat.choose (n + 1 - m) r
  have hrestrict :
      (∑ r ∈ Finset.Icc 1 n, f r) = ∑ r ∈ Finset.Icc 1 m, f r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans hm⟩
    · intro r hrn hrm
      have hmr : m < r := by
        have hr1 := (Finset.mem_Icc.mp hrn).1
        simp only [Finset.mem_Icc, hr1, true_and] at hrm
        lia
      have hlt : m - 1 < r - 1 := by lia
      dsimp [f]
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
  rw [show (∑ r ∈ Finset.Icc 1 n,
      Nat.choose r 0 * Nat.choose (m - 1) (r - 1) *
        Nat.choose (n + 1 - m) r) = ∑ r ∈ Finset.Icc 1 n, f r by rfl,
    hrestrict]
  calc
    (∑ r ∈ Finset.Icc 1 m, f r) =
        ∑ j ∈ Finset.range m,
          Nat.choose (m - 1) j * Nat.choose (n + 1 - m) (j + 1) := by
      have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
        ext r
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        lia
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      simp [Nat.add_comm 1 j]
    _ = ∑ r ∈ Finset.range (m + 1),
          Nat.choose (n + 1 - m) r *
            Nat.choose (m - 1) (m - r) := by
      rw [Finset.sum_range_succ']
      have hzero : Nat.choose (m - 1) m = 0 :=
        Nat.choose_eq_zero_of_lt (by lia)
      simp only [Nat.sub_zero, Nat.choose_zero_right, hzero, mul_zero,
        add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      have hcomp : m - (j + 1) = m - 1 - j := by lia
      rw [hcomp, Nat.choose_symm (by lia : j ≤ m - 1)]
      ring
    _ = Nat.choose ((n + 1 - m) + (m - 1)) m := by
      rw [Nat.add_choose_eq,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = Nat.choose n m := by
      have htop : n + 1 - m + (m - 1) = n := by lia
      rw [htop]

private theorem coeff_comp_binaryRunPolynomial_pos
    (n m k : ℕ) (hm0 : 0 < m) (hm : m ≤ n) (hk : k ≤ m)
    (hkA : k ≤ n + 1 - m) (hk0 : 0 < k) :
    ((binaryRunPolynomial n m).comp (X + 1)).coeff k =
      ((Nat.choose (n + 1 - m) k : ℝ) *
        (Nat.choose (n - k) (m - k) : ℝ)) /
        (Nat.choose n m : ℝ) := by
  rw [coeff_comp_binaryRunPolynomial n m k hm0]
  calc
    (∑ r ∈ Finset.Icc 1 n,
        (((Nat.choose (m - 1) (r - 1) : ℝ) *
            (Nat.choose (n + 1 - m) r : ℝ)) /
          (Nat.choose n m : ℝ)) * (Nat.choose r k : ℝ)) =
        (∑ r ∈ Finset.Icc 1 n,
          ((Nat.choose r k * Nat.choose (m - 1) (r - 1) *
            Nat.choose (n + 1 - m) r : ℕ) : ℝ)) /
          (Nat.choose n m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      ring
    _ = ((Nat.choose (n + 1 - m) k : ℝ) *
          (Nat.choose (n - k) (m - k) : ℝ)) /
          (Nat.choose n m : ℝ) := by
      congr 1
      exact_mod_cast binaryRun_weighted_sum_pos n m k hm0 hm hk hkA hk0

private theorem coeff_zero_comp_binaryRunPolynomial
    (n m : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
    ((binaryRunPolynomial n m).comp (X + 1)).coeff 0 = 1 := by
  rw [coeff_comp_binaryRunPolynomial n m 0 hm0]
  calc
    (∑ r ∈ Finset.Icc 1 n,
        (((Nat.choose (m - 1) (r - 1) : ℝ) *
            (Nat.choose (n + 1 - m) r : ℝ)) /
          (Nat.choose n m : ℝ)) * (Nat.choose r 0 : ℝ)) =
        (∑ r ∈ Finset.Icc 1 n,
          ((Nat.choose r 0 * Nat.choose (m - 1) (r - 1) *
            Nat.choose (n + 1 - m) r : ℕ) : ℝ)) /
          (Nat.choose n m : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      ring
    _ = (Nat.choose n m : ℝ) / (Nat.choose n m : ℝ) := by
      congr 1
      exact_mod_cast binaryRun_weighted_sum_zero n m hm0 hm
    _ = 1 := div_self (Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne')

/-- Shifted binary-run coefficient identity:
`[Y^k] J_{n,m}(1+Y) = choose(m,k) choose(n+1-m,k) / choose(n,k)`. -/
theorem coeff_comp_binaryRunPolynomial_all
    (n m k : ℕ) (hm0 : 0 < m) (hm : m ≤ n) :
    ((binaryRunPolynomial n m).comp (X + 1)).coeff k =
      ((Nat.choose m k : ℝ) * (Nat.choose (n + 1 - m) k : ℝ)) /
        (Nat.choose n k : ℝ) := by
  by_cases hk0 : k = 0
  · subst k
    rw [coeff_zero_comp_binaryRunPolynomial n m hm0 hm]
    simp
  have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
  by_cases hk : k ≤ m
  · by_cases hkA : k ≤ n + 1 - m
    · rw [coeff_comp_binaryRunPolynomial_pos n m k hm0 hm hk hkA hk0']
      have hkn : k ≤ n := hk.trans hm
      have hnm : (Nat.choose n m : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne'
      have hnk : (Nat.choose n k : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'
      have hmul := Nat.choose_mul (n := n) (k := m) (s := k) hk
      have hmulR : (Nat.choose n m : ℝ) * (Nat.choose m k : ℝ) =
          (Nat.choose n k : ℝ) *
            (Nat.choose (n - k) (m - k) : ℝ) := by
        exact_mod_cast hmul
      field_simp
      calc
        (Nat.choose (n + 1 - m) k : ℝ) *
              (Nat.choose (n - k) (m - k) : ℝ) *
              (Nat.choose n k : ℝ) =
            (Nat.choose (n + 1 - m) k : ℝ) *
              ((Nat.choose n k : ℝ) *
                (Nat.choose (n - k) (m - k) : ℝ)) := by ring
        _ = (Nat.choose (n + 1 - m) k : ℝ) *
              ((Nat.choose n m : ℝ) * (Nat.choose m k : ℝ)) := by
            rw [← hmulR]
        _ = (Nat.choose (n + 1 - m) k : ℝ) *
              (Nat.choose n m : ℝ) * (Nat.choose m k : ℝ) := by ring
    · have hkAlt : n + 1 - m < k := Nat.lt_of_not_ge hkA
      rw [coeff_comp_binaryRunPolynomial n m k hm0,
        Nat.choose_eq_zero_of_lt hkAlt]
      simp only [Nat.cast_zero, mul_zero, zero_div]
      apply Finset.sum_eq_zero
      intro r hr
      by_cases hrk : r < k
      · rw [Nat.choose_eq_zero_of_lt hrk]
        simp
      · have hAr : n + 1 - m < r :=
          lt_of_lt_of_le hkAlt (Nat.le_of_not_gt hrk)
        rw [Nat.choose_eq_zero_of_lt hAr]
        simp
  · have hmkt : m < k := Nat.lt_of_not_ge hk
    rw [coeff_comp_binaryRunPolynomial n m k hm0,
      Nat.choose_eq_zero_of_lt hmkt]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hrk : r < k
    · rw [Nat.choose_eq_zero_of_lt hrk]
      simp
    · have hmr : m < r := lt_of_lt_of_le hmkt (Nat.le_of_not_gt hrk)
      have hidx : m - 1 < r - 1 := by lia
      rw [Nat.choose_eq_zero_of_lt hidx]
      simp

/-- Coefficients of a shifted binary-run transform, expressed directly in
the input coefficients. -/
theorem coeff_comp_binaryRunTransform {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) (k : ℕ) :
    ((binaryRunTransform n p).comp (X + 1)).coeff k =
      p.sum fun m a =>
        a * (((Nat.choose m k : ℝ) *
          (Nat.choose (n + 1 - m) k : ℝ)) /
            (Nat.choose n k : ℝ)) := by
  rw [binaryRunTransform, Polynomial.basisTransform,
    Polynomial.sum_def]
  change ((Polynomial.compRingHom (X + 1))
      (∑ m ∈ p.support, C (p.coeff m) * binaryRunPolynomial n m)).coeff k =
    ∑ m ∈ p.support,
      p.coeff m * (((Nat.choose m k : ℝ) *
        (Nat.choose (n + 1 - m) k : ℝ)) /
          (Nat.choose n k : ℝ))
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  change ((C (p.coeff m) * binaryRunPolynomial n m).comp
      (X + 1)).coeff k = _
  rw [mul_comp, C_comp, coeff_C_mul]
  have hmle : m ≤ n :=
    (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hm)).trans hp
  by_cases hm0 : m = 0
  · subst m
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      rw [binaryRunPolynomial_zero]
      simp [Polynomial.coeff_one, hk0,
        Nat.choose_eq_zero_of_lt hkpos]
  · rw [coeff_comp_binaryRunPolynomial_all n m k
      (Nat.pos_of_ne_zero hm0) hmle]

/-- Range-sum form of `coeff_comp_binaryRunTransform`, convenient for
comparing an input with its Euler pointing. -/
theorem coeff_comp_binaryRunTransform_eq_sum_range {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) (k : ℕ) :
    ((binaryRunTransform n p).comp (X + 1)).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        p.coeff m * (((Nat.choose m k : ℝ) *
          (Nat.choose (n + 1 - m) k : ℝ)) /
            (Nat.choose n k : ℝ)) := by
  rw [coeff_comp_binaryRunTransform hp, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le <|
      (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hm)).trans hp
  · intro m hmrange hmsupport
    rw [Polynomial.notMem_support_iff.mp hmsupport, zero_mul]

/-- The shifted binary-run transform has degree at most `⌊(n+1)/2⌋` on the
degree-`n` input box. -/
theorem natDegree_comp_binaryRunTransform_le {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    ((binaryRunTransform n p).comp (X + 1)).natDegree ≤ (n + 1) / 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_comp_binaryRunTransform hp]
  rw [Polynomial.sum_def]
  apply Finset.sum_eq_zero
  intro m hm
  have hmle : m ≤ n := (Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hm)).trans hp
  have htwok : n + 1 < 2 * k := by lia
  by_cases hmk : k ≤ m
  · have hother : n + 1 - m < k := by lia
    rw [Nat.choose_eq_zero_of_lt hother]
    simp
  · have hmk' : m < k := Nat.lt_of_not_ge hmk
    rw [Nat.choose_eq_zero_of_lt hmk']
    simp

/-- The unshifted binary-run transform has the same global degree bound. -/
theorem natDegree_binaryRunTransform_le {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ n) :
    (binaryRunTransform n p).natDegree ≤ (n + 1) / 2 := by
  let q := binaryRunTransform n p
  have hrecover : q = (q.comp (X + 1)).comp (X - 1) := by
    simp [Polynomial.comp_assoc, q]
  change q.natDegree ≤ (n + 1) / 2
  rw [hrecover]
  calc
    ((q.comp (X + 1)).comp (X - 1)).natDegree ≤
        (q.comp (X + 1)).natDegree * (X - 1 : ℝ[X]).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ ((n + 1) / 2) * 1 := by
      gcongr
      · exact natDegree_comp_binaryRunTransform_le hp
      · simpa only [C_1] using (natDegree_X_sub_C (R := ℝ) 1).le
    _ = (n + 1) / 2 := by simp

/-- Reflection symmetry of the nonconstant binary-run basis images. -/
theorem binaryRunPolynomial_reflection (n m : ℕ)
    (hm0 : 0 < m) (hm : m ≤ n) :
    binaryRunPolynomial n (n + 1 - m) = binaryRunPolynomial n m := by
  have hreflect0 : 0 < n + 1 - m := by lia
  have hreflect_le : n + 1 - m ≤ n := by lia
  have hshift :
      (binaryRunPolynomial n (n + 1 - m)).comp (X + 1) =
        (binaryRunPolynomial n m).comp (X + 1) := by
    ext k
    rw [coeff_comp_binaryRunPolynomial_all n (n + 1 - m) k
        hreflect0 hreflect_le,
      coeff_comp_binaryRunPolynomial_all n m k hm0 hm]
    have hsub : n + 1 - (n + 1 - m) = m := by lia
    rw [hsub]
    ring
  have hinverse := congrArg (fun p : ℝ[X] => p.comp (X - 1)) hshift
  simpa [Polynomial.comp_assoc] using hinverse

end RealRooted
