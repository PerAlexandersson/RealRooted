import RealRooted.SymmetricDecomposition
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Gamma transforms and real-rootedness

This file packages the univariate gamma transform used for symmetric
decompositions and proves real-rootedness criteria for the transformed
polynomials.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

section

/-- The basis term `x^i (1+x)^(d-2i)` in the gamma expansion of a symmetric
degree-`d` polynomial. -/
def gammaBasisTerm (d i : ℕ) : ℝ[X] :=
  X ^ i * (X + 1) ^ (d - 2 * i)

/-- The ambient-degree `d` gamma transform associated with a coefficient
polynomial `γ`. Terms above `⌊d / 2⌋` are ignored. -/
def gammaTransform (d : ℕ) (γ : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (d / 2 + 1), C (γ.coeff i) * gammaBasisTerm d i

/-- Predicate saying that `γ` is the gamma-polynomial of `p` in ambient degree
`d`. -/
def IsGammaExpansion (d : ℕ) (p γ : ℝ[X]) : Prop :=
  p = gammaTransform d γ

/-- Current library-language wrapper for “all roots are negative/nonpositive”. -/
def HasRootsNonpos (p : ℝ[X]) : Prop :=
  ∀ r ∈ p.roots, r ≤ 0

@[simp] lemma gammaBasisTerm_zero (d : ℕ) :
    gammaBasisTerm d 0 = (X + 1) ^ d := by
  simp [gammaBasisTerm]

@[simp] lemma gammaTransform_zero (d : ℕ) :
    gammaTransform d (0 : ℝ[X]) = 0 := by
  simp [gammaTransform]

@[simp] lemma gammaTransform_add (d : ℕ) (γ δ : ℝ[X]) :
    gammaTransform d (γ + δ) = gammaTransform d γ + gammaTransform d δ := by
  unfold gammaTransform
  calc
    ∑ i ∈ Finset.range (d / 2 + 1), C ((γ + δ).coeff i) * gammaBasisTerm d i
      = ∑ i ∈ Finset.range (d / 2 + 1),
          (C (γ.coeff i) * gammaBasisTerm d i + C (δ.coeff i) * gammaBasisTerm d i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [coeff_add, C_add, add_mul]
    _ = gammaTransform d γ + gammaTransform d δ := by simp [gammaTransform, Finset.sum_add_distrib]

@[simp] lemma gammaTransform_C_mul (d : ℕ) (a : ℝ) (γ : ℝ[X]) :
    gammaTransform d (C a * γ) = C a * gammaTransform d γ := by
  unfold gammaTransform
  rw [mul_sum]
  grind

lemma gammaTransform_monomial (d n : ℕ) (a : ℝ) :
    gammaTransform d (monomial n a) =
      if n ≤ d / 2 then C a * gammaBasisTerm d n else 0 := by
  by_cases h : n ≤ d / 2
  · have hn : n ∈ Finset.range (d / 2 + 1) := by simp_all
    unfold gammaTransform
    rw [Finset.sum_eq_single n]
    · simp_all
    · intro k hk hkn
      have hcoeff : (monomial n a).coeff k = 0 := by simp [coeff_monomial, mt Eq.symm hkn]
      simp_all
    · lia
  · unfold gammaTransform
    have hsum :
        ∑ k ∈ Finset.range (d / 2 + 1),
          C ((monomial n a).coeff k) * gammaBasisTerm d k = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hklt : k < d / 2 + 1 := Finset.mem_range.mp hk
      have hkn : k ≠ n := by lia
      have hcoeff : (monomial n a).coeff k = 0 := by simp [coeff_monomial, mt Eq.symm hkn]
      simp_all
    lia

@[simp] lemma IdTransform_X_add_one :
    IdTransform 1 (X + 1 : ℝ[X]) = X + 1 := by
  simp [IdTransform, add_comm]

lemma IdTransform_raise {m k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ m) :
    IdTransform (m + k) p = X ^ k * IdTransform m p := by
  induction k with
  | zero =>
      lia
  | succ k ih =>
      have hp' : p.natDegree ≤ m + k := le_trans hp (Nat.le_add_right _ _)
      calc
        IdTransform (m + (k + 1)) p = X * IdTransform (m + k) p := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (IdTransform_succ (d := m + k) (p := p) hp')
        _ = X * (X ^ k * IdTransform m p) := by lia
        _ = (X * X ^ k) * IdTransform m p := by grind
        _ = X ^ (k + 1) * IdTransform m p := by grind

lemma IdTransform_X_pow_mul {m k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ m) :
    IdTransform (k + m) (X ^ k * p) = IdTransform m p := by
  induction k with
  | zero =>
      lia
  | succ k ih =>
      have hkdeg : (X ^ k * p).natDegree ≤ k + m := by
        calc
          (X ^ k * p).natDegree ≤ (X ^ k).natDegree + p.natDegree := Polynomial.natDegree_mul_le
          _ ≤ k + m := by simp_all
      calc
        IdTransform (k.succ + m) (X ^ k.succ * p) = IdTransform (k + m) (X ^ k * p) := by
          simpa [pow_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc] using
            (IdTransform_X_mul_succ (d := k + m) (p := X ^ k * p) hkdeg)
        _ = IdTransform m p := ih

lemma IdTransform_X_add_one_pow (n : ℕ) :
    IdTransform n ((X + 1 : ℝ[X]) ^ n) = (X + 1) ^ n := by
  ext k
  by_cases hk : k ≤ n
  · rw [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_le hk]
    simp [Polynomial.coeff_X_add_one_pow, Nat.choose_symm hk]
  · have hkn : n < k := lt_of_not_ge hk
    rw [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hkn]

lemma IdTransform_gammaBasisTerm (d i : ℕ) (hi : 2 * i ≤ d) :
    IdTransform d (gammaBasisTerm d i) = gammaBasisTerm d i := by
  let n := d - 2 * i
  have hd_eq : d = i + (d - i) := by lia
  have hterm :
      gammaBasisTerm d i = X ^ i * ((X + 1 : ℝ[X]) ^ n) := by
    simp [gammaBasisTerm, n]
  have hqdeg0 : ((X + 1 : ℝ[X]) ^ n).natDegree ≤ n := natDegree_X_add_one_pow_le n
  have hqdeg : ((X + 1 : ℝ[X]) ^ n).natDegree ≤ d - i := by lia
  calc
    IdTransform d (gammaBasisTerm d i)
        = IdTransform (i + (d - i)) (gammaBasisTerm d i) := by lia
    _ = IdTransform (i + (d - i)) (X ^ i * ((X + 1 : ℝ[X]) ^ n)) := by lia
    _ = IdTransform (d - i) ((X + 1 : ℝ[X]) ^ n) :=
          IdTransform_X_pow_mul (m := d - i) (k := i) hqdeg
    _ = X ^ i * IdTransform n ((X + 1 : ℝ[X]) ^ n) := by
          rw [show d - i = n + i by
            lia]
          exact IdTransform_raise (m := n) (k := i) hqdeg0
    _ = X ^ i * ((X + 1 : ℝ[X]) ^ n) := by rw [IdTransform_X_add_one_pow]
    _ = gammaBasisTerm d i := by lia

lemma IdTransform_finsetSum {ι : Type} (d : ℕ) (s : Finset ι)
    (f : ι → ℝ[X]) :
    IdTransform d (∑ i ∈ s, f i) = ∑ i ∈ s, IdTransform d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      simp [Finset.sum_insert, hi, IdTransform_add, ih]

lemma gammaTransform_fixed (d : ℕ) (γ : ℝ[X]) :
    IdTransform d (gammaTransform d γ) = gammaTransform d γ := by
  classical
  unfold gammaTransform
  rw [IdTransform_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h2i : 2 * i ≤ d := by lia
  rw [IdTransform, Polynomial.reflect_C_mul]
  simpa [IdTransform] using
    congrArg (fun p => C (γ.coeff i) * p) (IdTransform_gammaBasisTerm d i h2i)

lemma hasNonnegCoeffs_gammaBasisTerm (d i : ℕ) :
    HasNonnegCoeffs (gammaBasisTerm d i) := by
  unfold gammaBasisTerm
  exact (hasNonnegCoeffs_X.pow i).mul (hasNonnegCoeffs_X_add_one.pow (d - 2 * i))

lemma hasNonnegCoeffs_gammaTransform {d : ℕ} {γ : ℝ[X]} (hγ : HasNonnegCoeffs γ) :
    HasNonnegCoeffs (gammaTransform d γ) := by
  unfold gammaTransform
  refine Finset.induction_on (s := Finset.range (d / 2 + 1)) ?base ?step
  · simpa using hasNonnegCoeffs_zero
  · intro i s hi ih
    rw [Finset.sum_insert hi]
    have hterm : HasNonnegCoeffs (C (γ.coeff i) * gammaBasisTerm d i) := by
      simpa [mul_assoc] using nonnegCoeffs_C_mul (hγ i) (hasNonnegCoeffs_gammaBasisTerm d i)
    exact hterm.add ih

lemma isRealRooted_X_add_one_pow : ∀ n : ℕ, ((((X + 1 : ℝ[X]) ^ n)) ≠ 0 ∧
  (((X + 1 : ℝ[X]) ^ n)).Splits)
  | 0 => by simp
  | n + 1 => by
      simpa [pow_succ, mul_comm] using
        isRealRooted_mul (isRealRooted_X_sub_C (-1 : ℝ)).1 (isRealRooted_X_sub_C (-1 : ℝ)).2
          (isRealRooted_X_add_one_pow n).1 (isRealRooted_X_add_one_pow n).2

lemma gammaBasisTerm_succ_succ (d i : ℕ) :
    gammaBasisTerm (d + 2) (i + 1) = X * gammaBasisTerm d i := by
  unfold gammaBasisTerm
  grind

lemma gammaTransform_X_mul_two (d : ℕ) (γ : ℝ[X]) :
    gammaTransform (d + 2) (X * γ) = X * gammaTransform d γ := by
  refine Polynomial.induction_on' γ ?_ ?_
  · intro p q hp hq
    rw [show X * (p + q) = X * p + X * q by grind]
    rw [gammaTransform_add, gammaTransform_add, hp, hq]
    ring
  · intro n a
    by_cases h : n ≤ d / 2
    · have hs : n + 1 ≤ (d + 2) / 2 := by lia
      simp [Polynomial.X_mul_monomial, gammaTransform_monomial, h,
        gammaBasisTerm_succ_succ, mul_assoc, mul_comm]
    · have hs : ¬ n + 1 ≤ (d + 2) / 2 := by lia
      simp [Polynomial.X_mul_monomial, gammaTransform_monomial, h]

lemma gammaTransform_pad_two {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 2) γ = (X + 1) ^ 2 * gammaTransform d γ := by
  unfold gammaTransform
  have hhalf : (d + 2) / 2 + 1 = d / 2 + 2 := by lia
  rw [hhalf, Finset.sum_range_succ]
  have htop : γ.coeff (d / 2 + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hγ (Nat.lt_succ_self _))
  rw [htop]
  simp only [map_zero, zero_mul, add_zero]
  calc
    ∑ i ∈ Finset.range (d / 2 + 1), C (γ.coeff i) * gammaBasisTerm (d + 2) i
      = ∑ i ∈ Finset.range (d / 2 + 1),
          (X + 1) ^ 2 * (C (γ.coeff i) * gammaBasisTerm d i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : d + 2 - 2 * i = (d - 2 * i) + 2 := by lia
          rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_add]
          ring
    _ = (X + 1) ^ 2 * ∑ i ∈ Finset.range (d / 2 + 1), C (γ.coeff i) * gammaBasisTerm d i := by
          rw [Finset.mul_sum]
    _ = (X + 1) ^ 2 * gammaTransform d γ := by simp [gammaTransform]

lemma gammaTransform_odd (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * m + 1) γ = (X + 1) * gammaTransform (2 * m) γ := by
  have hhalf_odd : (2 * m + 1) / 2 = m := by lia
  have hhalf_even : (2 * m) / 2 = m := by lia
  calc
    gammaTransform (2 * m + 1) γ
      = ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i := by
          simp [gammaTransform, hhalf_odd]
    _ = ∑ i ∈ Finset.range (m + 1), (X + 1) * (C (γ.coeff i) * gammaBasisTerm (2 * m) i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : 2 * m + 1 - 2 * i = (2 * m - 2 * i) + 1 := by lia
          rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_succ]
          ring
    _ = (X + 1) * ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * m) i := by
          rw [Finset.mul_sum]
    _ = (X + 1) * gammaTransform (2 * m) γ := by simp [gammaTransform, hhalf_even]

/-- Repeated source-degree padding factors off two copies of `X + 1` at each
step. -/
lemma gammaTransform_add_two_mul (d k : ℕ) {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 2 * k) γ =
      (X + 1) ^ (2 * k) * gammaTransform d γ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkdeg : γ.natDegree ≤ (d + 2 * k) / 2 := by lia
      calc
        gammaTransform (d + 2 * (k + 1)) γ =
            gammaTransform ((d + 2 * k) + 2) γ := by congr 1
        _ = (X + 1) ^ 2 * gammaTransform (d + 2 * k) γ :=
          gammaTransform_pad_two hkdeg
        _ = (X + 1) ^ 2 *
            ((X + 1) ^ (2 * k) * gammaTransform d γ) := by rw [ih]
        _ = (X + 1) ^ (2 * (k + 1)) * gammaTransform d γ := by
          rw [show 2 * (k + 1) = 2 + 2 * k by lia, pow_add]
          ring

/-- Hoster--Stump, Proposition 2.5, equation (2.2), factorization input:
the excess ambient degree is exactly a power of `X + 1`. -/
theorem gammaTransform_eq_X_add_one_pow_mul_minimal
    {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform d γ =
      (X + 1) ^ (d - 2 * γ.natDegree) *
        gammaTransform (2 * γ.natDegree) γ := by
  let n := γ.natDegree
  let m := d / 2
  change gammaTransform d γ =
    (X + 1) ^ (d - 2 * n) * gammaTransform (2 * n) γ
  have hnm : n ≤ m := hγ
  have hbase : n ≤ (2 * n) / 2 := by simp
  have hiter := gammaTransform_add_two_mul (2 * n) (m - n) hbase
  rcases Nat.mod_two_eq_zero_or_one d with heven | hodd
  · have hd : d = 2 * m := by dsimp [m]; lia
    calc
      gammaTransform d γ =
          gammaTransform (2 * n + 2 * (m - n)) γ := by
            congr 1
            lia
      _ = (X + 1) ^ (2 * (m - n)) * gammaTransform (2 * n) γ := hiter
      _ = (X + 1) ^ (d - 2 * n) * gammaTransform (2 * n) γ := by
        rw [show 2 * (m - n) = d - 2 * n by lia]
  · have hd : d = 2 * m + 1 := by dsimp [m]; lia
    calc
      gammaTransform d γ = gammaTransform (2 * m + 1) γ := by congr 1
      _ = (X + 1) * gammaTransform (2 * m) γ := gammaTransform_odd m γ
      _ = (X + 1) *
          ((X + 1) ^ (2 * (m - n)) * gammaTransform (2 * n) γ) := by
            rw [show 2 * m = 2 * n + 2 * (m - n) by lia, hiter]
      _ = (X + 1) ^ (d - 2 * n) * gammaTransform (2 * n) γ := by
        rw [show d - 2 * n = 2 * (m - n) + 1 by lia, pow_succ']
        ring

lemma gammaTransform_even_succ (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * (m + 1)) γ =
      (X + 1) * gammaTransform (2 * m + 1) γ + C (γ.coeff (m + 1)) * X ^ (m + 1) := by
  have hhalf_even : (2 * (m + 1)) / 2 = m + 1 := by lia
  have hhalf_odd : (2 * m + 1) / 2 = m := by lia
  have hprefix :
      ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * (m + 1)) i
        = (X + 1) * gammaTransform (2 * m + 1) γ := by
    calc
      ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * (m + 1)) i
      = ∑ i ∈ Finset.range (m + 1),
          (X + 1) * (C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : 2 * (m + 1) - 2 * i = (2 * m + 1 - 2 * i) + 1 := by lia
          rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_succ]
          ring
    _ = (X + 1) * ∑ i ∈ Finset.range (m + 1),
        C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i := by rw [Finset.mul_sum]
    _ = (X + 1) * gammaTransform (2 * m + 1) γ := by simp [gammaTransform, hhalf_odd]
  calc
    gammaTransform (2 * (m + 1)) γ
      = (∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * (m + 1)) i) +
          C (γ.coeff (m + 1)) * gammaBasisTerm (2 * (m + 1)) (m + 1) := by
            simp [gammaTransform, hhalf_even, Finset.sum_range_succ]
    _ = (X + 1) * gammaTransform (2 * m + 1) γ + C (γ.coeff (m + 1)) * X ^ (m + 1) := by
          rw [hprefix]
          simp [gammaBasisTerm]

@[simp] lemma gammaTransform_odd_eval_neg_one (m : ℕ) (γ : ℝ[X]) :
    (gammaTransform (2 * m + 1) γ).eval (-1) = 0 := by
  rw [gammaTransform_odd]
  simp

lemma gammaTransform_even_eval_neg_one (m : ℕ) (γ : ℝ[X]) :
    (gammaTransform (2 * m) γ).eval (-1) = γ.coeff m * (-1) ^ m := by
  unfold gammaTransform
  have hhalf_even : (2 * m) / 2 = m := by lia
  rw [hhalf_even]
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single m]
  · simp [gammaBasisTerm]
  · intro i hi him
    have hi_lt : i < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) him
    have hpow_pos : 0 < 2 * m - 2 * i := by lia
    simp [gammaBasisTerm, hpow_pos.ne']
  · simp

/-- The minimal even gamma transform does not vanish at `-1`. -/
lemma gammaTransform_minimal_eval_neg_one_ne_zero {γ : ℝ[X]} (hγ : γ ≠ 0) :
    (gammaTransform (2 * γ.natDegree) γ).eval (-1) ≠ 0 := by
  rw [gammaTransform_even_eval_neg_one, Polynomial.coeff_natDegree]
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hγ)
    (pow_ne_zero _ (by norm_num))

/-- Equation (2.2) in Hoster--Stump, Proposition 2.5:
https://arxiv.org/abs/2508.15538. -/
theorem rootMultiplicity_neg_one_gammaTransform
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2) (hγ : γ ≠ 0) :
    (gammaTransform d γ).rootMultiplicity (-1) = d - 2 * γ.natDegree := by
  have hcore_eval := gammaTransform_minimal_eval_neg_one_ne_zero hγ
  have hcore_ne : gammaTransform (2 * γ.natDegree) γ ≠ 0 := by
    intro hzero
    simp [hzero] at hcore_eval
  have hcore_not_root :
      ¬(gammaTransform (2 * γ.natDegree) γ).IsRoot (-1) := by
    rw [Polynomial.IsRoot.def]
    exact hcore_eval
  have hlinear : (X + 1 : ℝ[X]) = X - C (-1) := by norm_num
  rw [gammaTransform_eq_X_add_one_pow_mul_minimal hγdeg, mul_comm, hlinear,
    rootMultiplicity_mul_X_sub_C_pow hcore_ne,
    rootMultiplicity_eq_zero hcore_not_root, zero_add]

lemma gammaTransform_even_isRoot_neg_one_iff (m : ℕ) (γ : ℝ[X]) :
    (gammaTransform (2 * m) γ).IsRoot (-1) ↔ γ.coeff m = 0 := by
  rw [Polynomial.IsRoot.def, gammaTransform_even_eval_neg_one]
  simp

lemma gammaTransform_even_succ_of_coeff_zero (m : ℕ) {γ : ℝ[X]}
    (hcoeff : γ.coeff (m + 1) = 0) :
    gammaTransform (2 * (m + 1)) γ = (X + 1) ^ 2 * gammaTransform (2 * m) γ := by
  rw [gammaTransform_even_succ, gammaTransform_odd]
  grind

lemma gammaTransform_even_succ_of_isRoot_neg_one (m : ℕ) {γ : ℝ[X]}
    (hroot : (gammaTransform (2 * (m + 1)) γ).IsRoot (-1)) :
    gammaTransform (2 * (m + 1)) γ = (X + 1) ^ 2 * gammaTransform (2 * m) γ :=
  gammaTransform_even_succ_of_coeff_zero m
    ((gammaTransform_even_isRoot_neg_one_iff (m + 1) γ).mp hroot)

lemma gammaTransform_even_injective :
    ∀ m : ℕ, ∀ {γ δ : ℝ[X]},
      γ.natDegree ≤ m →
      δ.natDegree ≤ m →
      gammaTransform (2 * m) γ = gammaTransform (2 * m) δ →
      γ = δ
  | 0, γ, δ, hγ, hδ, hEq => by
      have hγC : γ = C (γ.coeff 0) := by simpa using (Polynomial.eq_C_of_natDegree_le_zero hγ)
      have hδC : δ = C (δ.coeff 0) := by simpa using (Polynomial.eq_C_of_natDegree_le_zero hδ)
      have hcoeff : γ.coeff 0 = δ.coeff 0 := by
        have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hEq
        simpa [gammaTransform, gammaBasisTerm] using h0
      lia
  | m + 1, γ, δ, hγ, hδ, hEq => by
      have hcoeff_top : γ.coeff (m + 1) = δ.coeff (m + 1) := by
        have heval : (gammaTransform (2 * (m + 1)) γ).eval (-1) =
              (gammaTransform (2 * (m + 1)) δ).eval (-1) := by
          lia
        have hγeval : (gammaTransform (2 * (m + 1)) γ).eval (-1) =
              γ.coeff (m + 1) * (-1) ^ (m + 1) := by
          simpa using gammaTransform_even_eval_neg_one (m + 1) γ
        have hδeval : (gammaTransform (2 * (m + 1)) δ).eval (-1) =
              δ.coeff (m + 1) * (-1) ^ (m + 1) := by
          simpa using gammaTransform_even_eval_neg_one (m + 1) δ
        simp_all
      let c : ℝ := γ.coeff (m + 1)
      let γ' : ℝ[X] := γ - Polynomial.monomial (m + 1) c
      let δ' : ℝ[X] := δ - Polynomial.monomial (m + 1) c
      have hγ'_deg : γ'.natDegree ≤ m := by
        refine natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro k hk
        dsimp [γ', c]
        by_cases hk_top : k = m + 1
        · simp_all
        · have hk_gt : m + 1 < k := by lia
          have hγk : γ.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hγ hk_gt)
          have hk_ne' : m + 1 ≠ k := by lia
          rw [coeff_sub, hγk, Polynomial.coeff_monomial]
          simp [hk_ne']
      have hδ'_deg : δ'.natDegree ≤ m := by
        refine natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro k hk
        dsimp [δ', c]
        by_cases hk_top : k = m + 1
        · simp_all
        · have hk_gt : m + 1 < k := by lia
          have hδk : δ.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hδ hk_gt)
          have hk_ne' : m + 1 ≠ k := by lia
          rw [coeff_sub, hδk, Polynomial.coeff_monomial]
          simp [hk_ne']
      have hγsmall :
          gammaTransform (2 * m) γ' = gammaTransform (2 * m) γ := by
        dsimp [γ', c]
        rw [sub_eq_add_neg, gammaTransform_add]
        rw [show -(Polynomial.monomial (m + 1) (γ.coeff (m + 1))) =
              C (-1) * Polynomial.monomial (m + 1) (γ.coeff (m + 1)) by simp]
        rw [gammaTransform_C_mul]
        simp [gammaTransform_monomial]
      have hδsmall :
          gammaTransform (2 * m) δ' = gammaTransform (2 * m) δ := by
        dsimp [δ', c]
        rw [sub_eq_add_neg, gammaTransform_add]
        rw [show -(Polynomial.monomial (m + 1) (γ.coeff (m + 1))) =
              C (-1) * Polynomial.monomial (m + 1) (γ.coeff (m + 1)) by simp]
        rw [gammaTransform_C_mul]
        simp [gammaTransform_monomial]
      have hodd :
          gammaTransform (2 * m + 1) γ = gammaTransform (2 * m + 1) δ := by
        have hX1 : (X + 1 : ℝ[X]) ≠ 0 := by
          simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ))
        have hEq' :
            (X + 1) * gammaTransform (2 * m + 1) γ +
                C c * X ^ (m + 1) =
              (X + 1) * gammaTransform (2 * m + 1) δ +
                C c * X ^ (m + 1) := by
          simpa [gammaTransform_even_succ, hcoeff_top, c] using hEq
        simp_all
      have hX1 : (X + 1 : ℝ[X]) ≠ 0 := by
        simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ))
      have hsmall :
          gammaTransform (2 * m) γ' = gammaTransform (2 * m) δ' := by
        calc
          gammaTransform (2 * m) γ'
              = gammaTransform (2 * m) γ := hγsmall
          _ = gammaTransform (2 * m) δ := by
                apply mul_left_cancel₀ hX1
                simpa [gammaTransform_odd] using hodd
          _ = gammaTransform (2 * m) δ' := hδsmall.symm
      have htrunc : γ' = δ' :=
        gammaTransform_even_injective m hγ'_deg hδ'_deg hsmall
      grind

lemma gammaTransform_odd_injective (m : ℕ) {γ δ : ℝ[X]}
    (hγ : γ.natDegree ≤ m) (hδ : δ.natDegree ≤ m)
    (hEq : gammaTransform (2 * m + 1) γ = gammaTransform (2 * m + 1) δ) :
    γ = δ := by
  have hX1 : (X + 1 : ℝ[X]) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ))
  apply gammaTransform_even_injective m hγ hδ
  apply mul_left_cancel₀ hX1
  simpa [gammaTransform_odd] using hEq

theorem gammaTransform_injective_of_natDegree_le {d : ℕ} {γ δ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) (hδ : δ.natDegree ≤ d / 2)
    (hEq : gammaTransform d γ = gammaTransform d δ) :
    γ = δ := by
  rcases Nat.mod_two_eq_zero_or_one d with hd_even | hd_odd
  · have hd : d = 2 * (d / 2) := by lia
    have hEq' : gammaTransform (2 * (d / 2)) γ = gammaTransform (2 * (d / 2)) δ := by lia
    exact gammaTransform_even_injective (d / 2)
      hγ hδ hEq'
  · have hd : d = 2 * (d / 2) + 1 := by lia
    have hEq' : gammaTransform (2 * (d / 2) + 1) γ = gammaTransform (2 * (d / 2) + 1) δ := by lia
    exact gammaTransform_odd_injective (d / 2)
      hγ hδ hEq'

theorem gammaTransform_eq_zero_iff_of_natDegree_le {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform d γ = 0 ↔ γ = 0 := by
  constructor
  · intro hzero
    exact gammaTransform_injective_of_natDegree_le hγ (by simp) (by simp_all)
  · simp_all

lemma natDegree_gammaBasisTerm_le (d i : ℕ) (hi : i ≤ d / 2) :
    (gammaBasisTerm d i).natDegree ≤ d := by
  unfold gammaBasisTerm
  have hX : (X ^ i : ℝ[X]).natDegree = i := by simp
  have hX1 : (((X + 1 : ℝ[X]) ^ (d - 2 * i))).natDegree ≤ d - 2 * i :=
    natDegree_X_add_one_pow_le (d - 2 * i)
  calc
    (X ^ i * ((X + 1 : ℝ[X]) ^ (d - 2 * i))).natDegree
        ≤ (X ^ i).natDegree + ((X + 1 : ℝ[X]) ^ (d - 2 * i)).natDegree :=
          Polynomial.natDegree_mul_le
    _ = i + ((X + 1 : ℝ[X]) ^ (d - 2 * i)).natDegree := by lia
    _ ≤ i + (d - 2 * i) := Nat.add_le_add_left hX1 i
    _ ≤ d := by lia

lemma natDegree_gammaTransform_le (d : ℕ) (γ : ℝ[X]) : (gammaTransform d γ).natDegree ≤ d := by
  classical
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  unfold gammaTransform
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hcoeff : γ.coeff i = 0
  · simp [hcoeff]
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt ?_ hn
    rw [Polynomial.natDegree_C_mul hcoeff]
    exact natDegree_gammaBasisTerm_le d i hi_le

@[simp] lemma gammaTransform_eval_zero (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).eval 0 = γ.coeff 0 := by
  unfold gammaTransform
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    simp [gammaBasisTerm, hi0]
  · simp

@[simp] lemma coeff_zero_gammaTransform (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).coeff 0 = γ.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, gammaTransform_eval_zero,
    Polynomial.coeff_zero_eq_eval_zero]

@[simp] lemma coeff_ambient_gammaTransform (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).coeff d = γ.coeff 0 := by
  have hfix := gammaTransform_fixed d γ
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff d) hfix
  simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using hcoeff.symm

/-- The root map `ρ ↦ ρ / (1 + ρ)²` in Hoster--Stump, Proposition 2.5,
equation (2.1). Reciprocal roots of a palindromic polynomial have the same
image under this map. -/
def gammaRootMap (x : ℝ) : ℝ := x / (1 + x) ^ 2

/-- The surjectivity part of Hoster--Stump equation (2.1) on the preferred
reciprocal branch. For `y < 0`, the polynomial `x - y * (1 + x)^2` has
opposite signs at `-1` and `0`, so the intermediate value theorem supplies the
required representative in `(-1, 0)`. -/
theorem exists_mem_Ioo_gammaRootMap_eq {y : ℝ} (hy : y < 0) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 0, gammaRootMap x = y := by
  let q : ℝ[X] := X - C y * (X + 1) ^ 2
  have hzero : (0 : ℝ) ∈ Set.Icc (q.eval (-1)) (q.eval 0) := by simpa [q] using le_of_lt hy
  obtain ⟨x, hx, hxzero⟩ :=
    intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 0)
      q.continuous.continuousOn hzero
  have hx_ne_left : x ≠ -1 := by
    intro h
    subst x
    dsimp [q] at hxzero
    norm_num at hxzero
  have hx_ne_right : x ≠ 0 := by
    intro h
    subst x
    dsimp [q] at hxzero
    simp at hxzero
    linarith
  have hxmem : x ∈ Set.Ioo (-1 : ℝ) 0 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx_ne_left),
      lt_of_le_of_ne hx.2 hx_ne_right⟩
  refine ⟨x, hxmem, ?_⟩
  have hone : 1 + x ≠ 0 := by linarith [hxmem.1]
  dsimp [q] at hxzero
  simp only [eval_sub, eval_X, eval_mul, eval_C, eval_pow, eval_add, eval_one] at hxzero
  unfold gammaRootMap
  field_simp [hone]
  nlinarith

/-- The gamma root map identifies a nonzero real number with its reciprocal. -/
lemma gammaRootMap_inv {x : ℝ} (hx : x ≠ 0) :
    gammaRootMap x⁻¹ = gammaRootMap x := by
  by_cases h1x : 1 + x = 0
  · have hxneg : x = -1 := by linarith
    simp [gammaRootMap, hxneg]
  · unfold gammaRootMap
    have hone : 1 + x⁻¹ = (1 + x) / x := by
      field_simp [hx]
      ring
    rw [hone, div_pow]
    field_simp [hx, h1x]

/-- Hoster--Stump, Proposition 2.5: the gamma root map is strictly increasing
on the interval `(-1, 0)`. -/
theorem strictMonoOn_gammaRootMap :
    StrictMonoOn gammaRootMap (Set.Ioo (-1) 0) := by
  intro a ha b hb hab
  have ha1 : 0 < 1 + a := by linarith [ha.1]
  have hb1 : 0 < 1 + b := by linarith [hb.1]
  have hab_pos : 0 < b - a := sub_pos.mpr hab
  have hone : 0 < 1 - a * b := by
    have hproduct : 0 < (1 + a) * (1 - b) :=
      mul_pos ha1 (by linarith [hb.2])
    nlinarith
  have hfactor := mul_pos hab_pos hone
  simp only [gammaRootMap]
  rw [div_lt_div_iff₀ (sq_pos_of_pos ha1) (sq_pos_of_pos hb1)]
  nlinarith

/-- The monotone root-map step in Hoster--Stump, Proposition 2.5:
mapping roots in `(-1, 0)` by equation (2.1) preserves and reflects their
weak interleaving order. See https://arxiv.org/abs/2508.15538. -/
theorem interleaves_map_gammaRootMap_iff :
    ∀ {ss rs : List ℝ}
      (_ : ∀ x ∈ ss, x ∈ Set.Ioo (-1) 0)
      (_ : ∀ x ∈ rs, x ∈ Set.Ioo (-1) 0),
      List.Interleaves (fun x y : ℝ => x ≤ y)
          (ss.map gammaRootMap) (rs.map gammaRootMap) ↔
        List.Interleaves (fun x y : ℝ => x ≤ y) ss rs
  | [], rs, _, _ => by
      cases rs <;> simp
  | _ :: _, [], _, _ => by simp
  | s :: ss, r :: rs, hss, hrs => by
      rw [List.map_cons, List.map_cons, List.interleaves_cons_cons,
        List.interleaves_cons_cons,
        strictMonoOn_gammaRootMap.le_iff_le
          (hrs r (by simp)) (hss s (by simp))]
      apply and_congr_right
      intro _
      simpa only [List.map_cons] using
        interleaves_map_gammaRootMap_iff
          (ss := rs) (rs := s :: ss)
          (fun x hx => hrs x (List.mem_cons_of_mem r hx)) hss
termination_by ss rs => ss.length + rs.length

/-- The quadratic reciprocal-pair factor in Hoster--Stump, Proposition 2.5,
equation (2.1). See https://arxiv.org/abs/2508.15538. -/
lemma gammaQuadraticFactor_eq_mul_reciprocal {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ≠ -1) :
    X - C (gammaRootMap x) * (X + 1) ^ 2 =
      C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹) := by
  have h1x : 1 + x ≠ 0 := by
    intro h
    apply hx1
    linarith
  apply Polynomial.funext
  intro y
  simp only [eval_sub, eval_X, eval_mul, eval_C, eval_pow, eval_add, eval_one]
  unfold gammaRootMap
  field_simp [hx0, h1x]
  ring

lemma eval_gammaTransform_eq_mul_eval_gammaUntransform {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) {x : ℝ} (hx : x ≠ -1) :
    (gammaTransform d γ).eval x = (1 + x) ^ d * γ.eval (x / (1 + x) ^ 2) := by
  have h1x_ne : 1 + x ≠ 0 := by grind
  unfold gammaTransform
  rw [Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hγdeg)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h2k_le : 2 * k ≤ d := by lia
  calc
    (C (γ.coeff k) * gammaBasisTerm d k).eval x
        = γ.coeff k * x ^ k * (x + 1) ^ (d - 2 * k) := by simp [gammaBasisTerm, mul_assoc]
    _ = γ.coeff k * x ^ k * (1 + x) ^ (d - 2 * k) := by grind
    _ = γ.coeff k * (x ^ k * (1 + x) ^ (d - 2 * k)) := by grind
    _ = γ.coeff k * ((1 + x) ^ d * (x / (1 + x) ^ 2) ^ k) := by
          have hterm :
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k = x ^ k * (1 + x) ^ (d - 2 * k) := by
            calc
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k
                  = (1 + x) ^ d * (x ^ k * (((1 + x) ^ 2) ^ k)⁻¹) := by
                      rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * (((1 + x) ^ 2) ^ k)⁻¹) := by grind
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ (2 * k))⁻¹) := by rw [pow_mul]
              _ = x ^ k * (1 + x) ^ (d - 2 * k) := by rw [← pow_sub₀ (1 + x) h1x_ne h2k_le]
          lia
    _ = (1 + x) ^ d * (γ.coeff k * (x / (1 + x) ^ 2) ^ k) := by ring

lemma gammaUntransform_nonpos {x : ℝ} (hx0 : x ≤ 0) (hx : x ≠ -1) :
    x / (1 + x) ^ 2 ≤ 0 := by
  have h1x_ne : 1 + x ≠ 0 := by grind
  have hsq_pos : 0 < (1 + x) ^ 2 := by positivity
  have hinv_nonneg : 0 ≤ ((1 + x) ^ 2)⁻¹ := inv_nonneg.mpr hsq_pos.le
  simpa [div_eq_mul_inv] using mul_nonpos_of_nonpos_of_nonneg hx0 hinv_nonneg

lemma hasRootsNonpos_of_dvd {p q : ℝ[X]}
    (hp_nonpos : HasRootsNonpos p) (hp0 : p ≠ 0)
    (hqp : q ∣ p) (hq0 : q ≠ 0) :
    HasRootsNonpos q := by
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq0).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact hp_nonpos r ((mem_roots hp0).mpr hrp)

lemma HasRootsNonpos.mul {p q : ℝ[X]}
    (hp : HasRootsNonpos p) (hq : HasRootsNonpos q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    HasRootsNonpos (p * q) := by
  intro r hr
  have hrpq : (p * q).IsRoot r := (mem_roots (mul_ne_zero hp0 hq0)).mp hr
  rw [Polynomial.IsRoot.def, eval_mul] at hrpq
  exact (mul_eq_zero.mp hrpq).elim
    (fun hpr => hp r ((mem_roots hp0).mpr hpr))
    (fun hqr => hq r ((mem_roots hq0).mpr hqr))

lemma hasRootsNonpos_X_sub_C {r : ℝ} (hr : r ≤ 0) :
    HasRootsNonpos (X - C r) := by
  intro s hs
  simp_all

lemma isRoot_gamma_of_isRoot_gammaTransform {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) {x : ℝ} (hx : x ≠ -1)
    (hroot : (gammaTransform d γ).IsRoot x) :
    γ.IsRoot (x / (1 + x) ^ 2) := by
  rw [Polynomial.IsRoot.def] at hroot ⊢
  rw [eval_gammaTransform_eq_mul_eval_gammaUntransform hγdeg hx] at hroot
  have h1x_ne : 1 + x ≠ 0 := by grind
  simp_all

lemma rootPullback_nonpos_of_gammaTransform {x : ℝ}
    (hx : x ≠ -1) (hx0 : x ≤ 0) :
    (x / (1 + x) ^ 2) ≤ 0 :=
  gammaUntransform_nonpos hx0 hx

lemma gammaTransform_X_sub_C_mul_two {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) (r : ℝ) :
    gammaTransform (d + 2) ((X - C r) * γ) =
      (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by
  have hmul : (X - C r) * γ = X * γ + C (-r) * γ := by simp [sub_eq_add_neg, add_mul]
  calc
    gammaTransform (d + 2) ((X - C r) * γ)
      = gammaTransform (d + 2) (X * γ + C (-r) * γ) := by lia
    _ = gammaTransform (d + 2) (X * γ) + C (-r) * gammaTransform (d + 2) γ := by
          rw [gammaTransform_add, gammaTransform_C_mul]
    _ = X * gammaTransform d γ + C (-r) * ((X + 1) ^ 2 * gammaTransform d γ) := by
          rw [gammaTransform_X_mul_two, gammaTransform_pad_two hγ]
    _ = X * gammaTransform d γ - (C r * (X + 1) ^ 2) * gammaTransform d γ := by
          simp [sub_eq_add_neg, mul_assoc]
    _ = (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by grind

/-- Iterated form of the quadratic factor in Hoster--Stump, Proposition 2.5,
equation (2.1). -/
lemma gammaTransform_X_sub_C_pow_mul_two
    {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) (r : ℝ) :
    ∀ m : ℕ,
      gammaTransform (d + 2 * m) ((X - C r) ^ m * γ) =
        (X - C r * (X + 1) ^ 2) ^ m * gammaTransform d γ
  | 0 => by simp
  | m + 1 => by
      have hdeg :
          ((X - C r) ^ m * γ).natDegree ≤ (d + 2 * m) / 2 := by
        calc
          ((X - C r) ^ m * γ).natDegree
              ≤ ((X - C r) ^ m).natDegree + γ.natDegree :=
            natDegree_mul_le
          _ ≤ m * (X - C r).natDegree + γ.natDegree :=
            Nat.add_le_add_right natDegree_pow_le _
          _ ≤ m * 1 + d / 2 :=
            Nat.add_le_add (Nat.mul_le_mul_left m (natDegree_X_sub_C_le r)) hγ
          _ ≤ (d + 2 * m) / 2 := by lia
      calc
        gammaTransform (d + 2 * (m + 1)) ((X - C r) ^ (m + 1) * γ) =
            gammaTransform ((d + 2 * m) + 2)
              ((X - C r) * ((X - C r) ^ m * γ)) := by
                rw [show d + 2 * (m + 1) = (d + 2 * m) + 2 by lia]
                congr 1
                rw [pow_succ]
                ring
        _ = (X - C r * (X + 1) ^ 2) *
              gammaTransform (d + 2 * m) ((X - C r) ^ m * γ) :=
          gammaTransform_X_sub_C_mul_two hdeg r
        _ = (X - C r * (X + 1) ^ 2) *
              ((X - C r * (X + 1) ^ 2) ^ m * gammaTransform d γ) := by
          rw [gammaTransform_X_sub_C_pow_mul_two hγ r m]
        _ = (X - C r * (X + 1) ^ 2) ^ (m + 1) *
              gammaTransform d γ := by
          rw [pow_succ]
          ring

/-- Algebraic reciprocal-pair factorization away from `0` and `-1`. -/
lemma gammaTransform_X_sub_C_pow_gammaRootMap_of_ne
    {d m : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ≠ -1) :
    gammaTransform (d + 2 * m) ((X - C (gammaRootMap x)) ^ m * γ) =
      (C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹)) ^ m *
        gammaTransform d γ := by
  rw [gammaTransform_X_sub_C_pow_mul_two hγ,
    gammaQuadraticFactor_eq_mul_reciprocal hx0 hx1]

/-- A gamma root of multiplicity `m` yields reciprocal transform roots, each
with the same extracted multiplicity, in Hoster--Stump equation (2.1). -/
lemma gammaTransform_X_sub_C_pow_gammaRootMap
    {d m : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 0) :
    gammaTransform (d + 2 * m) ((X - C (gammaRootMap x)) ^ m * γ) =
      (C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹)) ^ m *
        gammaTransform d γ :=
  gammaTransform_X_sub_C_pow_gammaRootMap_of_ne hγ
    (ne_of_lt hx.2) (ne_of_gt hx.1)

/-- Extracting one gamma root produces the reciprocal transform-root pair in
Hoster--Stump, Proposition 2.5, equation (2.1). -/
lemma gammaTransform_X_sub_C_gammaRootMap
    {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 0) :
    gammaTransform (d + 2) ((X - C (gammaRootMap x)) * γ) =
      (C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹)) *
        gammaTransform d γ := by
  simpa using
    (gammaTransform_X_sub_C_pow_gammaRootMap (m := 1) hγ hx)

/-- Multiplicity form of Hoster--Stump, Proposition 2.5, equation (2.1), on
both reciprocal halves of the negative real axis. -/
theorem rootMultiplicity_gammaTransform_of_neg
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) {x : ℝ} (hx : x < 0) (hx1 : x ≠ -1) :
    (gammaTransform d γ).rootMultiplicity x =
      γ.rootMultiplicity (gammaRootMap x) := by
  let r := gammaRootMap x
  let m := γ.rootMultiplicity r
  obtain ⟨q, hγq, hq_not_dvd⟩ :=
    γ.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hγ r
  change γ = (X - C r) ^ m * q at hγq
  have hq : q ≠ 0 := by
    intro hzero
    apply hγ
    rw [hγq, hzero, mul_zero]
  have hdeg_eq : γ.natDegree = m + q.natDegree := by
    rw [hγq, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hq,
      natDegree_pow, natDegree_X_sub_C, mul_one]
  have hm : 2 * m ≤ d := by
    have hbound : m + q.natDegree ≤ d / 2 := hdeg_eq ▸ hγdeg
    lia
  have hqdeg : q.natDegree ≤ (d - 2 * m) / 2 := by
    have hbound : m + q.natDegree ≤ d / 2 := hdeg_eq ▸ hγdeg
    lia
  have hx0 : x ≠ 0 := ne_of_lt hx
  have htransform :=
    gammaTransform_X_sub_C_pow_gammaRootMap_of_ne
      (d := d - 2 * m) (m := m) hqdeg hx0 hx1
  have hambient : d - 2 * m + 2 * m = d := by lia
  have hfull := htransform
  rw [hambient, ← hγq] at hfull
  have h1x : 1 + x ≠ 0 := by
    intro h
    apply hx1
    linarith
  have hr0 : r ≠ 0 := by
    dsimp [r, gammaRootMap]
    exact div_ne_zero hx0 (pow_ne_zero _ h1x)
  have hxxinv : x ≠ x⁻¹ := by
    intro heq
    have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    rw [← heq] at hmul
    rcases lt_or_gt_of_ne hx1 with hlt | hgt <;> nlinarith
  have hcore_not_root :
      ¬(gammaTransform (d - 2 * m) q).IsRoot x := by
    intro hroot
    apply hq_not_dvd
    rw [dvd_iff_isRoot]
    simpa [r, gammaRootMap] using
      isRoot_gamma_of_isRoot_gammaTransform hqdeg hx1 hroot
  have hcore_eval : (gammaTransform (d - 2 * m) q).eval x ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hcore_not_root
  let p :=
    (C (-r) * (X - C x⁻¹)) ^ m * gammaTransform (d - 2 * m) q
  have hp_eval : p.eval x ≠ 0 := by
    dsimp [p]
    simp only [eval_mul, eval_pow, eval_C, eval_sub, eval_X]
    exact mul_ne_zero
      (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr hr0)
        (sub_ne_zero.mpr hxxinv)))
      hcore_eval
  have hp : p ≠ 0 := by
    intro hzero
    apply hp_eval
    simp [hzero]
  have hp_not_root : ¬p.IsRoot x := by
    rw [Polynomial.IsRoot.def]
    exact hp_eval
  have hfactor :
      gammaTransform d γ = p * (X - C x) ^ m := by
    rw [hfull]
    dsimp [p, r]
    simp only [mul_pow]
    ring
  change (gammaTransform d γ).rootMultiplicity x = m
  rw [hfactor, rootMultiplicity_mul_X_sub_C_pow hp,
    rootMultiplicity_eq_zero hp_not_root, zero_add]

/-- Multiplicity form of Hoster--Stump equation (2.1) on the preferred branch
`(-1, 0)`. -/
theorem rootMultiplicity_gammaTransform_of_mem_Ioo
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 0) :
    (gammaTransform d γ).rootMultiplicity x =
      γ.rootMultiplicity (gammaRootMap x) :=
  rootMultiplicity_gammaTransform_of_neg hγdeg hγ hx.2 (ne_of_gt hx.1)

/-! ## Ordered root completion for Hoster--Stump Proposition 2.5

The following private helpers formalize the two cases after equation (2.2).
Preferred roots lie in `(-1, 0)`; their reciprocal roots lie below `-1`, and
the replicated center block records the multiplicity of `-1`.
-/

private noncomputable def reciprocalCenterRoots (m : ℕ) (s : List ℝ) : List ℝ :=
  (s.map fun x => x⁻¹).reverse ++ (List.replicate m (-1) ++ s)

private lemma map_interleave (f : α → β) : ∀ l₁ l₂ : List α,
    (l₁.interleave l₂).map f = (l₁.map f).interleave (l₂.map f)
  | _, [] => by simp
  | l₁, b :: l₂ => by
      simp only [List.interleave_cons, List.map_cons]
      rw [map_interleave f l₂ l₁]
termination_by l₁ l₂ => l₁.length + l₂.length

private lemma mem_interleave_of_lengths {x : α} : ∀ l₁ l₂ : List α,
    (l₁.length = l₂.length ∨ l₁.length + 1 = l₂.length) →
      x ∈ l₁.interleave l₂ → x ∈ l₁ ∨ x ∈ l₂
  | _, [], _, hx => by simp at hx
  | l₁, b :: l₂, hlen, hx => by
      rw [List.interleave_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr (by simp)
      · have htail : l₂.length = l₁.length ∨ l₂.length + 1 = l₁.length := by
          simp only [List.length_cons] at hlen
          lia
        rcases mem_interleave_of_lengths l₂ l₁ htail hx with hx | hx
        · exact Or.inr (by simp [hx])
        · exact Or.inl hx
termination_by l₁ l₂ => l₁.length + l₂.length

private lemma interleave_replicate_succ (m : ℕ) (a : α) :
    (List.replicate m a).interleave (List.replicate (m + 1) a) =
      List.replicate (2 * m + 1) a := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ (n := m)]
      rw [List.replicate_succ (n := m + 1)]
      rw [List.interleave_cons, List.interleave_cons]
      rw [ih]
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by lia]
      rfl

private lemma isChain_reverse_inv_center_iff
    {l : List ℝ} (m : ℕ)
    (hlmem : ∀ x ∈ l, x ∈ Set.Ioo (-1 : ℝ) 0) :
    ((l.reverse.map fun x => x⁻¹) ++
        (List.replicate (2 * m + 1) (-1) ++ l)).IsChain (· ≤ ·) ↔
      l.IsChain (· ≤ ·) := by
  let a := l.reverse.map fun x => x⁻¹
  let c := List.replicate (2 * m + 1) (-1 : ℝ)
  constructor
  · intro h
    have hp := h.pairwise
    rw [List.pairwise_append, List.pairwise_append] at hp
    exact hp.2.1.2.1.isChain
  · intro hl
    have ha : a.Pairwise (· ≤ ·) := by
      dsimp [a]
      rw [List.pairwise_map, List.pairwise_reverse]
      exact hl.pairwise.imp_of_mem fun hx hy hxy =>
        inv_antitoneOn_Iio (hlmem _ hx).2 (hlmem _ hy).2 hxy
    have hc : c.Pairwise (· ≤ ·) := by simp [c]
    have hac : (a ++ c).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨ha, hc, ?_⟩
      intro x hx y hy
      dsimp [a] at hx
      rw [List.mem_map] at hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzmem : z ∈ l := List.mem_reverse.mp hz
      have hzlt : z⁻¹ < -1 := by
        rw [inv_eq_one_div]
        exact (div_lt_iff_of_neg (hlmem z hzmem).2).2
          (by nlinarith [(hlmem z hzmem).1])
      have hy' : y = -1 := by simpa [c] using hy
      linarith
    have hacl : ((a ++ c) ++ l).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨hac, hl.pairwise, ?_⟩
      intro x hx y hy
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · dsimp [a] at hx
        rw [List.mem_map] at hx
        rcases hx with ⟨z, hz, rfl⟩
        have hzmem : z ∈ l := List.mem_reverse.mp hz
        have hzlt : z⁻¹ < -1 := by
          rw [inv_eq_one_div]
          exact (div_lt_iff_of_neg (hlmem z hzmem).2).2
            (by nlinarith [(hlmem z hzmem).1])
        linarith [(hlmem y hy).1]
      · have hx' : x = -1 := by simpa [c] using hx
        linarith [(hlmem y hy).1]
    simpa [a, c, List.append_assoc] using hacl.isChain

private lemma interleave_reciprocalCenterRoots_same
    {ss rs : List ℝ} (m : ℕ) (hlen : ss.length = rs.length) :
    (reciprocalCenterRoots m ss).interleave
        (reciprocalCenterRoots (m + 1) rs) =
      ((rs.interleave ss).reverse.map fun x => x⁻¹) ++
        (List.replicate (2 * m + 1) (-1) ++ rs.interleave ss) := by
  unfold reciprocalCenterRoots
  rw [List.interleave_append_append_of_length_eq_length]
  · rw [List.interleave_append_append_of_length_add_one_eq_length]
    · rw [interleave_replicate_succ]
      congr 1
      simpa only [map_interleave, List.map_reverse] using
        (List.reverse_interleave_of_length_eq_length
          (l₁ := rs.map fun x => x⁻¹) (l₂ := ss.map fun x => x⁻¹)
          (by simpa only [List.length_map] using hlen.symm)).symm
    · simp
  · simp [hlen]

private lemma interleave_reciprocalCenterRoots_succ
    {ss rs : List ℝ} (m : ℕ) (hlen : ss.length + 1 = rs.length) :
    (reciprocalCenterRoots (m + 1) ss).interleave
        (reciprocalCenterRoots m rs) =
      ((ss.interleave rs).reverse.map fun x => x⁻¹) ++
        (List.replicate (2 * m + 1) (-1) ++ ss.interleave rs) := by
  unfold reciprocalCenterRoots
  rw [List.interleave_append_append_of_length_add_one_eq_length]
  · rw [List.interleave_append_append_of_length_add_one_eq_length]
    · rw [interleave_replicate_succ]
      congr 1
      simpa only [map_interleave, List.map_reverse] using
        (List.reverse_interleave_of_length_add_one_eq_length
          (l₁ := ss.map fun x => x⁻¹) (l₂ := rs.map fun x => x⁻¹)
          (by simpa only [List.length_map] using hlen)).symm
    · simp
  · simp [hlen]

/-- Equal gamma degrees give one additional central root on the right transform.
This is the first backward case in Hoster--Stump, Proposition 2.5. -/
private lemma listInterlaces_reciprocalCenterRoots_same_iff
    {ss rs : List ℝ} (m : ℕ)
    (hss : ∀ x ∈ ss, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hrs : ∀ x ∈ rs, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hlen : ss.length = rs.length) :
    ListInterlaces (reciprocalCenterRoots m ss)
        (reciprocalCenterRoots (m + 1) rs) ↔
      ListAlternates ss rs := by
  have hfull_len :
      (reciprocalCenterRoots m ss).length + 1 =
        (reciprocalCenterRoots (m + 1) rs).length := by
    simp [reciprocalCenterRoots, hlen]
    lia
  rw [listInterlaces_iff_interleaves_of_length hfull_len]
  constructor
  · intro h
    have hc := ((List.interleaves_iff_length_isChain_interleave).1 h).2
    rw [interleave_reciprocalCenterRoots_same m hlen,
      isChain_reverse_inv_center_iff m] at hc
    · apply (listAlternates_iff_interleaves_of_length hlen).2
      apply (List.interleaves_iff_length_isChain_interleave).2
      exact ⟨Or.inl hlen.symm, hc⟩
    · intro x hx
      rcases mem_interleave_of_lengths rs ss (Or.inl hlen.symm) hx with hx | hx
      · exact hrs x hx
      · exact hss x hx
  · intro h
    have hi := (listAlternates_iff_interleaves_of_length hlen).1 h
    apply (List.interleaves_iff_length_isChain_interleave).2
    refine ⟨Or.inr hfull_len, ?_⟩
    rw [interleave_reciprocalCenterRoots_same m hlen,
      isChain_reverse_inv_center_iff m]
    · exact ((List.interleaves_iff_length_isChain_interleave).1 hi).2
    · intro x hx
      rcases mem_interleave_of_lengths rs ss (Or.inl hlen.symm) hx with hx | hx
      · exact hrs x hx
      · exact hss x hx

/-- Successive gamma degrees remove one central root from the right transform.
This is the second backward case in Hoster--Stump, Proposition 2.5. -/
private lemma listInterlaces_reciprocalCenterRoots_succ_iff
    {ss rs : List ℝ} (m : ℕ)
    (hss : ∀ x ∈ ss, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hrs : ∀ x ∈ rs, x ∈ Set.Ioo (-1 : ℝ) 0)
    (hlen : ss.length + 1 = rs.length) :
    ListInterlaces (reciprocalCenterRoots (m + 1) ss)
        (reciprocalCenterRoots m rs) ↔
      ListInterlaces ss rs := by
  have hfull_len :
      (reciprocalCenterRoots (m + 1) ss).length + 1 =
        (reciprocalCenterRoots m rs).length := by
    simp [reciprocalCenterRoots]
    lia
  rw [listInterlaces_iff_interleaves_of_length hfull_len]
  constructor
  · intro h
    have hc := ((List.interleaves_iff_length_isChain_interleave).1 h).2
    rw [interleave_reciprocalCenterRoots_succ m hlen,
      isChain_reverse_inv_center_iff m] at hc
    · apply (listInterlaces_iff_interleaves_of_length hlen).2
      apply (List.interleaves_iff_length_isChain_interleave).2
      exact ⟨Or.inr hlen, hc⟩
    · intro x hx
      rcases mem_interleave_of_lengths ss rs (Or.inr hlen) hx with hx | hx
      · exact hss x hx
      · exact hrs x hx
  · intro h
    have hi := (listInterlaces_iff_interleaves_of_length hlen).1 h
    apply (List.interleaves_iff_length_isChain_interleave).2
    refine ⟨Or.inr hfull_len, ?_⟩
    rw [interleave_reciprocalCenterRoots_succ m hlen,
      isChain_reverse_inv_center_iff m]
    · exact ((List.interleaves_iff_length_isChain_interleave).1 hi).2
    · intro x hx
      rcases mem_interleave_of_lengths ss rs (Or.inr hlen) hx with hx | hx
      · exact hss x hx
      · exact hrs x hx

/-- Exact root-multiset form of Hoster--Stump, Proposition 2.5, equations
(2.1) and (2.2): the roots of the gamma transform consist of reciprocal
pairs, together with the exceptional roots at `-1` prescribed by the degree.
-/
theorem roots_gammaTransform_eq_reciprocal_add_neg_one_add
    {d : Nat} {γ : Real[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0)
    (hneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0) :
    (gammaTransform d γ).roots =
      ((gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : Real) 0)).map (fun x => x⁻¹) +
        Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) +
          (gammaTransform d γ).roots.filter
            (fun x => x ∈ Set.Ioo (-1 : Real) 0) := by
  classical
  let s := (gammaTransform d γ).roots.filter
    (fun x => x ∈ Set.Ioo (-1 : Real) 0)
  change (gammaTransform d γ).roots =
    s.map (fun x => x⁻¹) +
      Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s
  have hs_Ioo {x : Real} (hx : x ∈ s) : x ∈ Set.Ioo (-1 : Real) 0 := by
    change x ∈ (gammaTransform d γ).roots.filter
      (fun z => z ∈ Set.Ioo (-1 : Real) 0) at hx
    exact (Multiset.mem_filter.mp hx).2
  have hinv_Ioo {x : Real} (hx : x < -1) : x⁻¹ ∈ Set.Ioo (-1 : Real) 0 := by
    constructor
    · rw [inv_eq_one_div]
      exact (lt_div_iff_of_neg (by linarith)).2 (by nlinarith)
    · exact inv_lt_zero.mpr (by linarith)
  have hinv_lt_neg_one {x : Real} (hx : x ∈ Set.Ioo (-1 : Real) 0) :
      x⁻¹ < -1 := by
    rw [inv_eq_one_div]
    exact (div_lt_iff_of_neg hx.2).2 (by nlinarith [hx.1])
  refine Multiset.ext.mpr fun x => ?_
  by_cases hxlt : x < -1
  · have hx0 : x ≠ 0 := by linarith
    have hxi := hinv_Ioo hxlt
    have hcount_inv :
        (gammaTransform d γ).roots.count x =
          (s.map (fun z => z⁻¹)).count x := by
      calc
        (gammaTransform d γ).roots.count x =
            (gammaTransform d γ).rootMultiplicity x :=
          Polynomial.count_roots (gammaTransform d γ)
        _ = γ.rootMultiplicity (gammaRootMap x) :=
          rootMultiplicity_gammaTransform_of_neg hγdeg hγ
            (by linarith) (by linarith)
        _ = γ.rootMultiplicity (gammaRootMap x⁻¹) := by rw [gammaRootMap_inv hx0]
        _ = (gammaTransform d γ).rootMultiplicity x⁻¹ :=
          (rootMultiplicity_gammaTransform_of_neg hγdeg hγ hxi.2
            (ne_of_gt hxi.1)).symm
        _ = (gammaTransform d γ).roots.count x⁻¹ :=
          (Polynomial.count_roots (gammaTransform d γ)).symm
        _ = s.count x⁻¹ := by
          simpa [s] using
            (Multiset.count_filter_of_pos
              (s := (gammaTransform d γ).roots) (a := x⁻¹)
              (p := fun z : Real => z ∈ Set.Ioo (-1) 0) hxi).symm
        _ = (s.map (fun z => z⁻¹)).count x := by
          simpa using
            (Multiset.count_map_eq_count' (fun z : Real => z⁻¹) s
              inv_injective x⁻¹).symm
    have hs_zero : s.count x = 0 := by
      apply Multiset.count_filter_of_neg
      intro hxmem
      linarith [hxmem.1]
    have hrep_zero :
        (Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real)).count x = 0 := by
      rw [Multiset.count_replicate]
      simp [Ne.symm (ne_of_lt hxlt)]
    calc
      (gammaTransform d γ).roots.count x =
          (s.map (fun z => z⁻¹)).count x := hcount_inv
      _ = (s.map (fun z => z⁻¹) +
          Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count x := by
        simp [Multiset.count_add, hs_zero, hrep_zero]
  · by_cases hxeq : x = -1
    · subst x
      have hs_zero : s.count (-1) = 0 := by
        apply Multiset.count_filter_of_neg
        simp
      have hinv_zero : (s.map (fun z => z⁻¹)).count (-1) = 0 := by
        apply Multiset.count_eq_zero_of_notMem
        rw [Multiset.mem_map]
        rintro ⟨z, hzs, hz⟩
        have hzlt := hinv_lt_neg_one (hs_Ioo hzs)
        rw [hz] at hzlt
        linarith
      calc
        (gammaTransform d γ).roots.count (-1) =
            (gammaTransform d γ).rootMultiplicity (-1) :=
          Polynomial.count_roots (gammaTransform d γ)
        _ = d - 2 * γ.natDegree :=
          rootMultiplicity_neg_one_gammaTransform hγdeg hγ
        _ = (s.map (fun z => z⁻¹) +
            Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count (-1) := by
          simp [Multiset.count_add, hs_zero, hinv_zero]
    · by_cases hxneg : x < 0
      · have hxmem : x ∈ Set.Ioo (-1 : Real) 0 :=
          ⟨lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm hxeq), hxneg⟩
        have hinv_zero : (s.map (fun z => z⁻¹)).count x = 0 := by
          apply Multiset.count_eq_zero_of_notMem
          rw [Multiset.mem_map]
          rintro ⟨z, hzs, hz⟩
          have hzlt := hinv_lt_neg_one (hs_Ioo hzs)
          rw [hz] at hzlt
          linarith [hxmem.1]
        have hs_count :
            (gammaTransform d γ).roots.count x = s.count x := by
          simpa [s] using
            (Multiset.count_filter_of_pos
              (s := (gammaTransform d γ).roots) (a := x)
              (p := fun z : Real => z ∈ Set.Ioo (-1) 0) hxmem).symm
        have hrep_zero :
            (Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real)).count x = 0 := by
          rw [Multiset.count_replicate]
          simp [Ne.symm hxeq]
        calc
          (gammaTransform d γ).roots.count x = s.count x := hs_count
          _ = (s.map (fun z => z⁻¹) +
              Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count x := by
            simp [Multiset.count_add, hinv_zero, hrep_zero]
      · have hx_not_mem : x ∉ (gammaTransform d γ).roots := by
          intro hxroot
          exact hxneg (hneg x hxroot)
        have hs_zero : s.count x = 0 := by
          apply Multiset.count_filter_of_neg
          intro hxmem
          exact hxneg hxmem.2
        have hinv_zero : (s.map (fun z => z⁻¹)).count x = 0 := by
          apply Multiset.count_eq_zero_of_notMem
          rw [Multiset.mem_map]
          rintro ⟨z, hzs, hz⟩
          have hzlt := hinv_lt_neg_one (hs_Ioo hzs)
          rw [hz] at hzlt
          linarith
        have hrep_zero :
            (Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real)).count x = 0 := by
          rw [Multiset.count_replicate]
          simp [Ne.symm hxeq]
        calc
          (gammaTransform d γ).roots.count x = 0 :=
            Multiset.count_eq_zero_of_notMem hx_not_mem
          _ = (s.map (fun z => z⁻¹) +
              Multiset.replicate (d - 2 * γ.natDegree) (-1 : Real) + s).count x := by
            simp [Multiset.count_add, hs_zero, hinv_zero, hrep_zero]

/-- Exact root-multiset form of Hoster--Stump, Proposition 2.5, equation
(2.1): the negative gamma roots are the images of the transform roots on the
preferred reciprocal branch `(-1, 0)`, with multiplicity. -/
theorem roots_eq_map_filter_roots_gammaTransform
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2) (hγ : γ ≠ 0)
    (hγneg : ∀ y ∈ γ.roots, y < 0) :
    γ.roots =
      ((gammaTransform d γ).roots.filter
        (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).map gammaRootMap := by
  classical
  let s := (gammaTransform d γ).roots.filter
    (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)
  have hs_Ioo {x : ℝ} (hx : x ∈ s) : x ∈ Set.Ioo (-1 : ℝ) 0 := by
    change x ∈ (gammaTransform d γ).roots.filter
      (fun z => z ∈ Set.Ioo (-1 : ℝ) 0) at hx
    exact (Multiset.mem_filter.mp hx).2
  refine Multiset.ext.mpr fun y => ?_
  by_cases hy : y < 0
  · obtain ⟨x, hx, hxy⟩ := exists_mem_Ioo_gammaRootMap_eq hy
    have hcount_map : (s.map gammaRootMap).count y = s.count x := by
      rw [← hxy]
      calc
        (s.map gammaRootMap).count (gammaRootMap x) =
            (s.filter
              (fun z => gammaRootMap x = gammaRootMap z)).card :=
          Multiset.count_map gammaRootMap s (gammaRootMap x)
        _ = (s.filter (fun z => x = z)).card := by
          exact congrArg Multiset.card <|
            Multiset.filter_congr fun z hz =>
              strictMonoOn_gammaRootMap.injOn.eq_iff hx (hs_Ioo hz)
        _ = s.count x :=
          (Multiset.count_eq_card_filter_eq s x).symm
    calc
      γ.roots.count y = γ.rootMultiplicity y :=
        Polynomial.count_roots γ
      _ = γ.rootMultiplicity (gammaRootMap x) := by rw [hxy]
      _ = (gammaTransform d γ).rootMultiplicity x :=
        (rootMultiplicity_gammaTransform_of_mem_Ioo hγdeg hγ hx).symm
      _ = (gammaTransform d γ).roots.count x :=
        (Polynomial.count_roots (gammaTransform d γ)).symm
      _ = s.count x := by
        simpa [s] using
          (Multiset.count_filter_of_pos
            (s := (gammaTransform d γ).roots) (a := x)
            (p := fun z : ℝ => z ∈ Set.Ioo (-1) 0) hx).symm
      _ = (s.map gammaRootMap).count y := hcount_map.symm
      _ = (((gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).map gammaRootMap).count y := by
        rfl
  · have hy_not_mem : y ∉ γ.roots := by
      intro hyroot
      exact hy (hγneg y hyroot)
    have hy_not_map : y ∉ s.map gammaRootMap := by
      rw [Multiset.mem_map]
      rintro ⟨x, hxs, hxy⟩
      apply hy
      rw [← hxy]
      unfold gammaRootMap
      exact div_neg_of_neg_of_pos (hs_Ioo hxs).2
        (sq_pos_of_pos (by linarith [(hs_Ioo hxs).1]))
    calc
      γ.roots.count y = 0 :=
        Multiset.count_eq_zero_of_notMem hy_not_mem
      _ = (s.map gammaRootMap).count y :=
        (Multiset.count_eq_zero_of_notMem hy_not_map).symm
      _ = (((gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).map gammaRootMap).count y := by
        rfl

lemma hasNonnegCoeffs_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    HasNonnegCoeffs (X - C r * (X + 1) ^ 2) := by
  have hneg : 0 ≤ -r := by simp_all
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using
    hasNonnegCoeffs_X.add
      (nonnegCoeffs_C_mul hneg (hasNonnegCoeffs_X_add_one.pow 2))

lemma isRealRooted_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    ((X - C r * (X + 1) ^ 2) ≠ 0 ∧ (X - C r * (X + 1) ^ 2).Splits) := by
  by_cases hr0 : r = 0
  · simp_all
  · set t : ℝ := -r with ht_def
    have hrlt : r < 0 := lt_of_le_of_ne hr hr0
    have ht_pos : 0 < t := by simp_all
    have hpoly :
        X - C r * (X + 1) ^ 2 = C t * X ^ 2 + C (2 * t + 1) * X + C t := by
      subst t
      ext n
      cases n with
      | zero =>
          simp [Polynomial.coeff_X_add_one_pow]
      | succ n =>
          cases n with
          | zero =>
              simp [Polynomial.coeff_X_add_one_pow]
              ring
          | succ n =>
              cases n with
              | zero =>
                  simp [Polynomial.coeff_X_add_one_pow, coeff_X, coeff_one]
              | succ n =>
                  have hpow0 : (((X + 1 : ℝ[X]) ^ 2).coeff (n + 3)) = 0 :=
                    Polynomial.coeff_eq_zero_of_natDegree_lt
                      (lt_of_le_of_lt (natDegree_X_add_one_pow_le 2) (by lia))
                  simp [coeff_X, coeff_one, hpow0]
    have hroots :
        (C t * X ^ 2 + C (2 * t + 1) * X + C t).roots =
          {(-(2 * t + 1) - Real.sqrt (t * 4 + 1)) / (2 * t),
            (-(2 * t + 1) + Real.sqrt (t * 4 + 1)) / (2 * t)} := by
      apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero' (a := t) (b := 2 * t + 1)
        (c := t) (ha := ne_of_gt ht_pos)).2
      grind
    rw [hpoly]
    refine ⟨?_, ?_⟩
    · intro hzero
      simp_all
    · rw [Polynomial.splits_iff_card_roots, hroots,
        Polynomial.natDegree_quadratic (ne_of_gt ht_pos)]
      simp

/-- The gamma transform preserves real-rootedness on nonnegative-coefficient
inputs whose degree fits the ambient floor `d / 2`. -/
theorem isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits) (hγnn : HasNonnegCoeffs γ) : ((gammaTransform d γ) ≠ 0 ∧
      (gammaTransform d γ).Splits) := by
  let P : ℕ → Prop := fun n =>
    ∀ d : ℕ, ∀ γ : ℝ[X],
      γ.natDegree = n →
      γ.natDegree ≤ d / 2 →
      (γ ≠ 0 ∧ γ.Splits) →
      HasNonnegCoeffs γ →
      ((gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih d γ hγdeg_eq hbound hrr hnn
    by_cases hn0 : n = 0
    · have hγC : γ = C (γ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show γ.natDegree ≤ 0 by lia))
      rw [hγC]
      have hcoeff_ne : γ.coeff 0 ≠ 0 := by grind
      have hgt :
          gammaTransform d (C (γ.coeff 0)) = C (γ.coeff 0) * (X + 1) ^ d := by
        simpa [gammaBasisTerm_zero] using
          (gammaTransform_monomial d 0 (γ.coeff 0))
      rw [hgt]
      exact isRealRooted_C_mul
        (isRealRooted_X_add_one_pow d).1 (isRealRooted_X_add_one_pow d).2 hcoeff_ne
    · have hroots_pos : 0 < γ.roots.card := by
        rw [card_roots_of_splits hrr.2, hγdeg_eq]
        lia
      obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hr_root : γ.IsRoot r := (mem_roots hrr.1).mp hr_mem
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
      have hq' : γ = (X - C r) * q := by lia
      have hq_dvd : q ∣ γ := ⟨X - C r, by grind⟩
      have hq_ne : q ≠ 0 := by simp_all
      have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hrr.2 hnn r hr_mem
      have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hrr.1 hrr.2 hq_ne hq_dvd
      have hγ_pos : HasPosLeadingCoeff γ := hnn.pos_leadingCoeff hrr.1
      have hq_pos : HasPosLeadingCoeff q :=
        hasPosLeadingCoeff_of_X_sub_C_mul (r := r) (by simp_all)
      have hq_nn : HasNonnegCoeffs q :=
        hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
          hrr.1 hrr.2 hnn hq_rr.1 hq_rr.2 hq_pos hq_dvd
      have hqdeg_lt : q.natDegree < n := by
        have hmuldeg : γ.natDegree = q.natDegree + 1 := by
          rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          lia
        lia
      have hqbound : q.natDegree ≤ (d - 2) / 2 := by lia
      have hd : d = (d - 2) + 2 := by lia
      rw [hd, hq', gammaTransform_X_sub_C_mul_two hqbound r]
      have hgqf := isRealRooted_gammaQuadraticFactor hr_nonpos
      have hih := ih q.natDegree hqdeg_lt (d - 2) q rfl hqbound hq_rr hq_nn
      exact isRealRooted_mul hgqf.1 hgqf.2 hih.1 hih.2
  grind

theorem hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits) (hγnn : HasNonnegCoeffs γ) :
    HasRootsNonpos (gammaTransform d γ) := by
  intro r hr
  exact roots_nonpos_of_nonneg_coeffs
    (isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs hγdeg hγ_ne hγ_splits hγnn).2
    (hasNonnegCoeffs_gammaTransform hγnn) r hr

theorem isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp_ne : (gammaTransform (2 * γ.natDegree) γ) ≠ 0)
    (hp_splits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ := by
  let P : ℕ → Prop := fun n =>
    ∀ γ : ℝ[X],
      γ.natDegree = n →
      ((gammaTransform (2 * n) γ) ≠ 0 ∧ (gammaTransform (2 * n) γ).Splits) →
      HasRootsNonpos (gammaTransform (2 * n) γ) →
      (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih δ hδdeg hpδ hpδ_nonpos
    have hδ0_main : δ ≠ 0 := fun hzero => by simp_all
    by_cases hn0 : n = 0
    · have hδC : δ = C (δ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show δ.natDegree ≤ 0 by lia))
      have hc : δ.coeff 0 ≠ 0 := by grind
      refine ⟨isRealRooted_of_deg_zero hδ0_main (by lia), ?_⟩
      intro r hr
      have : False := by
        rw [hδC] at hr
        simp at hr
      lia
    · by_cases hcoeff0 : δ.coeff 0 = 0
      · have hXdvd : X ∣ δ := Polynomial.X_dvd_iff.mpr hcoeff0
        obtain ⟨ζ, hδX⟩ := hXdvd
        have hζ0 : ζ ≠ 0 := by simp_all
        have hζdeg_succ : n = ζ.natDegree + 1 := by simp_all
        have hζdeg_lt : ζ.natDegree < n := by lia
        have hq_eq :
            gammaTransform (2 * n) δ = X * gammaTransform (2 * ζ.natDegree) ζ := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) (X * ζ) := by lia
            _ = gammaTransform (2 * ζ.natDegree + 2) (X * ζ) := by grind
            _ = X * gammaTransform (2 * ζ.natDegree) ζ :=
                  gammaTransform_X_mul_two (2 * ζ.natDegree) ζ
        have hq0 : gammaTransform (2 * ζ.natDegree) ζ ≠ 0 := by simp_all
        have hq_dvd : gammaTransform (2 * ζ.natDegree) ζ ∣ gammaTransform (2 * n) δ := by simp_all
        have hq_rr : ((gammaTransform (2 * ζ.natDegree) ζ) ≠ 0 ∧
          (gammaTransform (2 * ζ.natDegree) ζ).Splits) :=
          isRealRooted_of_dvd hpδ.1 hpδ.2 hq0 hq_dvd
        have hq_nonpos : HasRootsNonpos (gammaTransform (2 * ζ.natDegree) ζ) :=
          hasRootsNonpos_of_dvd hpδ_nonpos hpδ.1 hq_dvd hq0
        rcases (ih ζ.natDegree hζdeg_lt) ζ rfl hq_rr hq_nonpos with ⟨hζ_rr, hζ_nonpos⟩
        have hX_nonpos : HasRootsNonpos (X : ℝ[X]) := by
          simpa using hasRootsNonpos_X_sub_C (r := (0 : ℝ)) (by simp)
        refine ⟨?_, ?_⟩
        · simp_all
        · rw [hδX]
          exact hX_nonpos.mul hζ_nonpos (by simp) hζ_rr.1
      · have htop : δ.coeff n ≠ 0 := by
          have htop' : δ.coeff δ.natDegree ≠ 0 := by
            rw [Polynomial.coeff_natDegree]
            simp_all
          lia
        have htop_deg : (gammaTransform (2 * n) δ).natDegree = 2 * n :=
          Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
            (natDegree_gammaTransform_le (2 * n) δ)
            (by simp_all)
        have hroots_pos : 0 < (gammaTransform (2 * n) δ).roots.card := by
          rw [card_roots_of_splits hpδ.2, htop_deg]
          lia
        obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hx_root : (gammaTransform (2 * n) δ).IsRoot x := (mem_roots hpδ.1).mp hx_mem
        have hx_nonpos : x ≤ 0 := hpδ_nonpos x hx_mem
        have hx_ne_neg_one : x ≠ -1 := by
          intro hx_eq
          have hx_root_neg_one : (gammaTransform (2 * n) δ).IsRoot (-1) := by lia
          exact htop ((gammaTransform_even_isRoot_neg_one_iff n δ).mp hx_root_neg_one)
        let y : ℝ := x / (1 + x) ^ 2
        have hy_nonpos : y ≤ 0 :=
          rootPullback_nonpos_of_gammaTransform hx_ne_neg_one hx_nonpos
        have hy_root : δ.IsRoot y := by
          dsimp [y]
          exact isRoot_gamma_of_isRoot_gammaTransform
            (d := 2 * n) (γ := δ) (by lia) hx_ne_neg_one hx_root
        obtain ⟨ε, hγ_fac0⟩ := dvd_iff_isRoot.mpr hy_root
        have hγ_fac : δ = (X - C y) * ε := by lia
        have hε0 : ε ≠ 0 := by simp_all
        have hεdeg_succ : n = ε.natDegree + 1 := by
          calc
            n = δ.natDegree := by lia
            _ = ((X - C y) * ε).natDegree := by lia
            _ = 1 + ε.natDegree := by rw [natDegree_mul (X_sub_C_ne_zero y) hε0, natDegree_X_sub_C]
            _ = ε.natDegree + 1 := by lia
        have hεdeg_lt : ε.natDegree < n := by lia
        have hq_eq :
            gammaTransform (2 * n) δ =
              (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) ((X - C y) * ε) := by lia
            _ = gammaTransform (2 * ε.natDegree + 2) ((X - C y) * ε) := by grind
            _ = (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε :=
                  gammaTransform_X_sub_C_mul_two (γ := ε) (by lia) y
        have hq0 : gammaTransform (2 * ε.natDegree) ε ≠ 0 := by simp_all
        have hq_dvd : gammaTransform (2 * ε.natDegree) ε ∣ gammaTransform (2 * n) δ := by simp_all
        have hq_rr : ((gammaTransform (2 * ε.natDegree) ε) ≠ 0 ∧
          (gammaTransform (2 * ε.natDegree) ε).Splits) :=
          isRealRooted_of_dvd hpδ.1 hpδ.2 hq0 hq_dvd
        have hq_nonpos : HasRootsNonpos (gammaTransform (2 * ε.natDegree) ε) :=
          hasRootsNonpos_of_dvd hpδ_nonpos hpδ.1 hq_dvd hq0
        rcases (ih ε.natDegree hεdeg_lt) ε rfl hq_rr hq_nonpos with ⟨hε_rr, hε_nonpos⟩
        refine ⟨?_, ?_⟩
        · simp_all
        · rw [hγ_fac]
          exact (hasRootsNonpos_X_sub_C hy_nonpos).mul hε_nonpos (X_sub_C_ne_zero y) hε_rr.1
  grind

theorem isRealRooted_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp_ne : (gammaTransform (2 * γ.natDegree) γ) ≠ 0)
    (hp_splits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) : (γ ≠ 0 ∧ γ.Splits) :=
  (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    hp_ne hp_splits hp_nonpos).1

theorem hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp_ne : (gammaTransform (2 * γ.natDegree) γ) ≠ 0)
    (hp_splits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    HasRootsNonpos γ :=
  (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    hp_ne hp_splits hp_nonpos).2

lemma hasRootsNonpos_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    HasRootsNonpos (X - C r * (X + 1) ^ 2) := by
  intro s hs
  exact roots_nonpos_of_nonneg_coeffs
    (isRealRooted_gammaQuadraticFactor hr).2
    (hasNonnegCoeffs_gammaQuadraticFactor hr)
    s hs

theorem isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits) (hγ_nonpos : HasRootsNonpos γ) :
      ((gammaTransform d γ) ≠ 0 ∧
      (gammaTransform d γ).Splits) ∧
      HasRootsNonpos (gammaTransform d γ) := by
  let P : ℕ → Prop := fun n =>
    ∀ d : ℕ, ∀ γ : ℝ[X],
      γ.natDegree = n →
      γ.natDegree ≤ d / 2 →
      (γ ≠ 0 ∧ γ.Splits) →
      HasRootsNonpos γ →
      ((gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits) ∧
        HasRootsNonpos (gammaTransform d γ)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih d δ hδdeg hbound hδ_rr hδ_nonpos
    by_cases hn0 : n = 0
    · have hδC : δ = C (δ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show δ.natDegree ≤ 0 by lia))
      have hcoeff_ne : δ.coeff 0 ≠ 0 := by grind
      have hgt :
          gammaTransform d (C (δ.coeff 0)) = C (δ.coeff 0) * (X + 1) ^ d := by
        simpa [gammaBasisTerm_zero] using
          (gammaTransform_monomial d 0 (δ.coeff 0))
      rw [hδC, hgt]
      refine ⟨isRealRooted_C_mul
        (isRealRooted_X_add_one_pow d).1 (isRealRooted_X_add_one_pow d).2 hcoeff_ne, ?_⟩
      intro r hr
      rw [roots_C_mul _ hcoeff_ne] at hr
      exact roots_nonpos_of_nonneg_coeffs
        (isRealRooted_X_add_one_pow d).2
        (hasNonnegCoeffs_X_add_one.pow d)
        r hr
    · have hroots_pos : 0 < δ.roots.card := by
        rw [card_roots_of_splits hδ_rr.2, hδdeg]
        lia
      obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hr_root : δ.IsRoot r := (mem_roots hδ_rr.1).mp hr_mem
      have hr_nonpos : r ≤ 0 := hδ_nonpos r hr_mem
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
      have hδq : δ = (X - C r) * q := by lia
      have hq_dvd : q ∣ δ := ⟨X - C r, by grind⟩
      have hq_ne : q ≠ 0 := by simp_all
      have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hδ_rr.1 hδ_rr.2 hq_ne hq_dvd
      have hq_nonpos : HasRootsNonpos q :=
        hasRootsNonpos_of_dvd hδ_nonpos hδ_rr.1 hq_dvd hq_ne
      have hqdeg_lt : q.natDegree < n := by
        have hmuldeg : δ.natDegree = q.natDegree + 1 := by
          rw [hδq, natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          lia
        lia
      have hqbound : q.natDegree ≤ (d - 2) / 2 := by lia
      have hd : d = (d - 2) + 2 := by lia
      have ihq : ((gammaTransform (d - 2) q) ≠ 0 ∧
            (gammaTransform (d - 2) q).Splits) ∧
            HasRootsNonpos (gammaTransform (d - 2) q) :=
        ih q.natDegree hqdeg_lt (d - 2) q rfl hqbound hq_rr hq_nonpos
      rw [hd, hδq, gammaTransform_X_sub_C_mul_two hqbound r]
      refine ⟨?_, ?_⟩
      · exact isRealRooted_mul (isRealRooted_gammaQuadraticFactor hr_nonpos).1
          (isRealRooted_gammaQuadraticFactor hr_nonpos).2 ihq.1.1 ihq.1.2
      · exact (hasRootsNonpos_gammaQuadraticFactor hr_nonpos).mul ihq.2
          (isRealRooted_gammaQuadraticFactor hr_nonpos).1 ihq.1.1
  grind

lemma gammaTransform_even_shift (m k : ℕ) (γ : ℝ[X]) (hγ : γ.natDegree ≤ m) :
    gammaTransform (2 * (m + k)) γ =
      (X + 1) ^ (2 * k) * gammaTransform (2 * m) γ := by
  induction k with
  | zero =>
      lia
  | succ k ih =>
      have hhalf : (2 * (m + k)) / 2 = m + k := by lia
      have hstep : γ.natDegree ≤ (2 * (m + k)) / 2 := by lia
      calc
        gammaTransform (2 * (m + k.succ)) γ
            = gammaTransform (2 * (m + k) + 2) γ := by lia
        _ = (X + 1) ^ 2 * gammaTransform (2 * (m + k)) γ := by
              simpa using gammaTransform_pad_two (d := 2 * (m + k)) (γ := γ) hstep
        _ = (X + 1) ^ 2 * ((X + 1) ^ (2 * k) * gammaTransform (2 * m) γ) := by lia
        _ = ((X + 1) ^ 2 * (X + 1) ^ (2 * k)) * gammaTransform (2 * m) γ := by grind
        _ = (X + 1) ^ (2 + 2 * k) * gammaTransform (2 * m) γ := by grind
        _ = (X + 1) ^ (2 * (k + 1)) * gammaTransform (2 * m) γ := by lia

lemma gammaTransform_pad_to_minimal {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    gammaTransform d γ =
      (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by
  let m : ℕ := γ.natDegree
  let n : ℕ := d / 2
  have hm : m ≤ n := by lia
  have hshift :
      gammaTransform (2 * n) γ =
        (X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ := by
    have hshift' :=
      gammaTransform_even_shift (m := m) (k := n - m) (γ := γ) (by lia)
    simp_all
  rcases Nat.mod_two_eq_zero_or_one d with hd_even | hd_odd
  · grind
  · have hd : d = 2 * n + 1 := by lia
    have hpow : d - 2 * m = 1 + 2 * (n - m) := by lia
    calc
      gammaTransform d γ = gammaTransform (2 * n + 1) γ := by lia
      _ = (X + 1) * gammaTransform (2 * n) γ := gammaTransform_odd n γ
      _ = (X + 1) * ((X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ) := by lia
      _ = (X + 1) ^ (1 + 2 * (n - m)) * gammaTransform (2 * m) γ := by grind
      _ = (X + 1) ^ (d - 2 * m) * gammaTransform (2 * m) γ := by lia
      _ = (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by lia

lemma gammaTransform_minimal_dvd {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    gammaTransform (2 * γ.natDegree) γ ∣ gammaTransform d γ := by
  refine ⟨(X + 1) ^ (d - 2 * γ.natDegree), ?_⟩
  calc
    gammaTransform d γ =
        (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ :=
      gammaTransform_pad_to_minimal (d := d) (γ := γ) hγdeg
    _ = gammaTransform (2 * γ.natDegree) γ * (X + 1) ^ (d - 2 * γ.natDegree) := by ring

theorem isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hp_ne : (gammaTransform d γ) ≠ 0) (hp_splits : (gammaTransform d γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform d γ)) : (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ := by
  let q : ℝ[X] := gammaTransform (2 * γ.natDegree) γ
  have hq0 : q ≠ 0 := by
    intro hq_zero
    have hγ0 : γ = 0 :=
      (gammaTransform_eq_zero_iff_of_natDegree_le
        (d := 2 * γ.natDegree) (γ := γ) (by lia)).mp (by lia)
    simp_all
  have hqdvd : q ∣ gammaTransform d γ := by
    simpa [q] using gammaTransform_minimal_dvd (d := d) (γ := γ) hγdeg
  have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hp_ne hp_splits hq0 hqdvd
  have hq_nonpos : HasRootsNonpos q := hasRootsNonpos_of_dvd hp_nonpos hp_ne hqdvd hq0
  simpa [q] using
    (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
      (γ := γ) hq_rr.1 hq_rr.2 hq_nonpos)

/-- Planning stub for the gamma-polynomial real-rootedness criterion.

The intended theorem is the standard equivalence: for a symmetric polynomial
`p` of ambient degree `d`, the gamma-polynomial is real-rooted with
nonpositive roots if and only if `p` is real-rooted with nonpositive roots.
The symmetry hypothesis is expressed using `IdTransform d p = p` so this file
can be built directly on top of `SymmetricDecomposition`. -/
def gammaRealRootedIffPolynomialRealRootedNonposStatement : Prop :=
  ∀ {d : ℕ} {p γ : ℝ[X]},
    γ.natDegree ≤ d / 2 →
    p.natDegree ≤ d →
    IdTransform d p = p →
    IsGammaExpansion d p γ →
    (((γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ) ↔ ((p ≠ 0 ∧ p.Splits) ∧ HasRootsNonpos p))

theorem gammaRealRootedIffPolynomialRealRootedNonpos :
    gammaRealRootedIffPolynomialRealRootedNonposStatement := by
  intro d p γ hγdeg _ _ hGamma
  unfold IsGammaExpansion at hGamma
  subst p
  constructor
  · intro hγ
    exact isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
      (d := d) (γ := γ) hγdeg hγ.1.1 hγ.1.2 hγ.2
  · intro hp
    exact isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
      (d := d) (γ := γ) hγdeg hp.1.1 hp.1.2 hp.2

end
private lemma roots_neg_of_nonnegCoeffs_of_coeff_zero_ne
    {p : ℝ[X]} (hnn : HasNonnegCoeffs p) (hzero : p.coeff 0 ≠ 0) :
    ∀ x ∈ p.roots, x < 0 := by
  intro x hx
  have hxle := roots_nonpos_of_hasNonnegCoeffs hnn x hx
  have hxne : x ≠ 0 := by
    intro hxeq
    subst x
    have hroot : p.eval 0 = 0 := isRoot_of_mem_roots hx
    apply hzero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact hroot
  exact lt_of_le_of_ne hxle hxne

private noncomputable def preferredRoots (d : ℕ) (γ : ℝ[X]) : List ℝ :=
  ((gammaTransform d γ).roots.filter
    (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)).sort (· ≤ ·)

private lemma preferredRoots_pairwise (d : ℕ) (γ : ℝ[X]) :
    (preferredRoots d γ).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

private lemma mem_preferredRoots {d : ℕ} {γ : ℝ[X]} {x : ℝ}
    (hx : x ∈ preferredRoots d γ) : x ∈ Set.Ioo (-1 : ℝ) 0 := by
  rw [preferredRoots, Multiset.mem_sort] at hx
  exact (Multiset.mem_filter.mp hx).2

private lemma coe_map_gammaRootMap_preferredRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hγneg : ∀ x ∈ γ.roots, x < 0) :
    (↑((preferredRoots d γ).map gammaRootMap) : Multiset ℝ) = γ.roots := by
  change Multiset.map gammaRootMap (↑(preferredRoots d γ) : Multiset ℝ) = γ.roots
  rw [show (↑(preferredRoots d γ) : Multiset ℝ) =
    (gammaTransform d γ).roots.filter
      (fun x => x ∈ Set.Ioo (-1 : ℝ) 0) by simp [preferredRoots]]
  exact (roots_eq_map_filter_roots_gammaTransform hγdeg hγ hγneg).symm

private lemma length_preferredRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hγsplits : γ.Splits)
    (hγneg : ∀ x ∈ γ.roots, x < 0) :
    (preferredRoots d γ).length = γ.natDegree := by
  have hcoe := coe_map_gammaRootMap_preferredRoots hγdeg hγ hγneg
  have hcard := congrArg Multiset.card hcoe
  simpa [card_roots_of_splits hγsplits] using hcard

private lemma map_gammaRootMap_preferredRoots_pairwise (d : ℕ) (γ : ℝ[X]) :
    ((preferredRoots d γ).map gammaRootMap).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact (preferredRoots_pairwise d γ).imp_of_mem fun hx hy hxy =>
    strictMonoOn_gammaRootMap.monotoneOn
      (mem_preferredRoots hx) (mem_preferredRoots hy) hxy

private lemma Prec.sorted_roots_shape {f g : ℝ[X]} (h : Prec f g) :
    let ss := f.roots.sort (· ≤ ·)
    let rs := g.roots.sort (· ≤ ·)
    ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs)) := by
  rcases h with ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_sort : ss = f.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hss (Multiset.pairwise_sort _ _)
    exact Multiset.coe_eq_coe.mp (hss_eq.trans (Multiset.sort_eq _ _).symm)
  have hrs_sort : rs = g.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs (Multiset.pairwise_sort _ _)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq _ _).symm)
  simpa [hss_sort, hrs_sort] using hshape

private lemma sort_roots_eq_map_gammaRootMap_preferredRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hγneg : ∀ x ∈ γ.roots, x < 0) :
    γ.roots.sort (· ≤ ·) = (preferredRoots d γ).map gammaRootMap := by
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
    (map_gammaRootMap_preferredRoots_pairwise d γ)
  exact Multiset.coe_eq_coe.mp
    ((Multiset.sort_eq _ _).trans
      (coe_map_gammaRootMap_preferredRoots hγdeg hγ hγneg).symm)

private lemma reciprocalCenterRoots_pairwise
    {s : List ℝ} (m : ℕ) (hs : s.Pairwise (· ≤ ·))
    (hsmem : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0) :
    (reciprocalCenterRoots m s).Pairwise (· ≤ ·) := by
  let a := s.reverse.map fun x => x⁻¹
  let c := List.replicate m (-1 : ℝ)
  have ha : a.Pairwise (· ≤ ·) := by
    dsimp [a]
    rw [List.pairwise_map, List.pairwise_reverse]
    exact hs.imp_of_mem fun hx hy hxy =>
      inv_antitoneOn_Iio (hsmem _ hx).2 (hsmem _ hy).2 hxy
  have hc : c.Pairwise (· ≤ ·) := by simp [c]
  have hac : (a ++ c).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨ha, hc, ?_⟩
    intro x hx y hy
    dsimp [a] at hx
    rw [List.mem_map] at hx
    rcases hx with ⟨z, hz, rfl⟩
    have hzmem : z ∈ s := List.mem_reverse.mp hz
    have hzlt : z⁻¹ < -1 := by
      rw [inv_eq_one_div]
      exact (div_lt_iff_of_neg (hsmem z hzmem).2).2
        (by nlinarith [(hsmem z hzmem).1])
    have hy' : y = -1 := by
      dsimp [c] at hy
      exact (List.mem_replicate.mp hy).2
    linarith
  have hacs : ((a ++ c) ++ s).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨hac, hs, ?_⟩
    intro x hx y hy
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · dsimp [a] at hx
      rw [List.mem_map] at hx
      rcases hx with ⟨z, hz, rfl⟩
      have hzmem : z ∈ s := List.mem_reverse.mp hz
      have hzlt : z⁻¹ < -1 := by
        rw [inv_eq_one_div]
        exact (div_lt_iff_of_neg (hsmem z hzmem).2).2
          (by nlinarith [(hsmem z hzmem).1])
      linarith [(hsmem y hy).1]
    · have hx' : x = -1 := by
        dsimp [c] at hx
        exact (List.mem_replicate.mp hx).2
      linarith [(hsmem y hy).1]
  simpa [reciprocalCenterRoots, a, c, List.append_assoc] using hacs

private lemma coe_reciprocalCenterRoots_eq_roots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0) :
    (↑(reciprocalCenterRoots (d - 2 * γ.natDegree)
      (preferredRoots d γ)) : Multiset ℝ) = (gammaTransform d γ).roots := by
  let s := preferredRoots d γ
  unfold reciprocalCenterRoots
  calc
    (↑((s.map fun x => x⁻¹).reverse ++
        (List.replicate (d - 2 * γ.natDegree) (-1 : ℝ) ++ s)) : Multiset ℝ) =
        (↑((s.map fun x => x⁻¹).reverse) : Multiset ℝ) +
          ((↑(List.replicate (d - 2 * γ.natDegree) (-1 : ℝ)) : Multiset ℝ) +
            (↑s : Multiset ℝ)) := by
      rfl
    _ = Multiset.map (fun x : ℝ => x⁻¹) (↑s : Multiset ℝ) +
          (Multiset.replicate (d - 2 * γ.natDegree) (-1) +
            (↑s : Multiset ℝ)) := by
      rw [Multiset.coe_reverse, Multiset.coe_replicate]
      rfl
    _ = (gammaTransform d γ).roots := by
      rw [show (↑s : Multiset ℝ) =
        (gammaTransform d γ).roots.filter
          (fun x => x ∈ Set.Ioo (-1 : ℝ) 0) by simp [s, preferredRoots]]
      simpa only [add_assoc] using
        (roots_gammaTransform_eq_reciprocal_add_neg_one_add hγdeg hγ hneg).symm

private lemma sort_roots_gammaTransform_eq_reciprocalCenterRoots
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) (hneg : ∀ x ∈ (gammaTransform d γ).roots, x < 0) :
    (gammaTransform d γ).roots.sort (· ≤ ·) =
      reciprocalCenterRoots (d - 2 * γ.natDegree) (preferredRoots d γ) := by
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
    (reciprocalCenterRoots_pairwise _ (preferredRoots_pairwise d γ)
      (fun _ hx => mem_preferredRoots hx))
  exact Multiset.coe_eq_coe.mp
    ((Multiset.sort_eq _ _).trans
      (coe_reciprocalCenterRoots_eq_roots hγdeg hγ hneg).symm)

/-- Hoster--Stump, Proposition 2.5: proper position is equivalent before and
after applying adjacent-degree gamma transforms. -/
theorem prec_gammaTransform_succ_iff
    {d : ℕ} {γ δ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2)
    (hδdeg : δ.natDegree ≤ (d + 1) / 2)
    (hγnn : HasNonnegCoeffs γ)
    (hδnn : HasNonnegCoeffs δ)
    (hγ0 : γ.coeff 0 ≠ 0)
    (hδ0 : δ.coeff 0 ≠ 0) :
    Prec (gammaTransform d γ) (gammaTransform (d + 1) δ) ↔
      Prec γ δ := by
  have hγ : γ ≠ 0 := by
    intro hzero
    apply hγ0
    simp [hzero]
  have hδ : δ ≠ 0 := by
    intro hzero
    apply hδ0
    simp [hzero]
  have hγmul : γ.natDegree * 2 ≤ d := Nat.mul_le_of_le_div 2 _ _ hγdeg
  have hδmul : δ.natDegree * 2 ≤ d + 1 := Nat.mul_le_of_le_div 2 _ _ hδdeg
  have hTγnn : HasNonnegCoeffs (gammaTransform d γ) :=
    hasNonnegCoeffs_gammaTransform hγnn
  have hTδnn : HasNonnegCoeffs (gammaTransform (d + 1) δ) :=
    hasNonnegCoeffs_gammaTransform hδnn
  have hTγ0 : (gammaTransform d γ).coeff 0 ≠ 0 := by simpa [coeff_zero_gammaTransform] using hγ0
  have hTδ0 : (gammaTransform (d + 1) δ).coeff 0 ≠ 0 := by
    simpa [coeff_zero_gammaTransform] using hδ0
  have hTγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hTγnn hTγ0
  have hTδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hTδnn hTδ0
  let ss := preferredRoots d γ
  let rs := preferredRoots (d + 1) δ
  have hss : ∀ x ∈ ss, x ∈ Set.Ioo (-1 : ℝ) 0 := by exact fun _ hx => mem_preferredRoots hx
  have hrs : ∀ x ∈ rs, x ∈ Set.Ioo (-1 : ℝ) 0 := by exact fun _ hx => mem_preferredRoots hx
  constructor
  · intro hTprec
    have hγrr :=
      isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
        hγdeg hTprec.1.1 hTprec.1.2
        (roots_nonpos_of_hasNonnegCoeffs hTγnn)
    have hδrr :=
      isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
        hδdeg hTprec.2.1.1 hTprec.2.1.2
        (roots_nonpos_of_hasNonnegCoeffs hTδnn)
    have hsslen : ss.length = γ.natDegree := by
      exact length_preferredRoots hγdeg hγ hγrr.1.2
        (roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0)
    have hrslen : rs.length = δ.natDegree := by
      exact length_preferredRoots hδdeg hδ hδrr.1.2
        (roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0)
    have hmult := rootMultiplicity_bounds_of_prec hTprec (-1)
    rw [rootMultiplicity_neg_one_gammaTransform hγdeg hγ,
      rootMultiplicity_neg_one_gammaTransform hδdeg hδ] at hmult
    have hdegcases : γ.natDegree = δ.natDegree ∨
        γ.natDegree + 1 = δ.natDegree := by
      lia
    have hsorted := hTprec.sorted_roots_shape
    rw [sort_roots_gammaTransform_eq_reciprocalCenterRoots hγdeg hγ hTγneg,
      sort_roots_gammaTransform_eq_reciprocalCenterRoots hδdeg hδ hTδneg] at hsorted
    have hfull :
        ListInterlaces
          (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
          (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
      rcases hsorted with hsorted | hsorted
      · exact hsorted.2
      · exfalso
        simp [reciprocalCenterRoots] at hsorted
        lia
    have hpreferred :
        ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
          (ss.length = rs.length ∧ ListAlternates ss rs)) := by
      rcases hdegcases with hsame | hsucc
      · right
        have hlen : ss.length = rs.length := by lia
        refine ⟨hlen, ?_⟩
        have hcenter : d + 1 - 2 * δ.natDegree =
            (d - 2 * γ.natDegree) + 1 := by
          lia
        rw [hcenter] at hfull
        exact (listInterlaces_reciprocalCenterRoots_same_iff
          (d - 2 * γ.natDegree) hss hrs hlen).1 hfull
      · left
        have hlen : ss.length + 1 = rs.length := by lia
        refine ⟨hlen, ?_⟩
        have hcenter : d - 2 * γ.natDegree =
            (d + 1 - 2 * δ.natDegree) + 1 := by
          lia
        rw [hcenter] at hfull
        exact (listInterlaces_reciprocalCenterRoots_succ_iff
          (d + 1 - 2 * δ.natDegree) hss hrs hlen).1 hfull
    have hγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0
    have hδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0
    refine ⟨hγrr.1, hδrr.1, ss.map gammaRootMap, rs.map gammaRootMap,
      ?_, ?_, coe_map_gammaRootMap_preferredRoots hγdeg hγ hγneg,
      coe_map_gammaRootMap_preferredRoots hδdeg hδ hδneg, ?_⟩
    · exact map_gammaRootMap_preferredRoots_pairwise d γ
    · exact map_gammaRootMap_preferredRoots_pairwise (d + 1) δ
    · rcases hpreferred with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
      · left
        refine ⟨by simpa using hlen, ?_⟩
        apply (listInterlaces_iff_interleaves_of_length (by simpa using hlen)).2
        apply (interleaves_map_gammaRootMap_iff hss hrs).2
        exact (listInterlaces_iff_interleaves_of_length hlen).1 hint
      · right
        refine ⟨by simpa using hlen, ?_⟩
        apply (listAlternates_iff_interleaves_of_length (by simpa using hlen)).2
        apply (interleaves_map_gammaRootMap_iff hrs hss).2
        exact (listAlternates_iff_interleaves_of_length hlen).1 halt
  · intro hprec
    have hγneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hγnn hγ0
    have hδneg := roots_neg_of_nonnegCoeffs_of_coeff_zero_ne hδnn hδ0
    have hsslen : ss.length = γ.natDegree :=
      length_preferredRoots hγdeg hγ hprec.1.2 hγneg
    have hrslen : rs.length = δ.natDegree :=
      length_preferredRoots hδdeg hδ hprec.2.1.2 hδneg
    have hsorted := hprec.sorted_roots_shape
    rw [sort_roots_eq_map_gammaRootMap_preferredRoots hγdeg hγ hγneg,
      sort_roots_eq_map_gammaRootMap_preferredRoots hδdeg hδ hδneg] at hsorted
    have hpreferred :
        ((ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
          (ss.length = rs.length ∧ ListAlternates ss rs)) := by
      rcases hsorted with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
      · left
        have hlen' : ss.length + 1 = rs.length := by simpa using hlen
        refine ⟨hlen', ?_⟩
        apply (listInterlaces_iff_interleaves_of_length hlen').2
        apply (interleaves_map_gammaRootMap_iff hss hrs).1
        exact (listInterlaces_iff_interleaves_of_length hlen).1 hint
      · right
        have hlen' : ss.length = rs.length := by simpa using hlen
        refine ⟨hlen', ?_⟩
        apply (listAlternates_iff_interleaves_of_length hlen').2
        apply (interleaves_map_gammaRootMap_iff hrs hss).1
        exact (listAlternates_iff_interleaves_of_length hlen).1 halt
    have hTγrr :=
      isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
        hγdeg hγ hprec.1.2 hγnn
    have hTδrr :=
      isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
        hδdeg hδ hprec.2.1.2 hδnn
    rcases hpreferred with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · have hcenter : d - 2 * γ.natDegree =
          (d + 1 - 2 * δ.natDegree) + 1 := by
        rw [hsslen, hrslen] at hlen
        lia
      have hfull :
          ListInterlaces
            (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
        rw [hcenter]
        exact (listInterlaces_reciprocalCenterRoots_succ_iff
          (d + 1 - 2 * δ.natDegree) hss hrs hlen).2 hint
      have hfull_len :
          (reciprocalCenterRoots (d - 2 * γ.natDegree) ss).length + 1 =
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs).length := by
        simp [reciprocalCenterRoots, hsslen, hrslen]
        lia
      have hi := (listInterlaces_iff_interleaves_of_length hfull_len).1 hfull
      refine ⟨hTγrr, hTδrr,
        reciprocalCenterRoots (d - 2 * γ.natDegree) ss,
        reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs,
        hi.pairwise_left, hi.pairwise_right,
        coe_reciprocalCenterRoots_eq_roots hγdeg hγ hTγneg,
        coe_reciprocalCenterRoots_eq_roots hδdeg hδ hTδneg,
        Or.inl ⟨hfull_len, hfull⟩⟩
    · have hcenter : d + 1 - 2 * δ.natDegree =
          (d - 2 * γ.natDegree) + 1 := by
        rw [hsslen, hrslen] at hlen
        lia
      have hfull :
          ListInterlaces
            (reciprocalCenterRoots (d - 2 * γ.natDegree) ss)
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs) := by
        rw [hcenter]
        exact (listInterlaces_reciprocalCenterRoots_same_iff
          (d - 2 * γ.natDegree) hss hrs hlen).2 halt
      have hfull_len :
          (reciprocalCenterRoots (d - 2 * γ.natDegree) ss).length + 1 =
            (reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs).length := by
        simp [reciprocalCenterRoots, hsslen, hrslen]
        lia
      have hi := (listInterlaces_iff_interleaves_of_length hfull_len).1 hfull
      refine ⟨hTγrr, hTδrr,
        reciprocalCenterRoots (d - 2 * γ.natDegree) ss,
        reciprocalCenterRoots (d + 1 - 2 * δ.natDegree) rs,
        hi.pairwise_left, hi.pairwise_right,
        coe_reciprocalCenterRoots_eq_roots hγdeg hγ hTγneg,
        coe_reciprocalCenterRoots_eq_roots hδdeg hδ hTδneg,
        Or.inl ⟨hfull_len, hfull⟩⟩

end RealRooted
