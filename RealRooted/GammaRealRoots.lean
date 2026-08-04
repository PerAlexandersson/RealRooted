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
    _ = gammaTransform d γ + gammaTransform d δ := by
          simp [gammaTransform, Finset.sum_add_distrib]

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
          _ ≤ k + m := by
              simp_all
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
        = IdTransform (i + (d - i)) (gammaBasisTerm d i) := by
            lia
    _ = IdTransform (i + (d - i)) (X ^ i * ((X + 1 : ℝ[X]) ^ n)) := by
          lia
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
    _ = (X + 1) * gammaTransform (2 * m) γ := by
          simp [gammaTransform, hhalf_even]

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
            gammaTransform ((d + 2 * k) + 2) γ := by congr 1 <;> lia
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
          gammaTransform (2 * n + 2 * (m - n)) γ := by congr 1 <;> lia
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
        C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i := by
          rw [Finset.mul_sum]
    _ = (X + 1) * gammaTransform (2 * m + 1) γ := by
          simp [gammaTransform, hhalf_odd]
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
  have hlinear : (X + 1 : ℝ[X]) = X - C (-1) := by ring
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

/-- The gamma root map identifies a nonzero real number with its reciprocal. -/
lemma gammaRootMap_inv {x : ℝ} (hx : x ≠ 0) :
    gammaRootMap x⁻¹ = gammaRootMap x := by
  by_cases h1x : 1 + x = 0
  · have hxneg : x = -1 := by linarith
    simp [gammaRootMap, hxneg]
  · unfold gammaRootMap
    field_simp [hx, h1x]
    ring

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
        = γ.coeff k * x ^ k * (x + 1) ^ (d - 2 * k) := by
            simp [gammaBasisTerm, mul_assoc]
    _ = γ.coeff k * x ^ k * (1 + x) ^ (d - 2 * k) := by
          grind
    _ = γ.coeff k * (x ^ k * (1 + x) ^ (d - 2 * k)) := by
          grind
    _ = γ.coeff k * ((1 + x) ^ d * (x / (1 + x) ^ 2) ^ k) := by
          have hterm :
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k = x ^ k * (1 + x) ^ (d - 2 * k) := by
            calc
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k
                  = (1 + x) ^ d * (x ^ k * (((1 + x) ^ 2) ^ k)⁻¹) := by
                      rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * (((1 + x) ^ 2) ^ k)⁻¹) := by grind
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ (2 * k))⁻¹) := by
                    rw [pow_mul]
              _ = x ^ k * (1 + x) ^ (d - 2 * k) := by
                    rw [← pow_sub₀ (1 + x) h1x_ne h2k_le]
          lia
    _ = (1 + x) ^ d * (γ.coeff k * (x / (1 + x) ^ 2) ^ k) := by
          ring

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
    _ = (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by
          grind

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
        have hq_dvd : gammaTransform (2 * ζ.natDegree) ζ ∣ gammaTransform (2 * n) δ := by
          simp_all
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
            _ = 1 + ε.natDegree := by
                  rw [natDegree_mul (X_sub_C_ne_zero y) hε0, natDegree_X_sub_C]
            _ = ε.natDegree + 1 := by lia
        have hεdeg_lt : ε.natDegree < n := by lia
        have hq_eq :
            gammaTransform (2 * n) δ =
              (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) ((X - C y) * ε) := by
              lia
            _ = gammaTransform (2 * ε.natDegree + 2) ((X - C y) * ε) := by grind
            _ = (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε :=
                  gammaTransform_X_sub_C_mul_two (γ := ε) (by lia) y
        have hq0 : gammaTransform (2 * ε.natDegree) ε ≠ 0 := by simp_all
        have hq_dvd : gammaTransform (2 * ε.natDegree) ε ∣ gammaTransform (2 * n) δ := by
          simp_all
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
            = gammaTransform (2 * (m + k) + 2) γ := by
                lia
        _ = (X + 1) ^ 2 * gammaTransform (2 * (m + k)) γ := by
              simpa using gammaTransform_pad_two (d := 2 * (m + k)) (γ := γ) hstep
        _ = (X + 1) ^ 2 * ((X + 1) ^ (2 * k) * gammaTransform (2 * m) γ) := by
              lia
        _ = ((X + 1) ^ 2 * (X + 1) ^ (2 * k)) * gammaTransform (2 * m) γ := by
              grind
        _ = (X + 1) ^ (2 + 2 * k) * gammaTransform (2 * m) γ := by
              grind
        _ = (X + 1) ^ (2 * (k + 1)) * gammaTransform (2 * m) γ := by
              lia

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
      _ = (X + 1) * ((X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ) := by
            lia
      _ = (X + 1) ^ (1 + 2 * (n - m)) * gammaTransform (2 * m) γ := by
            grind
      _ = (X + 1) ^ (d - 2 * m) * gammaTransform (2 * m) γ := by
            lia
      _ = (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by
            lia

lemma gammaTransform_minimal_dvd {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    gammaTransform (2 * γ.natDegree) γ ∣ gammaTransform d γ := by
  refine ⟨(X + 1) ^ (d - 2 * γ.natDegree), ?_⟩
  calc
    gammaTransform d γ =
        (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ :=
      gammaTransform_pad_to_minimal (d := d) (γ := γ) hγdeg
    _ = gammaTransform (2 * γ.natDegree) γ * (X + 1) ^ (d - 2 * γ.natDegree) := by
          ring

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
end RealRooted
