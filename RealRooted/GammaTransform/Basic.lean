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

/-- The gamma transform distributes over a finite sum. -/
theorem gammaTransform_finset_sum {ι : Type*} (d : ℕ) (s : Finset ι)
    (f : ι → ℝ[X]) :
    gammaTransform d (∑ i ∈ s, f i) = ∑ i ∈ s, gammaTransform d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert, hi, ih]

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

/-- A scalar monomial in the ambient gamma range maps to its basis term. -/
theorem gammaTransform_C_mul_X_pow {D i : ℕ} (a : ℝ)
    (hi : i ≤ D / 2) :
    gammaTransform D (C a * X ^ i) = C a * gammaBasisTerm D i := by
  rw [C_mul_X_pow_eq_monomial, gammaTransform_monomial, if_pos hi]

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

lemma natDegree_gammaTransform_le (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).natDegree ≤ d := by
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



end

end RealRooted
