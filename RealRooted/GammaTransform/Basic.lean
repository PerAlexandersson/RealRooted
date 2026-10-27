module

public import RealRooted.SymmetricDecomposition
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Gamma transforms and real-rootedness

This file packages the univariate gamma transform used for symmetric
decompositions and proves real-rootedness criteria for the transformed
polynomials.
-/

@[expose] public section

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
  simp only [gammaTransform, coeff_add, C_add, add_mul, Finset.sum_add_distrib]

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
  · rw [ite_eq_left h]
    unfold gammaTransform
    rw [Finset.sum_eq_single n]
    · simp
    · intro k _ hkn
      simp [coeff_monomial, hkn.symm]
    · simp_all
  · rw [ite_eq_right h]
    unfold gammaTransform
    apply Finset.sum_eq_zero
    intro k hk
    have hk_le : k ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnk : n ≠ k := by lia
    simp [coeff_monomial, hnk]

/-- A scalar monomial in the ambient gamma range maps to its basis term. -/
theorem gammaTransform_C_mul_X_pow {D i : ℕ} (a : ℝ)
    (hi : i ≤ D / 2) :
    gammaTransform D (C a * X ^ i) = C a * gammaBasisTerm D i := by
  rw [C_mul_X_pow_eq_monomial, gammaTransform_monomial, ite_eq_left hi]

lemma idTransform_X_add_one :
    idTransform 1 (X + 1 : ℝ[X]) = X + 1 := by
  simp [idTransform, add_comm]

lemma idTransform_raise {m k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ m) :
    idTransform (m + k) p = X ^ k * idTransform m p := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by lia,
        idTransform_succ (hp.trans (Nat.le_add_right _ _)), ih, pow_succ']
      ring

lemma idTransform_X_pow_mul {m k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ m) :
    idTransform (k + m) (X ^ k * p) = idTransform m p := by
  induction k with
  | zero =>
      lia
  | succ k ih =>
      have hkdeg : (X ^ k * p).natDegree ≤ k + m := by
        calc
          (X ^ k * p).natDegree ≤ (X ^ k).natDegree + p.natDegree := Polynomial.natDegree_mul_le
          _ ≤ k + m := by simp_all
      calc
        idTransform (k.succ + m) (X ^ k.succ * p) = idTransform (k + m) (X ^ k * p) := by
          simpa [pow_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc] using
            (idTransform_X_mul_succ (d := k + m) (p := X ^ k * p) hkdeg)
        _ = idTransform m p := ih

lemma idTransform_X_add_one_pow (n : ℕ) :
    idTransform n ((X + 1 : ℝ[X]) ^ n) = (X + 1) ^ n := by
  ext k
  by_cases hk : k ≤ n
  · rw [idTransform, Polynomial.coeff_reflect, Polynomial.revAt_le hk]
    simp [Polynomial.coeff_X_add_one_pow, Nat.choose_symm hk]
  · have hkn : n < k := lt_of_not_ge hk
    rw [idTransform, Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hkn]

lemma idTransform_gammaBasisTerm (d i : ℕ) (hi : 2 * i ≤ d) :
    idTransform d (gammaBasisTerm d i) = gammaBasisTerm d i := by
  let n := d - 2 * i
  have hd_eq : d = i + (d - i) := by lia
  have hterm :
      gammaBasisTerm d i = X ^ i * ((X + 1 : ℝ[X]) ^ n) := by
    simp [gammaBasisTerm, n]
  have hqdeg0 : ((X + 1 : ℝ[X]) ^ n).natDegree ≤ n := natDegree_X_add_one_pow_le n
  have hqdeg : ((X + 1 : ℝ[X]) ^ n).natDegree ≤ d - i := by lia
  calc
    idTransform d (gammaBasisTerm d i)
        = idTransform (i + (d - i)) (gammaBasisTerm d i) := by lia
    _ = idTransform (i + (d - i)) (X ^ i * ((X + 1 : ℝ[X]) ^ n)) := by lia
    _ = idTransform (d - i) ((X + 1 : ℝ[X]) ^ n) :=
          idTransform_X_pow_mul (m := d - i) (k := i) hqdeg
    _ = X ^ i * idTransform n ((X + 1 : ℝ[X]) ^ n) := by
          rw [show d - i = n + i by
            lia]
          exact idTransform_raise (m := n) (k := i) hqdeg0
    _ = X ^ i * ((X + 1 : ℝ[X]) ^ n) := by rw [idTransform_X_add_one_pow]
    _ = gammaBasisTerm d i := by lia

lemma idTransform_finsetSum {ι : Type} (d : ℕ) (s : Finset ι)
    (f : ι → ℝ[X]) :
    idTransform d (∑ i ∈ s, f i) = ∑ i ∈ s, idTransform d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      simp [Finset.sum_insert, hi, idTransform_add, ih]

lemma gammaTransform_fixed (d : ℕ) (γ : ℝ[X]) :
    idTransform d (gammaTransform d γ) = gammaTransform d γ := by
  classical
  unfold gammaTransform
  rw [idTransform_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h2i : 2 * i ≤ d := by lia
  rw [idTransform, Polynomial.reflect_C_mul]
  simpa [idTransform] using
    congrArg (fun p => C (γ.coeff i) * p) (idTransform_gammaBasisTerm d i h2i)

lemma hasNonnegCoeffs_gammaBasisTerm (d i : ℕ) :
    HasNonnegCoeffs (gammaBasisTerm d i) := by
  unfold gammaBasisTerm
  exact (hasNonnegCoeffs_X.pow i).mul (hasNonnegCoeffs_X_add_one.pow (d - 2 * i))

/-- The gamma transform preserves coefficientwise nonnegativity. -/
lemma hasNonnegCoeffs_gammaTransform {d : ℕ} {γ : ℝ[X]} (hγ : HasNonnegCoeffs γ) :
    HasNonnegCoeffs (gammaTransform d γ) := by
  unfold gammaTransform
  apply hasNonnegCoeffs_finsetSum
  intro i _
  exact hasNonnegCoeffs_C_mul (hγ i) (hasNonnegCoeffs_gammaBasisTerm d i)

/-- A positive constant gamma coefficient makes every coefficient in the
ambient degree box strictly positive. -/
theorem coeff_gammaTransform_pos_of_nonneg_of_coeff_zero_pos
    {d : ℕ} {γ : ℝ[X]} (hγ : HasNonnegCoeffs γ) (hγ0 : 0 < γ.coeff 0)
    {k : ℕ} (hk : k ≤ d) : 0 < (gammaTransform d γ).coeff k := by
  classical
  unfold gammaTransform
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_pos'
  · intro i hi
    exact (hasNonnegCoeffs_C_mul (hγ i)
      (hasNonnegCoeffs_gammaBasisTerm d i)) k
  · refine ⟨0, by simp, ?_⟩
    simp only [gammaBasisTerm_zero, coeff_C_mul]
    rw [show (X + 1 : ℝ[X]) = 1 + X by ring, Polynomial.coeff_one_add_X_pow]
    exact mul_pos hγ0 (by exact_mod_cast Nat.choose_pos hk)

lemma isRealRooted_X_add_one_pow (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n ≠ 0 ∧ ((X + 1 : ℝ[X]) ^ n).Splits) :=
  ⟨pow_ne_zero n (X_add_C_ne_zero 1),
    by simpa [sub_eq_add_neg] using
      (Polynomial.Splits.X_sub_C (-1 : ℝ)).pow n⟩

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

/-- If `γ` fits the ambient degree `d`, increasing that degree by two
multiplies its gamma transform by `(X + 1) ^ 2`. -/
lemma gammaTransform_pad_two {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 2) γ = (X + 1) ^ 2 * gammaTransform d γ := by
  unfold gammaTransform
  have hhalf : (d + 2) / 2 + 1 = d / 2 + 2 := by lia
  have htop : γ.coeff (d / 2 + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hγ (Nat.lt_succ_self _))
  rw [hhalf, Finset.sum_range_succ, htop]
  simp only [map_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : d + 2 - 2 * i = (d - 2 * i) + 2 := by lia
  rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_add]
  ring

lemma gammaTransform_odd (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * m + 1) γ = (X + 1) * gammaTransform (2 * m) γ := by
  have hhalf_odd : (2 * m + 1) / 2 = m := by lia
  have hhalf_even : (2 * m) / 2 = m := by lia
  unfold gammaTransform
  rw [hhalf_odd, hhalf_even, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : 2 * m + 1 - 2 * i = (2 * m - 2 * i) + 1 := by lia
  rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_succ]
  ring

/-- Repeated source-degree padding factors off two copies of `X + 1` at each
step. -/
lemma gammaTransform_add_two_mul (d k : ℕ) {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 2 * k) γ =
      (X + 1) ^ (2 * k) * gammaTransform d γ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 by lia,
        gammaTransform_pad_two (by lia), ih,
        show 2 * (k + 1) = 2 + 2 * k by lia, pow_add]
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
    rw [hd, show 2 * m = 2 * n + 2 * (m - n) by lia, hiter]
    congr 2
    lia
  · have hd : d = 2 * m + 1 := by dsimp [m]; lia
    rw [hd, gammaTransform_odd, show 2 * m = 2 * n + 2 * (m - n) by lia, hiter,
      show 2 * n + 2 * (m - n) + 1 - 2 * n = 2 * (m - n) + 1 by lia, pow_succ']
    ring

lemma gammaTransform_even_succ (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * (m + 1)) γ =
      (X + 1) * gammaTransform (2 * m + 1) γ + C (γ.coeff (m + 1)) * X ^ (m + 1) := by
  have hhalf_even : (2 * (m + 1)) / 2 = m + 1 := by lia
  have hhalf_odd : (2 * m + 1) / 2 = m := by lia
  unfold gammaTransform
  rw [hhalf_even, hhalf_odd, Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : 2 * (m + 1) - 2 * i = (2 * m + 1 - 2 * i) + 1 := by lia
    rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_succ]
    ring
  · simp [gammaBasisTerm]

/-- Increasing the ambient degree by one factors off one copy of `X + 1`
when the gamma polynomial fits the old degree box. -/
lemma gammaTransform_pad_one {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 1) γ = (X + 1) * gammaTransform d γ := by
  rcases Nat.mod_two_eq_zero_or_one d with heven | hodd
  · have hd : d = 2 * (d / 2) := by lia
    rw [hd]
    exact gammaTransform_odd (d / 2) γ
  · have hd : d = 2 * (d / 2) + 1 := by lia
    have hcoeff : γ.coeff (d / 2 + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by lia)
    rw [hd]
    have hs := gammaTransform_even_succ (d / 2) γ
    rw [hcoeff] at hs
    simp only [map_zero, zero_mul, add_zero] at hs
    have heq : 2 * (d / 2 + 1) = 2 * (d / 2) + 1 + 1 := by lia
    rw [← heq]
    exact hs

@[simp] lemma gammaTransform_odd_eval_neg_one (m : ℕ) (γ : ℝ[X]) :
    (gammaTransform (2 * m + 1) γ).eval (-1) = 0 := by
  rw [gammaTransform_odd]
  simp

lemma gammaTransform_even_eval_neg_one (m : ℕ) (γ : ℝ[X]) :
    (gammaTransform (2 * m) γ).eval (-1) = γ.coeff m * (-1) ^ m := by
  unfold gammaTransform
  have hhalf_even : (2 * m) / 2 = m := by lia
  rw [hhalf_even, Polynomial.eval_finsetSum, Finset.sum_eq_single m]
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
      have trunc_degree (p : ℝ[X]) (hp : p.natDegree ≤ m + 1) :
          (p - Polynomial.monomial (m + 1) (p.coeff (m + 1))).natDegree ≤ m := by
        refine natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro k hk
        by_cases hk_top : k = m + 1
        · simp_all
        · have hk_gt : m + 1 < k := by lia
          have hk_ne' : m + 1 ≠ k := by lia
          rw [coeff_sub,
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk_gt),
            Polynomial.coeff_monomial]
          simp [hk_ne']
      have hγ'_deg : γ'.natDegree ≤ m := by
        simpa [γ', c] using trunc_degree γ hγ
      have hδ'_deg : δ'.natDegree ≤ m := by
        simpa [δ', c, hcoeff_top] using trunc_degree δ hδ
      have transform_sub (p : ℝ[X]) (a : ℝ) :
          gammaTransform (2 * m) (p - Polynomial.monomial (m + 1) a) =
            gammaTransform (2 * m) p := by
        rw [sub_eq_add_neg, gammaTransform_add]
        rw [show -(Polynomial.monomial (m + 1) a) =
          C (-1) * Polynomial.monomial (m + 1) a by simp]
        rw [gammaTransform_C_mul]
        simp [gammaTransform_monomial]
      have hγsmall :
          gammaTransform (2 * m) γ' = gammaTransform (2 * m) γ := by
        simpa [γ', c] using transform_sub γ c
      have hδsmall :
          gammaTransform (2 * m) δ' = gammaTransform (2 * m) δ := by
        simpa [δ', c] using transform_sub δ c
      have hX1 : (X + 1 : ℝ[X]) ≠ 0 := by
        simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ))
      have hodd :
          gammaTransform (2 * m + 1) γ = gammaTransform (2 * m + 1) δ := by
        have hEq' :
            (X + 1) * gammaTransform (2 * m + 1) γ +
                C c * X ^ (m + 1) =
              (X + 1) * gammaTransform (2 * m + 1) δ +
                C c * X ^ (m + 1) := by
          simpa [gammaTransform_even_succ, hcoeff_top, c] using hEq
        simp_all
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

/-- The gamma transform is injective on polynomials whose degrees are at most
half the ambient degree. -/
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

/-- Within the ambient degree bound, a gamma transform vanishes exactly when
its gamma polynomial vanishes. -/
theorem gammaTransform_eq_zero_iff_of_natDegree_le {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform d γ = 0 ↔ γ = 0 := by
  constructor
  · intro hzero
    exact gammaTransform_injective_of_natDegree_le hγ (by simp) (by simpa using hzero)
  · rintro rfl
    simp

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
  simpa [idTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using hcoeff.symm



end

end RealRooted
