import RealRooted.SymmetricDecomposition
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Gamma transforms and real-rootedness

This file packages the univariate gamma transform used for symmetric
decompositions and proves real-rootedness criteria for the transformed
polynomials.
-/

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

set_option linter.flexible false in
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
  unfold gammaTransform
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp [gammaBasisTerm]

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
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_C_mul, C_mul]
  ring

lemma gammaTransform_monomial (d n : ℕ) (a : ℝ) :
    gammaTransform d (monomial n a) =
      if _h : n ≤ d / 2 then C a * gammaBasisTerm d n else 0 := by
  by_cases h : n ≤ d / 2
  · have hn : n ∈ Finset.range (d / 2 + 1) := by
      simpa using h
    unfold gammaTransform
    rw [Finset.sum_eq_single n]
    · have hcoeff : (monomial n a).coeff n = a := by
        simp
      rw [hcoeff]
      simp [h]
    · intro k hk hkn
      have hcoeff : (monomial n a).coeff k = 0 := by
        simp [coeff_monomial, mt Eq.symm hkn]
      rw [hcoeff]
      simp
    · intro hnot
      exact (hnot hn).elim
  · unfold gammaTransform
    have hsum :
        ∑ k ∈ Finset.range (d / 2 + 1),
          C ((monomial n a).coeff k) * gammaBasisTerm d k = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hklt : k < d / 2 + 1 := Finset.mem_range.mp hk
      have hkn : k ≠ n := by
        intro hEq
        exact h (Nat.lt_succ_iff.mp (hEq ▸ hklt))
      have hcoeff : (monomial n a).coeff k = 0 := by
        simp [coeff_monomial, mt Eq.symm hkn]
      rw [hcoeff]
      simp
    simpa [h] using hsum

@[simp] lemma IdTransform_X_add_one :
    IdTransform 1 (X + 1 : ℝ[X]) = X + 1 := by
  simp [IdTransform, add_comm]

lemma natDegree_X_add_one_pow_le (n : ℕ) :
    ((X + 1 : ℝ[X]) ^ n).natDegree ≤ n := by
  have hX1 : (X + 1 : ℝ[X]).natDegree ≤ 1 := by
    rw [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp, Polynomial.natDegree_X_add_C]
  simpa [one_mul] using (Polynomial.natDegree_pow_le_of_le n hX1)

lemma IdTransform_raise {m k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ m) :
    IdTransform (m + k) p = X ^ k * IdTransform m p := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hp' : p.natDegree ≤ m + k := le_trans hp (Nat.le_add_right _ _)
      calc
        IdTransform (m + (k + 1)) p = X * IdTransform (m + k) p := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (IdTransform_succ (d := m + k) (p := p) hp')
        _ = X * (X ^ k * IdTransform m p) := by rw [ih]
        _ = (X * X ^ k) * IdTransform m p := by rw [mul_assoc]
        _ = X ^ (k + 1) * IdTransform m p := by rw [pow_succ']

lemma IdTransform_X_pow_mul {m k : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ m) :
    IdTransform (k + m) (X ^ k * p) = IdTransform m p := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hkdeg : (X ^ k * p).natDegree ≤ k + m := by
        calc
          (X ^ k * p).natDegree ≤ (X ^ k).natDegree + p.natDegree := Polynomial.natDegree_mul_le
          _ ≤ k + m := by
              gcongr
              exact Polynomial.natDegree_X_pow_le k
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
    simp [Polynomial.coeff_X_add_one_pow, hk, Nat.choose_symm hk]
  · have hkn : n < k := lt_of_not_ge hk
    rw [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hkn]

lemma IdTransform_gammaBasisTerm (d i : ℕ) (hi : 2 * i ≤ d) :
    IdTransform d (gammaBasisTerm d i) = gammaBasisTerm d i := by
  let n := d - 2 * i
  have hd_eq : d = i + (d - i) := by omega
  have hterm :
      gammaBasisTerm d i = X ^ i * ((X + 1 : ℝ[X]) ^ n) := by
    simp [gammaBasisTerm, n]
  have hqdeg0 : ((X + 1 : ℝ[X]) ^ n).natDegree ≤ n := natDegree_X_add_one_pow_le n
  have hqdeg : ((X + 1 : ℝ[X]) ^ n).natDegree ≤ d - i := by
    rw [show d - i = n + i by
      dsimp [n]
      omega]
    exact le_trans hqdeg0 (Nat.le_add_right _ _)
  calc
    IdTransform d (gammaBasisTerm d i)
        = IdTransform (i + (d - i)) (gammaBasisTerm d i) := by
            simpa using congrArg (fun N => IdTransform N (gammaBasisTerm d i)) hd_eq
    _ = IdTransform (i + (d - i)) (X ^ i * ((X + 1 : ℝ[X]) ^ n)) := by
          rw [hterm]
    _ = IdTransform (d - i) ((X + 1 : ℝ[X]) ^ n) := by
          exact IdTransform_X_pow_mul (m := d - i) (k := i) hqdeg
    _ = X ^ i * IdTransform n ((X + 1 : ℝ[X]) ^ n) := by
          rw [show d - i = n + i by
            dsimp [n]
            omega]
          exact IdTransform_raise (m := n) (k := i) hqdeg0
    _ = X ^ i * ((X + 1 : ℝ[X]) ^ n) := by rw [IdTransform_X_add_one_pow]
    _ = gammaBasisTerm d i := by simp [gammaBasisTerm, n]

lemma IdTransform_finset_sum {ι : Type} (d : ℕ) (s : Finset ι)
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
  rw [IdTransform_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h2i : 2 * i ≤ d := by omega
  rw [IdTransform, Polynomial.reflect_C_mul]
  simpa [IdTransform] using
    congrArg (fun p => C (γ.coeff i) * p) (IdTransform_gammaBasisTerm d i h2i)

lemma hasNonnegCoeffs_gammaBasisTerm (d i : ℕ) :
    HasNonnegCoeffs (gammaBasisTerm d i) := by
  unfold gammaBasisTerm
  exact (HasNonnegCoeffs.pow hasNonnegCoeffs_X i).mul
    (HasNonnegCoeffs.pow hasNonnegCoeffs_X_add_one (d - 2 * i))

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

lemma isRealRooted_X_add_one_pow : ∀ n : ℕ, IsRealRooted (((X + 1 : ℝ[X]) ^ n))
  | 0 => by
      simpa using isRealRooted_of_deg_zero (p := (1 : ℝ[X])) one_ne_zero (by simp)
  | n + 1 => by
      simpa [pow_succ, mul_comm] using
        isRealRooted_mul (isRealRooted_X_sub_C (-1 : ℝ)) (isRealRooted_X_add_one_pow n)

lemma gammaBasisTerm_succ_succ (d i : ℕ) :
    gammaBasisTerm (d + 2) (i + 1) = X * gammaBasisTerm d i := by
  unfold gammaBasisTerm
  have hsub : d + 2 - 2 * (i + 1) = d - 2 * i := by omega
  rw [hsub]
  simp [pow_succ', mul_assoc]

lemma gammaTransform_X_mul_two (d : ℕ) (γ : ℝ[X]) :
    gammaTransform (d + 2) (X * γ) = X * gammaTransform d γ := by
  refine Polynomial.induction_on' γ ?_ ?_
  · intro p q hp hq
    rw [show X * (p + q) = X * p + X * q by ring]
    rw [gammaTransform_add, gammaTransform_add, hp, hq]
    ring
  · intro n a
    by_cases h : n ≤ d / 2
    · have hs : n + 1 ≤ (d + 2) / 2 := by
        omega
      simp [Polynomial.X_mul_monomial, gammaTransform_monomial, h, hs,
        gammaBasisTerm_succ_succ, mul_assoc, mul_left_comm, mul_comm]
    · have hs : ¬ n + 1 ≤ (d + 2) / 2 := by
        omega
      simp [Polynomial.X_mul_monomial, gammaTransform_monomial, h, hs]

lemma gammaTransform_pad_two {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform (d + 2) γ = (X + 1) ^ 2 * gammaTransform d γ := by
  unfold gammaTransform
  have hhalf : (d + 2) / 2 + 1 = d / 2 + 2 := by omega
  rw [hhalf, Finset.sum_range_succ]
  have htop : γ.coeff (d / 2 + 1) = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hγ (Nat.lt_succ_self _))
  rw [htop]
  simp
  calc
    ∑ i ∈ Finset.range (d / 2 + 1), C (γ.coeff i) * gammaBasisTerm (d + 2) i
      = ∑ i ∈ Finset.range (d / 2 + 1), (X + 1) ^ 2 * (C (γ.coeff i) * gammaBasisTerm d i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : d + 2 - 2 * i = (d - 2 * i) + 2 := by omega
          rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_add]
          ring
    _ = (X + 1) ^ 2 * ∑ i ∈ Finset.range (d / 2 + 1), C (γ.coeff i) * gammaBasisTerm d i := by
          rw [Finset.mul_sum]
    _ = (X + 1) ^ 2 * gammaTransform d γ := by simp [gammaTransform]

lemma gammaTransform_odd (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * m + 1) γ = (X + 1) * gammaTransform (2 * m) γ := by
  have hhalf_odd : (2 * m + 1) / 2 = m := by omega
  have hhalf_even : (2 * m) / 2 = m := by omega
  calc
    gammaTransform (2 * m + 1) γ
      = ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i := by
          simp [gammaTransform, hhalf_odd]
    _ = ∑ i ∈ Finset.range (m + 1), (X + 1) * (C (γ.coeff i) * gammaBasisTerm (2 * m) i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : 2 * m + 1 - 2 * i = (2 * m - 2 * i) + 1 := by omega
          rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_succ]
          ring
    _ = (X + 1) * ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * m) i := by
          rw [Finset.mul_sum]
    _ = (X + 1) * gammaTransform (2 * m) γ := by
          simp [gammaTransform, hhalf_even]

lemma gammaTransform_even_succ (m : ℕ) (γ : ℝ[X]) :
    gammaTransform (2 * (m + 1)) γ =
      (X + 1) * gammaTransform (2 * m + 1) γ + C (γ.coeff (m + 1)) * X ^ (m + 1) := by
  have hhalf_even : (2 * (m + 1)) / 2 = m + 1 := by omega
  have hhalf_odd : (2 * m + 1) / 2 = m := by omega
  have hprefix :
      ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * (m + 1)) i
        = (X + 1) * gammaTransform (2 * m + 1) γ := by
    calc
      ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * (m + 1)) i
      = ∑ i ∈ Finset.range (m + 1), (X + 1) * (C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hsub : 2 * (m + 1) - 2 * i = (2 * m + 1 - 2 * i) + 1 := by omega
          rw [gammaBasisTerm, gammaBasisTerm, hsub, pow_succ]
          ring
    _ = (X + 1) * ∑ i ∈ Finset.range (m + 1), C (γ.coeff i) * gammaBasisTerm (2 * m + 1) i := by
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
  have hhalf_even : (2 * m) / 2 = m := by omega
  rw [hhalf_even]
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single m]
  · simp [gammaBasisTerm]
  · intro i hi him
    have hi_lt : i < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) him
    have hpow_pos : 0 < 2 * m - 2 * i := by omega
    simp [gammaBasisTerm, hpow_pos.ne']
  · intro hm
    exact (hm (by simp)).elim

lemma gammaTransform_even_isRoot_neg_one_iff (m : ℕ) (γ : ℝ[X]) :
    (gammaTransform (2 * m) γ).IsRoot (-1) ↔ γ.coeff m = 0 := by
  rw [Polynomial.IsRoot.def, gammaTransform_even_eval_neg_one]
  have hpow_ne : (-1 : ℝ) ^ m ≠ 0 := by simp
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right hpow_ne
  · intro h
    simp [h]

lemma gammaTransform_even_succ_of_coeff_zero (m : ℕ) {γ : ℝ[X]}
    (hcoeff : γ.coeff (m + 1) = 0) :
    gammaTransform (2 * (m + 1)) γ = (X + 1) ^ 2 * gammaTransform (2 * m) γ := by
  rw [gammaTransform_even_succ, gammaTransform_odd]
  simp [hcoeff]
  ring

lemma gammaTransform_even_succ_of_isRoot_neg_one (m : ℕ) {γ : ℝ[X]}
    (hroot : (gammaTransform (2 * (m + 1)) γ).IsRoot (-1)) :
    gammaTransform (2 * (m + 1)) γ = (X + 1) ^ 2 * gammaTransform (2 * m) γ := by
  exact gammaTransform_even_succ_of_coeff_zero m
    ((gammaTransform_even_isRoot_neg_one_iff (m + 1) γ).mp hroot)

lemma gammaTransform_even_injective :
    ∀ m : ℕ, ∀ {γ δ : ℝ[X]},
      γ.natDegree ≤ m →
      δ.natDegree ≤ m →
      gammaTransform (2 * m) γ = gammaTransform (2 * m) δ →
      γ = δ
  | 0, γ, δ, hγ, hδ, hEq => by
      have hγC : γ = C (γ.coeff 0) := by
        simpa using (Polynomial.eq_C_of_natDegree_le_zero hγ)
      have hδC : δ = C (δ.coeff 0) := by
        simpa using (Polynomial.eq_C_of_natDegree_le_zero hδ)
      have hcoeff : γ.coeff 0 = δ.coeff 0 := by
        have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hEq
        simpa [gammaTransform, gammaBasisTerm] using h0
      rw [hγC, hδC, hcoeff]
  | m + 1, γ, δ, hγ, hδ, hEq => by
      have hcoeff_top : γ.coeff (m + 1) = δ.coeff (m + 1) := by
        have heval :
            (gammaTransform (2 * (m + 1)) γ).eval (-1) =
              (gammaTransform (2 * (m + 1)) δ).eval (-1) := by
          simpa using congrArg (fun p : ℝ[X] => p.eval (-1)) hEq
        have hγeval :
            (gammaTransform (2 * (m + 1)) γ).eval (-1) =
              γ.coeff (m + 1) * (-1) ^ (m + 1) := by
          simpa using gammaTransform_even_eval_neg_one (m + 1) γ
        have hδeval :
            (gammaTransform (2 * (m + 1)) δ).eval (-1) =
              δ.coeff (m + 1) * (-1) ^ (m + 1) := by
          simpa using gammaTransform_even_eval_neg_one (m + 1) δ
        rw [hγeval, hδeval] at heval
        exact mul_right_cancel₀ (by simp) heval
      let c : ℝ := γ.coeff (m + 1)
      let γ' : ℝ[X] := γ - Polynomial.monomial (m + 1) c
      let δ' : ℝ[X] := δ - Polynomial.monomial (m + 1) c
      have hγ'_deg : γ'.natDegree ≤ m := by
        refine natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro k hk
        dsimp [γ', c]
        by_cases hk_top : k = m + 1
        · subst hk_top
          rw [coeff_sub, Polynomial.coeff_monomial]
          simp
        · have hk_gt : m + 1 < k := by omega
          have hγk : γ.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hγ hk_gt)
          have hk_ne' : m + 1 ≠ k := by
            intro hEq
            exact hk_top hEq.symm
          rw [coeff_sub, hγk, Polynomial.coeff_monomial]
          simp [hk_ne']
      have hδ'_deg : δ'.natDegree ≤ m := by
        refine natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro k hk
        dsimp [δ', c]
        by_cases hk_top : k = m + 1
        · subst hk_top
          rw [coeff_sub, Polynomial.coeff_monomial]
          simp [hcoeff_top]
        · have hk_gt : m + 1 < k := by omega
          have hδk : δ.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hδ hk_gt)
          have hk_ne' : m + 1 ≠ k := by
            intro hEq
            exact hk_top hEq.symm
          rw [coeff_sub, hδk, Polynomial.coeff_monomial]
          simp [hk_ne']
      have hγsmall :
          gammaTransform (2 * m) γ' = gammaTransform (2 * m) γ := by
        dsimp [γ', c]
        rw [sub_eq_add_neg, gammaTransform_add]
        rw [show -(Polynomial.monomial (m + 1) (γ.coeff (m + 1))) =
              C (-1) * Polynomial.monomial (m + 1) (γ.coeff (m + 1)) by simp]
        rw [gammaTransform_C_mul]
        simp [gammaTransform_monomial, show ¬ (m + 1 ≤ (2 * m) / 2) by omega]
      have hδsmall :
          gammaTransform (2 * m) δ' = gammaTransform (2 * m) δ := by
        dsimp [δ', c]
        rw [sub_eq_add_neg, gammaTransform_add]
        rw [show -(Polynomial.monomial (m + 1) (γ.coeff (m + 1))) =
              C (-1) * Polynomial.monomial (m + 1) (γ.coeff (m + 1)) by simp]
        rw [gammaTransform_C_mul]
        simp [gammaTransform_monomial, show ¬ (m + 1 ≤ (2 * m) / 2) by omega]
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
        have hsub :=
          congrArg (fun q : ℝ[X] => q + -(C c * X ^ (m + 1))) hEq'
        have hmul :
            (X + 1) * gammaTransform (2 * m + 1) γ =
              (X + 1) * gammaTransform (2 * m + 1) δ := by
          simpa only [add_assoc, add_neg_cancel, add_zero] using hsub
        exact mul_left_cancel₀ hX1 hmul
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
      have hγdecomp : γ = γ' + Polynomial.monomial (m + 1) c := by
        dsimp [γ', c]
        simp [sub_eq_add_neg, add_assoc]
      have hδdecomp : δ = δ' + Polynomial.monomial (m + 1) c := by
        dsimp [δ', c]
        simp [sub_eq_add_neg, add_assoc]
      calc
        γ = γ' + Polynomial.monomial (m + 1) c := hγdecomp
        _ = δ' + Polynomial.monomial (m + 1) c := by rw [htrunc]
        _ = δ := hδdecomp.symm

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
  · have hd : d = 2 * (d / 2) := by omega
    have hEq' : gammaTransform (2 * (d / 2)) γ = gammaTransform (2 * (d / 2)) δ := by
      rw [← hd]
      exact hEq
    exact gammaTransform_even_injective (d / 2)
      hγ hδ hEq'
  · have hd : d = 2 * (d / 2) + 1 := by omega
    have hEq' : gammaTransform (2 * (d / 2) + 1) γ = gammaTransform (2 * (d / 2) + 1) δ := by
      rw [← hd]
      exact hEq
    exact gammaTransform_odd_injective (d / 2)
      hγ hδ hEq'

theorem gammaTransform_eq_zero_iff_of_natDegree_le {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) :
    gammaTransform d γ = 0 ↔ γ = 0 := by
  constructor
  · intro hzero
    exact gammaTransform_injective_of_natDegree_le hγ (by simp) (by simpa using hzero)
  · intro hzero
    simp [hzero]

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
    _ = i + ((X + 1 : ℝ[X]) ^ (d - 2 * i)).natDegree := by rw [hX]
    _ ≤ i + (d - 2 * i) := Nat.add_le_add_left hX1 i
    _ ≤ d := by omega

lemma natDegree_gammaTransform_le (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).natDegree ≤ d := by
  classical
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  unfold gammaTransform
  rw [Polynomial.finset_sum_coeff]
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
  rw [Polynomial.eval_finset_sum, Finset.sum_eq_single 0]
  · simp [gammaBasisTerm]
  · intro i hi hi0
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    simp [gammaBasisTerm, hi0, hi_pos.ne']
  · intro h0
    exact (h0 (by simp)).elim

@[simp] lemma coeff_zero_gammaTransform (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).coeff 0 = γ.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, gammaTransform_eval_zero,
    Polynomial.coeff_zero_eq_eval_zero]

@[simp] lemma coeff_ambient_gammaTransform (d : ℕ) (γ : ℝ[X]) :
    (gammaTransform d γ).coeff d = γ.coeff 0 := by
  have hfix := gammaTransform_fixed d γ
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff d) hfix
  simpa [IdTransform, Polynomial.coeff_reflect, Polynomial.revAt_zero] using hcoeff.symm

lemma eval_gammaTransform_eq_mul_eval_gammaUntransform {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) {x : ℝ} (hx : x ≠ -1) :
    (gammaTransform d γ).eval x = (1 + x) ^ d * γ.eval (x / (1 + x) ^ 2) := by
  have h1x_ne : 1 + x ≠ 0 := by
    intro h0
    apply hx
    linarith
  unfold gammaTransform
  rw [Polynomial.eval_finset_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hγdeg)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h2k_le : 2 * k ≤ d := by omega
  calc
    (C (γ.coeff k) * gammaBasisTerm d k).eval x
        = γ.coeff k * x ^ k * (x + 1) ^ (d - 2 * k) := by
            simp [gammaBasisTerm, mul_assoc]
    _ = γ.coeff k * x ^ k * (1 + x) ^ (d - 2 * k) := by
          rw [add_comm]
    _ = γ.coeff k * (x ^ k * (1 + x) ^ (d - 2 * k)) := by
          rw [mul_assoc]
    _ = γ.coeff k * ((1 + x) ^ d * (x / (1 + x) ^ 2) ^ k) := by
          have hterm :
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k = x ^ k * (1 + x) ^ (d - 2 * k) := by
            calc
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k
                  = (1 + x) ^ d * (x ^ k * (((1 + x) ^ 2) ^ k)⁻¹) := by
                      rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * (((1 + x) ^ 2) ^ k)⁻¹) := by ring
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ (2 * k))⁻¹) := by
                    rw [pow_mul]
              _ = x ^ k * (1 + x) ^ (d - 2 * k) := by
                    rw [← pow_sub₀ (1 + x) h1x_ne h2k_le]
          rw [← hterm]
    _ = (1 + x) ^ d * (γ.coeff k * (x / (1 + x) ^ 2) ^ k) := by
          ring

lemma gammaUntransform_nonpos {x : ℝ} (hx0 : x ≤ 0) (hx : x ≠ -1) :
    x / (1 + x) ^ 2 ≤ 0 := by
  have h1x_ne : 1 + x ≠ 0 := by
    intro h0
    apply hx
    linarith
  have hsq_pos : 0 < (1 + x) ^ 2 := by
    positivity
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
  rcases mul_eq_zero.mp hrpq with hpr | hqr
  · exact hp r ((mem_roots hp0).mpr hpr)
  · exact hq r ((mem_roots hq0).mpr hqr)

lemma hasRootsNonpos_X_sub_C {r : ℝ} (hr : r ≤ 0) :
    HasRootsNonpos (X - C r) := by
  intro s hs
  rw [roots_X_sub_C] at hs
  rcases Multiset.mem_singleton.mp hs with rfl
  exact hr

lemma isRoot_gamma_of_isRoot_gammaTransform {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) {x : ℝ} (hx : x ≠ -1)
    (hroot : (gammaTransform d γ).IsRoot x) :
    γ.IsRoot (x / (1 + x) ^ 2) := by
  rw [Polynomial.IsRoot.def] at hroot ⊢
  rw [eval_gammaTransform_eq_mul_eval_gammaUntransform hγdeg hx] at hroot
  have h1x_ne : 1 + x ≠ 0 := by
    intro h0
    apply hx
    linarith
  have hpow_ne : (1 + x) ^ d ≠ 0 := by
    exact pow_ne_zero _ h1x_ne
  exact (mul_eq_zero.mp hroot).resolve_left hpow_ne

lemma rootPullback_nonpos_of_gammaTransform {x : ℝ}
    (hx : x ≠ -1) (hx0 : x ≤ 0) :
    (x / (1 + x) ^ 2) ≤ 0 := by
  exact gammaUntransform_nonpos hx0 hx

lemma gammaTransform_X_sub_C_mul_two {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) (r : ℝ) :
    gammaTransform (d + 2) ((X - C r) * γ) =
      (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by
  have hmul : (X - C r) * γ = X * γ + C (-r) * γ := by
    simp [sub_eq_add_neg, add_mul]
  calc
    gammaTransform (d + 2) ((X - C r) * γ)
      = gammaTransform (d + 2) (X * γ + C (-r) * γ) := by rw [hmul]
    _ = gammaTransform (d + 2) (X * γ) + C (-r) * gammaTransform (d + 2) γ := by
          rw [gammaTransform_add, gammaTransform_C_mul]
    _ = X * gammaTransform d γ + C (-r) * ((X + 1) ^ 2 * gammaTransform d γ) := by
          rw [gammaTransform_X_mul_two, gammaTransform_pad_two hγ]
    _ = X * gammaTransform d γ - (C r * (X + 1) ^ 2) * gammaTransform d γ := by
          simp [sub_eq_add_neg, mul_assoc]
    _ = (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by
          rw [sub_mul]

lemma hasNonnegCoeffs_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    HasNonnegCoeffs (X - C r * (X + 1) ^ 2) := by
  have hneg : 0 ≤ -r := by linarith
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using
    hasNonnegCoeffs_X.add
      (nonnegCoeffs_C_mul hneg (HasNonnegCoeffs.pow hasNonnegCoeffs_X_add_one 2))

lemma isRealRooted_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    IsRealRooted (X - C r * (X + 1) ^ 2) := by
  by_cases hr0 : r = 0
  · subst hr0
    simpa using isRealRooted_X
  · set t : ℝ := -r with ht_def
    have hrlt : r < 0 := lt_of_le_of_ne hr hr0
    have ht_pos : 0 < t := by
      dsimp [t]
      linarith
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
                  have hpow0 : (((X + 1 : ℝ[X]) ^ 2).coeff (n + 3)) = 0 := by
                    apply Polynomial.coeff_eq_zero_of_natDegree_lt
                    exact lt_of_le_of_lt (natDegree_X_add_one_pow_le 2) (by omega)
                  simp [Polynomial.coeff_X_add_one_pow, coeff_X, coeff_one, hpow0]
    have hroots :
        (C t * X ^ 2 + C (2 * t + 1) * X + C t).roots =
          {(-(2 * t + 1) - Real.sqrt (t * 4 + 1)) / (2 * t),
            (-(2 * t + 1) + Real.sqrt (t * 4 + 1)) / (2 * t)} := by
      apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero' (a := t) (b := 2 * t + 1)
        (c := t) (ha := ne_of_gt ht_pos)).2
      constructor
      · field_simp [ht_pos.ne']
        ring
      · field_simp [ht_pos.ne']
        have hsq : (Real.sqrt (t * 4 + 1)) ^ 2 = t * 4 + 1 := by
          rw [Real.sq_sqrt]
          positivity
        calc
          (-(2 * t + 1) - Real.sqrt (t * 4 + 1)) *
              (-(2 * t + 1) + Real.sqrt (t * 4 + 1))
              = (2 * t + 1) ^ 2 - (Real.sqrt (t * 4 + 1)) ^ 2 := by ring
          _ = (2 * t + 1) ^ 2 - (t * 4 + 1) := by rw [hsq]
          _ = 2 ^ 2 * t ^ 2 := by ring
    rw [hpoly]
    refine ⟨?_, ?_⟩
    · intro hzero
      have hlead := congrArg Polynomial.leadingCoeff hzero
      rw [Polynomial.leadingCoeff_quadratic (ne_of_gt ht_pos),
        Polynomial.leadingCoeff_zero] at hlead
      exact (ne_of_gt ht_pos) hlead
    · rw [hroots, Polynomial.natDegree_quadratic (ne_of_gt ht_pos)]
      simp

lemma hasPosLeadingCoeff_of_X_sub_C_mul {q : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff ((X - C r) * q)) :
    HasPosLeadingCoeff q := by
  unfold HasPosLeadingCoeff at h ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using h

lemma hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
    {p q : ℝ[X]}
    (hp : IsRealRooted p) (hpnn : HasNonnegCoeffs p)
    (hq : IsRealRooted q) (hq_pos : HasPosLeadingCoeff q)
    (hqp : q ∣ p) :
    HasNonnegCoeffs q := by
  refine (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq).mpr ?_
  refine ⟨hq_pos, ?_⟩
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq.1).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact roots_nonpos_of_nonneg_coeffs hp hpnn r ((mem_roots hp.1).mpr hrp)

/-- The gamma transform preserves real-rootedness on nonnegative-coefficient
inputs whose degree fits the ambient floor `d / 2`. -/
theorem isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : IsRealRooted γ) (hγnn : HasNonnegCoeffs γ) :
    IsRealRooted (gammaTransform d γ) := by
  let P : ℕ → Prop := fun n =>
    ∀ d : ℕ, ∀ γ : ℝ[X],
      γ.natDegree = n →
      γ.natDegree ≤ d / 2 →
      IsRealRooted γ →
      HasNonnegCoeffs γ →
      IsRealRooted (gammaTransform d γ)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih d γ hγdeg_eq hbound hrr hnn
    by_cases hn0 : n = 0
    · have hγC : γ = C (γ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show γ.natDegree ≤ 0 by omega))
      rw [hγC]
      have hcoeff_ne : γ.coeff 0 ≠ 0 := by
        intro h0
        rw [hγC, h0] at hrr
        exact hrr.1 (by simp)
      have hgt :
          gammaTransform d (C (γ.coeff 0)) = C (γ.coeff 0) * (X + 1) ^ d := by
        simpa [gammaBasisTerm_zero] using
          (gammaTransform_monomial d 0 (γ.coeff 0))
      rw [hgt]
      exact isRealRooted_C_mul (isRealRooted_X_add_one_pow d) hcoeff_ne
    · have hroots_pos : 0 < γ.roots.card := by
        rw [hrr.2, hγdeg_eq]
        exact Nat.pos_of_ne_zero hn0
      obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hr_root : γ.IsRoot r := (mem_roots hrr.1).mp hr_mem
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
      have hq' : γ = (X - C r) * q := by
        simpa [mul_comm] using hq
      have hq_dvd : q ∣ γ := ⟨X - C r, by simpa [mul_comm] using hq⟩
      have hq_ne : q ≠ 0 := by
        intro hq0
        rw [hq0, mul_zero] at hq
        exact hrr.1 hq
      have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hrr hnn r hr_mem
      have hq_rr : IsRealRooted q := isRealRooted_of_dvd hrr hq_ne hq_dvd
      have hγ_pos : HasPosLeadingCoeff γ := hnn.pos_leadingCoeff hrr.1
      have hq_pos : HasPosLeadingCoeff q := by
        apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
        simpa [hq'] using hγ_pos
      have hq_nn : HasNonnegCoeffs q :=
        hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
          hrr hnn hq_rr hq_pos hq_dvd
      have hqdeg_lt : q.natDegree < n := by
        have hmuldeg : γ.natDegree = q.natDegree + 1 := by
          rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          omega
        omega
      have hqbound : q.natDegree ≤ (d - 2) / 2 := by
        have hmuldeg : γ.natDegree = q.natDegree + 1 := by
          rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          omega
        omega
      have hd : d = (d - 2) + 2 := by omega
      rw [hd, hq', gammaTransform_X_sub_C_mul_two hqbound r]
      exact isRealRooted_mul (isRealRooted_gammaQuadraticFactor hr_nonpos)
        (ih q.natDegree hqdeg_lt (d - 2) q rfl hqbound hq_rr hq_nn)
  exact hP γ.natDegree d γ rfl hγdeg hγ hγnn

theorem hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : IsRealRooted γ) (hγnn : HasNonnegCoeffs γ) :
    HasRootsNonpos (gammaTransform d γ) := by
  intro r hr
  exact roots_nonpos_of_nonneg_coeffs
    (isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs hγdeg hγ hγnn)
    (hasNonnegCoeffs_gammaTransform hγnn) r hr

theorem isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp : IsRealRooted (gammaTransform (2 * γ.natDegree) γ))
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    IsRealRooted γ ∧ HasRootsNonpos γ := by
  let P : ℕ → Prop := fun n =>
    ∀ γ : ℝ[X],
      γ.natDegree = n →
      IsRealRooted (gammaTransform (2 * n) γ) →
      HasRootsNonpos (gammaTransform (2 * n) γ) →
      IsRealRooted γ ∧ HasRootsNonpos γ
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih δ hδdeg hpδ hpδ_nonpos
    have hδ0_main : δ ≠ 0 := by
      intro hzero
      rw [hzero, gammaTransform_zero] at hpδ
      exact hpδ.1 rfl
    by_cases hn0 : n = 0
    · have hδC : δ = C (δ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show δ.natDegree ≤ 0 by omega))
      have hc : δ.coeff 0 ≠ 0 := by
        intro hc0
        apply hδ0_main
        rw [hδC, hc0]
        simp
      refine ⟨isRealRooted_of_deg_zero hδ0_main (by omega), ?_⟩
      intro r hr
      have : False := by
        rw [hδC] at hr
        simpa [hc] using hr
      exact this.elim
    · by_cases hcoeff0 : δ.coeff 0 = 0
      · have hXdvd : X ∣ δ := Polynomial.X_dvd_iff.mpr hcoeff0
        obtain ⟨ζ, hδX⟩ := hXdvd
        have hζ0 : ζ ≠ 0 := by
          intro hζzero
          apply hδ0_main
          rw [hδX, hζzero, mul_zero]
        have hζdeg_succ : n = ζ.natDegree + 1 := by
          calc
            n = δ.natDegree := by rw [hδdeg]
            _ = (X * ζ).natDegree := by rw [hδX]
            _ = 1 + ζ.natDegree := by
                  rw [natDegree_mul (by simp) hζ0, natDegree_X]
            _ = ζ.natDegree + 1 := by omega
        have hζdeg_lt : ζ.natDegree < n := by
          omega
        have hq_eq :
            gammaTransform (2 * n) δ = X * gammaTransform (2 * ζ.natDegree) ζ := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) (X * ζ) := by rw [hδX]
            _ = gammaTransform (2 * ζ.natDegree + 2) (X * ζ) := by
                  rw [show 2 * n = 2 * ζ.natDegree + 2 by omega]
            _ = X * gammaTransform (2 * ζ.natDegree) ζ := by
                  exact gammaTransform_X_mul_two (2 * ζ.natDegree) ζ
        have hq0 : gammaTransform (2 * ζ.natDegree) ζ ≠ 0 := by
          intro hzero
          exact hζ0
            ((gammaTransform_eq_zero_iff_of_natDegree_le
              (d := 2 * ζ.natDegree) (γ := ζ) (by omega)).mp hzero)
        have hq_dvd : gammaTransform (2 * ζ.natDegree) ζ ∣ gammaTransform (2 * n) δ := by
          refine ⟨X, ?_⟩
          simpa [mul_comm] using hq_eq
        have hq_rr : IsRealRooted (gammaTransform (2 * ζ.natDegree) ζ) :=
          isRealRooted_of_dvd hpδ hq0 hq_dvd
        have hq_nonpos : HasRootsNonpos (gammaTransform (2 * ζ.natDegree) ζ) :=
          hasRootsNonpos_of_dvd hpδ_nonpos hpδ.1 hq_dvd hq0
        rcases (ih ζ.natDegree hζdeg_lt) ζ rfl hq_rr hq_nonpos with ⟨hζ_rr, hζ_nonpos⟩
        have hX_nonpos : HasRootsNonpos (X : ℝ[X]) := by
          simpa using hasRootsNonpos_X_sub_C (r := (0 : ℝ)) (by norm_num)
        refine ⟨?_, ?_⟩
        · rw [hδX]
          simpa using isRealRooted_mul isRealRooted_X hζ_rr
        · rw [hδX]
          exact hX_nonpos.mul hζ_nonpos (by simp) hζ_rr.1
      · have htop : δ.coeff n ≠ 0 := by
          have htop' : δ.coeff δ.natDegree ≠ 0 := by
            rw [Polynomial.coeff_natDegree]
            exact leadingCoeff_ne_zero.mpr hδ0_main
          simpa [hδdeg] using htop'
        have htop_deg : (gammaTransform (2 * n) δ).natDegree = 2 * n := by
          apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
            (natDegree_gammaTransform_le (2 * n) δ)
          simpa using hcoeff0
        have hroots_pos : 0 < (gammaTransform (2 * n) δ).roots.card := by
          rw [hpδ.2, htop_deg]
          omega
        obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hx_root : (gammaTransform (2 * n) δ).IsRoot x := (mem_roots hpδ.1).mp hx_mem
        have hx_nonpos : x ≤ 0 := hpδ_nonpos x hx_mem
        have hx_ne_neg_one : x ≠ -1 := by
          intro hx_eq
          have hx_root_neg_one : (gammaTransform (2 * n) δ).IsRoot (-1) := by
            simpa [hx_eq] using hx_root
          exact htop ((gammaTransform_even_isRoot_neg_one_iff n δ).mp hx_root_neg_one)
        let y : ℝ := x / (1 + x) ^ 2
        have hy_nonpos : y ≤ 0 := by
          exact rootPullback_nonpos_of_gammaTransform hx_ne_neg_one hx_nonpos
        have hy_root : δ.IsRoot y := by
          dsimp [y]
          exact isRoot_gamma_of_isRoot_gammaTransform
            (d := 2 * n) (γ := δ) (by omega) hx_ne_neg_one hx_root
        obtain ⟨ε, hγ_fac0⟩ := dvd_iff_isRoot.mpr hy_root
        have hγ_fac : δ = (X - C y) * ε := by
          simpa [mul_comm] using hγ_fac0
        have hε0 : ε ≠ 0 := by
          intro hεzero
          apply hδ0_main
          rw [hγ_fac, hεzero, mul_zero]
        have hεdeg_succ : n = ε.natDegree + 1 := by
          calc
            n = δ.natDegree := by rw [hδdeg]
            _ = ((X - C y) * ε).natDegree := by rw [hγ_fac]
            _ = 1 + ε.natDegree := by
                  rw [natDegree_mul (X_sub_C_ne_zero y) hε0, natDegree_X_sub_C]
            _ = ε.natDegree + 1 := by omega
        have hεdeg_lt : ε.natDegree < n := by
          omega
        have hq_eq :
            gammaTransform (2 * n) δ =
              (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) ((X - C y) * ε) := by
              rw [hγ_fac]
            _ = gammaTransform (2 * ε.natDegree + 2) ((X - C y) * ε) := by
                  rw [show 2 * n = 2 * ε.natDegree + 2 by omega]
            _ = (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε := by
                  exact gammaTransform_X_sub_C_mul_two (γ := ε) (by omega) y
        have hq0 : gammaTransform (2 * ε.natDegree) ε ≠ 0 := by
          intro hzero
          exact hε0
            ((gammaTransform_eq_zero_iff_of_natDegree_le
              (d := 2 * ε.natDegree) (γ := ε) (by omega)).mp hzero)
        have hq_dvd : gammaTransform (2 * ε.natDegree) ε ∣ gammaTransform (2 * n) δ := by
          refine ⟨X - C y * (X + 1) ^ 2, ?_⟩
          simpa [mul_comm, mul_left_comm, mul_assoc] using hq_eq
        have hq_rr : IsRealRooted (gammaTransform (2 * ε.natDegree) ε) :=
          isRealRooted_of_dvd hpδ hq0 hq_dvd
        have hq_nonpos : HasRootsNonpos (gammaTransform (2 * ε.natDegree) ε) :=
          hasRootsNonpos_of_dvd hpδ_nonpos hpδ.1 hq_dvd hq0
        rcases (ih ε.natDegree hεdeg_lt) ε rfl hq_rr hq_nonpos with ⟨hε_rr, hε_nonpos⟩
        refine ⟨?_, ?_⟩
        · rw [hγ_fac]
          exact isRealRooted_mul (isRealRooted_X_sub_C y) hε_rr
        · rw [hγ_fac]
          exact (hasRootsNonpos_X_sub_C hy_nonpos).mul hε_nonpos (X_sub_C_ne_zero y) hε_rr.1
  simpa using hP γ.natDegree γ rfl hp hp_nonpos

theorem isRealRooted_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp : IsRealRooted (gammaTransform (2 * γ.natDegree) γ))
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    IsRealRooted γ :=
  (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal hp hp_nonpos).1

theorem hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp : IsRealRooted (gammaTransform (2 * γ.natDegree) γ))
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    HasRootsNonpos γ :=
  (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal hp hp_nonpos).2

lemma hasRootsNonpos_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    HasRootsNonpos (X - C r * (X + 1) ^ 2) := by
  intro s hs
  exact roots_nonpos_of_nonneg_coeffs
    (isRealRooted_gammaQuadraticFactor hr)
    (hasNonnegCoeffs_gammaQuadraticFactor hr)
    s hs

theorem isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : IsRealRooted γ) (hγ_nonpos : HasRootsNonpos γ) :
    IsRealRooted (gammaTransform d γ) ∧ HasRootsNonpos (gammaTransform d γ) := by
  let P : ℕ → Prop := fun n =>
    ∀ d : ℕ, ∀ γ : ℝ[X],
      γ.natDegree = n →
      γ.natDegree ≤ d / 2 →
      IsRealRooted γ →
      HasRootsNonpos γ →
      IsRealRooted (gammaTransform d γ) ∧ HasRootsNonpos (gammaTransform d γ)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih d δ hδdeg hbound hδ_rr hδ_nonpos
    by_cases hn0 : n = 0
    · have hδC : δ = C (δ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show δ.natDegree ≤ 0 by omega))
      have hcoeff_ne : δ.coeff 0 ≠ 0 := by
        intro h0
        rw [hδC, h0] at hδ_rr
        exact hδ_rr.1 (by simp)
      have hgt :
          gammaTransform d (C (δ.coeff 0)) = C (δ.coeff 0) * (X + 1) ^ d := by
        simpa [gammaBasisTerm_zero] using
          (gammaTransform_monomial d 0 (δ.coeff 0))
      rw [hδC, hgt]
      refine ⟨isRealRooted_C_mul (isRealRooted_X_add_one_pow d) hcoeff_ne, ?_⟩
      intro r hr
      rw [roots_C_mul _ hcoeff_ne] at hr
      exact roots_nonpos_of_nonneg_coeffs
        (isRealRooted_X_add_one_pow d)
        (HasNonnegCoeffs.pow hasNonnegCoeffs_X_add_one d)
        r hr
    · have hroots_pos : 0 < δ.roots.card := by
        rw [hδ_rr.2, hδdeg]
        exact Nat.pos_of_ne_zero hn0
      obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hr_root : δ.IsRoot r := (mem_roots hδ_rr.1).mp hr_mem
      have hr_nonpos : r ≤ 0 := hδ_nonpos r hr_mem
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
      have hδq : δ = (X - C r) * q := by
        simpa [mul_comm] using hq
      have hq_dvd : q ∣ δ := ⟨X - C r, by simpa [mul_comm] using hq⟩
      have hq_ne : q ≠ 0 := by
        intro hq0
        rw [hq0, mul_zero] at hq
        exact hδ_rr.1 hq
      have hq_rr : IsRealRooted q := isRealRooted_of_dvd hδ_rr hq_ne hq_dvd
      have hq_nonpos : HasRootsNonpos q :=
        hasRootsNonpos_of_dvd hδ_nonpos hδ_rr.1 hq_dvd hq_ne
      have hqdeg_lt : q.natDegree < n := by
        have hmuldeg : δ.natDegree = q.natDegree + 1 := by
          rw [hδq, natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          omega
        omega
      have hqbound : q.natDegree ≤ (d - 2) / 2 := by
        have hmuldeg : δ.natDegree = q.natDegree + 1 := by
          rw [hδq, natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          omega
        omega
      have hd : d = (d - 2) + 2 := by omega
      have ihq :
          IsRealRooted (gammaTransform (d - 2) q) ∧
            HasRootsNonpos (gammaTransform (d - 2) q) :=
        ih q.natDegree hqdeg_lt (d - 2) q rfl hqbound hq_rr hq_nonpos
      rw [hd, hδq, gammaTransform_X_sub_C_mul_two hqbound r]
      refine ⟨?_, ?_⟩
      · exact isRealRooted_mul (isRealRooted_gammaQuadraticFactor hr_nonpos) ihq.1
      · exact (hasRootsNonpos_gammaQuadraticFactor hr_nonpos).mul ihq.2
          (isRealRooted_gammaQuadraticFactor hr_nonpos).1 ihq.1.1
  exact hP γ.natDegree d γ rfl hγdeg hγ hγ_nonpos

lemma gammaTransform_even_shift (m k : ℕ) (γ : ℝ[X]) (hγ : γ.natDegree ≤ m) :
    gammaTransform (2 * (m + k)) γ =
      (X + 1) ^ (2 * k) * gammaTransform (2 * m) γ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hhalf : (2 * (m + k)) / 2 = m + k := by omega
      have hstep : γ.natDegree ≤ (2 * (m + k)) / 2 := by
        calc
          γ.natDegree ≤ m := hγ
          _ ≤ m + k := Nat.le_add_right _ _
          _ = (2 * (m + k)) / 2 := by simpa [hhalf]
      calc
        gammaTransform (2 * (m + k.succ)) γ
            = gammaTransform (2 * (m + k) + 2) γ := by
                rw [show 2 * (m + k.succ) = 2 * (m + k) + 2 by omega]
        _ = (X + 1) ^ 2 * gammaTransform (2 * (m + k)) γ := by
              simpa using gammaTransform_pad_two (d := 2 * (m + k)) (γ := γ) hstep
        _ = (X + 1) ^ 2 * ((X + 1) ^ (2 * k) * gammaTransform (2 * m) γ) := by
              rw [ih]
        _ = ((X + 1) ^ 2 * (X + 1) ^ (2 * k)) * gammaTransform (2 * m) γ := by
              rw [mul_assoc]
        _ = (X + 1) ^ (2 + 2 * k) * gammaTransform (2 * m) γ := by
              rw [← pow_add]
        _ = (X + 1) ^ (2 * (k + 1)) * gammaTransform (2 * m) γ := by
              rw [show 2 + 2 * k = 2 * (k + 1) by omega]

lemma gammaTransform_pad_to_minimal {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    gammaTransform d γ =
      (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by
  let m : ℕ := γ.natDegree
  let n : ℕ := d / 2
  have hm : m ≤ n := by simpa [m, n] using hγdeg
  have hshift :
      gammaTransform (2 * n) γ =
        (X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ := by
    have hshift' :=
      gammaTransform_even_shift (m := m) (k := n - m) (γ := γ) (by simpa [m] using hm)
    simpa [show m + (n - m) = n by omega] using hshift'
  rcases Nat.mod_two_eq_zero_or_one d with hd_even | hd_odd
  · have hd : d = 2 * n := by omega
    have hpow : d - 2 * m = 2 * (n - m) := by
      rw [hd]
      omega
    calc
      gammaTransform d γ = gammaTransform (2 * n) γ := by simpa [hd]
      _ = (X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ := hshift
      _ = (X + 1) ^ (d - 2 * m) * gammaTransform (2 * m) γ := by
            rw [hpow]
      _ = (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by
            simp [m]
  · have hd : d = 2 * n + 1 := by omega
    have hpow : d - 2 * m = 1 + 2 * (n - m) := by
      rw [hd]
      omega
    calc
      gammaTransform d γ = gammaTransform (2 * n + 1) γ := by simpa [hd]
      _ = (X + 1) * gammaTransform (2 * n) γ := gammaTransform_odd n γ
      _ = (X + 1) * ((X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ) := by
            rw [hshift]
      _ = (X + 1) ^ (1 + 2 * (n - m)) * gammaTransform (2 * m) γ := by
            have hpow1 :
                (X + 1 : ℝ[X]) ^ (1 + 2 * (n - m)) =
                  (X + 1) * (X + 1) ^ (2 * (n - m)) := by
              rw [show 1 + 2 * (n - m) = 2 * (n - m) + 1 by omega, pow_succ']
            rw [hpow1, mul_assoc]
      _ = (X + 1) ^ (d - 2 * m) * gammaTransform (2 * m) γ := by
            rw [hpow]
      _ = (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by
            simp [m]

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
    (hp : IsRealRooted (gammaTransform d γ))
    (hp_nonpos : HasRootsNonpos (gammaTransform d γ)) :
    IsRealRooted γ ∧ HasRootsNonpos γ := by
  let q : ℝ[X] := gammaTransform (2 * γ.natDegree) γ
  have hq0 : q ≠ 0 := by
    intro hq_zero
    have hγ0 : γ = 0 := by
      exact (gammaTransform_eq_zero_iff_of_natDegree_le
        (d := 2 * γ.natDegree) (γ := γ) (by omega)).mp (by simpa [q] using hq_zero)
    have hzero : gammaTransform d γ = 0 := by
      simpa [hγ0] using (gammaTransform_zero d : gammaTransform d (0 : ℝ[X]) = 0)
    exact hp.1 hzero
  have hqdvd : q ∣ gammaTransform d γ := by
    simpa [q] using gammaTransform_minimal_dvd (d := d) (γ := γ) hγdeg
  have hq_rr : IsRealRooted q := isRealRooted_of_dvd hp hq0 hqdvd
  have hq_nonpos : HasRootsNonpos q := hasRootsNonpos_of_dvd hp_nonpos hp.1 hqdvd hq0
  simpa [q] using
    (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
      (γ := γ) hq_rr hq_nonpos)

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
    ((IsRealRooted γ ∧ HasRootsNonpos γ) ↔
      (IsRealRooted p ∧ HasRootsNonpos p))

theorem gammaRealRootedIffPolynomialRealRootedNonpos :
    gammaRealRootedIffPolynomialRealRootedNonposStatement := by
  intro d p γ hγdeg _hpd _hsym hGamma
  unfold IsGammaExpansion at hGamma
  subst p
  constructor
  · intro hγ
    exact isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
      (d := d) (γ := γ) hγdeg hγ.1 hγ.2
  · intro hp
    exact isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
      (d := d) (γ := γ) hγdeg hp.1 hp.2

end
end RealRooted
