module

import RealRooted.Derivative.Algebra
import RealRooted.ObreschkoffConverse.DegreeGap
import RealRooted.ObreschkoffConverse.Derivative
import RealRooted.ProductSequence.Interlacing
import RealRooted.SameDegreeDerivative
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
public import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Fixed derivatives of products

Real-rootedness, interlacing, root-window, and pure-lag recurrence results for
fixed derivatives of `q * (X - C a) ^ n`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma roots_iterate_derivative_mem_Icc {p : ℝ[X]} {u v : ℝ}
    (hp : p.Splits) (hroots : ∀ x ∈ p.roots, x ∈ Set.Icc u v) :
    ∀ {r : ℕ}, r ≤ p.natDegree →
      ∀ x ∈ (derivative^[r] p).roots, x ∈ Set.Icc u v := by
  intro r hr
  induction r generalizing p with
  | zero => simpa using hroots
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      have hr_le : r ≤ p.natDegree := by lia
      have hiter_roots := ih hp hroots hr_le
      by_cases hdeg : 2 ≤ (derivative^[r] p).natDegree
      · exact roots_derivative_mem_Icc_of_roots_mem_Icc
          (hp.iterate_derivative r) hdeg hiter_roots
      · have hdeg_zero : (derivative (derivative^[r] p)).natDegree = 0 := by
          rw [(derivative^[r] p).natDegree_derivative]
          lia
        rw [eq_C_of_natDegree_eq_zero hdeg_zero]
        simp

/-- Every fixed derivative of `q * (X - a)^n` is standard and real-rooted,
with the expected degree. -/
theorem iterate_derivative_mul_X_sub_C_pow_standard
    {q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq : q.Splits)
    {r : ℕ} (hr : r ≤ q.natDegree) (a : ℝ) (n : ℕ) :
    HasPosLeadingCoeff (derivative^[r] (q * (X - C a) ^ n)) ∧
      derivative^[r] (q * (X - C a) ^ n) ≠ 0 ∧
      (derivative^[r] (q * (X - C a) ^ n)).Splits ∧
      (derivative^[r] (q * (X - C a) ^ n)).natDegree = q.natDegree + n - r := by
  have hpow_ne : ((X - C a) ^ n : ℝ[X]) ≠ 0 := pow_ne_zero n (X_sub_C_ne_zero a)
  have hp_ne : q * (X - C a) ^ n ≠ 0 := mul_ne_zero hq_pos.ne_zero hpow_ne
  have hp_deg : (q * (X - C a) ^ n).natDegree = q.natDegree + n := by
    rw [natDegree_mul hq_pos.ne_zero hpow_ne, natDegree_pow, natDegree_X_sub_C]
    ring
  have hrp : r ≤ (q * (X - C a) ^ n).natDegree := by rw [hp_deg]; lia
  have hp_pos : HasPosLeadingCoeff (q * (X - C a) ^ n) :=
    hq_pos.mul (hasPosLeadingCoeff_of_monic ((monic_X_sub_C a).pow n))
  refine ⟨hp_pos.iterate_derivative_of_le_natDegree hrp,
    iterate_derivative_ne_zero_of_le_natDegree hp_ne hrp,
    (hq.mul ((Polynomial.Splits.X_sub_C a).pow n)).iterate_derivative r, ?_⟩
  rw [natDegree_iterate_derivative_eq_sub hp_ne hrp, hp_deg]

/-- Fixed derivatives of consecutive products are in directed weak proper
position. -/
theorem strictInterl_iterate_derivative_mul_X_sub_C_pow_succ
    {q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq : q.Splits)
    {r : ℕ} (hr : r ≤ q.natDegree) (a : ℝ) (n : ℕ) :
    StrictInterl
      (derivative^[r] (q * (X - C a) ^ n))
      (derivative^[r] (q * (X - C a) ^ (n + 1))) := by
  have hpow_ne : ((X - C a) ^ n : ℝ[X]) ≠ 0 := pow_ne_zero n (X_sub_C_ne_zero a)
  have hp_ne : q * (X - C a) ^ n ≠ 0 := mul_ne_zero hq_pos.ne_zero hpow_ne
  have hp_splits : (q * (X - C a) ^ n).Splits :=
    hq.mul ((Polynomial.Splits.X_sub_C a).pow n)
  have hbase :
      Interl (q * (X - C a) ^ n) (q * (X - C a) ^ (n + 1)) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      (Interlaces.toStrictInterl
        (interlaces_self_mul_of_natDegree_eq_one hp_ne hp_splits
          (natDegree_X_sub_C a))).toInterl
  have hinter := hbase.iterate_derivative r
  exact hinter.toStrictInterl_of_ne
    (iterate_derivative_mul_X_sub_C_pow_standard hq_pos hq hr a n).2.1
    (iterate_derivative_mul_X_sub_C_pow_standard hq_pos hq hr a (n + 1)).2.1

/-- If the roots of `q` and the added root `a` lie in `[u, v]`, then the same
is true after any fixed number of derivatives. -/
theorem roots_iterate_derivative_mul_X_sub_C_pow_mem_Icc
    {q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq : q.Splits)
    {r : ℕ} (hr : r ≤ q.natDegree) {a u v : ℝ}
    (ha : a ∈ Set.Icc u v) (hroots : ∀ x ∈ q.roots, x ∈ Set.Icc u v)
    (n : ℕ) :
    ∀ x ∈ (derivative^[r] (q * (X - C a) ^ n)).roots, x ∈ Set.Icc u v := by
  have hpow_ne : ((X - C a) ^ n : ℝ[X]) ≠ 0 := pow_ne_zero n (X_sub_C_ne_zero a)
  have hp_ne : q * (X - C a) ^ n ≠ 0 := mul_ne_zero hq_pos.ne_zero hpow_ne
  have hp_deg : (q * (X - C a) ^ n).natDegree = q.natDegree + n := by
    rw [natDegree_mul hq_pos.ne_zero hpow_ne, natDegree_pow, natDegree_X_sub_C]
    ring
  apply roots_iterate_derivative_mem_Icc
    (hq.mul ((Polynomial.Splits.X_sub_C a).pow n))
  · intro x hx
    rw [roots_mul hp_ne] at hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact hroots x hx
    · rw [roots_pow, roots_X_sub_C] at hx
      simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
      rcases hx with ⟨_, rfl⟩
      exact ha
  · rw [hp_deg]
    lia

private def sequenceShift : Module.End ℝ[X] (ℕ → ℝ[X]) where
  toFun P n := P (n + 1)
  map_add' P Q := by ext n; simp
  map_smul' p P := by ext n; simp

private def sequenceMul (p : ℝ[X]) : Module.End ℝ[X] (ℕ → ℝ[X]) where
  toFun P n := p * P n
  map_add' P Q := by
    apply _root_.funext
    intro n
    simp [mul_add]
  map_smul' q P := by
    apply _root_.funext
    intro n
    change p * (q * P n) = q * (p * P n)
    ring

private def lagDifference (p : ℝ[X]) : Module.End ℝ[X] (ℕ → ℝ[X]) :=
  sequenceMul (-p) + sequenceShift

private lemma sequenceShift_pow_apply (P : ℕ → ℝ[X]) (m n : ℕ) :
    (sequenceShift ^ m) P n = P (n + m) := by
  induction m generalizing P n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      change P (n + m + 1) = P (n + (m + 1))
      rw [Nat.add_assoc]

private lemma sequenceMul_pow_apply (p : ℝ[X]) (P : ℕ → ℝ[X]) (m n : ℕ) :
    (sequenceMul p ^ m) P n = p ^ m * P n := by
  induction m generalizing P n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      change p ^ m * (p * P n) = p ^ (m + 1) * P n
      rw [pow_succ]
      ring

private lemma sequenceMul_commute_sequenceShift (p : ℝ[X]) :
    Commute (sequenceMul p) sequenceShift := by
  apply LinearMap.ext
  intro P
  apply _root_.funext
  intro n
  rfl

private lemma lagDifference_pow_apply (p : ℝ[X]) (P : ℕ → ℝ[X]) (m n : ℕ) :
    (lagDifference p ^ m) P n =
      ∑ i ∈ Finset.range (m + 1),
        (-1 : ℝ[X]) ^ i * (m.choose i : ℝ[X]) * p ^ i * P (n + m - i) := by
  have hpow := congr_fun
    (LinearMap.congr_fun ((sequenceMul_commute_sequenceShift (-p)).add_pow m) P) n
  unfold lagDifference
  rw [hpow]
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ m := by simpa using Finset.mem_range.mp hi
  rw [mul_assoc, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.natCast_apply, map_nsmul, map_nsmul]
  rw [Pi.smul_apply, nsmul_eq_mul]
  change (m.choose i : ℝ[X]) *
    (sequenceMul (-p) ^ i) ((sequenceShift ^ (m - i)) P) n = _
  rw [sequenceMul_pow_apply, sequenceShift_pow_apply, neg_pow]
  have hindex : n + (m - i) = n + m - i := by lia
  rw [hindex]
  ring

private lemma iterate_derivative_mul_X_sub_C (p : ℝ[X]) (a : ℝ) (m : ℕ) :
    derivative^[m] (p * (X - C a)) =
      derivative^[m] p * (X - C a) + m • derivative^[m - 1] p := by
  rw [mul_sub, Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_mul_X,
    mul_comm p (C a), Polynomial.iterate_derivative_C_mul]
  ring

private lemma lagDifference_derivative_succ (q : ℝ[X]) (a : ℝ) (r : ℕ) :
    lagDifference (X - C a)
        (fun n ↦ derivative^[r + 1] (q * (X - C a) ^ n)) =
      (r + 1 : ℝ[X]) • (fun n ↦ derivative^[r] (q * (X - C a) ^ n)) := by
  funext n
  change -(X - C a) * derivative^[r + 1] (q * (X - C a) ^ n) +
      derivative^[r + 1] (q * (X - C a) ^ (n + 1)) =
    (r + 1 : ℝ[X]) * derivative^[r] (q * (X - C a) ^ n)
  rw [show q * (X - C a) ^ (n + 1) =
    (q * (X - C a) ^ n) * (X - C a) by rw [pow_succ]; ring]
  rw [iterate_derivative_mul_X_sub_C]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  push_cast
  ring

private lemma lagDifference_pow_derivative_eq_zero (q : ℝ[X]) (a : ℝ) :
    ∀ r : ℕ,
      (lagDifference (X - C a) ^ (r + 1))
          (fun n ↦ derivative^[r] (q * (X - C a) ^ n)) = 0 := by
  intro r
  induction r with
  | zero =>
      rw [pow_one]
      apply _root_.funext
      intro n
      change -(X - C a) * (q * (X - C a) ^ n) +
        q * (X - C a) ^ (n + 1) = 0
      rw [pow_succ]
      ring
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by ring, pow_succ, Module.End.mul_apply,
        lagDifference_derivative_succ]
      simpa using congrArg (fun P ↦ (r + 1 : ℝ[X]) • P) ih

/-- The fixed-derivative sequence satisfies the pure-lag recurrence
`(S - (X - a)) ^ (r + 1) Q = 0` from index zero. -/
theorem sum_pow_mul_iterate_derivative_mul_X_sub_C_pow_eq_zero
    (q : ℝ[X]) (a : ℝ) (r n : ℕ) :
    ∑ i ∈ Finset.range (r + 2),
      (-1 : ℝ[X]) ^ i * (Nat.choose (r + 1) i : ℝ[X]) *
        (X - C a) ^ i *
          derivative^[r] (q * (X - C a) ^ (n + r + 1 - i)) = 0 := by
  calc
    _ = (lagDifference (X - C a) ^ (r + 1))
        (fun k ↦ derivative^[r] (q * (X - C a) ^ k)) n := by
      symm
      simpa [Nat.add_assoc] using lagDifference_pow_apply (X - C a)
        (fun k ↦ derivative^[r] (q * (X - C a) ^ k)) (r + 1) n
    _ = 0 := congr_fun (lagDifference_pow_derivative_eq_zero q a r) n

end RealRooted
