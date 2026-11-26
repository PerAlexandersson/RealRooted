module

public import RealRooted.PFPolynomial
import RealRooted.GarloffWagner.SchurProductPF
import RealRooted.Interlacing.NegativeRoots
import RealRooted.PosCombo
import RealRooted.CommonInterleaver.RootDesc
import Mathlib.Tactic

/-!
# Differential-factor chains for exponential substitution

We apply the endpoint-chain lemma to the factors `D + c` of a PF symbol.
Zero factors and constant images are included. Source: unpublished manuscript,
RealRooted issue #2415, round-four degree-raising substitutions.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- A derivative-plus-constant step preserves splitting and nonnegative
coefficients, and places its output before its input. -/
theorem interl_derivative_add_C_mul {p : ℝ[X]} (hp : IsPFPolynomial p)
    {c : ℝ} (hc : 0 ≤ c) :
    IsPFPolynomial (p.derivative + C c * p) ∧ Interl (p.derivative + C c * p) p := by
  have hd : Interl p.derivative p := by
    by_cases hdeg : p.natDegree = 0
    · rw [derivative_eq_zero.mpr hdeg]
      exact interl_zero_left p
    · exact (derivative_interlaces_of_natDegree_ne_zero hp.splits hdeg).toStrictInterl.toInterl
  have hself : Interl p p := Interl.refl (fun _ => hp.splits)
  have hnn := hp.hasNonnegCoeffs.derivative.add (hasNonnegCoeffs_C_mul hc hp.hasNonnegCoeffs)
  have h := interl_add_left_of_common_right_of_nonneg hd (hself.C_mul_left_of_nonneg hc)
    hp.hasNonnegCoeffs.derivative (hasNonnegCoeffs_C_mul hc hp.hasNonnegCoeffs)
  refine ⟨IsPFPolynomial.of_realRooted_nonneg hnn ?_, h⟩
  by_cases hz : p = 0
  · simp only [hz, derivative_zero, mul_zero, add_zero, Splits.zero]
  by_cases hout : p.derivative + C c * p = 0
  · rw [hout]
    exact Splits.zero
  exact (h.toStrictInterl_of_ne hout hz).1.2

/-- A differential factor with nonnegative constant cannot create a zero root
from a PF input with positive constant coefficient. Its output may vanish. -/
theorem eq_zero_or_coeff_zero_pos_derivative_add_C_mul {p : ℝ[X]}
    (hp : IsPFPolynomial p) (hp0 : 0 < p.coeff 0) {c : ℝ} (hc : 0 ≤ c) :
    p.derivative + C c * p = 0 ∨ 0 < (p.derivative + C c * p).coeff 0 := by
  by_cases hc0 : c = 0
  · simp only [hc0, map_zero, zero_mul, add_zero]
    by_cases hdeg : p.natDegree = 0
    · exact Or.inl (derivative_eq_zero.mpr hdeg)
    right
    have hroots := roots_neg_of_interlaces_of_right_roots_neg
      (derivative_interlaces_of_natDegree_ne_zero hp.splits hdeg) (fun r hr =>
        roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hp.hasNonnegCoeffs hp0.ne'
          r ((mem_roots (by intro h; simp only [h, coeff_zero, lt_self_iff_false] at hp0)).mpr hr))
    have hne : p.derivative.coeff 0 ≠ 0 := by
      intro hz
      have := hroots 0 (by simpa only [IsRoot.def, eval_zero, coeff_zero_eq_eval_zero] using hz)
      exact (lt_irrefl 0) this
    exact lt_of_le_of_ne (hp.hasNonnegCoeffs.derivative 0) (Ne.symm hne)
  · right
    have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    rw [coeff_add, coeff_C_mul]
    exact add_pos_of_nonneg_of_pos (hp.hasNonnegCoeffs.derivative 0) (mul_pos hcpos hp0)

/-- A finite differential-factor chain with a nonzero endpoint has no earlier
zero input, since all its transitions send zero to zero. -/
private theorem ne_zero_of_differential_chain_endpoint
    (Q : ℕ → ℝ[X]) (c : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ j < m, Q (j + 1) = (Q j).derivative + C (c j) * Q j)
    (hend : Q m ≠ 0) : ∀ j ≤ m, Q j ≠ 0 := by
  intro j hj
  have hback : ∀ k, k ≤ m → Q (m - k) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa only [Nat.sub_zero] using fun _ => hend
    | succ k ih =>
      intro hk hz
      have hidx : m - (k + 1) + 1 = m - k := by lia
      apply ih (by lia)
      rw [← hidx, hstep _ (by lia), hz, derivative_zero, mul_zero, add_zero]
  simpa only [Nat.sub_sub_self hj] using hback (m - j) (Nat.sub_le _ _)

/-- Reading a differential-factor chain backwards, endpoint interlacing puts
every intermediate image before the original image. The images are nonzero
whenever the corresponding inputs have positive constant coefficient. -/
theorem interl_map_differential_chain
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (Q : ℕ → ℝ[X]) (c : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ j < m, Q (j + 1) = (Q j).derivative + C (c j) * Q j)
    (hpos : ∀ j ≤ m, Q j ≠ 0 → 0 < (Q j).coeff 0)
    (hTc : ∀ p, (T p).coeff 0 = p.coeff 0)
    (hedge : ∀ j < m, Interl (T (Q (j + 1))) (T (Q j)))
    (hend : Interl (T (Q m)) (T (Q 0)))
    (hdeg : T (Q m) = 0 → (T (Q 0)).natDegree = 0) :
    ∀ j ≤ m, Interl (T (Q j)) (T (Q 0)) := by
  have hne (j : ℕ) (hj : j ≤ m) (hq : Q j ≠ 0) : T (Q j) ≠ 0 := by
    intro hz
    have h := hpos j hj hq
    rw [← hTc, hz, coeff_zero] at h
    exact (lt_irrefl 0) h
  by_cases hz : T (Q m) = 0
  · have hzero := hdeg hz
    have hb : ∀ j ≤ m, (T (Q j)).natDegree = 0 := by
      intro j
      induction j with
      | zero => exact fun _ => hzero
      | succ j ih =>
        intro hj
        by_cases hq : Q (j + 1) = 0
        · simp only [hq, map_zero, natDegree_zero]
        have hqprev : Q j ≠ 0 := by
          intro he
          rw [hstep j (by lia), he, derivative_zero, mul_zero, add_zero] at hq
          exact hq rfl
        have h := (hedge j (by lia)).toStrictInterl_of_ne
          (hne _ hj hq) (hne _ (by lia) hqprev)
        have := h.natDegree_le
        have := ih (by lia)
        lia
    exact fun j hj => interl_of_natDegree_eq_zero (hb j hj) hzero
  · have hqm : Q m ≠ 0 := by intro h; exact hz (by rw [h, map_zero])
    have hq := ne_zero_of_differential_chain_endpoint Q c m hstep hqm
    have hh : StrictInterl (T (Q m)) (T (Q 0)) :=
      hend.toStrictInterl_of_ne hz (hne 0 (Nat.zero_le _) (hq 0 (Nat.zero_le _)))
    have hc : ∀ k, 0 ≤ k → k < m →
        StrictInterl (T (Q (m - k))) (T (Q (m - (k + 1)))) := by
      intro k _ hk
      have hi : m - (k + 1) + 1 = m - k := by lia
      have h := (hedge (m - (k + 1)) (by lia)).toStrictInterl_of_ne
        (hne _ (by lia) (hq _ (by lia))) (hne _ (by lia) (hq _ (by lia)))
      simpa only [hi] using h
    intro j hj
    have h := strictInterl_chain_of_consecutive_of_endpoint
      (fun k => T (Q (m - k))) 0 m hc (by simpa only [Nat.sub_zero, Nat.sub_self] using hh)
      (m - j) m (Nat.zero_le _) (Nat.sub_le _ _) le_rfl
    simpa only [Nat.sub_sub_self hj, Nat.sub_self] using h.toInterl

end RealRooted.ExponentialRows
