import RealRooted.JacobiDeformation.Kernel
import RealRooted.JacobiDeformation.JacobiMoment
import RealRooted.JacobiDeformation.VandermondeIdentity
import RealRooted.JacobiDeformation.WeightNormalization

/-!
# Finite diagonal Jacobi kernel-weight identity

This is the source adaptation of the completed finite Aristotle proof.  Its
only generic finite-sum input is discharged below by the released
Chu--Vandermonde witness.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem risingFactorial_succ' (a : ℝ) (n : ℕ) :
    risingFactorial a (n + 1) = risingFactorial a n * (a + (n : ℝ)) := by
  unfold risingFactorial
  exact ascPochhammer_succ_eval n a

private theorem finiteRising_eq_risingFactorial (a : ℝ) (n : ℕ) :
    FiniteVandermonde.rising a n = risingFactorial a n := by
  induction n with
  | zero => simp [FiniteVandermonde.rising, risingFactorial]
  | succ n ih => rw [FiniteVandermonde.rising_succ, ih, risingFactorial_succ']

private theorem risingFactorial_eq_prod (a : ℝ) (n : ℕ) :
    risingFactorial a n = ∏ i ∈ Finset.range n, (a + (i : ℝ)) := by
  induction n with
  | zero => simp [risingFactorial]
  | succ n ih => rw [risingFactorial_succ', ih, Finset.prod_range_succ]

private theorem risingFactorial_reflect (d : ℝ) (n : ℕ) :
    risingFactorial (1 - (n : ℝ) - d) n =
      (-1 : ℝ) ^ n * risingFactorial d n := by
  have hpow : (-1 : ℝ) ^ n = ∏ _i ∈ Finset.range n, (-1 : ℝ) := by simp
  rw [risingFactorial_eq_prod, risingFactorial_eq_prod, hpow,
    ← Finset.prod_mul_distrib,
    ← Finset.prod_range_reflect (fun i => (-1 : ℝ) * (d + (i : ℝ))) n]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  have hcast : ((n - 1 - i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℝ) := by
    have h1 : 1 + i ≤ n := by lia
    have h2 : n = (n - 1 - i) + 1 + i := by lia
    have h2' := congrArg (fun x : ℕ => (x : ℝ)) h2
    push_cast at h2'
    linarith
  rw [hcast]
  ring

private theorem fallingFactorial_natCast (k j : ℕ) :
    fallingFactorial (k : ℝ) j = (k.descFactorial j : ℝ) := by
  simpa [fallingFactorial] using descPochhammer_eval_eq_descFactorial ℝ k j

private theorem fallingFactorial_natCast_eq_zero_of_lt {k j : ℕ} (hkj : k < j) :
    fallingFactorial (k : ℝ) j = 0 := by
  rw [fallingFactorial_natCast, Nat.descFactorial_eq_zero_iff_lt.mpr hkj]
  simp

private theorem cleared_vandermonde_shared (a c : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ i * (n.choose i : ℝ) * risingFactorial a i *
          risingFactorial (c + (i : ℝ)) (n - i) =
      risingFactorial (c - a) n := by
  simpa only [finiteRising_eq_risingFactorial] using
    FiniteVandermonde.cleared_identity a c n

private theorem factorial_div_eq_fallingFactorial {m j : ℕ} (hjm : j ≤ m) :
    (m.factorial : ℝ) / ((m - j).factorial : ℝ) =
      fallingFactorial (m : ℝ) j := by
  rw [fallingFactorial, descPochhammer_eval_eq_descFactorial]
  have hsub : m - j + j = m := Nat.sub_add_cancel hjm
  have h := Nat.factorial_mul_descFactorial (n := m) (k := j) hjm
  have hcast : ((m - j).factorial : ℝ) * (m.descFactorial j : ℝ) =
      (m.factorial : ℝ) := by
    simpa [hsub] using congrArg (fun x : ℕ => (x : ℝ)) h
  field_simp [Nat.factorial_ne_zero]
  linarith [hcast]

private theorem diagonal_weight_factorial_identity
    (m j : ℕ) (hjm : j ≤ m) (s : ℝ) (hs : 0 < s) (delta : ℝ) :
    (-1 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ k * (m.choose k : ℝ) *
            risingFactorial ((m : ℝ) + s - 1 + delta) k *
            fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) =
      (m.factorial : ℝ) / ((m - j).factorial : ℝ) *
          risingFactorial ((m : ℝ) + s - 1 + delta) j *
          risingFactorial delta (m - j) / risingFactorial s (m + j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjm
  set b : ℝ := ((j + n : ℕ) : ℝ) + s - 1 + delta with hb
  have hsub : j + n - j = n := by lia
  rw [hsub]
  have hsplit : ∑ k ∈ Finset.range (j + n + 1),
      ((-1 : ℝ) ^ k * ((j + n).choose k : ℝ) * risingFactorial b k *
          fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) =
      ∑ l ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ (j + l) * ((j + n).choose (j + l) : ℝ) *
            risingFactorial b (j + l) * fallingFactorial ((j + l : ℕ) : ℝ) j /
              risingFactorial s ((j + l) + j)) := by
    have hrw : j + n + 1 = j + (n + 1) := by lia
    rw [hrw, Finset.sum_range_add]
    have hzero : ∑ k ∈ Finset.range j,
        ((-1 : ℝ) ^ k * ((j + n).choose k : ℝ) * risingFactorial b k *
            fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [fallingFactorial_natCast_eq_zero_of_lt (Finset.mem_range.mp hk)]
      ring
    rw [hzero, zero_add]
  have hterm : ∀ l ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ (j + l) * ((j + n).choose (j + l) : ℝ) *
          risingFactorial b (j + l) * fallingFactorial ((j + l : ℕ) : ℝ) j /
            risingFactorial s ((j + l) + j)) =
        ((-1 : ℝ) ^ j * ((j + n).descFactorial j : ℝ) *
            risingFactorial b j / risingFactorial s (j + n + j)) *
          ((-1 : ℝ) ^ l * (n.choose l : ℝ) *
            risingFactorial (b + (j : ℝ)) l *
            risingFactorial ((s + ((2 * j : ℕ) : ℝ)) + (l : ℝ)) (n - l)) := by
    intro l hl
    have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have h1 : fallingFactorial ((j + l : ℕ) : ℝ) j =
        ((j + l).descFactorial j : ℝ) := fallingFactorial_natCast _ _
    have h2 : (((j + n).choose (j + l) : ℕ) : ℝ) *
        (((j + l).descFactorial j : ℕ) : ℝ) =
        (((j + n).descFactorial j : ℕ) : ℝ) * ((n.choose l : ℕ) : ℝ) := by
      have hchoose := Nat.choose_mul (n := j + n) (k := j + l) (s := j)
        (Nat.le_add_right j l)
      have h1' : j + n - j = n := by lia
      have h2' : j + l - j = l := by lia
      rw [h1', h2'] at hchoose
      calc
        (((j + n).choose (j + l) : ℕ) : ℝ) *
            (((j + l).descFactorial j : ℕ) : ℝ) =
            ((j.factorial : ℝ) * ((j + n).choose (j + l) : ℝ)) *
              ((j + l).choose j : ℝ) := by
              rw [Nat.descFactorial_eq_factorial_mul_choose]
              norm_num only [Nat.cast_mul]
              ring
        _ = (j.factorial : ℝ) *
            (((j + n).choose (j + l) : ℝ) * ((j + l).choose j : ℝ)) := by ring
        _ = (j.factorial : ℝ) * ((j + n).choose j : ℝ) * (n.choose l : ℝ) := by
              rw [show ((j + n).choose (j + l) : ℝ) * ((j + l).choose j : ℝ) =
                ((j + n).choose j : ℝ) * (n.choose l : ℝ) by
                  exact_mod_cast hchoose]
              ring
        _ = (((j + n).descFactorial j : ℕ) : ℝ) * (n.choose l : ℝ) := by
              rw [Nat.descFactorial_eq_factorial_mul_choose]
              norm_num only [Nat.cast_mul]
    have h3 : risingFactorial b (j + l) =
        risingFactorial b j * risingFactorial (b + (j : ℝ)) l := by
      simpa using (risingFactorial_mul_shift b j l).symm
    have h4 : risingFactorial s (j + n + j) =
        risingFactorial s ((j + l) + j) *
          risingFactorial ((s + ((2 * j : ℕ) : ℝ)) + (l : ℝ)) (n - l) := by
      have he : j + n + j = ((j + l) + j) + (n - l) := by lia
      rw [he, ← risingFactorial_mul_shift]
      have hcast : (((j + l) + j : ℕ) : ℝ) = ((2 * j : ℕ) : ℝ) + (l : ℝ) := by
        push_cast
        ring
      rw [hcast]
      ring_nf
    have hden1 : risingFactorial s ((j + l) + j) ≠ 0 :=
      (risingFactorial_pos _ hs).ne'
    have hden2 : risingFactorial s (j + n + j) ≠ 0 :=
      (risingFactorial_pos _ hs).ne'
    have hpow : (-1 : ℝ) ^ (j + l) = (-1 : ℝ) ^ j * (-1 : ℝ) ^ l :=
      pow_add _ _ _
    rw [h1, hpow, h3, div_mul_eq_mul_div, div_eq_div_iff hden1 hden2, h4]
    linear_combination ((-1 : ℝ) ^ j * (-1 : ℝ) ^ l * risingFactorial b j *
      risingFactorial (b + (j : ℝ)) l *
      risingFactorial ((s + ((2 * j : ℕ) : ℝ)) + (l : ℝ)) (n - l) *
        risingFactorial s ((j + l) + j)) * h2
  rw [hsplit, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hV := cleared_vandermonde_shared (b + (j : ℝ))
    (s + ((2 * j : ℕ) : ℝ)) n
  rw [hV]
  have harg : (s + ((2 * j : ℕ) : ℝ)) - (b + (j : ℝ)) =
      1 - (n : ℝ) - delta := by
    rw [hb]
    push_cast
    ring
  rw [harg, risingFactorial_reflect]
  have hsign : (-1 : ℝ) ^ (j + n) *
      ((-1 : ℝ) ^ j * (-1 : ℝ) ^ n) = 1 := by
    rw [pow_add]
    have h1 : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have h2 : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    calc
      (-1 : ℝ) ^ j * (-1 : ℝ) ^ n *
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ n) =
          ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) *
            ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) := by ring
      _ = 1 := by rw [h1, h2]; norm_num
  have hfac := factorial_div_eq_fallingFactorial
    (m := j + n) (j := j) (by lia)
  rw [fallingFactorial_natCast, hsub] at hfac
  rw [← hfac]
  linear_combination (((j + n).factorial : ℝ) / (n.factorial : ℝ) *
    risingFactorial b j * risingFactorial delta n /
      risingFactorial s (j + n + j)) * hsign

/-- The alternating diagonal-weight sum is the actual finite Jacobi kernel
weight.  No sign or nonvanishing condition on `delta` is used. -/
theorem diagonal_weight_identity
    (m j : ℕ) (hjm : j ≤ m) (s : ℝ) (hs : 0 < s) (delta : ℝ) :
    (-1 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1),
        ((-1 : ℝ) ^ k * (m.choose k : ℝ) *
            risingFactorial ((m : ℝ) + s - 1 + delta) k *
            fallingFactorial (k : ℝ) j / risingFactorial s (k + j)) =
      kernelWeight m delta s j := by
  rw [diagonal_weight_factorial_identity m j hjm s hs delta,
    factorial_div_eq_fallingFactorial hjm]
  rfl

end RealRooted.JacobiDeformation
