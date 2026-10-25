module

public import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.MagicCone

/-!
# The endpoint relation of the weighted magic cone

For `w ≥ 0` write `E_n` and `G_n` for the right and left endpoints of the weighted deco Bernstein
image row.  We prove `G_n = Σ_k C(n,k) E_k`, recurrences for `G_n`, palindromicity and simple
negative roots of `E_n`, and strict interlacing of consecutive `E_n`.  The endpoint relation
`G_n ≪ E_n` and nonvanishing of the endpoint resultant then reduce to one sign condition,
`G_n(ρ) E_n'(ρ) > 0` at the roots `ρ` of `E_n`, which stays an explicit hypothesis: it is the
open part of issue #1263 (verified for `n ≤ 7`).  The all-`n` results were found by Aristotle
(project eadb38f3).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The left endpoint of the weighted magic row is the binomial sum of the
weighted deco Eulerian polynomials. -/
theorem weightedDecoMagicBasisImage_zero_eq_sum (w : ℝ) (n : ℕ) :
    weightedDecoMagicBasisImage w n 0 =
    ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w k := by
  simp only [weightedDecoMagicBasisImage, weightedDecoTransform,
    Polynomial.basisTransform, pow_zero, one_mul, Nat.sub_zero]
  rw [sum_over_range' _ (fun _ => by simp) (n + 1)]
  · simp [coeff_one_add_X_pow]
  · have hdegree : ((1 + X : ℝ[X]) ^ n).natDegree ≤ n := by
      simp
    lia

/-- The recurrence of `E` written uniformly for all indices, with `E_{-1} = 0`. -/
private theorem weightedDecoEulerian_succ_all (w : ℝ) (k : ℕ) : weightedDecoEulerian w (k + 1) =
    (X - X ^ 2) * derivative (weightedDecoEulerian w k) +
      (C 1 + C ((k : ℝ) + 1) * X) * weightedDecoEulerian w k +
        C w * X * (if k = 0 then 0 else weightedDecoEulerian w (k - 1)) := by
  rcases k with _ | k
  · simp [weightedDecoEulerian]
  · rw [weightedDecoEulerian_recurrence]
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    congr 3
    ring_nf

private def Gh (w : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w k

private theorem Gh_succ (w : ℝ) (n : ℕ) : Gh w (n + 1) = Gh w n +
    ∑ k ∈ Finset.range (n + 1),
      C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w (k + 1) := by
  unfold Gh
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, map_add, add_mul, Finset.sum_add_distrib]
  simp only [Nat.succ_eq_add_one]
  rw [Finset.sum_range_succ'
    (fun k => C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w k) n]
  rw [Finset.sum_range_succ
    (fun k => C ((n.choose (k + 1) : ℕ) : ℝ) * weightedDecoEulerian w (k + 1)) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, map_zero, zero_mul, add_zero,
    Nat.choose_zero_right]
  ring

private theorem Gh_hockey (w : ℝ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range n, C ((n.choose (k + 1) : ℕ) : ℝ) * weightedDecoEulerian w k =
      ∑ i ∈ Finset.range n, Gh w i
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ (fun i => Gh w i), ← Gh_hockey w n]
    simp only [Nat.choose_succ_succ, Nat.cast_add, map_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ
      (fun k => C ((n.choose (k + 1) : ℕ) : ℝ) * weightedDecoEulerian w k) n]
    simp only [Nat.choose_succ_self, Nat.cast_zero, map_zero, zero_mul, add_zero]
    unfold Gh
    ring

private theorem Gh_weighted (w : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℕ) : ℝ) *
      (C (k : ℝ) * weightedDecoEulerian w k) =
      C (n : ℝ) * (Gh w n - Gh w (n - 1)) := by
  rcases n with _ | m
  · simp
  · rw [Finset.sum_range_succ', Nat.add_sub_cancel, Gh_succ, add_sub_cancel_left,
      Finset.mul_sum]
    simp only [Nat.cast_zero, map_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := Nat.add_one_mul_choose_eq m k
    have h' : ((m + 1 : ℕ) : ℝ) * ((m.choose k : ℕ) : ℝ) =
        (((m + 1).choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, ← h']

private theorem Gh_step (w : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w (k + 1) =
      (X - X ^ 2) * derivative (Gh w n) + (1 + X) * Gh w n +
        X * (C (n : ℝ) * (Gh w n - Gh w (n - 1))) +
          C w * X * ∑ i ∈ Finset.range n, Gh w i := by
  rw [← Gh_weighted, ← Gh_hockey]
  have hpred : ∑ k ∈ Finset.range n,
      C ((n.choose (k + 1) : ℕ) : ℝ) * weightedDecoEulerian w k =
      ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℕ) : ℝ) *
        (if k = 0 then 0 else weightedDecoEulerian w (k - 1)) := by
    rw [Finset.sum_range_succ']
    simp
  rw [hpred]
  unfold Gh
  rw [derivative_sum]
  simp only [derivative_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [weightedDecoEulerian_succ_all]
  simp only [map_add, map_one]
  ring

theorem weightedDecoMagicBasisImage_zero_succ (w : ℝ) (n : ℕ) :
    weightedDecoMagicBasisImage w (n + 1) 0 =
      (X - X ^ 2) * derivative (weightedDecoMagicBasisImage w n 0) +
        (C 2 + C ((n : ℝ) + 1) * X) * weightedDecoMagicBasisImage w n 0 -
          C (n : ℝ) * X * weightedDecoMagicBasisImage w (n - 1) 0 +
            C w * X * ∑ i ∈ Finset.range n, weightedDecoMagicBasisImage w i 0 := by
  have hG : ∀ m, weightedDecoMagicBasisImage w m 0 = Gh w m := fun m =>
    weightedDecoMagicBasisImage_zero_eq_sum w m
  simp only [hG]
  rw [Gh_succ, Gh_step]
  simp only [map_add, map_one, map_ofNat]
  ring

theorem weightedDecoMagicBasisImage_zero_succ_succ (w : ℝ) (n : ℕ) :
    weightedDecoMagicBasisImage w (n + 2) 0 =
      (X - X ^ 2) * (derivative (weightedDecoMagicBasisImage w (n + 1) 0) -
        derivative (weightedDecoMagicBasisImage w n 0)) +
        (C 3 + C ((n : ℝ) + 2) * X) * weightedDecoMagicBasisImage w (n + 1) 0 -
          (C 2 + C (2 * (n : ℝ) + 2 - w) * X) * weightedDecoMagicBasisImage w n 0 +
            C (n : ℝ) * X * weightedDecoMagicBasisImage w (n - 1) 0 := by
  have h1 := weightedDecoMagicBasisImage_zero_succ w (n + 1)
  have h0 := weightedDecoMagicBasisImage_zero_succ w n
  rw [Finset.sum_range_succ, Nat.add_sub_cancel] at h1
  simp only [map_add, map_sub, map_mul, map_ofNat, map_natCast, Nat.cast_add, Nat.cast_one,
    map_one] at h1 h0 ⊢
  linear_combination h1 - h0

theorem weightedDecoEulerian_palindromic (w : ℝ) : ∀ n k, k ≤ n →
    (weightedDecoEulerian w n).coeff k = (weightedDecoEulerian w n).coeff (n - k)
  | 0, k, hk => by
    obtain rfl : k = 0 := by lia
    rfl
  | 1, k, hk => by
    interval_cases k <;> simp [weightedDecoEulerian, coeff_one, coeff_X]
  | n + 2, k, hk => by
    have h0 : (weightedDecoEulerian w (n + 2)).coeff 0 = 1 := by
      rw [weightedDecoEulerian_coeff_zero]
    have hn := (weightedDecoEulerian_monic w (n + 2)).leadingCoeff
    rcases k with _ | j
    · rw [Nat.sub_zero, h0]
      simpa [leadingCoeff, weightedDecoEulerian_natDegree] using hn.symm
    · by_cases hj : j = n + 1
      · subst hj
        rw [Nat.sub_self, h0]
        simpa [leadingCoeff, weightedDecoEulerian_natDegree] using hn
      · obtain ⟨l, hl⟩ : ∃ l, n - j = l := ⟨_, rfl⟩
        have hjn : j ≤ n := by lia
        rw [show n + 2 - (j + 1) = l + 1 by lia, weightedDecoEulerian_coeff_succ_succ,
          weightedDecoEulerian_coeff_succ_succ]
        have hp1 := weightedDecoEulerian_palindromic w (n + 1) (j + 1) (by lia)
        have hp2 := weightedDecoEulerian_palindromic w (n + 1) j (by lia)
        have hq := weightedDecoEulerian_palindromic w n j hjn
        rw [show n + 1 - (j + 1) = l by lia] at hp1
        rw [show n + 1 - j = l + 1 by lia] at hp2
        rw [hl] at hq
        rw [hp1, hp2, hq]
        have hcast : (l : ℝ) = n - j := by
          rw [← hl, Nat.cast_sub hjn]
        rw [hcast]
        ring

/-- The open endpoint sign condition from issue #1263.  It is deliberately an
explicit hypothesis: its all-rank proof is not supplied by this module. -/
def EndpointSignCondition (w : ℝ) (n : ℕ) : Prop :=
  ∀ ρ, (weightedDecoEulerian w n).IsRoot ρ →
    0 < (weightedDecoMagicBasisImage w n 0).eval ρ *
      (weightedDecoEulerian w n).derivative.eval ρ

/-- The already formalized weighted Eulerian family has `n` simple negative
roots at every nonnegative weight. -/
theorem weightedDecoEulerian_roots {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    (weightedDecoEulerian w n).Splits ∧ (weightedDecoEulerian w n).natDegree = n ∧
      (weightedDecoEulerian w n).roots.Nodup ∧
        ∀ r, (weightedDecoEulerian w n).IsRoot r → r < 0 := by
  refine ⟨weightedDecoEulerian_splits hw n, weightedDecoEulerian_natDegree w n,
    (weightedDecoEulerian_hasSimpleRoots hw n).roots_nodup, ?_⟩
  intro r hr
  exact weightedDecoEulerian_root_neg hw n hr

/-- The right endpoint of the rank-`n` magic row is the weighted deco
Eulerian polynomial of rank `n`. -/
@[simp]
theorem weightedDecoMagicBasisImage_self (w : ℝ) (n : ℕ) :
    weightedDecoMagicBasisImage w n n = weightedDecoEulerian w n := by
  rw [weightedDecoMagicBasisImage, Nat.sub_self, pow_zero, mul_one]
  exact weightedDecoTransform_X_pow w n

/-- Consecutive right endpoints strictly interlace for every nonnegative
weight. -/
theorem weightedDecoMagicBasisImage_self_strictInterl
    {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    StrictInterl (weightedDecoMagicBasisImage w n n)
      (weightedDecoMagicBasisImage w (n + 1) (n + 1)) := by
  simp only [weightedDecoMagicBasisImage_self]
  exact weightedDecoEulerian_strictInterl hw n

private theorem weightedDecoMagicBasisImage_zero_monic (w : ℝ) (n : ℕ) :
    (weightedDecoMagicBasisImage w n 0).Monic := by
  rw [weightedDecoMagicBasisImage, pow_zero, one_mul, Nat.sub_zero]
  have hmonic : ((1 + X : ℝ[X]) ^ n).Monic := by
    simpa only [C_1, add_comm] using (monic_X_add_C (R := ℝ) 1).pow n
  exact weightedDecoTransform_monic w hmonic

private theorem weightedDecoMagicBasisImage_zero_natDegree (w : ℝ) (n : ℕ) :
    (weightedDecoMagicBasisImage w n 0).natDegree = n := by
  simpa only [weightedDecoMagicBasisImage, pow_zero, one_mul, Nat.sub_zero,
    weightedDecoDiagonal, C_1, add_comm] using
      weightedDecoDiagonal_natDegree w n 1

private theorem weightedDecoMagicBasisImage_zero_sub_self_eq_sum
    (w : ℝ) (n : ℕ) :
    weightedDecoMagicBasisImage w n 0 - weightedDecoEulerian w n =
      ∑ k ∈ Finset.range n,
        C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w k := by
  rw [weightedDecoMagicBasisImage_zero_eq_sum, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, map_one, one_mul]
  ring

private theorem weightedDecoMagicBasisImage_zero_sub_self_hasNonnegCoeffs
    {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    HasNonnegCoeffs
      (weightedDecoMagicBasisImage w n 0 - weightedDecoEulerian w n) := by
  rw [weightedDecoMagicBasisImage_zero_sub_self_eq_sum]
  apply hasNonnegCoeffs_finsetSum
  intro k hk
  exact (hasNonnegCoeffs_C (by positivity)).mul
    (weightedDecoEulerian_hasNonnegCoeffs hw k)

private theorem weightedDecoMagicBasisImage_zero_sub_self_ne_zero
    {w : ℝ} (hw : 0 ≤ w) {n : ℕ} (hn : 0 < n) :
    weightedDecoMagicBasisImage w n 0 - weightedDecoEulerian w n ≠ 0 := by
  intro hzero
  have hcoeff :
      (weightedDecoMagicBasisImage w n 0 - weightedDecoEulerian w n).coeff 0 = 0 := by
    rw [hzero]
    simp
  rw [weightedDecoMagicBasisImage_zero_sub_self_eq_sum, finsetSum_coeff] at hcoeff
  have hpos : 0 < ∑ k ∈ Finset.range n,
      (C ((n.choose k : ℕ) : ℝ) * weightedDecoEulerian w k).coeff 0 := by
    apply Finset.sum_pos'
    · intro k hk
      simp only [coeff_C_mul]
      exact mul_nonneg (by positivity)
        ((weightedDecoEulerian_hasNonnegCoeffs hw k) 0)
    · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
      simp
  linarith

/-- The open sign condition implies both the endpoint relation and endpoint
resultant nonvanishing.  The sign condition is the unproved all-rank input of
issue #1263; every other step is formalized here. -/
theorem weightedDecoMagicBasisImage_endpoint_and_resultant_ne_zero_of_sign
    {w : ℝ} (hw : 0 ≤ w) (n : ℕ) (hsign : EndpointSignCondition w n) :
    StrictInterl (weightedDecoMagicBasisImage w n 0)
        (weightedDecoMagicBasisImage w n n) ∧
      Polynomial.resultant (weightedDecoMagicBasisImage w n 0)
        (weightedDecoEulerian w n) ≠ 0 := by
  let G := weightedDecoMagicBasisImage w n 0
  let E := weightedDecoEulerian w n
  by_cases hn : n = 0
  · subst n
    have hmonic : E.Monic := weightedDecoEulerian_monic w 0
    refine ⟨?_, ?_⟩
    · simpa [E] using
        StrictInterl.refl hmonic.ne_zero (weightedDecoEulerian_splits hw 0)
    · simp [weightedDecoMagicBasisImage]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let D := G - E
    have hGmonic : G.Monic := weightedDecoMagicBasisImage_zero_monic w n
    have hEmonic : E.Monic := weightedDecoEulerian_monic w n
    have hGdeg : G.natDegree = n := weightedDecoMagicBasisImage_zero_natDegree w n
    have hEdeg : E.natDegree = n := weightedDecoEulerian_natDegree w n
    have hDdeg : D.natDegree < E.natDegree := by
      have hGmonoDegree : G.IsMonicOfDegree n := ⟨hGdeg, hGmonic⟩
      have hEmonoDegree : E.IsMonicOfDegree n := ⟨hEdeg, hEmonic⟩
      change (G - E).natDegree < E.natDegree
      rw [hEdeg]
      exact hGmonoDegree.natDegree_sub_lt (by lia) hEmonoDegree
    have hDsign : ∀ r, E.IsRoot r → 0 < D.eval r * E.derivative.eval r := by
      intro r hr
      have hEeval : E.eval r = 0 := hr
      simpa [D, G, E, eval_sub, hEeval] using hsign r hr
    have hDinter : Interlaces D E :=
      interlaces_of_eval_mul_derivative_pos (weightedDecoEulerian_splits hw n)
        (hasPosLeadingCoeff_of_monic hEmonic) hDdeg hDsign
    have hDne : D ≠ 0 := by
      simpa [D, G, E] using
        weightedDecoMagicBasisImage_zero_sub_self_ne_zero hw hnpos
    have hDnonneg : HasNonnegCoeffs D := by
      simpa [D, G, E] using
        weightedDecoMagicBasisImage_zero_sub_self_hasNonnegCoeffs hw n
    have hDpos : HasPosLeadingCoeff D := hDnonneg.pos_leadingCoeff hDne
    have hEpos : HasPosLeadingCoeff E := hasPosLeadingCoeff_of_monic hEmonic
    have hEself : StrictInterl E E :=
      StrictInterl.refl hEmonic.ne_zero (weightedDecoEulerian_splits hw n)
    have hGE : StrictInterl G E := by
      have hadd := StrictInterl.add_of_right_of_posLeadingCoeff
        hDinter.toStrictInterl hEself hDpos hEpos
      simpa [D, sub_add_cancel] using hadd
    refine ⟨?_, ?_⟩
    · simpa [G, E] using hGE
    · apply resultant_ne_zero
      apply isCoprime_of_no_common_real_root_of_isRealRooted hGE.1.1 hGE.1.2
      intro r hGroot hEroot
      have hpositive := hsign r hEroot
      rw [Polynomial.IsRoot.def.mp hGroot, zero_mul] at hpositive
      exact (lt_irrefl 0) hpositive

/-- The endpoint relation follows from the explicit open sign hypothesis. -/
theorem weightedDecoMagicBasisImage_endpoint_of_sign
    {w : ℝ} (hw : 0 ≤ w) (n : ℕ) (hsign : EndpointSignCondition w n) :
    StrictInterl (weightedDecoMagicBasisImage w n 0)
      (weightedDecoMagicBasisImage w n n) :=
  (weightedDecoMagicBasisImage_endpoint_and_resultant_ne_zero_of_sign
    hw n hsign).1

/-- The endpoint resultant is nonzero under the explicit open sign
hypothesis. -/
theorem weightedDeco_endpoint_resultant_ne_zero_of_sign
    {w : ℝ} (hw : 0 ≤ w) (n : ℕ) (hsign : EndpointSignCondition w n) :
    Polynomial.resultant (weightedDecoMagicBasisImage w n 0)
      (weightedDecoEulerian w n) ≠ 0 :=
  (weightedDecoMagicBasisImage_endpoint_and_resultant_ne_zero_of_sign
    hw n hsign).2

/-- Conditional weighted magic-cone theorem.  The root sign condition is the
open input from issue #1263; given it, the PF conclusion is unconditional in
the magic-expansion coefficients. -/
theorem weightedDecoTransform_isPF_of_magicExpansion_of_sign
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {d : ℕ} {c : ℕ → ℝ}
    (hsign : EndpointSignCondition w d)
    (hc : ∀ k, k ≤ d → 0 ≤ c k) :
    IsPFPolynomial
      (weightedDecoTransform w (EulerianTransform.magicExpansion d c)) :=
  weightedDecoTransform_isPF_of_magicExpansion_of_endpoint hw0 hw1
    (weightedDecoMagicBasisImage_endpoint_of_sign hw0 d hsign) hc

end RealRooted.Applications.OEIS
