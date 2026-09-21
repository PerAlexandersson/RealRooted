import RealRooted.Applications.OEIS.A144696.StrictInterlacing
import RealRooted.CommonInterleaver.RootDesc
import RealRooted.EulerianCompletion.ProperPosition
import RealRooted.GeneralizedEulerian
import RealRooted.SymmetricDecomposition.Theorem26

/-!
# Reciprocal endpoint for the A144696 Bernstein-image triangle

The A144696 row polynomial is expressed through two consecutive ordinary
Eulerian polynomials. Its resulting symmetric decomposition has a tight
lowering-Euler component, so Brändén--Solus Theorem 2.6 supplies the reciprocal
proper-position endpoint needed by the Bernstein-row chain.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Twice the A144696 row polynomial is the sum of two consecutive ordinary
Eulerian expressions. -/
theorem a144696Polynomial_eulerian_identity (n : ℕ) :
    C 2 * a144696Polynomial n =
      generalizedEulerian 1 (n + 1) +
        (1 - X) * generalizedEulerian 1 n := by
  induction n with
  | zero =>
      simp [a144696Polynomial, generalizedEulerian]
      simpa only [one_add_one_eq_two] using
        (Polynomial.C_ofNat (R := ℝ) 2)
  | succ n ih =>
      have ih' := congrArg Polynomial.derivative ih
      have hder : C 2 * (a144696Polynomial n).derivative =
          (generalizedEulerian 1 (n + 1)).derivative +
            (-generalizedEulerian 1 n +
              (1 - X) * (generalizedEulerian 1 n).derivative) := by
        simpa only [derivative_C, zero_mul, zero_add, derivative_add,
          derivative_mul, derivative_sub, derivative_one, derivative_X,
          one_mul, neg_mul, zero_sub] using ih'
      have hE : generalizedEulerian 1 (n + 1) =
          (1 + C ((n : ℝ) + 1) * X) * generalizedEulerian 1 n +
            X * (1 - X) * (generalizedEulerian 1 n).derivative := by
        rw [generalizedEulerian_succ]
        simp only [one_mul, map_add, map_one]
      have hEsucc : generalizedEulerian 1 (n + 1 + 1) =
          (1 + C ((n : ℝ) + 2) * X) *
              generalizedEulerian 1 (n + 1) +
            X * (1 - X) * (generalizedEulerian 1 (n + 1)).derivative := by
        convert generalizedEulerian_succ 1 (n + 1) using 1
        norm_num [map_add, map_ofNat]
        left
        ring
      rw [a144696Polynomial_succ]
      push_cast
      calc
        C 2 *
              ((1 + C ((n : ℝ) + 2) * X) * a144696Polynomial n +
                X * (1 - X) * (a144696Polynomial n).derivative) =
            (1 + C ((n : ℝ) + 2) * X) *
                (C 2 * a144696Polynomial n) +
              X * (1 - X) * (C 2 * (a144696Polynomial n).derivative) := by
                ring
        _ = (1 + C ((n : ℝ) + 2) * X) *
                (generalizedEulerian 1 (n + 1) +
                  (1 - X) * generalizedEulerian 1 n) +
              X * (1 - X) *
                ((generalizedEulerian 1 (n + 1)).derivative +
                  (-generalizedEulerian 1 n +
                    (1 - X) * (generalizedEulerian 1 n).derivative)) := by
              rw [ih, hder]
        _ = ((1 + C ((n : ℝ) + 2) * X) *
                generalizedEulerian 1 (n + 1) +
              X * (1 - X) * (generalizedEulerian 1 (n + 1)).derivative) +
              (1 - X) *
                ((1 + C ((n : ℝ) + 1) * X) *
                    generalizedEulerian 1 n +
                  X * (1 - X) * (generalizedEulerian 1 n).derivative) := by
              norm_num [map_add, map_ofNat]
              ring
        _ = generalizedEulerian 1 (n + 1 + 1) +
              (1 - X) * generalizedEulerian 1 (n + 1) := by
              rw [← hE, ← hEsucc]

/-- The Eulerian identity gives an explicit symmetric decomposition of twice
the A144696 row polynomial. -/
theorem a144696Polynomial_isIdDecomposition (n : ℕ) (hn : 1 ≤ n) :
    IsIdDecomposition n (C 2 * a144696Polynomial n)
      (C 2 * generalizedEulerian 1 n)
      (loweringEulerStep n (generalizedEulerian 1 n)) := by
  have hE : generalizedEulerian 1 (n + 1) =
      (1 + C ((n : ℝ) + 1) * X) * generalizedEulerian 1 n +
        X * (1 - X) * (generalizedEulerian 1 n).derivative := by
    rw [generalizedEulerian_succ]
    simp only [one_mul, map_add, map_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a144696Polynomial_eulerian_identity, hE]
    simp only [loweringEulerStep]
    norm_num [map_add, map_ofNat]
    ring
  · exact (natDegree_C_mul_le 2 (generalizedEulerian 1 n)).trans_eq
      (generalizedEulerian_natDegree 1 n)
  · exact natDegree_loweringEulerStep_le_pred hn
      (generalizedEulerian_natDegree 1 n).le
  · rw [IdTransform, Polynomial.reflect_C_mul,
      generalizedEulerian_one_reflect]
  · simpa [IdTransform] using
      (reflect_loweringEulerStep_of_reflect hn
        (generalizedEulerian_one_reflect n))

private theorem a144696Polynomial_reciprocal_prec_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    StrictInterl (reciprocalShift n (a144696Polynomial n))
      (a144696Polynomial n) := by
  let E := generalizedEulerian 1 n
  let b := loweringEulerStep n E
  have hEinv := generalizedEulerian_invariants (c := (1 : ℝ)) (by norm_num) n
  have hEnn : HasNonnegCoeffs E := hEinv.2.1
  have hEsplits : E.Splits := hEinv.2.2
  have hEpf : IsPFPolynomial E :=
    IsPFPolynomial.of_realRooted_nonneg hEnn hEsplits
  have hbE : StrictInterl b E := by
    apply loweringEulerStep_prec_self_of_reflect hn hEpf
    · exact generalizedEulerian_natDegree 1 n
    · simp [E]
    · exact generalizedEulerian_one_reflect n
  have hbA : StrictInterl b (C 2 * E) :=
    StrictInterl.C_mul_right hbE (by norm_num)
  have hbnn : HasNonnegCoeffs b := by
    exact loweringEulerStep_nonneg hEnn
      (generalizedEulerian_natDegree 1 n).le
  have hAnn : HasNonnegCoeffs (C 2 * E) :=
    nonnegCoeffs_C_mul (by norm_num) hEnn
  have hpdeg : (C 2 * a144696Polynomial n).natDegree ≤ n := by
    rw [natDegree_C_mul (by norm_num), natDegree_a144696Polynomial]
  have hendpoint :
      StrictInterl (IdTransform n (C 2 * a144696Polynomial n))
        (C 2 * a144696Polynomial n) :=
    (brandenSolusTheorem26_forward_of_prec_b_a hpdeg
      (a144696Polynomial_isIdDecomposition n (by lia)) hAnn hbnn hbA).2.2
  have hscaled :
      StrictInterl (C 2 * reciprocalShift n (a144696Polynomial n))
        (C 2 * a144696Polynomial n) := by
    simpa [IdTransform, reciprocalShift, Polynomial.reflect_C_mul] using hendpoint
  have hleft := StrictInterl.C_mul_left hscaled
    (a := (2 : ℝ)⁻¹) (by norm_num)
  have hboth := StrictInterl.C_mul_right hleft
    (a := (2 : ℝ)⁻¹) (by norm_num)
  have hcancel (p : ℝ[X]) : C (2 : ℝ)⁻¹ * (C 2 * p) = p := by
    rw [← mul_assoc, ← map_mul]
    norm_num
  rw [hcancel, hcancel] at hboth
  exact hboth

/-- The reciprocal of an A144696 row polynomial precedes the polynomial
itself. This is the endpoint relation for the reflected Bernstein chain. -/
theorem a144696Polynomial_reciprocal_prec (n : ℕ) :
    StrictInterl (reciprocalShift n (a144696Polynomial n))
      (a144696Polynomial n) := by
  rcases n with _ | n
  · rw [a144696Polynomial_zero]
    have hone : reciprocalShift 0 (1 : ℝ[X]) = 1 := by
      ext k
      rcases k with _ | k
      · simp [reciprocalShift]
      · simp [reciprocalShift]
    rw [hone]
    have hone0 : (1 : ℝ[X]) ≠ 0 := one_ne_zero
    have honesplits : (1 : ℝ[X]).Splits := by simp
    exact StrictInterl.refl hone0 honesplits
  · rcases n with _ | n
    · have hQ : a144696Polynomial 1 = (1 + C 2 * X : ℝ[X]) := by
        rw [a144696Polynomial_succ]
        simp [a144696Polynomial]
      rw [hQ]
      have hreflect :
          reciprocalShift 1 (1 + C 2 * X : ℝ[X]) = X + C 2 := by
        ext k
        rcases k with _ | k
        · simp [reciprocalShift]
        · rcases k with _ | k
          · simp [reciprocalShift]
          · simp [reciprocalShift]
      rw [hreflect]
      have hbase : StrictInterl (X + C 2 : ℝ[X]) (X + C (1 / 2 : ℝ)) :=
        (StrictInterl.X_add_C_iff (a := (1 / 2 : ℝ)) (b := 2)).2 (by norm_num)
      have hright := StrictInterl.C_mul_right hbase (a := (2 : ℝ)) (by norm_num)
      have hrewrite : C 2 * (X + C (1 / 2 : ℝ)) = 1 + C 2 * X := by
        calc
          C 2 * (X + C (1 / 2 : ℝ)) =
              C 2 * X + C 2 * C (1 / 2 : ℝ) := by ring
          _ = C 2 * X + C 1 := by rw [← map_mul]; norm_num
          _ = 1 + C 2 * X := by simp [add_comm]
      rwa [hrewrite] at hright
    · exact a144696Polynomial_reciprocal_prec_of_two_le (by lia)

/-- Finite second-order differential recurrence for the left endpoint of the
A144696 Bernstein-image row. -/
theorem a144696BernsteinImage_zero_recurrence {d : ℕ} (hd : 1 ≤ d) :
    a144696BernsteinImage (d + 1) 0 =
      (C 2 + C ((d : ℝ) + 2) * X) * a144696BernsteinImage d 0 +
        X * (1 - X) * (a144696BernsteinImage d 0).derivative -
          C (d : ℝ) * X * a144696BernsteinImage (d - 1) 0 := by
  rw [a144696BernsteinImage_pascal (d := d + 1) (k := 0) (by lia)]
  simp only [Nat.add_sub_cancel]
  rw [a144696BernsteinImage_succ (d := d) (k := 0) (by lia)]
  have hpascal := a144696BernsteinImage_pascal (d := d) (k := 0) (by lia)
  have hreplace : a144696BernsteinImage d 1 =
      a144696BernsteinImage d 0 - a144696BernsteinImage (d - 1) 0 := by
    linear_combination -hpascal
  rw [hreplace]
  push_cast
  norm_num [map_add, map_natCast, map_ofNat]
  ring

/-- Coefficient form of the finite left-endpoint recurrence. -/
theorem coeff_succ_a144696BernsteinImage_zero {d k : ℕ} (hd : 1 ≤ d) :
    (a144696BernsteinImage (d + 1) 0).coeff (k + 1) =
      ((k : ℝ) + 3) * (a144696BernsteinImage d 0).coeff (k + 1) +
        ((d : ℝ) - k + 2) * (a144696BernsteinImage d 0).coeff k -
          (d : ℝ) * (a144696BernsteinImage (d - 1) 0).coeff k := by
  have hshape : a144696BernsteinImage (d + 1) 0 =
      (C 1 * X + C (-1) * X ^ 2) *
          (a144696BernsteinImage d 0).derivative +
        (C 2 + C ((d : ℝ) + 2) * X) * a144696BernsteinImage d 0 +
          C (-(d : ℝ)) * X * a144696BernsteinImage (d - 1) 0 := by
    rw [a144696BernsteinImage_zero_recurrence hd]
    simp only [map_one, map_neg, one_mul, neg_one_mul]
    ring
  rw [hshape, coeff_add,
    Polynomial.coeff_quadratic_derivative_add_linear_mul_succ]
  rw [show C (-(d : ℝ)) * X * a144696BernsteinImage (d - 1) 0 =
      C (-(d : ℝ)) * (X * a144696BernsteinImage (d - 1) 0) by ring]
  simp only [coeff_C_mul, coeff_X_mul]
  ring

/-- The constant coefficient of the left Bernstein endpoint is `2 ^ d`. -/
theorem coeff_zero_a144696BernsteinImage_zero (d : ℕ) :
    (a144696BernsteinImage d 0).coeff 0 = (2 : ℝ) ^ d := by
  rw [a144696BernsteinImage_eq_sum, Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul, coeff_zero_a144696Polynomial, mul_one, Nat.sub_zero]
  exact_mod_cast Nat.sum_range_choose d

/-- The top coefficient of the left Bernstein endpoint is `2 ^ d`. -/
theorem coeff_top_a144696BernsteinImage_zero (d : ℕ) :
    (a144696BernsteinImage d 0).coeff d = (2 : ℝ) ^ d := by
  calc
    (a144696BernsteinImage d 0).coeff d =
        (a144696BernsteinImage d 0).leadingCoeff := by
      rw [leadingCoeff, natDegree_a144696BernsteinImage (show 0 ≤ d by lia)]
    _ = (2 : ℝ) ^ d := leadingCoeff_a144696BernsteinImage (by lia)

/-- The coefficients of the left Bernstein endpoint are palindromic. -/
theorem coeff_symm_a144696BernsteinImage_zero : ∀ d i j : ℕ, i + j = d →
    (a144696BernsteinImage d 0).coeff i =
      (a144696BernsteinImage d 0).coeff j := by
  intro d
  induction d using Nat.twoStepInduction with
  | zero =>
      intro i j hij
      have hi : i = 0 := by lia
      have hj : j = 0 := by lia
      rw [hi, hj]
  | one =>
      intro i j hij
      rcases i with _ | i
      · have hj : j = 1 := by lia
        rw [hj, coeff_zero_a144696BernsteinImage_zero,
          coeff_top_a144696BernsteinImage_zero]
      · have hi : i = 0 := by lia
        have hj : j = 0 := by lia
        subst i
        subst j
        rw [coeff_top_a144696BernsteinImage_zero,
          coeff_zero_a144696BernsteinImage_zero]
  | more n ih0 ih1 =>
      intro i j hij
      rcases i with _ | i
      · have hj : j = n + 2 := by lia
        rw [hj, coeff_zero_a144696BernsteinImage_zero,
          coeff_top_a144696BernsteinImage_zero]
      · rcases j with _ | j
        · have hi : i = n + 1 := by lia
          rw [hi, coeff_top_a144696BernsteinImage_zero,
            coeff_zero_a144696BernsteinImage_zero]
        · have hsum : i + j = n := by lia
          have hcrossLeft := ih1 (i + 1) j (by lia)
          have hcrossRight := ih1 i (j + 1) (by lia)
          have hlag := ih0 i j hsum
          rw [coeff_succ_a144696BernsteinImage_zero
                (d := n + 1) (k := i) (by lia),
            coeff_succ_a144696BernsteinImage_zero
                (d := n + 1) (k := j) (by lia)]
          simp only [Nat.add_sub_cancel]
          rw [hcrossLeft, hcrossRight, hlag]
          have hcast : (i : ℝ) + (j : ℝ) = (n : ℝ) := by
            exact_mod_cast hsum
          have hfactorLeft : (i : ℝ) + 3 =
              ((n + 1 : ℕ) : ℝ) - j + 2 := by
            push_cast
            linarith
          have hfactorRight : ((n + 1 : ℕ) : ℝ) - i + 2 =
              (j : ℝ) + 3 := by
            push_cast
            linarith
          rw [hfactorLeft, hfactorRight]
          ring

/-- The left endpoint of every A144696 Bernstein-image row is fixed by
reflection in its degree. -/
theorem a144696BernsteinImage_zero_reflect (d : ℕ) :
    (a144696BernsteinImage d 0).reflect d =
      a144696BernsteinImage d 0 := by
  ext i
  rw [coeff_reflect]
  by_cases hi : i ≤ d
  · rw [revAt_le hi]
    exact coeff_symm_a144696BernsteinImage_zero
      d (d - i) i (Nat.sub_add_cancel hi)
  · rw [revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]

/-- Every earlier member of an A144696 Bernstein-image row precedes every
later member. The proof concatenates the reflected and direct adjacent chains;
the reciprocal row-polynomial endpoint closes Wagner's endpoint-chain
criterion. -/
theorem a144696BernsteinImage_prec {d i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ d) :
    StrictInterl (a144696BernsteinImage d i) (a144696BernsteinImage d j) := by
  let H : ℕ → ℝ[X] := fun t ↦
    if t < d then
      reciprocalShift d (a144696BernsteinImage d (d - t))
    else
      a144696BernsteinImage d (t - d)
  have hpf : ∀ k, k ≤ d → IsPFPolynomial (a144696BernsteinImage d k) := by
    intro k hk
    exact IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_a144696BernsteinImage d k)
      (a144696BernsteinImage_splits hk)
  have hcons : ∀ k, 0 ≤ k → k < 2 * d → StrictInterl (H k) (H (k + 1)) := by
    intro k _ hk
    by_cases hkd : k < d
    · have hrange : d - (k + 1) < d := by lia
      have hstep := a144696BernsteinImage_horizontal_prec hrange
      have hindex : d - k = d - (k + 1) + 1 := by lia
      rw [← hindex] at hstep
      have hrev := reciprocalShift_reverses_prec
        (hpf (d - (k + 1)) (by lia)) (hpf (d - k) (by lia))
        (natDegree_a144696BernsteinImage (by lia)).le
        (natDegree_a144696BernsteinImage (by lia)).le hstep
      by_cases hsucc : k + 1 < d
      · simpa [H, hkd, hsucc, hindex] using hrev
      · have heq : k + 1 = d := by lia
        simpa [H, hkd, hsucc, heq, reciprocalShift,
          a144696BernsteinImage_zero_reflect d] using hrev
    · have hindex : k + 1 - d = (k - d) + 1 := by lia
      have hrange : k - d < d := by lia
      simpa [H, hkd, show ¬ k + 1 < d by lia, hindex] using
        (a144696BernsteinImage_horizontal_prec hrange)
  have hend : StrictInterl (H 0) (H (2 * d)) := by
    by_cases hd0 : d = 0
    · subst d
      dsimp [H]
      rw [a144696BernsteinImage_diagonal]
      have hone0 : a144696Polynomial 0 ≠ 0 := by
        rw [a144696Polynomial_zero]
        exact one_ne_zero
      have honesplits : (a144696Polynomial 0).Splits := by
        rw [a144696Polynomial_zero]
        simp
      exact StrictInterl.refl hone0 honesplits
    · dsimp [H]
      rw [ite_eq_left (Nat.pos_of_ne_zero hd0), ite_eq_right (by lia)]
      rw [show 2 * d - d = d by lia, a144696BernsteinImage_diagonal]
      exact a144696Polynomial_reciprocal_prec d
  have hall := prec_chain_of_consecutive_of_endpoint H 0 (2 * d)
    hcons hend
  have hresult := hall (d + i) (d + j) (by lia) (by lia) (by lia)
  simpa [H] using hresult

/-- The ordered list of Bernstein images in ambient degree `d`. -/
def a144696BernsteinImageRow (d : ℕ) : List ℝ[X] :=
  List.ofFn fun k : Fin (d + 1) ↦ a144696BernsteinImage d k

/-- Every A144696 Bernstein-image row is an interlacing sequence with
nonnegative coefficients. -/
theorem a144696BernsteinImageRow_isInterlacingSeqNonneg (d : ℕ) :
    IsInterlacingSeqNonneg (a144696BernsteinImageRow d) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [a144696BernsteinImageRow, List.mem_ofFn] at hp
    rcases hp with ⟨k, rfl⟩
    have hk : k.val ≤ d := by lia
    exact ⟨⟨(hasPosLeadingCoeff_a144696BernsteinImage hk).ne_zero,
      a144696BernsteinImage_splits hk⟩,
      hasNonnegCoeffs_a144696BernsteinImage d k⟩
  · rw [isInterlacingSeq_iff_pairwise, List.pairwise_iff_get]
    intro i j hij
    dsimp only [a144696BernsteinImageRow] at i j ⊢
    erw [List.get_ofFn, List.get_ofFn]
    exact a144696BernsteinImage_prec hij.le (by lia)

end RealRooted
