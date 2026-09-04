import RealRooted.Apolarity
import RealRooted.DegreeDropReversal
import RealRooted.HadamardProduct
import RealRooted.PFPolynomial

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Hadamard and Schur--Szego algebra

Foundational coefficient-support, fixed-degree Schur--Szego composition,
diagonal-operator, Jensen-section, and degree-three discriminant identities.
-/

theorem support_hadamardProduct_eq_filter_right (p q : ℝ[X]) :
    (hadamardProduct p q).support = p.support.filter fun n => q.coeff n ≠ 0 := by
  rw [hadamardProduct_eq_diagonalOperator, support_diagonalOperator_eq_filter]

theorem support_hadamardProduct_eq_filter_left (p q : ℝ[X]) :
    (hadamardProduct p q).support = q.support.filter fun n => p.coeff n ≠ 0 :=
  (congrArg (fun r : ℝ[X] => r.support) (hadamardProduct_comm p q)).trans
    (support_hadamardProduct_eq_filter_right q p)

/-- The support of a Hadamard product is the intersection of the two
supports. -/
theorem support_hadamardProduct_eq (p q : ℝ[X]) :
    (hadamardProduct p q).support = p.support ∩ q.support := by
  rw [support_hadamardProduct_eq_filter_right]
  ext n
  simp [mem_support_iff]

/-- The support of a Hadamard product is contained in the left support. -/
theorem support_hadamardProduct_subset_left (p q : ℝ[X]) :
    (hadamardProduct p q).support ⊆ p.support :=
  (support_hadamardProduct_eq p q).symm ▸
    (Finset.inter_subset_left : p.support ∩ q.support ⊆ p.support)

/-- The support of a Hadamard product is contained in the right support. -/
theorem support_hadamardProduct_subset_right (p q : ℝ[X]) :
    (hadamardProduct p q).support ⊆ q.support :=
  (support_hadamardProduct_eq p q).symm ▸
    (Finset.inter_subset_right : p.support ∩ q.support ⊆ q.support)

theorem natDegree_hadamardProduct_le_left (p q : ℝ[X]) :
    (hadamardProduct p q).natDegree ≤ p.natDegree :=
  (hadamardProduct_eq_diagonalOperator p q).symm ▸
    natDegree_diagonalOperator_le _ _

theorem natDegree_hadamardProduct_le_right (p q : ℝ[X]) :
    (hadamardProduct p q).natDegree ≤ q.natDegree :=
  (hadamardProduct_comm p q).symm ▸ natDegree_hadamardProduct_le_left q p

/-- A Hadamard product vanishes exactly when the two coefficient supports are
disjoint. -/
theorem hadamardProduct_eq_zero_iff_support_disjoint (p q : ℝ[X]) :
    hadamardProduct p q = 0 ↔ Disjoint p.support q.support := by
  rw [← support_eq_empty, support_hadamardProduct_eq,
    Finset.disjoint_iff_inter_eq_empty]

/-- Fixed-degree Schur--Szego composition.  If
`f = ∑ binom(n,k) a_k X^k` and `g = ∑ binom(n,k) b_k X^k`, then
`schurSzegoComp n f g = ∑ binom(n,k) a_k b_k X^k`. -/
def schurSzegoComp (n : Nat) (f g : ℝ[X]) : ℝ[X] :=
  Finset.sum (Finset.range (n + 1))
    (fun k => monomial k (f.coeff k * g.coeff k / (Nat.choose n k : ℝ)))

theorem coeff_schurSzegoComp (n k : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff k =
      if k ≤ n then f.coeff k * g.coeff k / (Nat.choose n k : ℝ) else 0 := by
  rw [schurSzegoComp, finsetSum_coeff]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    simp [coeff_monomial, hk]
  · rw [if_neg hk]
    simp [coeff_monomial, Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_not_le hk))]

theorem coeff_schurSzegoComp_of_le {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k / (Nat.choose n k : ℝ) := by
  simp [coeff_schurSzegoComp, hk]

theorem coeff_schurSzegoComp_eq_zero_of_lt {n k : Nat} (hk : n < k) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff k = 0 := by
  simp [coeff_schurSzegoComp, not_le_of_gt hk]

theorem schurSzegoComp_comm (n : Nat) (f g : ℝ[X]) :
    schurSzegoComp n f g = schurSzegoComp n g f := by
  ext k
  simp [coeff_schurSzegoComp, mul_comm]

theorem natDegree_schurSzegoComp_le (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hk =>
    coeff_schurSzegoComp_eq_zero_of_lt hk f g

/-- The fixed-degree Schur--Szegő composition of two binomial lifts is the
binomial lift of the coefficientwise Hadamard product of the underlying
coefficient sequences. -/
theorem schurSzegoComp_binomialLift (n : Nat) (f₀ g₀ : ℝ[X]) :
    schurSzegoComp n (binomialLift n f₀) (binomialLift n g₀) =
      binomialLift n (hadamardProduct f₀ g₀) := by
  ext k
  simp only [coeff_schurSzegoComp, coeff_binomialLift, coeff_hadamardProduct]
  by_cases hk : k ≤ n
  · simp only [if_pos hk]
    have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    field_simp
  · simp only [if_neg hk]

/-- Evaluation form of `schurSzegoComp_binomialLift`. -/
theorem schurSzegoComp_eval_eq_apolarEval (n : Nat) (f₀ g₀ : ℝ[X]) (z : ℝ) :
    (schurSzegoComp n (binomialLift n f₀) (binomialLift n g₀)).eval z =
      apolarEval n (hadamardProduct f₀ g₀) z := by
  rw [schurSzegoComp_binomialLift, eval_binomialLift]

theorem choose_mul_coeff_schurSzegoComp_of_le {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (Nat.choose n k : ℝ) * (schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k := by
  rw [coeff_schurSzegoComp_of_le hk]
  field_simp [Nat.cast_choose_ne_zero (R := ℝ) hk]

theorem choose_mul_coeff_schurSzegoComp_eq_coeff_hadamardProduct_of_le
    {n k : Nat} (hk : k ≤ n) (f g : ℝ[X]) :
    (Nat.choose n k : ℝ) * (schurSzegoComp n f g).coeff k =
      (hadamardProduct f g).coeff k := by
  rw [choose_mul_coeff_schurSzegoComp_of_le hk, coeff_hadamardProduct]

/-- Constant coefficient of a fixed-degree Schur--Szegő composition. -/
theorem coeff_zero_schurSzegoComp (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  simpa using coeff_schurSzegoComp_of_le (Nat.zero_le n) f g

/-- Linear coefficient of a fixed-degree Schur--Szegő composition. -/
theorem coeff_one_schurSzegoComp_of_one_le
    {n : Nat} (hn : 1 ≤ n) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff 1 =
      f.coeff 1 * g.coeff 1 / (n : ℝ) := by
  simpa [Nat.choose_one_right] using coeff_schurSzegoComp_of_le hn f g

/-- Quadratic coefficient of a fixed-degree Schur--Szegő composition, with
`Nat.choose n 2` expanded. -/
theorem coeff_two_schurSzegoComp_of_two_le
    {n : Nat} (hn : 2 ≤ n) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff 2 =
      2 * (f.coeff 2 * g.coeff 2) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hden : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := (mul_pos hn0 hn1).ne'
  rw [coeff_schurSzegoComp_of_le hn, Nat.cast_choose_two]
  field_simp [hden]

/-- Cubic coefficient of a fixed-degree Schur--Szegő composition, with
`Nat.choose n 3` expanded. -/
theorem coeff_three_schurSzegoComp_of_three_le
    {n : Nat} (hn : 3 ≤ n) (f g : ℝ[X]) :
    (schurSzegoComp n f g).coeff 3 =
      6 * (f.coeff 3 * g.coeff 3) /
        ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hn2 : 0 < (n : ℝ) - 2 := by linarith
  have hdenpos : 0 < (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) :=
    mul_pos (mul_pos hn0 hn1) hn2
  have hden : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ≠ 0 := hdenpos.ne'
  rw [coeff_schurSzegoComp_of_le hn, Nat.cast_choose_three]
  field_simp [hden]

/-- Fixed-degree Schur--Szego composition is a diagonal operator. -/
theorem schurSzegoComp_eq_diagonalOperator (n : Nat) (f g : ℝ[X]) :
    schurSzegoComp n f g =
      diagonalOperator (fun k => g.coeff k / (Nat.choose n k : ℝ)) f := by
  ext k
  rw [coeff_diagonalOperator, coeff_schurSzegoComp]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    ring
  · rw [if_neg hk]
    simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)]

/-- Coefficient expansion of the cubic discriminant of a fixed-degree
Schur--Szegő composition.  This is the Schur--Szegő analogue of
`cubicDiscr_diagonalOperator`, with the second factor converted to the
normalized diagonal sequence `g.coeff k / Nat.choose n k`. -/
theorem cubicDiscr_schurSzegoComp (n : Nat) (f g : ℝ[X]) :
    cubicDiscr (schurSzegoComp n f g) =
      18 * ((g.coeff 3 / (Nat.choose n 3 : ℝ)) * f.coeff 3) *
          ((g.coeff 2 / (Nat.choose n 2 : ℝ)) * f.coeff 2) *
          ((g.coeff 1 / (Nat.choose n 1 : ℝ)) * f.coeff 1) *
          ((g.coeff 0 / (Nat.choose n 0 : ℝ)) * f.coeff 0)
        - 4 * ((g.coeff 2 / (Nat.choose n 2 : ℝ)) * f.coeff 2) ^ 3 *
          ((g.coeff 0 / (Nat.choose n 0 : ℝ)) * f.coeff 0)
        + ((g.coeff 2 / (Nat.choose n 2 : ℝ)) * f.coeff 2) ^ 2 *
          ((g.coeff 1 / (Nat.choose n 1 : ℝ)) * f.coeff 1) ^ 2
        - 4 * ((g.coeff 3 / (Nat.choose n 3 : ℝ)) * f.coeff 3) *
          ((g.coeff 1 / (Nat.choose n 1 : ℝ)) * f.coeff 1) ^ 3
        - 27 * ((g.coeff 3 / (Nat.choose n 3 : ℝ)) * f.coeff 3) ^ 2 *
          ((g.coeff 0 / (Nat.choose n 0 : ℝ)) * f.coeff 0) ^ 2 := by
  rw [schurSzegoComp_eq_diagonalOperator, cubicDiscr_diagonalOperator]

/-- Arithmetic core for rewriting the level-`n` degree-three Jensen section in
terms of an iterated derivative of the reflected degree-`n` polynomial. -/
theorem six_mul_choose_mul_descFactorial_sub_three_eq_choose_three_mul_factorial
    {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ 3) :
    6 * (Nat.choose n k * (n - k).descFactorial (n - 3)) =
      Nat.choose 3 k * Nat.factorial n := by
  interval_cases k
  · simp
    have hsub : n - (n - 3) = 3 := by lia
    simpa [hsub, Nat.factorial] using
      Nat.factorial_mul_descFactorial (n := n) (k := n - 3) (by lia)
  · norm_num [Nat.choose_one_right]
    have hsub : n - 1 - (n - 3) = 2 := by lia
    have hdesc : 2 * (n - 1).descFactorial (n - 3) = Nat.factorial (n - 1) := by
      simpa [hsub, Nat.factorial] using
        Nat.factorial_mul_descFactorial (n := n - 1) (k := n - 3) (by lia)
    have hfact : Nat.factorial (n - 1) * n = Nat.factorial n := by
      simpa [Nat.descFactorial_one, mul_comm] using
        Nat.factorial_mul_descFactorial (n := n) (k := 1) (by lia)
    calc
      6 * (n * (n - 1).descFactorial (n - 3)) =
          3 * ((2 * (n - 1).descFactorial (n - 3)) * n) := by ring
      _ = 3 * (Nat.factorial (n - 1) * n) := by rw [hdesc]
      _ = 3 * Nat.factorial n := by rw [hfact]
  · norm_num
    have hsub : n - 2 - (n - 3) = 1 := by lia
    have hdesc : (n - 2).descFactorial (n - 3) = Nat.factorial (n - 2) := by
      simpa [hsub] using
        Nat.factorial_mul_descFactorial (n := n - 2) (k := n - 3) (by lia)
    have hchoose :
        Nat.choose n 2 * 2 * Nat.factorial (n - 2) = Nat.factorial n := by
      simpa [Nat.factorial] using
        Nat.choose_mul_factorial_mul_factorial (show 2 ≤ n from by lia)
    calc
      6 * (Nat.choose n 2 * (n - 2).descFactorial (n - 3)) =
          3 * (Nat.choose n 2 * 2 * (n - 2).descFactorial (n - 3)) := by
        ring
      _ = 3 * (Nat.choose n 2 * 2 * Nat.factorial (n - 2)) := by rw [hdesc]
      _ = 3 * Nat.factorial n := by rw [hchoose]
  · norm_num
    rw [Nat.descFactorial_self,
      ← Nat.choose_mul_factorial_mul_factorial (show 3 ≤ n from hn)]
    ring

/-- Real-valued ratio form of
`six_mul_choose_mul_descFactorial_sub_three_eq_choose_three_mul_factorial`. -/
theorem choose_three_div_choose_eq_six_mul_descFactorial_div_factorial
    {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ 3) :
    (Nat.choose 3 k : ℝ) / (Nat.choose n k : ℝ) =
      (6 : ℝ) * ((n - k).descFactorial (n - 3) : ℝ) /
        Nat.factorial n := by
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 :=
    Nat.cast_choose_ne_zero (R := ℝ) (hk.trans hn)
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h :
      (6 : ℝ) *
          ((Nat.choose n k : ℝ) * ((n - k).descFactorial (n - 3) : ℝ)) =
        (Nat.choose 3 k : ℝ) * (Nat.factorial n : ℝ) := by
    exact_mod_cast
      six_mul_choose_mul_descFactorial_sub_three_eq_choose_three_mul_factorial
        hn hk
  field_simp [hchoose, hfact]
  rw [← h]
  ring

/-- Coefficient form of
`choose_three_div_choose_eq_six_mul_descFactorial_div_factorial`, matching the
degree-three Jensen coefficient with the scaled reflected-derivative
coefficient. -/
theorem choose_three_mul_normalized_coeff_eq_descFactorial_coeff
    {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ 3) (p : ℝ[X]) :
    (Nat.choose 3 k : ℝ) * (p.coeff k / (Nat.choose n k : ℝ)) =
      ((6 : ℝ) / Nat.factorial n) *
        (((n - k).descFactorial (n - 3) : ℝ) * p.coeff k) := by
  calc
    (Nat.choose 3 k : ℝ) * (p.coeff k / (Nat.choose n k : ℝ)) =
        ((Nat.choose 3 k : ℝ) / (Nat.choose n k : ℝ)) * p.coeff k := by ring
    _ = ((6 : ℝ) * ((n - k).descFactorial (n - 3) : ℝ) / Nat.factorial n) *
        p.coeff k := by
      rw [choose_three_div_choose_eq_six_mul_descFactorial_div_factorial hn hk]
    _ = ((6 : ℝ) / Nat.factorial n) *
        (((n - k).descFactorial (n - 3) : ℝ) * p.coeff k) := by ring

/-- Coefficient form of the level-`n` degree-three Jensen section, written with
the descending-factorial coefficient that appears after reflecting and
differentiating `n - 3` times. -/
theorem coeff_jensenPolynomial_three_normalized_eq_descFactorial_coeff
    {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ 3) (p : ℝ[X]) :
    (jensenPolynomial 3 (fun j => p.coeff j / (Nat.choose n j : ℝ))).coeff k =
      ((6 : ℝ) / Nat.factorial n) *
        (((n - k).descFactorial (n - 3) : ℝ) * p.coeff k) := by
  simpa [coeff_jensenPolynomial, hk] using
    choose_three_mul_normalized_coeff_eq_descFactorial_coeff hn hk p

/-- Coefficient form of the reflected iterated-derivative side of the
level-`n` degree-three Jensen section identity. -/
theorem coeff_reflect_iterate_derivative_reflect_eq_descFactorial_coeff
    {n k : ℕ} (hn : 3 ≤ n) (hk : k ≤ 3) (p : ℝ[X]) :
    (reflect 3 ((derivative^[n - 3]) (reflect n p))).coeff k =
      ((n - k).descFactorial (n - 3) : ℝ) * p.coeff k := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hk,
    Polynomial.coeff_iterate_derivative, Polynomial.coeff_reflect,
    show 3 - k + (n - 3) = n - k from by lia,
    Polynomial.revAt_le (Nat.sub_le n k), Nat.sub_sub_self (hk.trans hn),
    nsmul_eq_mul]

/-- The level-`n` degree-three Jensen section is a scalar multiple of the
degree-three reflection of the `(n - 3)`rd derivative of the degree-`n`
reflection. -/
theorem jensenPolynomial_three_normalized_eq_reflect_iterate_derivative
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ)) =
      C ((6 : ℝ) / Nat.factorial n) *
        reflect 3 ((derivative^[n - 3]) (reflect n p)) := by
  ext k
  by_cases hk : k ≤ 3
  · rw [coeff_jensenPolynomial_three_normalized_eq_descFactorial_coeff hn hk p,
      coeff_C_mul,
      coeff_reflect_iterate_derivative_reflect_eq_descFactorial_coeff hn hk p]
  · have hder_deg : ((derivative^[n - 3]) (reflect n p)).natDegree ≤ 3 :=
      (natDegree_iterate_derivative _ _).trans <| by
        have : (reflect n p).natDegree ≤ n :=
          Polynomial.natDegree_reflect_le.trans (by rw [max_eq_left hpdeg])
        lia
    have hzero : (reflect 3 ((derivative^[n - 3]) (reflect n p))).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt
        (Polynomial.natDegree_reflect_le.trans (by rw [max_eq_left hder_deg]))
        (Nat.lt_of_not_le hk)
    rw [coeff_C_mul, hzero, mul_zero, coeff_jensenPolynomial, if_neg hk]

/-- If the left factor has degree at most three, the fixed-degree
Schur--Szego composition is the degree-three Jensen polynomial attached to the
coefficientwise product of the two binomial-normalized coefficient sequences. -/
theorem schurSzegoComp_eq_jensenPolynomial_three_normalized
    {n : Nat} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    schurSzegoComp n f p =
      jensenPolynomial 3 (fun k =>
        (p.coeff k / (Nat.choose n k : ℝ)) *
          (f.coeff k / (Nat.choose 3 k : ℝ))) := by
  ext k
  rw [coeff_schurSzegoComp, coeff_jensenPolynomial]
  by_cases hk3 : k ≤ 3
  · have hchoose3 : (Nat.choose 3 k : ℝ) ≠ 0 :=
      Nat.cast_choose_ne_zero (R := ℝ) hk3
    by_cases hkn : k ≤ n
    · simp only [hk3, hkn, if_true]
      field_simp [hchoose3]
    · have hnlt : n < k := Nat.lt_of_not_le hkn
      simp [hk3, hkn, Nat.choose_eq_zero_of_lt hnlt]
  · have hklt : 3 < k := Nat.lt_of_not_le hk3
    have hfcoeff : f.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hfdeg hklt)
    simp [hk3, hfcoeff]

/-- Cubic-discriminant form of
`schurSzegoComp_eq_jensenPolynomial_three_normalized`. -/
theorem cubicDiscr_schurSzegoComp_eq_jensenPolynomial_three_normalized
    {n : Nat} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    cubicDiscr (schurSzegoComp n f p) =
      cubicDiscr
        (jensenPolynomial 3 (fun k =>
          (p.coeff k / (Nat.choose n k : ℝ)) *
            (f.coeff k / (Nat.choose 3 k : ℝ)))) :=
  congrArg cubicDiscr (schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg)

/-- Diagonal-operator form of
`schurSzegoComp_eq_jensenPolynomial_three_normalized`: the degree-`≤ 3` factor
provides the diagonal sequence acting on the degree-three Jensen polynomial of
the other binomially normalized coefficient sequence. -/
theorem schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized
    {n : Nat} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    schurSzegoComp n f p =
      diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))) := by
  rw [schurSzegoComp_eq_jensenPolynomial_three_normalized hfdeg,
    ← jensenPolynomial_mul_sequence_eq_diagonalOperator
      3 (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (fun k => p.coeff k / (Nat.choose n k : ℝ))]
  congr with k
  ring

/-- Cubic-discriminant form of
`schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized`. -/
theorem cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized
    {n : Nat} {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3) :
    cubicDiscr (schurSzegoComp n f p) =
      cubicDiscr
        (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
          (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ)))) :=
  congrArg cubicDiscr
    (schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized hfdeg)

/-- Degree-three Schur--Szego composition, written as a diagonal operator applied
to a reflected iterated derivative of the right factor. -/
theorem schurSzegoComp_eq_diagonalOperator_reflect_iterate_derivative_three
    {n : Nat} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n) :
    schurSzegoComp n f p =
      diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (C ((6 : ℝ) / Nat.factorial n) *
          reflect 3 ((derivative^[n - 3]) (reflect n p))) := by
  rw [schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized hfdeg,
    jensenPolynomial_three_normalized_eq_reflect_iterate_derivative hn hpdeg]

/-- Scalar-pulled form of
`schurSzegoComp_eq_diagonalOperator_reflect_iterate_derivative_three`. -/
theorem schurSzegoComp_eq_C_mul_diagonalOperator_reflect_iterate_derivative_three
    {n : Nat} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n) :
    schurSzegoComp n f p =
      C ((6 : ℝ) / Nat.factorial n) *
        diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
          (reflect 3 ((derivative^[n - 3]) (reflect n p))) := by
  rw [schurSzegoComp_eq_diagonalOperator_reflect_iterate_derivative_three
    hn hfdeg hpdeg, diagonalOperator_C_mul]

/-- Cubic discriminant form of
`schurSzegoComp_eq_C_mul_diagonalOperator_reflect_iterate_derivative_three`. -/
theorem cubicDiscr_schurSzegoComp_eq_reflect_diagonalOperator_three
    {n : Nat} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n) :
    cubicDiscr (schurSzegoComp n f p) =
      ((6 : ℝ) / Nat.factorial n) ^ 4 *
        cubicDiscr
          (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
            (reflect 3 ((derivative^[n - 3]) (reflect n p)))) := by
  rw [schurSzegoComp_eq_C_mul_diagonalOperator_reflect_iterate_derivative_three
    hn hfdeg hpdeg, cubicDiscr_C_mul]

/-- Nonnegativity transfer through the reflected-derivative form of degree-three
Schur--Szego composition. -/
theorem cubicDiscr_schurSzegoComp_nonneg_of_reflect_diagonalOperator_three
    {n : Nat} (hn : 3 ≤ n) {f p : ℝ[X]}
    (hfdeg : f.natDegree ≤ 3) (hpdeg : p.natDegree ≤ n)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (reflect 3 ((derivative^[n - 3]) (reflect n p))))) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) := by
  rw [cubicDiscr_schurSzegoComp_eq_reflect_diagonalOperator_three hn hfdeg hpdeg]
  positivity

/-- Iterated derivatives of a splitting polynomial are zero or split. -/
theorem iterate_derivative_eq_zero_or_splits {p : ℝ[X]} (hsplit : p.Splits)
    (n : ℕ) :
    (derivative^[n]) p = 0 ∨ ((derivative^[n]) p).Splits := by
  induction n with
  | zero => exact Or.inr hsplit
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using eq_zero_or_splits_derivative ih

/-- The iterated derivative of the degree-`n` reflection has degree at most
three after `n - 3` derivatives. -/
theorem natDegree_iterate_derivative_reflect_le_three
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    ((derivative^[n - 3]) (reflect n p)).natDegree ≤ 3 := by
  calc
    ((derivative^[n - 3]) (reflect n p)).natDegree ≤
        (reflect n p).natDegree - (n - 3) := by
      simpa using natDegree_iterate_derivative (reflect n p) (n - 3)
    _ ≤ n - (n - 3) := Nat.sub_le_sub_right
      (Polynomial.natDegree_reflect_le.trans <| by rw [max_eq_left hpdeg]) _
    _ = 3 := by lia

/-- The reflected iterated-derivative section has degree at most three. -/
theorem natDegree_reflect_iterate_derivative_reflect_le_three
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n) :
    (reflect 3 ((derivative^[n - 3]) (reflect n p))).natDegree ≤ 3 :=
  Polynomial.natDegree_reflect_le.trans <| by
    rw [max_eq_left (natDegree_iterate_derivative_reflect_le_three hn hpdeg)]

/-- The reflected iterated-derivative section of a splitting polynomial also
splits. -/
theorem reflect_iterate_derivative_reflect_splits_of_splits
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    (reflect 3 ((derivative^[n - 3]) (reflect n p))).Splits := by
  have hreflect : (reflect n p).Splits :=
    DegreeDropReversal.splits_reflect_of_splits hsplit hpdeg
  have hqsplit : ((derivative^[n - 3]) (reflect n p)).Splits :=
    (iterate_derivative_eq_zero_or_splits hreflect (n - 3)).elim
      (fun h => by simp [h]) id
  exact DegreeDropReversal.splits_reflect_of_splits hqsplit
    (natDegree_iterate_derivative_reflect_le_three hn hpdeg)

/-- The level-`n` degree-three Jensen section of a splitting polynomial is
real-rooted, via the reflected iterated-derivative identity. -/
theorem jensenPolynomial_three_normalized_eq_zero_or_splits_of_splits
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ)) = 0 ∨
      (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))).Splits := by
  simpa [jensenPolynomial_three_normalized_eq_reflect_iterate_derivative hn hpdeg] using
    Or.inr ((reflect_iterate_derivative_reflect_splits_of_splits hn hpdeg hsplit).C_mul _)

/-- Cubic-discriminant nonnegativity for the level-`n` degree-three Jensen
section of a splitting polynomial. -/
theorem cubicDiscr_jensenPolynomial_three_normalized_nonneg_of_splits
    {n : ℕ} (hn : 3 ≤ n) {p : ℝ[X]} (hpdeg : p.natDegree ≤ n)
    (hsplit : p.Splits) :
    0 ≤ cubicDiscr
      (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))) := by
  rcases jensenPolynomial_three_normalized_eq_zero_or_splits_of_splits
      hn hpdeg hsplit with hzero | hsplit'
  · simp [hzero, cubicDiscr]
  · exact cubicDiscr_nonneg_of_splits_natDegree_le_three
      (natDegree_jensenPolynomial_le 3 _) hsplit'

/-- Denominator-cleared numerator of the fixed-degree Schur--Szegő cubic
discriminant after substituting the coefficient formulas
`(schurSzegoComp n f p).coeff k = f.coeff k * p.coeff k / C(n, k)`. -/
def schurSzegoCompCubicDiscrNumerator (n : ℕ) (f p : ℝ[X]) : ℝ :=
  18 * (f.coeff 3 * p.coeff 3) * (f.coeff 2 * p.coeff 2)
      * (f.coeff 1 * p.coeff 1) * (f.coeff 0 * p.coeff 0)
      * (n : ℝ) ^ 2 * (Nat.choose n 2 : ℝ) ^ 2 * (Nat.choose n 3 : ℝ)
    - 4 * (f.coeff 2 * p.coeff 2) ^ 3 * (f.coeff 0 * p.coeff 0)
      * (n : ℝ) ^ 3 * (Nat.choose n 3 : ℝ) ^ 2
    + (f.coeff 2 * p.coeff 2) ^ 2 * (f.coeff 1 * p.coeff 1) ^ 2
      * (n : ℝ) * (Nat.choose n 2 : ℝ) * (Nat.choose n 3 : ℝ) ^ 2
    - 4 * (f.coeff 3 * p.coeff 3) * (f.coeff 1 * p.coeff 1) ^ 3
      * (Nat.choose n 2 : ℝ) ^ 3 * (Nat.choose n 3 : ℝ)
    - 27 * (f.coeff 3 * p.coeff 3) ^ 2 * (f.coeff 0 * p.coeff 0) ^ 2
      * (n : ℝ) ^ 3 * (Nat.choose n 2 : ℝ) ^ 3

/-- Denominator-cleared form of the cubic-discriminant nonnegativity target for
the fixed-degree Schur--Szegő composition, for a level `n ≥ 3`.

Substituting the explicit coefficient formulas into `cubicDiscr` produces a
rational function with denominator
`(n : ℝ)^3 * C(n,2)^3 * C(n,3)^2`, which is positive when `3 ≤ n`.  Clearing it
gives nonnegativity of `schurSzegoCompCubicDiscrNumerator n f p`. -/
theorem cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (f p : ℝ[X]) :
    0 ≤ cubicDiscr (schurSzegoComp n f p) ↔
      0 ≤ schurSzegoCompCubicDiscrNumerator n f p := by
  have h1n : 1 ≤ n := le_trans (by norm_num) hn
  have h2n : 2 ≤ n := le_trans (by norm_num) hn
  have hc2R : (0 : ℝ) < (Nat.choose n 2 : ℝ) := by exact_mod_cast Nat.choose_pos h2n
  have hc3R : (0 : ℝ) < (Nat.choose n 3 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hn
  have hc2ne : (Nat.choose n 2 : ℝ) ≠ 0 := ne_of_gt hc2R
  have hc3ne : (Nat.choose n 3 : ℝ) ≠ 0 := ne_of_gt hc3R
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hKpos : (0 : ℝ) <
      (n : ℝ) ^ 3 * (Nat.choose n 2 : ℝ) ^ 3 * (Nat.choose n 3 : ℝ) ^ 2 := by
    positivity
  have hEq : cubicDiscr (schurSzegoComp n f p)
      * ((n : ℝ) ^ 3 * (Nat.choose n 2 : ℝ) ^ 3 * (Nat.choose n 3 : ℝ) ^ 2) =
      schurSzegoCompCubicDiscrNumerator n f p := by
    unfold cubicDiscr schurSzegoCompCubicDiscrNumerator
    rw [coeff_schurSzegoComp_of_le (Nat.zero_le n) f p,
        coeff_schurSzegoComp_of_le h1n f p,
        coeff_schurSzegoComp_of_le h2n f p,
        coeff_schurSzegoComp_of_le hn f p,
        Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one]
    field_simp
  rw [← mul_nonneg_iff_of_pos_right hKpos, hEq]

/-- The diagonal-operator Jensen form is enough for the denominator-cleared
cubic-discriminant numerator.

This isolates the remaining degree-three PF-factor kernel: after the
`p`-side has been rewritten as its normalized Jensen section, it remains to
prove cubic-discriminant nonnegativity for the diagonal action attached to the
degree-`≤ 3` PF factor `f`. -/
theorem schurSzegoCompCubicDiscrNumerator_nonneg_of_diagonalOperator_jensen_nonneg
    {n : ℕ} (hn : 3 ≤ n) {f p : ℝ[X]} (hfdeg : f.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr
      (diagonalOperator (fun k => f.coeff k / (Nat.choose 3 k : ℝ))
        (jensenPolynomial 3 (fun k => p.coeff k / (Nat.choose n k : ℝ))))) :
    0 ≤ schurSzegoCompCubicDiscrNumerator n f p :=
  (cubicDiscr_schurSzegoComp_nonneg_iff_of_three_le hn f p).1 <| by
    simpa [cubicDiscr_schurSzegoComp_eq_diagonalOperator_jensenPolynomial_three_normalized
      hfdeg] using hdisc

theorem support_schurSzegoComp_eq_filter_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support =
      f.support.filter (fun k => g.coeff k / (Nat.choose n k : ℝ) ≠ 0) := by
  rw [schurSzegoComp_eq_diagonalOperator, support_diagonalOperator_eq_filter]

theorem support_schurSzegoComp_eq_filter_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support =
      g.support.filter (fun k => f.coeff k / (Nat.choose n k : ℝ) ≠ 0) :=
  (congrArg (fun r : ℝ[X] => r.support) (schurSzegoComp_comm n f g)).trans
    (support_schurSzegoComp_eq_filter_right n g f)

theorem support_schurSzegoComp_eq_hadamardProduct_inter_range
    (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support =
      (hadamardProduct f g).support ∩ Finset.range (n + 1) := by
  rw [support_schurSzegoComp_eq_filter_right, support_hadamardProduct_eq_filter_right]
  ext k
  by_cases hk : k ≤ n
  · have hchoose_nat : Nat.choose n k ≠ 0 := Nat.choose_ne_zero hk
    simp [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, hk, hchoose_nat]
  · have hchoose_nat : Nat.choose n k = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hk)
    simp [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, hk, hchoose_nat]

theorem support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    (schurSzegoComp n f g).support = (hadamardProduct f g).support := by
  rw [support_schurSzegoComp_eq_hadamardProduct_inter_range, Finset.inter_eq_left]
  intro k hk
  have hk_le : k ≤ (hadamardProduct f g).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (mem_support_iff.mp hk)
  simpa [Finset.mem_range] using Nat.lt_succ_of_le (hk_le.trans hfg)

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 := by
  rw [← support_eq_empty, ← support_eq_empty,
    support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le hfg]

theorem support_schurSzegoComp_eq_inter_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    (schurSzegoComp n f g).support = f.support ∩ g.support := by
  rw [support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le hfg,
    support_hadamardProduct_eq]

theorem schurSzegoComp_eq_zero_iff_support_disjoint_of_hadamardProduct_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hfg : (hadamardProduct f g).natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ Disjoint f.support g.support := by
  rw [schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le hfg,
    hadamardProduct_eq_zero_iff_support_disjoint]

theorem support_schurSzegoComp_eq_hadamardProduct_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    (schurSzegoComp n f g).support = (hadamardProduct f g).support :=
  support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 :=
  schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem support_schurSzegoComp_eq_inter_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    (schurSzegoComp n f g).support = f.support ∩ g.support :=
  support_schurSzegoComp_eq_inter_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem schurSzegoComp_eq_zero_iff_support_disjoint_of_left_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hf : f.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ Disjoint f.support g.support :=
  schurSzegoComp_eq_zero_iff_support_disjoint_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_left f g).trans hf)

theorem support_schurSzegoComp_eq_hadamardProduct_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    (schurSzegoComp n f g).support = (hadamardProduct f g).support :=
  support_schurSzegoComp_eq_hadamardProduct_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ hadamardProduct f g = 0 :=
  schurSzegoComp_eq_zero_iff_hadamardProduct_eq_zero_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem support_schurSzegoComp_eq_inter_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    (schurSzegoComp n f g).support = f.support ∩ g.support :=
  support_schurSzegoComp_eq_inter_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem schurSzegoComp_eq_zero_iff_support_disjoint_of_right_natDegree_le
    {n : Nat} {f g : ℝ[X]} (hg : g.natDegree ≤ n) :
    schurSzegoComp n f g = 0 ↔ Disjoint f.support g.support :=
  schurSzegoComp_eq_zero_iff_support_disjoint_of_hadamardProduct_natDegree_le
    ((natDegree_hadamardProduct_le_right f g).trans hg)

theorem schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le
    {n : Nat} {gamma : ℕ → ℝ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    schurSzegoComp n (jensenPolynomial n gamma) p = diagonalOperator gamma p := by
  rw [schurSzegoComp_eq_diagonalOperator]
  ext k
  rw [coeff_diagonalOperator, coeff_diagonalOperator, coeff_jensenPolynomial]
  by_cases hk : k ≤ n
  · have hchoose : (Nat.choose n k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hk
    simp only [hk, if_true]
    field_simp [hchoose]
  · have hk_lt : n < k := Nat.lt_of_not_le hk
    have hp_coeff : p.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hk_lt)
    simp [hk, hp_coeff]

@[simp] theorem schurSzegoComp_zero_left (n : Nat) (p : ℝ[X]) :
    schurSzegoComp n 0 p = 0 := by
  ext k
  simp [coeff_schurSzegoComp]

@[simp] theorem schurSzegoComp_zero_right (n : Nat) (f : ℝ[X]) :
    schurSzegoComp n f 0 = 0 := by
  rw [schurSzegoComp_comm, schurSzegoComp_zero_left]

/-- Schur--Szego composition is additive in its left argument. -/
theorem schurSzegoComp_add_left (n : Nat) (f f' g : ℝ[X]) :
    schurSzegoComp n (f + f') g =
      schurSzegoComp n f g + schurSzegoComp n f' g := by
  simpa [schurSzegoComp_eq_diagonalOperator] using
    diagonalOperator_add (fun k => g.coeff k / (Nat.choose n k : ℝ)) f f'

/-- Schur--Szego composition is additive in its right argument. -/
theorem schurSzegoComp_add_right (n : Nat) (f g g' : ℝ[X]) :
    schurSzegoComp n f (g + g') =
      schurSzegoComp n f g + schurSzegoComp n f g' := by
  rw [schurSzegoComp_comm n f (g + g'), schurSzegoComp_add_left,
    schurSzegoComp_comm n g f, schurSzegoComp_comm n g' f]

/-- Scalars pull out of the left argument of a Schur--Szego composition. -/
theorem schurSzegoComp_C_mul_left (n : Nat) (a : ℝ) (f g : ℝ[X]) :
    schurSzegoComp n (C a * f) g = C a * schurSzegoComp n f g := by
  simpa [schurSzegoComp_eq_diagonalOperator] using
    diagonalOperator_C_mul (fun k => g.coeff k / (Nat.choose n k : ℝ)) a f

/-- Scalars pull out of the right argument of a Schur--Szego composition. -/
theorem schurSzegoComp_C_mul_right (n : Nat) (a : ℝ) (f g : ℝ[X]) :
    schurSzegoComp n f (C a * g) = C a * schurSzegoComp n f g := by
  rw [schurSzegoComp_comm n f (C a * g), schurSzegoComp_C_mul_left,
    schurSzegoComp_comm n g f]

theorem natDegree_schurSzegoComp_le_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).natDegree ≤ f.natDegree :=
  (schurSzegoComp_eq_diagonalOperator n f g).symm ▸
    natDegree_diagonalOperator_le _ _

theorem natDegree_schurSzegoComp_le_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).natDegree ≤ g.natDegree :=
  (schurSzegoComp_comm n f g).symm ▸ natDegree_schurSzegoComp_le_left n g f

/-- The support of a Schur--Szego composition is contained in the left
support. -/
theorem support_schurSzegoComp_subset_left (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support ⊆ f.support :=
  (support_schurSzegoComp_eq_filter_right n f g).symm ▸
    Finset.filter_subset _ _

/-- The support of a Schur--Szego composition is contained in the right
support. -/
theorem support_schurSzegoComp_subset_right (n : Nat) (f g : ℝ[X]) :
    (schurSzegoComp n f g).support ⊆ g.support :=
  (support_schurSzegoComp_eq_filter_left n f g).symm ▸
    Finset.filter_subset _ _

/-- Nonnegative coefficients are preserved by fixed-degree Schur--Szego
composition. -/
theorem HasNonnegCoeffs.schurSzegoComp {n : Nat} {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) :
    HasNonnegCoeffs (schurSzegoComp n f g) :=
  (schurSzegoComp_eq_diagonalOperator n f g).symm ▸
    hf.diagonalOperator fun k => div_nonneg (hg k) (by positivity)
end RealRooted
