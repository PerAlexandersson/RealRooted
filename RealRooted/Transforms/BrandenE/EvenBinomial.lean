module

public import RealRooted.GeneralizedEulerian
public import RealRooted.SymmetricDecomposition.FPolynomial
public import RealRooted.Transforms.BrandenE.WeightedSum

/-!
# The even-binomial cone of Brändén's E transform

The even binomial sum of the ambient-degree basis images is real-rooted. We
also identify it as the f-polynomial transform of the average of the type-B
Eulerian polynomial and `(1 - X) ^ n`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The even indices in an ambient binomial basis. -/
def evenBinomialIndices (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Even

/-- The even binomial sum before applying Brändén's E transform. -/
def brandenEvenBinomialInput (n : ℕ) : ℝ[X] :=
  brandenBasisWeightedInput n (evenBinomialIndices n) fun k => n.choose k

/-- The E-image of the even binomial sum. -/
def brandenEvenBinomialImage (n : ℕ) : ℝ[X] :=
  brandenBasisWeightedSum n (evenBinomialIndices n) fun k => n.choose k

theorem brandenE_evenBinomialInput (n : ℕ) :
    brandenE (brandenEvenBinomialInput n) = brandenEvenBinomialImage n := by
  simpa [brandenEvenBinomialInput, brandenEvenBinomialImage] using
    (brandenE_basisWeightedInput (R := ℝ) n (evenBinomialIndices n)
      fun k => (n.choose k : ℝ))

private theorem zero_mem_evenBinomialIndices (n : ℕ) :
    0 ∈ evenBinomialIndices n := by
  simp [evenBinomialIndices]

private theorem mem_evenBinomialIndices_le {n k : ℕ}
    (hk : k ∈ evenBinomialIndices n) : k ≤ n := by
  simp [evenBinomialIndices] at hk
  lia

/-- The even binomial E-image is nonzero and split over the reals. -/
theorem brandenEvenBinomialImage_ne_zero_and_splits (n : ℕ) :
    brandenEvenBinomialImage n ≠ 0 ∧ (brandenEvenBinomialImage n).Splits := by
  rw [brandenEvenBinomialImage]
  apply brandenBasisWeightedSum_ne_zero_and_splits_of_nonneg_of_exists_pos
  · intro k hk
    exact mem_evenBinomialIndices_le hk
  · intro k _
    positivity
  · refine ⟨0, zero_mem_evenBinomialIndices n, ?_⟩
    simp

/-- Differentiating an f-polynomial can be expressed through the transform of
the derivative of its input. -/
theorem fPolynomial_derivative_identity {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    (X + 1) ^ 2 * (fPolynomial d p).derivative =
      C (d : ℝ) * (X + 1) * fPolynomial d p +
        fPolynomial d p.derivative := by
  classical
  have hfsum (s : Finset ℕ) (g : ℕ → ℝ[X]) :
      fPolynomial d (∑ i ∈ s, g i) = ∑ i ∈ s, fPolynomial d (g i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp_all
  rw [p.as_sum_range]
  rw [hfsum, Polynomial.derivative_sum, Finset.mul_sum]
  rw [Polynomial.derivative_sum, hfsum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := by grind
  rw [fPolynomial_monomial, ite_eq_left hk_le]
  rcases k with _ | k
  · have hder : derivative (monomial 0 (p.coeff 0)) = 0 := by simp
    rw [hder, fPolynomial_zero]
    by_cases hd : d = 0
    · simp_all
    · have hdform : d = (d - 1) + 1 := by lia
      simp only [derivative_mul, derivative_C, derivative_pow, derivative_add,
        derivative_one, derivative_X, zero_mul, add_zero]
      grind
  · rw [Polynomial.derivative_monomial]
    rw [fPolynomial_monomial, ite_eq_left (by lia)]
    by_cases heq : k + 1 = d
    · subst d
      simp only [tsub_self, pow_zero, mul_one, derivative_mul, derivative_C,
        derivative_X_pow, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
      push_cast
      norm_num at *
      ring
    · have hlt : k + 1 < d := lt_of_le_of_ne hk_le heq
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      simp only [derivative_mul, derivative_C, derivative_pow, derivative_add,
        derivative_one, derivative_X, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
      push_cast
      norm_num at *
      simp only [show k + 1 + m - k = m + 1 by lia,
        show k + 1 + m + 1 - k = m + 2 by lia]
      grind

private theorem fPolynomial_generalizedEulerian_two_succ (n : ℕ) :
    fPolynomial (n + 1) (generalizedEulerian 2 (n + 1)) =
      (1 + C 2 * X) * fPolynomial n (generalizedEulerian 2 n) +
        C 2 * X * (1 + X) *
          (fPolynomial n (generalizedEulerian 2 n)).derivative := by
  cases n with
  | zero =>
      rw [show generalizedEulerian 2 1 = 1 + X by
        rw [generalizedEulerian]
        rw [show generalizedEulerian 2 0 = 1 by rfl]
        simp]
      rw [show generalizedEulerian 2 0 = 1 by rfl]
      rw [show (1 + X : ℝ[X]) = monomial 0 1 + monomial 1 1 by
        rw [monomial_one_one_eq_X]
        simp,
        fPolynomial_add, fPolynomial_monomial, fPolynomial_monomial]
      rw [show (1 : ℝ[X]) = monomial 0 1 by simp, fPolynomial_monomial]
      norm_num [map_one, map_ofNat]
      ring
  | succ n =>
      let p := generalizedEulerian 2 (n + 1)
      have hpdeg : p.natDegree = n + 1 :=
        (generalizedEulerian_invariants (c := 2) (by norm_num) (n + 1)).1
      have hpderdeg : p.derivative.natDegree ≤ n := by simp_all
      have hrec :
          generalizedEulerian 2 (n + 2) =
            p + C (2 * (n + 1 : ℝ) + 1) * (X * p) +
              C 2 * (X * p.derivative) +
                C (-2) * (X * (X * p.derivative)) := by
        rw [generalizedEulerian_succ]
        grind
      rw [hrec]
      simp only [fPolynomial_add, fPolynomial_C_mul]
      rw [fPolynomial_succ_of_natDegree_le (by grind)]
      rw [fPolynomial_X_mul_succ, fPolynomial_X_mul_succ,
        fPolynomial_X_mul_succ]
      rw [fPolynomial_X_mul_succ n p.derivative]
      have hpad :
          fPolynomial (n + 1) p.derivative =
            (X + 1) * fPolynomial n p.derivative :=
        fPolynomial_succ_of_natDegree_le hpderdeg
      have hder := fPolynomial_derivative_identity
        (d := n + 1) (p := p) hpdeg.le
      rw [hpad] at hder
      rw [hpad]
      change
        (X + 1) * fPolynomial (n + 1) p +
            C (2 * (n + 1 : ℝ) + 1) * (X * fPolynomial (n + 1) p) +
              C 2 * (X * ((X + 1) * fPolynomial n p.derivative)) +
                C (-2) * (X * (X * fPolynomial n p.derivative)) =
          (1 + C 2 * X) * fPolynomial (n + 1) p +
            C 2 * X * (1 + X) * (fPolynomial (n + 1) p).derivative
      push_cast at hder ⊢
      norm_num [map_one, map_ofNat, map_add, map_mul, map_neg] at hder ⊢
      have hfac :
          (X + 1) *
              ((X + 1) * (fPolynomial (n + 1) p).derivative -
                ((n : ℝ[X]) + 1) * fPolynomial (n + 1) p -
                  fPolynomial n p.derivative) = 0 := by
        grind
      have hx1 : (X + 1 : ℝ[X]) ≠ 0 := by
        simpa using Polynomial.X_add_C_ne_zero (1 : ℝ)
      have hcore :
          (X + 1) * (fPolynomial (n + 1) p).derivative -
              ((n : ℝ[X]) + 1) * fPolynomial (n + 1) p -
                fPolynomial n p.derivative = 0 :=
        (mul_eq_zero.mp hfac).resolve_left hx1
      grind

/-- The f-polynomial transform of the type-B Eulerian row is the E-image of
the doubled Pascal power. -/
theorem fPolynomial_generalizedEulerian_two (n : ℕ) :
    fPolynomial n (generalizedEulerian 2 n) =
      brandenE ((1 + C 2 * X) ^ n) := by
  induction n with
  | zero =>
      rw [show generalizedEulerian 2 0 = 1 by rfl]
      have hE : brandenE (1 : ℝ[X]) = 1 := by
        rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
        rfl
      simpa [fPolynomial] using hE.symm
  | succ n ih =>
      rw [fPolynomial_generalizedEulerian_two_succ, ih]
      rw [pow_succ']
      exact (brandenE_one_add_C_mul_X 2 ((1 + C 2 * X) ^ n)).symm

theorem fPolynomial_one_sub_X_pow (n : ℕ) :
    fPolynomial n ((1 - X) ^ n) = 1 := by
  induction n with
  | zero => simp [fPolynomial]
  | succ n ih =>
      have hdeg : ((1 - X) ^ n : ℝ[X]).natDegree ≤ n := by
        have hlin : (1 - X : ℝ[X]).natDegree = 1 := by
          compute_degree
          norm_num
        simp_all
      rw [pow_succ']
      rw [show (1 - X) * (1 - X) ^ n =
          C (-1 : ℝ) * ((X - C 1) * (1 - X) ^ n) by grind]
      rw [fPolynomial_C_mul,
        fPolynomial_X_sub_C_mul_succ n 1 hdeg, ih]
      simp

private theorem two_mul_even_binomial_sum (a b : ℝ[X]) (n : ℕ) :
    C (2 : ℝ) *
        (∑ k ∈ (Finset.range (n + 1)).filter Even,
          C (n.choose k : ℝ) * a ^ k * b ^ (n - k)) =
      (a + b) ^ n + (-a + b) ^ n := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum, add_pow, add_pow,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rcases Nat.even_or_odd k with heven | hodd
  · rw [ite_eq_left heven]
    have hneg : (-a) ^ k = a ^ k := by simp_all
    rw [hneg]
    norm_num [map_ofNat]
    ring
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr hodd)]
    have hneg : (-a) ^ k = -(a ^ k) := by
      rw [show -a = (-1 : ℝ[X]) * a by ring, mul_pow,
        hodd.neg_one_pow, neg_one_mul]
    simp_all

/-- Closed form for the even binomial input to Brändén's E transform. -/
theorem brandenEvenBinomialInput_eq (n : ℕ) :
    brandenEvenBinomialInput n =
      C (1 / 2 : ℝ) * (((1 + C 2 * X) ^ n + 1 : ℝ[X])) := by
  have h := two_mul_even_binomial_sum X (X + 1) n
  have ha : X + (X + 1) = (1 + C 2 * X : ℝ[X]) := by
    norm_num [map_ofNat]
    ring
  have hb : -X + (X + 1) = (1 : ℝ[X]) := by ring
  rw [ha, hb, one_pow] at h
  rw [brandenEvenBinomialInput, brandenBasisWeightedInput, evenBinomialIndices]
  simp only [brandenBinomialBasis]
  have hhalf : C (1 / 2 : ℝ) * C 2 = (1 : ℝ[X]) := by
    rw [← C_mul]
    norm_num
  grind

/-- The f-polynomial transform of the type-D average is the even binomial
E-image. -/
theorem fPolynomial_typeD_average_eq_evenBinomialImage (n : ℕ) :
    fPolynomial n
        (C (1 / 2 : ℝ) * (generalizedEulerian 2 n + (1 - X) ^ n)) =
      brandenEvenBinomialImage n := by
  rw [fPolynomial_C_mul, fPolynomial_add,
    fPolynomial_generalizedEulerian_two, fPolynomial_one_sub_X_pow]
  rw [← brandenE_evenBinomialInput, brandenEvenBinomialInput_eq,
    brandenE_C_mul, brandenE_add]
  have hEone : brandenE (1 : ℝ[X]) = 1 := by
    rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
    rfl
  simp_all

end RealRooted
