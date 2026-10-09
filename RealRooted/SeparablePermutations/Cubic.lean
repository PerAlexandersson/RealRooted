import RealRooted.SeparablePermutations.Gamma

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted.SeparablePermutations

private lemma gammaBasisTerm_mul (a b i j : ℕ) (hi : 2 * i ≤ a) (hj : 2 * j ≤ b) :
    gammaBasisTerm a i * gammaBasisTerm b j = gammaBasisTerm (a + b) (i + j) := by
  unfold RealRooted.gammaBasisTerm
  have hsub : a + b - 2 * (i + j) = (a - 2 * i) + (b - 2 * j) := by
    lia
  rw [hsub, pow_add]
  ring

private lemma gammaTransform_mul_of_natDegree_le {a b : ℕ} {p q : ℝ[X]}
    (hp : p.natDegree ≤ a / 2) (hq : q.natDegree ≤ b / 2) :
    gammaTransform (a + b) (p * q) = gammaTransform a p * gammaTransform b q := by
  rw [p.as_sum_range_C_mul_X_pow' (n := a / 2 + 1) (by lia),
    q.as_sum_range_C_mul_X_pow' (n := b / 2 + 1) (by lia)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp_rw [gammaTransform_finset_sum]
  simp only [gammaTransform_C_mul, mul_assoc]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i ≤ b / 2 := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hj' : j ≤ a / 2 := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hij : i + j ≤ (a + b) / 2 := by
    lia
  rw [show X ^ j * (C (q.coeff i) * X ^ i) =
      C (q.coeff i) * X ^ (i + j) by
        rw [pow_add]
        ring]
  have hpa : gammaTransform a (X ^ j) = gammaBasisTerm a j := by
    simpa using (gammaTransform_C_mul_X_pow (D := a) (i := j) 1 (by lia))
  have hqb : gammaTransform b (X ^ i) = gammaBasisTerm b i := by
    simpa using (gammaTransform_C_mul_X_pow (D := b) (i := i) 1 (by lia))
  have hbasis : gammaBasisTerm a j * gammaBasisTerm b i =
      gammaBasisTerm (a + b) (i + j) := by
    rw [gammaBasisTerm_mul a b j i (by lia) (by lia)]
    simp [Nat.add_comm]
  rw [gammaTransform_C_mul_X_pow _ hij, hpa, hqb, ← hbasis]
  ring

private lemma gammaTransform_succ_of_natDegree_le (d : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ d / 2) :
    gammaTransform (d + 1) p = (X + 1) * gammaTransform d p := by
  rcases Nat.even_or_odd d with hd | hd
  · obtain ⟨m, rfl⟩ := hd
    simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (gammaTransform_odd m p)
  · obtain ⟨m, rfl⟩ := hd
    have hdiv : (2 * m + 1) / 2 = m := by
      apply Nat.div_eq_of_lt_le <;> lia
    have hp' : p.natDegree ≤ m := by simpa [hdiv] using hp
    have hp'' : p.natDegree ≤ (2 * m) / 2 := by simpa using hp'
    calc
      gammaTransform (2 * m + 1 + 1) p = gammaTransform (2 * m + 2) p := by
        congr 1
      _ = (X + 1) ^ 2 * gammaTransform (2 * m) p :=
        gammaTransform_pad_two (d := 2 * m) (γ := p) hp''
      _ = (X + 1) * ((X + 1) * gammaTransform (2 * m) p) := by ring
      _ = (X + 1) * gammaTransform (2 * m + 1) p := by
        rw [gammaTransform_odd]

private lemma gammaTransform_three_mul_of_natDegree_le
    {a b c : ℕ} {p q r : ℝ[X]}
    (hp : p.natDegree ≤ a / 2) (hq : q.natDegree ≤ b / 2)
    (hr : r.natDegree ≤ c / 2) :
    gammaTransform (a + b + c) (p * q * r) =
      gammaTransform a p * gammaTransform b q * gammaTransform c r := by
  calc
    gammaTransform (a + b + c) (p * q * r) =
        gammaTransform (a + b) (p * q) * gammaTransform c r := by
      rw [gammaTransform_mul_of_natDegree_le]
      · exact Polynomial.natDegree_mul_le.trans (by lia)
      · exact hr
    _ = gammaTransform a p * gammaTransform b q * gammaTransform c r := by
      rw [gammaTransform_mul_of_natDegree_le hp hq]

/-- The ambient-degree gamma transform of a family of gamma-polynomials. -/
def transformedPolynomial (Γ : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  gammaTransform (n - 1) (Γ n)

@[simp] theorem transformedPolynomial_zero {Γ : ℕ → ℝ[X]} (hΓ : Γ 0 = 0) :
    transformedPolynomial Γ 0 = 0 := by
  simp [transformedPolynomial, hΓ]

private lemma transformedPolynomial_mul_sum
    {Γ : ℕ → ℝ[X]} (hzero : Γ 0 = 0)
    (hdeg : ∀ m, (Γ m).natDegree ≤ (m - 1) / 2) {n : ℕ} (hn : 2 ≤ n) :
    gammaTransform (n - 1)
        (X * ∑ i ∈ range n, Γ i * Γ (n - 1 - i)) =
      X * ∑ i ∈ range n,
        transformedPolynomial Γ i * transformedPolynomial Γ (n - 1 - i) := by
  by_cases hn2 : n = 2
  · subst n
    simp [transformedPolynomial, hzero, Finset.sum_range_succ]
  have hn3 : 3 ≤ n := by lia
  calc
    gammaTransform (n - 1) (X * ∑ i ∈ range n, Γ i * Γ (n - 1 - i)) =
        gammaTransform ((n - 3) + 2) (X * ∑ i ∈ range n, Γ i * Γ (n - 1 - i)) := by
      congr 1; lia
    _ = X * gammaTransform (n - 3) (∑ i ∈ range n, Γ i * Γ (n - 1 - i)) :=
      gammaTransform_X_mul_two _ _
    _ = X * ∑ i ∈ range n, transformedPolynomial Γ i *
          transformedPolynomial Γ (n - 1 - i) := by
      rw [gammaTransform_finset_sum]
      apply congrArg (fun p : ℝ[X] => X * p)
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg (fun p : ℝ[X] => p)
      by_cases hi0 : i = 0
      · subst hi0
        simp [transformedPolynomial, hzero]
      by_cases hj0 : n - 1 - i = 0
      · rw [hj0]
        simp [transformedPolynomial, hzero]
      have hi_pos : 1 ≤ i := by lia
      have hj_pos : 1 ≤ n - 1 - i := by lia
      have hmul := gammaTransform_mul_of_natDegree_le
        (a := i - 1) (b := n - 1 - i - 1) (p := Γ i) (q := Γ (n - 1 - i))
        (hdeg i) (hdeg (n - 1 - i))
      calc
        gammaTransform (n - 3) (Γ i * Γ (n - 1 - i)) =
            gammaTransform (i - 1 + (n - 1 - i - 1))
              (Γ i * Γ (n - 1 - i)) := by congr 1; lia
        _ = gammaTransform (i - 1) (Γ i) *
              gammaTransform (n - 1 - i - 1) (Γ (n - 1 - i)) := hmul
        _ = transformedPolynomial Γ i * transformedPolynomial Γ (n - 1 - i) := by
          rfl

private lemma transformedPolynomial_three_sum
    {Γ : ℕ → ℝ[X]} (hzero : Γ 0 = 0)
    (hdeg : ∀ m, (Γ m).natDegree ≤ (m - 1) / 2) {n : ℕ} (hn : 2 ≤ n) :
    gammaTransform (n - 1)
        (X * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          Γ i * Γ j * Γ (n - i - j)) =
      X * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
        transformedPolynomial Γ i * transformedPolynomial Γ j *
          transformedPolynomial Γ (n - i - j) := by
  by_cases hn2 : n = 2
  · subst n
    simp [transformedPolynomial, hzero, Finset.sum_range_succ]
  have hn3 : 3 ≤ n := by lia
  calc
    gammaTransform (n - 1)
        (X * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          Γ i * Γ j * Γ (n - i - j)) =
        gammaTransform ((n - 3) + 2)
          (X * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
            Γ i * Γ j * Γ (n - i - j)) := by
      congr 1; lia
    _ = X * gammaTransform (n - 3)
        (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          Γ i * Γ j * Γ (n - i - j)) := gammaTransform_X_mul_two _ _
    _ = X * ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
        transformedPolynomial Γ i * transformedPolynomial Γ j *
          transformedPolynomial Γ (n - i - j) := by
      simp_rw [gammaTransform_finset_sum]
      apply congrArg (fun p : ℝ[X] => X * p)
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hi0 : i = 0
      · subst hi0
        simp [transformedPolynomial, hzero]
      by_cases hj0 : j = 0
      · subst hj0
        simp [transformedPolynomial, hzero]
      by_cases hk0 : n - i - j = 0
      · rw [hk0]
        simp [transformedPolynomial, hzero]
      have hi_pos : 1 ≤ i := by lia
      have hj_pos : 1 ≤ j := by lia
      have hk_pos : 1 ≤ n - i - j := by lia
      have hmul := gammaTransform_three_mul_of_natDegree_le
        (a := i - 1) (b := j - 1) (c := n - i - j - 1)
        (p := Γ i) (q := Γ j) (r := Γ (n - i - j))
        (hdeg i) (hdeg j) (hdeg (n - i - j))
      calc
        gammaTransform (n - 3) (Γ i * Γ j * Γ (n - i - j)) =
            gammaTransform (i - 1 + (j - 1) + (n - i - j - 1))
              (Γ i * Γ j * Γ (n - i - j)) := by congr 1; lia
        _ = gammaTransform (i - 1) (Γ i) * gammaTransform (j - 1) (Γ j) *
              gammaTransform (n - i - j - 1) (Γ (n - i - j)) := hmul
        _ = transformedPolynomial Γ i * transformedPolynomial Γ j *
              transformedPolynomial Γ (n - i - j) := by rfl

/-! The gamma recurrence is kept as a hypothesis here: its independent proof is the
    combinatorial/algebraic part of the Fu--Lin--Zeng argument. -/

/-- The gamma substitution sends the Fu--Lin--Zeng cubic recurrence to the descent cubic. -/
theorem transformedPolynomial_cubic
    {Γ : ℕ → ℝ[X]} (hzero : Γ 0 = 0) (hone : Γ 1 = 1)
    (hdeg : ∀ n, (Γ n).natDegree ≤ (n - 1) / 2)
    (hrec : ∀ {n : ℕ}, 2 ≤ n →
      Γ n = Γ (n - 1) + X * (∑ i ∈ range n, Γ i * Γ (n - 1 - i)) +
        X * (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          Γ i * Γ j * Γ (n - i - j))) :
    ∀ {n : ℕ}, 2 ≤ n →
      transformedPolynomial Γ n = transformedPolynomial Γ (n - 1) +
        X * transformedPolynomial Γ (n - 1) +
        X * (∑ i ∈ range n,
          transformedPolynomial Γ i * transformedPolynomial Γ (n - 1 - i)) +
        X * (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          transformedPolynomial Γ i * transformedPolynomial Γ j *
            transformedPolynomial Γ (n - i - j)) := by
  intro n hn
  have hbase : transformedPolynomial Γ 1 = 1 := by
    simp [transformedPolynomial, hone, RealRooted.gammaTransform]
  rw [transformedPolynomial, hrec hn]
  rw [gammaTransform_add, gammaTransform_add]
  have hprev : (Γ (n - 1)).natDegree ≤ (n - 2) / 2 := by
    simpa [show n - 1 - 1 = n - 2 by lia] using hdeg (n - 1)
  have hshift := gammaTransform_succ_of_natDegree_le (n - 2) (Γ (n - 1)) hprev
  have hshift' : gammaTransform (n - 1) (Γ (n - 1)) =
      (X + 1) * gammaTransform (n - 2) (Γ (n - 1)) := by
    calc
      gammaTransform (n - 1) (Γ (n - 1)) =
          gammaTransform ((n - 2) + 1) (Γ (n - 1)) := by congr 1; lia
      _ = (X + 1) * gammaTransform (n - 2) (Γ (n - 1)) := hshift
  have hquad := transformedPolynomial_mul_sum hzero hdeg hn
  have hcube := transformedPolynomial_three_sum hzero hdeg hn
  have hprevpoly : transformedPolynomial Γ (n - 1) =
      gammaTransform (n - 2) (Γ (n - 1)) := by
    unfold transformedPolynomial
    rw [show n - 1 - 1 = n - 2 by lia]
  rw [hshift']
  rw [hquad, hcube]
  rw [hprevpoly]
  ring

/-- The descent-polynomial cubic follows once the separate gamma-polynomial cubic is supplied.

The hypothesis `hrec` is the explicit boundary at which the independent
Fu--Lin--Zeng gamma recurrence enters this algebraic transfer file. -/
theorem descentPolynomial_cubic_of_gammaPolynomial_cubic
    (hrec : ∀ {n : ℕ}, 2 ≤ n →
      gammaPolynomial n = gammaPolynomial (n - 1) +
        X * (∑ i ∈ range n, gammaPolynomial i * gammaPolynomial (n - 1 - i)) +
        X * (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          gammaPolynomial i * gammaPolynomial j * gammaPolynomial (n - i - j))) :
    ∀ {n : ℕ}, 2 ≤ n →
      descentPolynomial n = descentPolynomial (n - 1) + X * descentPolynomial (n - 1) +
        X * (∑ i ∈ range n, descentPolynomial i * descentPolynomial (n - 1 - i)) +
        X * (∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          descentPolynomial i * descentPolynomial j * descentPolynomial (n - i - j)) := by
  have hdeg : ∀ n, (gammaPolynomial n).natDegree ≤ (n - 1) / 2 := by
    intro n
    match n with
    | 0 => simp [gammaPolynomial_zero]
    | 1 => simp [gammaPolynomial_one]
    | N + 2 => rw [natDegree_gammaPolynomial (by lia)]
  intro n hn
  simpa [transformedPolynomial, descentPolynomial] using
    (transformedPolynomial_cubic (Γ := gammaPolynomial) gammaPolynomial_zero
      gammaPolynomial_one hdeg hrec hn)

end RealRooted.SeparablePermutations
