module

public import RealRooted.MaWang.EndpointMultiplicity
import RealRooted.DerivativeRecurrence.ClosedInterval
import RealRooted.MaWang.DerivativeStep
import RealRooted.MaWang.EndpointClassification

/-!
# Cubic derivative steps with a cancelling top coefficient

We study `(a + b X + κ n X²) f + κ X (1 - X²) f'`. The coefficient of degree
`n + 2` cancels for degree-`n` inputs. The closed window is `[-1, 0]`.

Source: the unpublished manuscript in RealRooted issue #2192, comment on the cubic family.
The endpoint argument is Ma--Wang, *q-Eulerian polynomials and polynomials with only real zeros*,
Theorem 2; the alternating-run specialization is Section 3.3, Proposition 8
(arXiv:math/0611826v2). Related Lean: the existing `fPolynomial` route in
`SymmetricDecomposition/FPolynomialSequence.lean` remains a separate transform-based proof.
-/

public section

open Polynomial Set

namespace RealRooted.MaWang

/-- The cubic derivative step whose top coefficient cancels on degree-`n` inputs. -/
@[expose] noncomputable def cubicEndpointStep (a b kappa : ℝ) (n : ℕ) (f : ℝ[X]) : ℝ[X] :=
  (C a + C b * X + C (kappa * n) * X ^ 2) * f +
    C kappa * X * (1 - X ^ 2) * f.derivative

/-- The cubic step in a form suitable for coefficient extraction. -/
private lemma cubicEndpointStep_expand (a b kappa : ℝ) (n : ℕ) (f : ℝ[X]) :
    cubicEndpointStep a b kappa n f = C a * f + C b * (X * f) +
      C (kappa * n) * (X ^ 2 * f) + C kappa * (X * f.derivative) -
        C kappa * (X ^ 3 * f.derivative) := by
  unfold cubicEndpointStep
  ring

/-- Constant coefficient of a cubic endpoint step. -/
@[simp] theorem cubicEndpointStep_coeff_zero (a b kappa : ℝ) (n : ℕ) (f : ℝ[X]) :
    (cubicEndpointStep a b kappa n f).coeff 0 = a * f.coeff 0 := by
  simp only [cubicEndpointStep_expand, coeff_add, coeff_sub, coeff_C_mul,
    coeff_X_pow_mul']; simp

/-- Linear coefficient of a cubic endpoint step. -/
theorem cubicEndpointStep_coeff_one (a b kappa : ℝ) (n : ℕ) (f : ℝ[X]) :
    (cubicEndpointStep a b kappa n f).coeff 1 = (a + kappa) * f.coeff 1 + b * f.coeff 0 := by
  simp only [cubicEndpointStep_expand, coeff_add, coeff_sub, coeff_C_mul,
    coeff_X_mul, coeff_X_pow_mul', coeff_derivative]
  simp
  ring

/-- Coefficients from degree two onward satisfy a three-diagonal rule. -/
theorem cubicEndpointStep_coeff_add_two (a b kappa : ℝ) (n j : ℕ) (f : ℝ[X]) :
    (cubicEndpointStep a b kappa n f).coeff (j + 2) =
      (a + kappa * (j + 2)) * f.coeff (j + 2) + b * f.coeff (j + 1) +
        kappa * ((n : ℝ) - j) * f.coeff j := by
  cases j with
  | zero =>
    simp only [cubicEndpointStep_expand, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_mul, coeff_X_pow_mul', coeff_derivative]
    simp
    ring
  | succ j =>
    simp only [cubicEndpointStep_expand, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_mul, coeff_X_pow_mul', coeff_derivative]
    simp [Nat.add_assoc]
    ring

/-- Cubic top cancellation gives degree at most `n+1` on a degree-at-most-`n` input. -/
theorem cubicEndpointStep_natDegree_le {a b kappa : ℝ} {n : ℕ} {f : ℝ[X]}
    (hf : f.natDegree ≤ n) : (cubicEndpointStep a b kappa n f).natDegree ≤ n + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  obtain ⟨j, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by lia⟩
  rw [cubicEndpointStep_coeff_add_two,
    coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by lia)),
    coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by lia))]
  by_cases hn : j = n
  · simp [hn]
  · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by lia))]
    ring

/-- A nonnegative input retains nonnegative coefficients under cubic top cancellation. -/
theorem cubicEndpointStep_hasNonnegCoeffs {a b kappa : ℝ} {n : ℕ} {f : ℝ[X]}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ kappa)
    (hf : f.natDegree ≤ n) (hnn : HasNonnegCoeffs f) :
    HasNonnegCoeffs (cubicEndpointStep a b kappa n f) := by
  intro j
  match j with
  | 0 => simpa using mul_nonneg ha (hnn 0)
  | 1 => rw [cubicEndpointStep_coeff_one]; positivity [hnn 0, hnn 1]
  | j + 2 =>
    rw [cubicEndpointStep_coeff_add_two]
    have hlast : 0 ≤ kappa * ((n : ℝ) - j) * f.coeff j := by
      by_cases hj : j ≤ n
      · have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
        positivity [hnn j]
      · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by lia)), mul_zero]
    positivity [hnn (j + 2), hnn (j + 1)]

/-- The leading coefficient after cancellation is positive when `b>0`. -/
theorem cubicEndpointStep_natDegree_leadingCoeff {a b kappa : ℝ} {n : ℕ} {f : ℝ[X]}
    (hb : 0 < b) (hk : 0 ≤ kappa) (hf : f.natDegree = n)
    (hpos : HasPosLeadingCoeff f) (hnn : HasNonnegCoeffs f) :
    (cubicEndpointStep a b kappa n f).natDegree = n + 1 ∧
      HasPosLeadingCoeff (cubicEndpointStep a b kappa n f) := by
  have hc : 0 < (cubicEndpointStep a b kappa n f).coeff (n + 1) := by
    cases n with
    | zero =>
      rw [cubicEndpointStep_coeff_one, coeff_eq_zero_of_natDegree_lt (by lia), mul_zero,
        zero_add]
      exact mul_pos hb (by simpa [HasPosLeadingCoeff, leadingCoeff, hf] using hpos)
    | succ n =>
      rw [show n + 1 + 1 = n + 2 by lia, cubicEndpointStep_coeff_add_two,
        coeff_eq_zero_of_natDegree_lt (by lia), mul_zero, zero_add]
      have htop : 0 < f.coeff (n + 1) := by
        simpa [HasPosLeadingCoeff, leadingCoeff, hf] using hpos
      have hsub : ((n + 1 : ℕ) : ℝ) - n = 1 := by push_cast; ring
      rw [hsub, mul_one]
      exact add_pos_of_pos_of_nonneg (mul_pos hb htop) (mul_nonneg hk (hnn n))
  have hd := natDegree_eq_of_le_of_coeff_ne_zero (cubicEndpointStep_natDegree_le hf.le) hc.ne'
  exact ⟨hd, by simpa [HasPosLeadingCoeff, leadingCoeff, hd] using hc⟩

/-- The cubic step's closed-window criterion, with the degree cancellation checked. -/
theorem cubicEndpointStep_roots_mem_Icc_iff {a b kappa : ℝ} {n : ℕ} {f : ℝ[X]}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < kappa) (hf : f.natDegree = n)
    (hpos : HasPosLeadingCoeff f) (hnn : HasNonnegCoeffs f) (hs : f.Splits)
    (hroots : ∀ r ∈ f.roots, r ∈ Icc (-1 : ℝ) 0) :
    (cubicEndpointStep a b kappa n f).Splits ∧
      Interlaces f (cubicEndpointStep a b kappa n f) ∧
      ((∀ r ∈ (cubicEndpointStep a b kappa n f).roots, r ∈ Icc (-1 : ℝ) 0) ↔
        kappa * n + a - b - 2 * kappa * f.rootMultiplicity (-1) ≤ 0) := by
  have hd := cubicEndpointStep_natDegree_leadingCoeff (a := a) hb hk.le hf hpos hnn
  have hv : ∀ r ∈ Icc (-1 : ℝ) 0, (C kappa * X * (1 - X ^ 2) : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow]
    have hsq : 0 ≤ 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hk.le hr.2) hsq
  have ht := derivativeStep_roots_mem_Icc_iff hpos hd.2
    (by simpa only [cubicEndpointStep, hf] using hd.1)
    hs hroots hv (by simp) (by simp)
  change _ ∧ _ ∧ _ at ht
  refine ⟨ht.1, ht.2.1, ht.2.2.trans ?_⟩
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, derivative_mul,
    derivative_sub, derivative_one, derivative_X, derivative_pow, derivative_C,
    eval_sub, eval_one, eval_zero]
  norm_num
  constructor
  · intro h
    linarith [h.1]
  · intro h
    constructor
    · linarith
    · positivity

/-- At `-1` the cubic step increases multiplicity exactly at its affine threshold. -/
private lemma cubicEndpointStep_rootMultiplicity {a b kappa : ℝ} {n : ℕ} {f : ℝ[X]}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < kappa) (hf : f.natDegree = n)
    (hpos : HasPosLeadingCoeff f) (hnn : HasNonnegCoeffs f) (hs : f.Splits)
    (hroots : ∀ r ∈ f.roots, r ∈ Icc (-1 : ℝ) 0) :
    (cubicEndpointStep a b kappa n f).rootMultiplicity (-1) =
      if kappa * n + a - b - 2 * kappa * f.rootMultiplicity (-1) = 0
        then f.rootMultiplicity (-1) + 1 else f.rootMultiplicity (-1) := by
  have hd := cubicEndpointStep_natDegree_leadingCoeff (a := a) hb hk.le hf hpos hnn
  have ht := cubicEndpointStep_roots_mem_Icc_iff ha hb hk hf hpos hnn hs hroots
  have hm := rootMultiplicity_derivativeStep_of_eval_eq_zero hpos hd.2
    (by simpa only [cubicEndpointStep, hf] using hd.1) ht.2.1.toStrictInterl (by simp :
      (C kappa * X * (1 - X ^ 2) : ℝ[X]).eval (-1) = 0)
  change (cubicEndpointStep a b kappa n f).rootMultiplicity (-1) = _ at hm
  rw [hm]
  apply if_congr _ rfl rfl
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, derivative_mul,
    derivative_sub, derivative_one, derivative_X, derivative_pow, derivative_C,
    eval_sub, eval_one, eval_zero]
  norm_num
  constructor <;> intro h <;> nlinarith

/-- Positive constant seeds yield nonnegative cubic rows of exact degree `n` and positive
leading coefficient, regardless of whether the rows remain in the endpoint window. -/
theorem cubicEndpointSequence_coefficients {P : ℕ → ℝ[X]} {a b kappa c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < kappa) (hc : 0 < c)
    (h0 : P 0 = C c) (hrec : ∀ n, P (n + 1) = cubicEndpointStep a b kappa n (P n)) :
    ∀ n, (P n).natDegree = n ∧ HasPosLeadingCoeff (P n) ∧ HasNonnegCoeffs (P n) := by
  intro n
  induction n with
  | zero =>
    rw [h0]
    exact ⟨natDegree_C c, by simpa [HasPosLeadingCoeff] using hc,
      by intro j; simp only [coeff_C]; split_ifs <;> positivity⟩
  | succ n ih =>
    rw [hrec n]
    have hd := cubicEndpointStep_natDegree_leadingCoeff (a := a) hb hk.le ih.1 ih.2.1 ih.2.2
    exact ⟨hd.1, hd.2, cubicEndpointStep_hasNonnegCoeffs ha.le hb.le hk.le ih.1.le ih.2.2⟩

/-- The cubic family stays in `[-1,0]` when the normalized intercept is a natural number.
Its endpoint multiplicity is the exact affine hit count, and consecutive rows interlace. -/
theorem cubicEndpointSequence {P : ℕ → ℝ[X]} {a b kappa c : ℝ} (s : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < kappa) (hc : 0 < c)
    (hparam : b - a = kappa * s) (h0 : P 0 = C c)
    (hrec : ∀ n, P (n + 1) = cubicEndpointStep a b kappa n (P n)) :
    ∀ n, (P n).Splits ∧ (∀ r ∈ (P n).roots, r ∈ Icc (-1 : ℝ) 0) ∧
      (P n).rootMultiplicity (-1) = affineEndpointMultiplicity 2 s n ∧
      Interlaces (P n) (P (n + 1)) := by
  have hcoeff := cubicEndpointSequence_coefficients ha hb hk hc h0 hrec
  have hinv : ∀ n, (P n).Splits ∧ (∀ r ∈ (P n).roots, r ∈ Icc (-1 : ℝ) 0) ∧
      (P n).rootMultiplicity (-1) = affineEndpointMultiplicity 2 s n := by
    intro n
    induction n with
    | zero =>
      rw [h0]
      simp [affineEndpointMultiplicity, Polynomial.Splits.C]
    | succ n ih =>
      have ht := cubicEndpointStep_roots_mem_Icc_iff ha hb hk (hcoeff n).1
        (hcoeff n).2.1 (hcoeff n).2.2 ih.1 ih.2.1
      have hm := cubicEndpointStep_rootMultiplicity ha hb hk (hcoeff n).1
        (hcoeff n).2.1 (hcoeff n).2.2 ih.1 ih.2.1
      have hbound := affineEndpointMultiplicity_threshold 2 s n (by norm_num)
      have hineq : kappa * n + a - b - 2 * kappa * (P n).rootMultiplicity (-1) ≤ 0 := by
        rw [ih.2.2]
        norm_num at hbound
        nlinarith
      rw [← hrec n] at ht hm
      refine ⟨ht.1, ht.2.2.mpr hineq, ?_⟩
      rw [hm, ih.2.2, affineEndpointMultiplicity_succ 2 s n (by norm_num)]
      apply if_congr _ rfl rfl
      norm_num
      constructor <;> intro h <;> nlinarith
  intro n
  have hi := hinv n
  exact ⟨hi.1, hi.2.1, hi.2.2, by
    rw [hrec n]
    exact (cubicEndpointStep_roots_mem_Icc_iff ha hb hk (hcoeff n).1
      (hcoeff n).2.1 (hcoeff n).2.2 hi.1 hi.2.1).2.1⟩

/-- Sharp all-index window classification for the cubic family: `(b-a)/κ` must be a
nonnegative integer. This is independent of the positive constant seed normalization. -/
theorem cubicEndpointSequence_roots_mem_Icc_iff {P : ℕ → ℝ[X]} {a b kappa c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < kappa) (hc : 0 < c)
    (h0 : P 0 = C c) (hrec : ∀ n, P (n + 1) = cubicEndpointStep a b kappa n (P n)) :
    (∀ n, (P n).Splits ∧ ∀ r ∈ (P n).roots, r ∈ Icc (-1 : ℝ) 0) ↔
      ∃ s : ℕ, b - a = kappa * s := by
  constructor
  · intro hall
    have hcoeff := cubicEndpointSequence_coefficients ha hb hk hc h0 hrec
    let m : ℕ → ℕ := fun n => (P n).rootMultiplicity (-1)
    have hm0 : m 0 = 0 := by simp [m, h0]
    have hstep : ∀ n, m (n + 1) =
        if (1 / 2 : ℝ) * n - (b - a) / (2 * kappa) = m n then m n + 1 else m n := by
      intro n
      have ht := cubicEndpointStep_rootMultiplicity ha hb hk (hcoeff n).1
        (hcoeff n).2.1 (hcoeff n).2.2 (hall n).1 (hall n).2
      dsimp [m]
      rw [hrec n, ht]
      apply if_congr _ rfl rfl
      field_simp
      constructor <;> intro h <;> nlinarith
    have hbound : ∀ n, (1 / 2 : ℝ) * n - (b - a) / (2 * kappa) ≤ m n := by
      intro n
      have ht := cubicEndpointStep_roots_mem_Icc_iff ha hb hk (hcoeff n).1
        (hcoeff n).2.1 (hcoeff n).2.2 (hall n).1 (hall n).2
      have hineq := ht.2.2.mp (by rw [← hrec n]; exact (hall (n + 1)).2)
      dsimp [m]
      have heq : (1 / 2 : ℝ) * n - (b - a) / (2 * kappa) =
          (kappa * n + a - b) / (2 * kappa) := by field_simp; ring
      rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * kappa)]
      nlinarith
    obtain ⟨s, -, hs⟩ := exists_affine_hit (by norm_num : (0 : ℝ) < 1 / 2)
      hm0 hstep hbound 0
    refine ⟨s, ?_⟩
    norm_num at hs
    rw [sub_eq_zero, eq_div_iff (by positivity : (2 * kappa) ≠ 0)] at hs
    nlinarith
  · rintro ⟨s, hs⟩ n
    exact ⟨(cubicEndpointSequence s ha hb hk hc hs h0 hrec n).1,
      (cubicEndpointSequence s ha hb hk hc hs h0 hrec n).2.1⟩

/-- The cubic recurrence never acquires a zero root from a positive constant seed. -/
theorem cubicEndpointSequence_eval_zero {P : ℕ → ℝ[X]} {a b kappa c : ℝ}
    (h0 : P 0 = C c) (hrec : ∀ n, P (n + 1) = cubicEndpointStep a b kappa n (P n))
    (n : ℕ) : (P n).eval 0 = c * a ^ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [hrec n, ← coeff_zero_eq_eval_zero, cubicEndpointStep_coeff_zero,
      coeff_zero_eq_eval_zero, ih, pow_succ]
    ring

/-- Every interior root in the confined cubic family is simple. -/
theorem cubicEndpointSequence_interior_rootMultiplicity_le_one
    {P : ℕ → ℝ[X]} {a b kappa c : ℝ} (s : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < kappa) (hc : 0 < c)
    (hparam : b - a = kappa * s) (h0 : P 0 = C c)
    (hrec : ∀ n, P (n + 1) = cubicEndpointStep a b kappa n (P n))
    (n : ℕ) {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 0) : (P n).rootMultiplicity r ≤ 1 := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hstep := (cubicEndpointSequence s ha hb hk hc hparam h0 hrec n).2.2.2
    rw [hrec n, cubicEndpointStep] at hstep ⊢
    apply rootMultiplicity_derivativeStep_le_one hstep.toStrictInterl _ ih
    simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one, eval_pow, ne_eq, mul_eq_zero]
    have hsq : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    exact fun h => h.elim (fun h => h.elim hk.ne' hr.2.ne) hsq.ne'

end RealRooted.MaWang
