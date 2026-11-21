module

public import RealRooted.MultiplierSequence
import RealRooted.Hadamard.Grace
import RealRooted.QuadraticRoot

/-!
# Symmetric quadratic multipliers on a finite degree range

We classify the diagonal weights `a + b k (d - k)` on degrees at most `d`.
For `d ≥ 2`, PF preservation is equivalent to `a ≥ 0` and `b ≥ 0`.
For `d ≤ 1`, only `a ≥ 0` is required. All statements include zero outputs,
and no sign condition is imposed on weights beyond the degree bound.

Source: the unpublished manuscript proof recorded in RealRooted issue #2317,
<https://github.com/PerAlexandersson/RealRooted/issues/2317>.
We use the existing quadratic Jensen identity and finite Schur–Szegő theorem.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A PF Jensen polynomial gives finite PF preservation, regardless of the
values of the diagonal sequence beyond the degree bound. -/
theorem isFinitePFMultiplierSequence_iff_jensen_isPF
    {d : ℕ} {gamma : ℕ → ℝ} :
    IsFinitePFMultiplierSequence d gamma ↔ IsPFPolynomial (jensenPolynomial d gamma) := by
  refine ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence, ?_⟩
  intro hj p hp hdeg
  rw [← schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hdeg]
  exact hj.schurSzegoComp hp (natDegree_jensenPolynomial_le d gamma) hdeg

/-- Pointwise natural powers of a finite PF multiplier remain finite PF multipliers. -/
theorem IsFinitePFMultiplierSequence.pow {d : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFinitePFMultiplierSequence d gamma) (N : ℕ) :
    IsFinitePFMultiplierSequence d (fun k => gamma k ^ N) := by
  induction N with
  | zero => intro p hp _; simpa using hp
  | succ N ih =>
      intro p hp hdeg
      simpa only [pow_succ] using (ih.mul hgamma) hp hdeg

/-- Jensen factorization of the symmetric quadratic weight on a finite degree range. -/
theorem jensenPolynomial_symmetric_quadratic (a b : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    jensenPolynomial d (fun k => a + b * (k : ℝ) * ((d : ℝ) - k)) =
      (X + 1) ^ (d - 2) *
        (C a * X ^ 2 + C (2 * a + b * (d : ℝ) * ((d : ℝ) - 1)) * X + C a) := by
  have hseq : (fun k : ℕ => a + b * (k : ℝ) * ((d : ℝ) - k)) =
      (fun k : ℕ => -b * (k : ℝ) ^ 2 + (b * d) * k + a) := by
    funext k
    ring
  rw [hseq, jensenPolynomial_quadratic_sequence_factor _ _ _ d hd]
  congr 1
  simp only [map_add, map_mul, map_neg, map_sub, map_ofNat, map_one]
  ring

/-- Removing a power of `X + 1` from a PF product leaves a PF polynomial. -/
private lemma isPFPolynomial_of_X_add_one_pow_mul {p : ℝ[X]} (n : ℕ)
    (hp : IsPFPolynomial ((X + 1) ^ n * p)) : IsPFPolynomial p := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
      apply ih
      apply hp.of_X_sub_C_mul_factor (u := -1)
      simp only [C_neg, C_1, sub_neg_eq_add, pow_succ]
      ring

/-- A symmetric quadratic with nonnegative end coefficients is PF exactly when
its middle coefficient is at least twice an end coefficient. -/
private lemma isPFPolynomial_symmetric_quadratic_iff (a m : ℝ) :
    IsPFPolynomial (C a * X ^ 2 + C m * X + C a) ↔ 0 ≤ a ∧ 2 * a ≤ m := by
  constructor
  · intro hp
    have ha := hp.hasNonnegCoeffs 0
    have hm := hp.hasNonnegCoeffs 1
    have hdisc := quadratic_disc_coeff_le_of_splits_natDegree_le_two
      (p := C a * X ^ 2 + C m * X + C a) (by compute_degree) hp.splits
    norm_num [coeff_add, coeff_C_mul, coeff_X_pow] at ha hm hdisc
    exact ⟨ha, by nlinarith⟩
  · rintro ⟨ha, hm⟩
    apply IsPFPolynomial.of_realRooted_nonneg
    · exact (((hasNonnegCoeffs_C ha).mul (hasNonnegCoeffs_X.pow 2)).add
        ((hasNonnegCoeffs_C (by linarith : 0 ≤ m)).mul hasNonnegCoeffs_X)).add
          (hasNonnegCoeffs_C ha)
    · apply quadraticPoly_splits_of_discrim_nonneg_or_linear
      dsimp [discrim]
      nlinarith

/-- For degree bounds at least two, a symmetric quadratic diagonal weight preserves
PF polynomials exactly when both parameters are nonnegative. -/
theorem isFinitePFMultiplierSequence_symmetric_quadratic_iff
    {d : ℕ} (hd : 2 ≤ d) (a b : ℝ) :
    IsFinitePFMultiplierSequence d (fun k => a + b * (k : ℝ) * ((d : ℝ) - k)) ↔
      0 ≤ a ∧ 0 ≤ b := by
  rw [isFinitePFMultiplierSequence_iff_jensen_isPF,
    jensenPolynomial_symmetric_quadratic a b hd]
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by lia : 0 < d)
  have hdsub : 0 < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  constructor
  · intro hp
    obtain ⟨ha, hb⟩ := (isPFPolynomial_symmetric_quadratic_iff a _).mp
      (isPFPolynomial_of_X_add_one_pow_mul (d - 2) hp)
    refine ⟨ha, ?_⟩
    have hprod : 0 ≤ b * ((d : ℝ) * ((d : ℝ) - 1)) := by nlinarith [hb]
    exact nonneg_of_mul_nonneg_left hprod (mul_pos hdpos hdsub)
  · rintro ⟨ha, hb⟩
    apply (isPFPolynomial_X_add_one.pow (d - 2)).mul
    apply (isPFPolynomial_symmetric_quadratic_iff a _).mpr
    exact ⟨ha, le_add_of_nonneg_right (mul_nonneg (mul_nonneg hb hdpos.le) hdsub.le)⟩

/-- In degrees zero and one, the symmetric quadratic weight acts as a constant,
so PF preservation requires only nonnegativity of that constant. -/
theorem isFinitePFMultiplierSequence_symmetric_quadratic_le_one_iff
    {d : ℕ} (hd : d ≤ 1) (a b : ℝ) :
    IsFinitePFMultiplierSequence d (fun k => a + b * (k : ℝ) * ((d : ℝ) - k)) ↔
      0 ≤ a := by
  constructor
  · intro h
    have hp := h IsPFPolynomial.one (by simp)
    have hc := hp.hasNonnegCoeffs 0
    simpa using hc
  · intro ha p hp hdeg
    have heq : diagonalOperator (fun k => a + b * (k : ℝ) * ((d : ℝ) - k)) p =
        C a * p := by
      ext k
      by_cases hk : k ≤ d
      · have hzero : (k : ℝ) * ((d : ℝ) - k) = 0 := by
          have : k = 0 ∨ k = d := by lia
          rcases this with rfl | rfl <;> simp
        simp only [coeff_diagonalOperator, coeff_C_mul]
        rw [mul_assoc b, hzero, mul_zero, add_zero]
      · have hc := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by lia : d < k))
        simp [hc]
    rw [heq]
    exact (IsPFPolynomial.of_C_nonneg ha).mul hp

/-- A PF polynomial remains PF after the nonnegative symmetric quadratic weight
is applied on any containing degree range. -/
theorem IsPFPolynomial.diagonalOperator_symmetric_quadratic
    {p : ℝ[X]} (hp : IsPFPolynomial p) {d : ℕ} (hdeg : p.natDegree ≤ d)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsPFPolynomial (diagonalOperator (fun k => a + b * (k : ℝ) * ((d : ℝ) - k)) p) := by
  by_cases hd : 2 ≤ d
  · exact (isFinitePFMultiplierSequence_symmetric_quadratic_iff hd a b).mpr ⟨ha, hb⟩ hp hdeg
  · exact (isFinitePFMultiplierSequence_symmetric_quadratic_le_one_iff
      (by lia) a b).mpr ha hp hdeg

end RealRooted
