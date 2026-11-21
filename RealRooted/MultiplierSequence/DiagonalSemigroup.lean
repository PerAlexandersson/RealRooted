module

public import RealRooted.MultiplierSequence.Infinite
import RealRooted.MultiplierSequence.FiniteQuadraticExponential
import RealRooted.MultiplierSequence.Bidiagonal
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Diagonal PF semigroups and local Jensen tests

We classify the diagonal semigroups `X^k ↦ exp (t g k) X^k` on a finite degree range.
For `d ≥ 2`, preservation at all nonnegative times and real-rootedness of one Jensen
family along positive times tending to zero are equivalent to a quadratic generator
with nonpositive quadratic coefficient on `0, …, d`.

Source: the unpublished manuscript statement in RealRooted issue #2320,
<https://github.com/PerAlexandersson/RealRooted/issues/2320>.
The converse uses cubic Jensen discriminants after forward shifts: their leading
term at time zero is a negative square of the third forward difference.
-/

public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- Forward shifting a finite PF multiplier consumes one degree of its range. -/
theorem IsFinitePFMultiplierSequence.shift_one {gamma : ℕ → ℝ} {n : ℕ}
    (hgamma : IsFinitePFMultiplierSequence (n + 1) gamma) :
    IsFinitePFMultiplierSequence n (fun k => gamma (k + 1)) := by
  intro p hp hdeg
  have hXdeg : (X * p).natDegree ≤ n + 1 := calc
    _ ≤ 1 + p.natDegree := by simpa using natDegree_mul_le (p := X) (q := p)
    _ ≤ n + 1 := by lia
  have hPF := hgamma hp.X_mul hXdeg
  apply hPF.of_X_sub_C_mul_factor (u := 0)
  simp only [C_0, sub_zero]
  ext (_ | k) <;> simp [coeff_X_mul]

/-- Forward shifting a finite PF multiplier consumes the shift from its degree range. -/
theorem IsFinitePFMultiplierSequence.shift {gamma : ℕ → ℝ} (r : ℕ) {n : ℕ}
    (hgamma : IsFinitePFMultiplierSequence (n + r) gamma) :
    IsFinitePFMultiplierSequence n (fun k => gamma (k + r)) := by
  induction r generalizing gamma with
  | zero =>
      intro p hp hdeg
      simpa using hgamma hp hdeg
  | succ r ih =>
      have h1 : IsFinitePFMultiplierSequence (n + r) (fun k => gamma (k + 1)) :=
        IsFinitePFMultiplierSequence.shift_one hgamma
      have h2 : IsFinitePFMultiplierSequence n (fun k => gamma (k + r + 1)) := ih h1
      intro p hp hdeg
      simpa only [Nat.add_assoc] using h2 hp hdeg

/-- Vanishing third forward differences determine a quadratic on a finite interval. -/
private lemma eq_quadratic_of_third_difference {d : ℕ} (g : ℕ → ℝ)
    (hdiff : ∀ r, r + 3 ≤ d → g r - 3 * g (r + 1) + 3 * g (r + 2) - g (r + 3) = 0) :
    ∀ k, k ≤ d → g k =
      ((g 2 - 2 * g 1 + g 0) / 2) * (k : ℝ) ^ 2 +
        (g 1 - g 0 - (g 2 - 2 * g 1 + g 0) / 2) * k + g 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      rcases k with (_ | _ | _ | k)
      · simp
      · norm_num
      · norm_num
        ring
      · have h0 := ih k (by lia) (by lia)
        have h1 := ih (k + 1) (by lia) (by lia)
        have h2 := ih (k + 2) (by lia) (by lia)
        have h3 := hdiff k (by lia)
        rw [h0, h1, h2] at h3
        norm_num [Nat.cast_add, Nat.cast_one] at h3 ⊢
        linarith

/-- The second-order term of the cubic Jensen discriminant forces the third
forward difference of a generator to vanish at a repeated-root initial row. -/
private lemma cubic_exp_third_difference (g : ℕ → ℝ) {τ : ℕ → ℝ}
    (hpos : ∀ n, 0 < τ n) (hτ : Tendsto τ atTop (𝓝 0))
    (hs : ∀ n, (jensenPolynomial 3 (fun k => Real.exp (τ n * g k))).Splits) :
    g 0 - 3 * g 1 + 3 * g 2 - g 3 = 0 := by
  let Z (n k : ℕ) := (Real.exp (τ n * g k) - 1) / τ n
  have hne : Tendsto τ atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hτ, ?_⟩
    exact Filter.Eventually.of_forall (fun n => (hpos n).ne')
  have hZ (k : ℕ) : Tendsto (fun n => Z n k) atTop (𝓝 (g k)) := by
    have hd := ((hasDerivAt_id (0 : ℝ)).mul_const (g k)).exp
    simpa [Z, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hd.tendsto_slope_zero.comp hne
  let R₃ (z : Fin 4 → ℝ) :=
    6 * (z 0 * z 1 * z 2 + z 0 * z 1 * z 3 + z 0 * z 2 * z 3 + z 1 * z 2 * z 3) -
      4 * (z 2 ^ 3 + 3 * z 0 * z 2 ^ 2) + 6 * (z 1 * z 2 ^ 2 + z 1 ^ 2 * z 2) -
      4 * (z 1 ^ 3 + 3 * z 3 * z 1 ^ 2) - 2 * (z 3 * z 0 ^ 2 + z 3 ^ 2 * z 0)
  let R₄ (z : Fin 4 → ℝ) :=
    6 * z 0 * z 1 * z 2 * z 3 - 4 * z 0 * z 2 ^ 3 + 3 * z 1 ^ 2 * z 2 ^ 2 -
      4 * z 3 * z 1 ^ 3 - z 3 ^ 2 * z 0 ^ 2
  let G (v : ℝ × (Fin 4 → ℝ)) :=
    -(v.2 0 - 3 * v.2 1 + 3 * v.2 2 - v.2 3) ^ 2 + v.1 * R₃ v.2 + v.1 ^ 2 * R₄ v.2
  have hG : Continuous G := by dsimp [G, R₃, R₄]; fun_prop
  have hlim : Tendsto (fun n => G (τ n, fun k : Fin 4 => Z n k)) atTop
      (𝓝 (-(g 0 - 3 * g 1 + 3 * g 2 - g 3) ^ 2)) := by
    simpa [G, Function.comp_def] using hG.continuousAt.tendsto.comp
      (hτ.prodMk_nhds (tendsto_pi_nhds.mpr (fun k : Fin 4 => hZ k)))
  have hnonneg (n : ℕ) : 0 ≤ G (τ n, fun k : Fin 4 => Z n k) := by
    have heq (k : ℕ) : Real.exp (τ n * g k) = 1 + τ n * Z n k := by
      dsimp [Z]
      field_simp [(hpos n).ne']
      ring
    have hdisc := cubicDiscr_jensenPolynomial_three_nonneg_of_eq_zero_or_splits
      (Or.inr (hs n))
    rw [cubicDiscr_jensenPolynomial_three] at hdisc
    have hid : 6 * Real.exp (τ n * g 3) * Real.exp (τ n * g 2) *
          Real.exp (τ n * g 1) * Real.exp (τ n * g 0) -
        4 * Real.exp (τ n * g 2) ^ 3 * Real.exp (τ n * g 0) +
        3 * Real.exp (τ n * g 2) ^ 2 * Real.exp (τ n * g 1) ^ 2 -
        4 * Real.exp (τ n * g 3) * Real.exp (τ n * g 1) ^ 3 -
        Real.exp (τ n * g 3) ^ 2 * Real.exp (τ n * g 0) ^ 2 =
          τ n ^ 2 * G (τ n, fun k : Fin 4 => Z n k) := by
      rw [heq 0, heq 1, heq 2, heq 3]
      dsimp [G, R₃, R₄]
      ring
    rw [hid, ← mul_assoc] at hdisc
    exact nonneg_of_mul_nonneg_right hdisc (mul_pos (by norm_num) (sq_pos_of_pos (hpos n)))
  have hlim_nonneg := ge_of_tendsto hlim (Filter.Eventually.of_forall hnonneg)
  nlinarith [sq_nonneg (g 0 - 3 * g 1 + 3 * g 2 - g 3)]

/-- A PF-preserving diagonal exponential semigroup has a quadratic generator on
its finite degree range. Its coefficients are determined by the first three values. -/
private lemma eq_quadratic_of_forall_isFinitePFMultiplierSequence_exp
    {d : ℕ} (g : ℕ → ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → IsFinitePFMultiplierSequence d (fun k => Real.exp (t * g k))) :
    ∀ k, k ≤ d → g k =
      ((g 2 - 2 * g 1 + g 0) / 2) * (k : ℝ) ^ 2 +
        (g 1 - g 0 - (g 2 - 2 * g 1 + g 0) / 2) * k + g 0 := by
  apply eq_quadratic_of_third_difference g
  intro r hr
  have hshift (t : ℝ) (ht : 0 ≤ t) : IsFinitePFMultiplierSequence 3
      (fun k => Real.exp (t * g (k + r))) :=
    IsFinitePFMultiplierSequence.shift r (IsFinitePFMultiplierSequence.mono (by lia) (h t ht))
  have hsplit (n : ℕ) : (jensenPolynomial 3
      (fun k => Real.exp ((1 / (n + 1 : ℝ)) * g (k + r)))).Splits :=
    (isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
      (hshift _ (by positivity))).splits
  have hdiff := cubic_exp_third_difference (fun k => g (k + r))
    (fun n => by positivity : ∀ n : ℕ, 0 < 1 / (n + 1 : ℝ))
    tendsto_one_div_add_atTop_nhds_zero_nat hsplit
  simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using hdiff

/-- Finite diagonal exponential PF semigroups are exactly the quadratic generators
with nonpositive quadratic coefficient, restricted to the finite degree range. -/
theorem forall_isFinitePFMultiplierSequence_exp_iff_quadratic
    {d : ℕ} (hd : 2 ≤ d) (g : ℕ → ℝ) :
    (∀ t : ℝ, 0 ≤ t → IsFinitePFMultiplierSequence d (fun k => Real.exp (t * g k))) ↔
      ∃ A B C₀ : ℝ, A ≤ 0 ∧
        ∀ k, k ≤ d → g k = A * (k : ℝ) ^ 2 + B * k + C₀ := by
  constructor
  · intro h
    refine ⟨(g 2 - 2 * g 1 + g 0) / 2,
      g 1 - g 0 - (g 2 - 2 * g 1 + g 0) / 2, g 0, ?_,
      eq_quadratic_of_forall_isFinitePFMultiplierSequence_exp g h⟩
    have hj := isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
      (IsFinitePFMultiplierSequence.mono hd (h 1 zero_le_one))
    have hlog := hj.coeffLogConcaveUpTo_of_isPF_jensenPolynomial 1 (by norm_num) (by norm_num)
    norm_num at hlog
    have hexp : Real.exp (g 0 + g 2) ≤ Real.exp (g 1 + g 1) := by
      simpa only [Real.exp_add, pow_two] using hlog
    have := Real.exp_le_exp.mp hexp
    linarith
  · rintro ⟨A, B, C₀, hA, hg⟩ t ht p hp hdeg
    have heq : diagonalOperator (fun k => Real.exp (t * g k)) p =
        diagonalOperator (fun k => Real.exp (t * (A * (k : ℝ) ^ 2 + B * k + C₀))) p :=
      diagonalOperator_congr_of_eq_on_degree (fun k hk => congrArg (fun x => Real.exp (t * x))
        (hg k hk)) hdeg
    rw [heq]
    exact isFinitePFMultiplierSequence_exp_mul_quadratic d hA B C₀ ht hp hdeg

/-- A single Jensen family splitting along positive times tending to zero
characterizes precisely the quadratic generators with nonpositive quadratic coefficient. -/
theorem exists_local_jensen_splits_iff_quadratic
    {d : ℕ} (hd : 2 ≤ d) (g : ℕ → ℝ) :
    (∃ τ : ℕ → ℝ, (∀ n, 0 < τ n) ∧ Tendsto τ atTop (𝓝 0) ∧
      ∀ n, (jensenPolynomial d (fun k => Real.exp (τ n * g k))).Splits) ↔
      ∃ A B C₀ : ℝ, A ≤ 0 ∧
        ∀ k, k ≤ d → g k = A * (k : ℝ) ^ 2 + B * k + C₀ :=
  (forall_isFinitePFMultiplierSequence_exp_iff_local_jensen d g).symm.trans
    (forall_isFinitePFMultiplierSequence_exp_iff_quadratic hd g)

/-- In degrees zero and one, every real generator gives a PF-preserving diagonal semigroup. -/
theorem isFinitePFMultiplierSequence_exp_of_le_one
    {d : ℕ} (hd : d ≤ 1) (g : ℕ → ℝ) (t : ℝ) :
    IsFinitePFMultiplierSequence d (fun k => Real.exp (t * g k)) :=
  isFinitePFMultiplierSequence_of_natDegree_le_one hd (fun _ => Real.exp_nonneg _)

/-- On all polynomial degrees, a diagonal PF semigroup has one quadratic generator
on all natural indices, with nonpositive quadratic coefficient. -/
theorem forall_isPFMultiplierSequence_exp_iff_quadratic (g : ℕ → ℝ) :
    (∀ t : ℝ, 0 ≤ t → IsPFMultiplierSequence (fun k => Real.exp (t * g k))) ↔
      ∃ A B C₀ : ℝ, A ≤ 0 ∧ ∀ k, g k = A * (k : ℝ) ^ 2 + B * k + C₀ := by
  constructor
  · intro h
    refine ⟨(g 2 - 2 * g 1 + g 0) / 2,
      g 1 - g 0 - (g 2 - 2 * g 1 + g 0) / 2, g 0, ?_, ?_⟩
    · obtain ⟨A, B, C₀, hA, hg⟩ :=
        (forall_isFinitePFMultiplierSequence_exp_iff_quadratic (d := 2) le_rfl g).mp
          (fun t ht => IsPFMultiplierSequence.finite (h t ht) 2)
      have h0 := hg 0 (by norm_num)
      have h1 := hg 1 (by norm_num)
      have h2 := hg 2 le_rfl
      norm_num at h0 h1 h2
      linarith
    · intro k
      exact eq_quadratic_of_forall_isFinitePFMultiplierSequence_exp g
        (fun t ht => IsPFMultiplierSequence.finite (h t ht) k) k le_rfl
  · rintro ⟨A, B, C₀, hA, hg⟩ t ht d
    have hseq : g = fun k : ℕ => A * (k : ℝ) ^ 2 + B * k + C₀ := funext hg
    rw [hseq]
    intro p hp hdeg
    exact isFinitePFMultiplierSequence_exp_mul_quadratic d hA B C₀ ht hp hdeg

end RealRooted
