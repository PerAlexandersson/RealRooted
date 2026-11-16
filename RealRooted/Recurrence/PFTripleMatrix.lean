module

public import RealRooted.Recurrence.CubicTransition
import RealRooted.ProductOrientation
import RealRooted.AffineProperPosition
import RealRooted.OperatorMatrix.Directed
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.WagnerX.ListInterlacing

/-!
# A sharp matrix criterion for ordered Pólya-frequency triples

The multiplication-operator matrix
`[[0, 0, 1], [l X, 0, 1], [c X, d X, a + b X]]` sends an input triple `(p, u, r)` to
`(r, r + l X p, c X p + d X u + (a + b X) r)`.  For `l > 0` it preserves every ordered
Pólya-frequency triple exactly when `a, b, d ≥ 0` and `a l ≤ c`
(`RealRooted.PreservesScaledPFTriple.iff`); `l = 1` is `RealRooted.PreservesPFTriple.iff`.  No
degree or
nonzero hypotheses are needed: the zero-`r` branch of the proof establishes the output
comparison `X p ≼ X (c p + d u)` directly.

As a corollary, the variable-parameter third-order recurrence
`P (s + 2) = (a s + b s X) P (s + 1) + e s X P s + d s X² P (s - 1)` with seeds `0, 0, 1`
has ordered Pólya-frequency triples `(P s, P s + κ X P (s - 1), P (s + 1))` for every positive
scale `κ` with `a s κ² - e s κ + d s ≤ 0` (`isOrderedPFTriple_of_recurrence_scaled`); the
choice `κ = 1` needs only `a s + d s ≤ e s` (`isOrderedPFTriple_of_recurrence`).
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The matrix `[[0, 0, 1], [l X, 0, 1], [c X, d X, a + b X]]` preserves every ordered
Pólya-frequency triple: it sends `(p, u, r)` to `(r, r + l X p, c X p + d X u + (a + b X) r)`. -/
@[expose] def PreservesScaledPFTriple (l a b c d : ℝ) : Prop :=
  ∀ p u r : ℝ[X], IsOrderedPFTriple p u r →
    IsOrderedPFTriple r (r + C l * (X * p))
      (C c * (X * p) + C d * (X * u) + (C a + C b * X) * r)

/-- The matrix `[[0, 0, 1], [X, 0, 1], [c X, d X, a + b X]]` preserves every ordered
Pólya-frequency triple: it sends `(p, u, r)` to `(r, r + X p, c X p + d X u + (a + b X) r)`. -/
@[expose] def PreservesPFTriple (a b c d : ℝ) : Prop :=
  ∀ p u r : ℝ[X], IsOrderedPFTriple p u r →
    IsOrderedPFTriple r (r + X * p) (C c * (X * p) + C d * (X * u) + (C a + C b * X) * r)

/-- The unscaled matrix is the scaled one with `l = 1`. -/
theorem preservesPFTriple_iff_preservesScaledPFTriple (a b c d : ℝ) :
    PreservesPFTriple a b c d ↔ PreservesScaledPFTriple 1 a b c d := by
  simp [PreservesPFTriple, PreservesScaledPFTriple]

private lemma isPFPolynomial_of_interl_left {r N : ℝ[X]} (hr : r ≠ 0) (h : Interl r N)
    (hN : HasNonnegCoeffs N) : IsPFPolynomial N := by
  refine IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hN ?_
  rcases h with h | h | h
  · exact absurd h hr
  · exact Or.inl h
  · exact Or.inr h.2.1.2

private lemma interl_sum4_right {p q₁ q₂ q₃ q₄ : ℝ[X]} {a₁ a₂ a₃ a₄ : ℝ}
    (h₁ : Interl p q₁) (h₂ : Interl p q₂) (h₃ : Interl p q₃) (h₄ : Interl p q₄)
    (n₁ : HasNonnegCoeffs q₁) (n₂ : HasNonnegCoeffs q₂) (n₃ : HasNonnegCoeffs q₃)
    (n₄ : HasNonnegCoeffs q₄) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) :
    Interl p (C a₁ * q₁ + C a₂ * q₂ + C a₃ * q₃ + C a₄ * q₄) := by
  have n₁₂ : HasNonnegCoeffs (C a₁ * q₁ + C a₂ * q₂) :=
    (hasNonnegCoeffs_C_mul ha₁ n₁).add (hasNonnegCoeffs_C_mul ha₂ n₂)
  have n₁₂₃ : HasNonnegCoeffs (C a₁ * q₁ + C a₂ * q₂ + C a₃ * q₃) :=
    n₁₂.add (hasNonnegCoeffs_C_mul ha₃ n₃)
  have s₁₂ := interl_nonneg_combo_right_of_common_left_of_nonneg h₁ h₂ n₁ n₂ ha₁ ha₂
  have s₁₂₃ := interl_add_right_of_common_left_of_nonneg s₁₂
    (h₃.C_mul_right_of_nonneg ha₃) n₁₂ (hasNonnegCoeffs_C_mul ha₃ n₃)
  exact interl_add_right_of_common_left_of_nonneg s₁₂₃
    (h₄.C_mul_right_of_nonneg ha₄) n₁₂₃ (hasNonnegCoeffs_C_mul ha₄ n₄)

/-- The step with nonzero `r`: the output is `(r, L, N)` with `N = a L + b X r +
(c - a l) X p + d X u`, and `r`, `L` are both common left interleavers of the four summands. -/
private lemma isOrderedPFTriple_step_of_ne_zero {l a b c d : ℝ} (hl : 0 < l) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hc : a * l ≤ c) {p u r : ℝ[X]} (h : IsOrderedPFTriple p u r)
    (hr0 : r ≠ 0) :
    IsOrderedPFTriple r (r + C l * (X * p))
      (C c * (X * p) + C d * (X * u) + (C a + C b * X) * r) := by
  obtain ⟨hp, hu, hr, hpu, hpr, hur⟩ := h
  have hrXp : Interl r (X * p) := interl_mul_X_of_interl hpr hp.hasNonnegCoeffs hr.hasNonnegCoeffs
  have hrXu : Interl r (X * u) := interl_mul_X_of_interl hur hu.hasNonnegCoeffs hr.hasNonnegCoeffs
  have hrXr : Interl r (X * r) :=
    interl_mul_X_of_interl hr.interl_self hr.hasNonnegCoeffs hr.hasNonnegCoeffs
  have hXpXp : Interl (X * p) (X * p) := hp.X_mul.interl_self
  have hXpXu : Interl (X * p) (X * u) := hpu.mul_X_both
  have hXpXr : Interl (X * p) (X * r) := hpr.mul_X_both
  have hnXp := hp.X_mul.hasNonnegCoeffs
  have hnXu := hu.X_mul.hasNonnegCoeffs
  have hnXr := hr.X_mul.hasNonnegCoeffs
  have hnLXp := hasNonnegCoeffs_C_mul hl.le hnXp
  have hnL : HasNonnegCoeffs (r + C l * (X * p)) := hr.hasNonnegCoeffs.add hnLXp
  have hrL : Interl r (r + C l * (X * p)) :=
    interl_add_right_of_common_left_of_nonneg hr.interl_self
      (hrXp.C_mul_right_of_nonneg hl.le) hr.hasNonnegCoeffs hnLXp
  have hL : IsPFPolynomial (r + C l * (X * p)) := isPFPolynomial_of_interl_left hr0 hrL hnL
  have hLXp : Interl (r + C l * (X * p)) (X * p) :=
    interl_add_left_of_common_right_of_nonneg hrXp (hXpXp.C_mul_left_of_nonneg hl.le)
      hr.hasNonnegCoeffs hnLXp
  have hLXu : Interl (r + C l * (X * p)) (X * u) :=
    interl_add_left_of_common_right_of_nonneg hrXu (hXpXu.C_mul_left_of_nonneg hl.le)
      hr.hasNonnegCoeffs hnLXp
  have hLXr : Interl (r + C l * (X * p)) (X * r) :=
    interl_add_left_of_common_right_of_nonneg hrXr (hXpXr.C_mul_left_of_nonneg hl.le)
      hr.hasNonnegCoeffs hnLXp
  have hN : C c * (X * p) + C d * (X * u) + (C a + C b * X) * r =
      C a * (r + C l * (X * p)) + C b * (X * r) + C (c - a * l) * (X * p) +
        C d * (X * u) := by
    simp only [map_sub, map_mul]
    ring
  have hnN : HasNonnegCoeffs (C a * (r + C l * (X * p)) + C b * (X * r) +
      C (c - a * l) * (X * p) + C d * (X * u)) :=
    (((hasNonnegCoeffs_C_mul ha hnL).add (hasNonnegCoeffs_C_mul hb hnXr)).add
      (hasNonnegCoeffs_C_mul (sub_nonneg.mpr hc) hnXp)).add (hasNonnegCoeffs_C_mul hd hnXu)
  have hrN : Interl r (C a * (r + C l * (X * p)) + C b * (X * r) + C (c - a * l) * (X * p) +
      C d * (X * u)) :=
    interl_sum4_right hrL hrXr hrXp hrXu hnL hnXr hnXp hnXu ha hb (sub_nonneg.mpr hc) hd
  have hLN : Interl (r + C l * (X * p)) (C a * (r + C l * (X * p)) + C b * (X * r) +
      C (c - a * l) * (X * p) + C d * (X * u)) :=
    interl_sum4_right hL.interl_self hLXr hLXp hLXu hnL hnXr hnXp hnXu ha hb
      (sub_nonneg.mpr hc) hd
  rw [hN]
  exact ⟨hr, hL, isPFPolynomial_of_interl_left hr0 hrN hnN, hrL, hrN, hLN⟩

/-- The step with `r = 0`: the output `(0, l X p, c X p + d X u)` is still an ordered
Pólya-frequency triple, because `p ≼ u` gives `X p ≼ X u`. -/
private lemma isOrderedPFTriple_step_of_eq_zero {l c d : ℝ} (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hd : 0 ≤ d) {p u : ℝ[X]} (hp : IsPFPolynomial p) (hu : IsPFPolynomial u)
    (hpu : Interl p u) :
    IsOrderedPFTriple 0 (C l * (X * p)) (C c * (X * p) + C d * (X * u)) := by
  have hXpXp : Interl (X * p) (X * p) := hp.X_mul.interl_self
  have hXpXu : Interl (X * p) (X * u) := hpu.mul_X_both
  have hLpf : IsPFPolynomial (C l * (X * p)) := (IsPFPolynomial.of_C_nonneg hl).mul hp.X_mul
  have hcXp : IsPFPolynomial (C c * (X * p)) := (IsPFPolynomial.of_C_nonneg hc).mul hp.X_mul
  have hdXu : IsPFPolynomial (C d * (X * u)) := (IsPFPolynomial.of_C_nonneg hd).mul hu.X_mul
  have hNpf : IsPFPolynomial (C c * (X * p) + C d * (X * u)) :=
    hcXp.add_of_interl hdXu ((hXpXu.C_mul_left_of_nonneg hc).C_mul_right_of_nonneg hd)
  have hLN : Interl (C l * (X * p)) (C c * (X * p) + C d * (X * u)) :=
    (interl_nonneg_combo_right_of_common_left_of_pf hXpXp hXpXu hp.X_mul hu.X_mul hc
      hd).C_mul_left_of_nonneg hl
  exact ⟨IsPFPolynomial.zero, hLpf, hNpf, interl_zero_left _, interl_zero_left _, hLN⟩

/-- **Sufficiency.**  For `l > 0`, the nonnegativity conditions `a, b, d ≥ 0` and `a l ≤ c`
make the matrix preserve every ordered Pólya-frequency triple, including inputs and outputs
with zero coordinates. -/
theorem PreservesScaledPFTriple.of_nonneg {l a b c d : ℝ} (hl : 0 < l) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hc : a * l ≤ c) : PreservesScaledPFTriple l a b c d := by
  intro p u r h
  rcases eq_or_ne r 0 with rfl | hr0
  · have hc0 : 0 ≤ c := (mul_nonneg ha hl.le).trans hc
    simpa using isOrderedPFTriple_step_of_eq_zero hl.le hc0 hd h.1 h.2.1 h.2.2.2.1
  · exact isOrderedPFTriple_step_of_ne_zero hl ha hb hd hc h hr0

/-- A zero-aware comparison of two affine polynomials with nonnegative coefficients orders
their cross products. -/
private lemma mul_le_mul_of_interl_affine {u v U V : ℝ} (hu : 0 < u) (hv : 0 ≤ v) (hU : 0 ≤ U)
    (hV : 0 < V) (h : Interl (C u * X + C v) (C U * X + C V)) : V * u ≤ v * U := by
  have hf0 : (C u * X + C v : ℝ[X]) ≠ 0 := by
    intro h0
    simpa [natDegree_linear hu.ne'] using congrArg natDegree h0
  have hg0 : (C U * X + C V : ℝ[X]) ≠ 0 := by
    intro h0
    simpa [hV.ne'] using congrArg (coeff · 0) h0
  have hstrict := h.toStrictInterl_of_ne hf0 hg0
  have hle := hstrict.natDegree_le
  rw [natDegree_linear hu.ne'] at hle
  rcases hU.eq_or_lt with rfl | hUpos
  · simp at hle
  · have hdeg : (C u * X + C v : ℝ[X]).natDegree = (C U * X + C V : ℝ[X]).natDegree := by
      rw [natDegree_linear hu.ne', natDegree_linear hUpos.ne']
    have := eval_cross_le_of_strictInterl_sameDegree_of_nonneg hstrict hdeg
      ((hasNonnegCoeffs_C_mul hu.le hasNonnegCoeffs_X).add (hasNonnegCoeffs_C hv))
      ((hasNonnegCoeffs_C_mul hU hasNonnegCoeffs_X).add (hasNonnegCoeffs_C hV.le))
    simpa [leadingCoeff, natDegree_linear hu.ne', natDegree_linear hUpos.ne'] using this

/-- **Necessity.**  If the matrix preserves every ordered Pólya-frequency triple, then
`a, b, d ≥ 0` and `a l ≤ c`. -/
theorem _root_.RealRooted.PreservesScaledPFTriple.nonneg {l a b c d : ℝ} (hl : 0 < l)
    (h : PreservesScaledPFTriple l a b c d) : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ d ∧ a * l ≤ c := by
  have h001 : IsOrderedPFTriple (0 : ℝ[X]) 0 1 :=
    ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, IsPFPolynomial.one,
      interl_zero_left 0, interl_zero_left 1, interl_zero_left 1⟩
  have h010 : IsOrderedPFTriple (0 : ℝ[X]) 1 0 :=
    ⟨IsPFPolynomial.zero, IsPFPolynomial.one, IsPFPolynomial.zero,
      interl_zero_left 1, interl_zero_left 0, interl_zero_right 1⟩
  have h100 : IsOrderedPFTriple (1 : ℝ[X]) 0 0 :=
    ⟨IsPFPolynomial.one, IsPFPolynomial.zero, IsPFPolynomial.zero,
      interl_zero_right 1, interl_zero_right 1, interl_zero_left 0⟩
  have h1 := (h 0 0 1 h001).2.2.1.hasNonnegCoeffs
  have h2 := (h 0 1 0 h010).2.2.1.hasNonnegCoeffs
  have h3 := (h 1 0 0 h100).2.2.1.hasNonnegCoeffs
  have ha : 0 ≤ a := by simpa using h1 0
  have hb : 0 ≤ b := by simpa using h1 1
  have hd : 0 ≤ d := by simpa using h2 1
  have hc0 : 0 ≤ c := by simpa using h3 1
  refine ⟨ha, hb, hd, ?_⟩
  by_contra hlt
  push Not at hlt
  have hapos : 0 < a := by
    by_contra ha0
    have : a = 0 := le_antisymm (not_lt.mp ha0) ha
    subst this
    simp at hlt
    linarith
  have hgap : 0 < a * l - c := sub_pos.mpr hlt
  set K : ℝ := 1 + b / (a * l - c) with hK
  have hKpos : 0 < K := by positivity
  have hcross : (a * l - c) * K > b := by
    rw [hK, mul_add, mul_div_cancel₀ _ hgap.ne']
    linarith
  have htriple : IsOrderedPFTriple (C K) 0 1 :=
    ⟨IsPFPolynomial.of_C_nonneg hKpos.le, IsPFPolynomial.zero, IsPFPolynomial.one,
      interl_zero_right _, interl_C_C K 1, interl_zero_left 1⟩
  have hLN := (h (C K) 0 1 htriple).2.2.2.2.2
  have hL : (1 : ℝ[X]) + C l * (X * C K) = C (l * K) * X + C 1 := by
    simp only [map_mul, map_one]
    ring
  have hN : C c * (X * C K) + C d * (X * 0) + (C a + C b * X) * 1 =
      C (c * K + b) * X + C a := by
    simp only [map_mul, map_add]
    ring
  rw [hL, hN] at hLN
  have hineq := mul_le_mul_of_interl_affine (mul_pos hl hKpos) zero_le_one
    (by positivity) hapos hLN
  nlinarith

/-- **The scaled criterion.**  For `l > 0`, the matrix `[[0, 0, 1], [l X, 0, 1],
[c X, d X, a + b X]]` preserves every ordered Pólya-frequency triple if and only if
`a, b, d ≥ 0` and `a l ≤ c`.  There are no degree or nonzero-coordinate hypotheses. -/
theorem PreservesScaledPFTriple.iff {l : ℝ} (hl : 0 < l) (a b c d : ℝ) :
    PreservesScaledPFTriple l a b c d ↔ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ d ∧ a * l ≤ c :=
  ⟨RealRooted.PreservesScaledPFTriple.nonneg hl, fun ⟨ha, hb, hd, hc⟩ ↦
    RealRooted.PreservesScaledPFTriple.of_nonneg hl ha hb hd hc⟩

/-- **The sharp criterion.**  The matrix `[[0, 0, 1], [X, 0, 1], [c X, d X, a + b X]]`
preserves every ordered Pólya-frequency triple if and only if `a, b, d ≥ 0` and `a ≤ c`.
There are no degree or nonzero-coordinate hypotheses. -/
theorem PreservesPFTriple.iff (a b c d : ℝ) :
    PreservesPFTriple a b c d ↔ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ d ∧ a ≤ c := by
  rw [preservesPFTriple_iff_preservesScaledPFTriple,
    PreservesScaledPFTriple.iff one_pos]
  simp

/-! ### Third-order recurrences -/

section Recurrence

variable {a b d e : ℕ → ℝ} {P : ℕ → ℝ[X]}

/-- The `s`th step of the third-order recurrence is the matrix step at `l = κ`, `c = e - d / κ`,
`d / κ`, applied to the state `(P s, P s + κ X P (s - 1), P (s + 1))`. -/
private lemma third_order_step {κ : ℝ} (hκ : κ ≠ 0) (s : ℕ)
    (hrec : P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1)) :
    C (e s - d s / κ) * (X * P s) + C (d s / κ) * (X * (P s + C κ * (X * P (s - 1)))) +
      (C (a s) + C (b s) * X) * P (s + 1) = P (s + 2) := by
  have h1 : (C (d s / κ) * C κ : ℝ[X]) = C (d s) := by
    rw [← C_mul]
    congr 1
    field_simp
  rw [hrec, map_sub]
  linear_combination (X ^ 2 * P (s - 1)) * h1

/-- **Orbit theorem, scaled form.**  Let `κ > 0`, `a s, b s, d s ≥ 0` and
`a s κ² - e s κ + d s ≤ 0`.  If `P` satisfies
`P (s + 2) = (a s + b s X) P (s + 1) + e s X P s + d s X² P (s - 1)` with `P 0 = 0`,
`P 1 = 1` (so `P (-1) = P 0 = 0`, using the truncated subtraction `0 - 1 = 0`), then
`(P s, P s + κ X P (s - 1), P (s + 1))` is an ordered Pólya-frequency triple for all `s`. -/
theorem isOrderedPFTriple_of_recurrence_scaled {κ : ℝ} (hκ : 0 < κ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s)
    (hq : ∀ s, a s * κ ^ 2 - e s * κ + d s ≤ 0)
    (hrec : ∀ s, P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1))
    (h0 : P 0 = 0) (h1 : P 1 = 1) (s : ℕ) :
    IsOrderedPFTriple (P s) (P s + C κ * (X * P (s - 1))) (P (s + 1)) := by
  induction s with
  | zero =>
      simp only [Nat.zero_sub, Nat.zero_add, h0, h1, mul_zero, add_zero]
      exact ⟨IsPFPolynomial.zero, IsPFPolynomial.zero, IsPFPolynomial.one,
        interl_zero_left 0, interl_zero_left 1, interl_zero_left 1⟩
  | succ s ih =>
      have hdκ : 0 ≤ d s / κ := div_nonneg (hd s) hκ.le
      have hc : a s * κ ≤ e s - d s / κ := by
        have : d s / κ ≤ e s - a s * κ := by
          rw [div_le_iff₀ hκ]
          nlinarith [hq s]
        linarith
      have hstep := RealRooted.PreservesScaledPFTriple.of_nonneg hκ (ha s) (hb s) hdκ hc _ _ _ ih
      rw [third_order_step hκ.ne' s (hrec s)] at hstep
      simpa using hstep

/-- Under the hypotheses of `isOrderedPFTriple_of_recurrence_scaled`, every `P s` is PF. -/
theorem isPFPolynomial_of_recurrence_scaled {κ : ℝ} (hκ : 0 < κ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s)
    (hq : ∀ s, a s * κ ^ 2 - e s * κ + d s ≤ 0)
    (hrec : ∀ s, P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1))
    (h0 : P 0 = 0) (h1 : P 1 = 1) (s : ℕ) : IsPFPolynomial (P s) :=
  (isOrderedPFTriple_of_recurrence_scaled hκ ha hb hd hq hrec h0 h1 s).1

/-- Under the hypotheses of `isOrderedPFTriple_of_recurrence_scaled`, consecutive
rows weakly interlace. -/
theorem interl_of_recurrence_scaled {κ : ℝ} (hκ : 0 < κ)
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s)
    (hq : ∀ s, a s * κ ^ 2 - e s * κ + d s ≤ 0)
    (hrec : ∀ s, P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1))
    (h0 : P 0 = 0) (h1 : P 1 = 1) (s : ℕ) : Interl (P s) (P (s + 1)) :=
  (isOrderedPFTriple_of_recurrence_scaled hκ ha hb hd hq hrec h0 h1 s).2.2.2.2.1

/-- **Orbit theorem.**  Let `a s, b s, d s ≥ 0` and `a s + d s ≤ e s`.  If `P` satisfies
`P (s + 2) = (a s + b s X) P (s + 1) + e s X P s + d s X² P (s - 1)` with `P 0 = 0`,
`P 1 = 1`, then `(P s, P s + X P (s - 1), P (s + 1))` is an ordered Pólya-frequency triple
for all `s`.  This is the scale `κ = 1` of `isOrderedPFTriple_of_recurrence_scaled`. -/
theorem isOrderedPFTriple_of_recurrence
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s)
    (he : ∀ s, a s + d s ≤ e s)
    (hrec : ∀ s, P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1))
    (h0 : P 0 = 0) (h1 : P 1 = 1) (s : ℕ) :
    IsOrderedPFTriple (P s) (P s + X * P (s - 1)) (P (s + 1)) := by
  simpa using isOrderedPFTriple_of_recurrence_scaled one_pos ha hb hd
    (fun s ↦ by linarith [he s]) hrec h0 h1 s

/-- Under the hypotheses of `isOrderedPFTriple_of_recurrence`, every `P s` is PF. -/
theorem isPFPolynomial_of_recurrence
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s)
    (he : ∀ s, a s + d s ≤ e s)
    (hrec : ∀ s, P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1))
    (h0 : P 0 = 0) (h1 : P 1 = 1) (s : ℕ) : IsPFPolynomial (P s) :=
  isPFPolynomial_of_recurrence_scaled one_pos ha hb hd (fun s ↦ by linarith [he s]) hrec h0 h1 s

/-- Under the hypotheses of `isOrderedPFTriple_of_recurrence`, consecutive rows weakly
interlace. -/
theorem interl_of_recurrence
    (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s) (hd : ∀ s, 0 ≤ d s)
    (he : ∀ s, a s + d s ≤ e s)
    (hrec : ∀ s, P (s + 2) = (C (a s) + C (b s) * X) * P (s + 1) + C (e s) * X * P s +
      C (d s) * X ^ 2 * P (s - 1))
    (h0 : P 0 = 0) (h1 : P 1 = 1) (s : ℕ) : Interl (P s) (P (s + 1)) :=
  interl_of_recurrence_scaled one_pos ha hb hd (fun s ↦ by linarith [he s]) hrec h0 h1 s

end Recurrence

@[deprecated (since := "2026-11-14")]
alias preservesScaledPFTriple_of_nonneg := PreservesScaledPFTriple.of_nonneg

end RealRooted
