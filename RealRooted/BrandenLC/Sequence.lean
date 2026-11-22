module

public import RealRooted.BrandenLC
import RealRooted.PFPolynomial.Closure
import RealRooted.CoefficientShape

/-!
# Iterated log-concavity for limits of PF polynomials

Brändén's polynomial transform extends to coefficientwise limits of PF
polynomials. Every finite iterate remains a Pólya-frequency sequence.
The approximation hypothesis matters: an arbitrary infinite PF sequence is
not assumed to admit PF polynomial approximants.

The finite preservation theorem is from P. Brändén, *Iterated sequences and the
geometry of zeros*, https://arxiv.org/abs/0909.1927.
-/

@[expose] public section

open Polynomial Filter Topology

namespace RealRooted

/-- The log-concavity transform of a sequence, with the preceding entry at
index zero set to zero. -/
def logConcavitySequence {R : Type*} [Ring R] (a : ℕ → R) (k : ℕ) : R :=
  a k ^ 2 - (if k = 0 then 0 else a (k - 1)) * a (k + 1)

/-- The polynomial and sequence log-concavity transforms have identical
coefficients, including indices above the polynomial degree. -/
theorem coeff_logConcavityTransform_eq (p : ℝ[X]) (k : ℕ) :
    (Branden.logConcavityTransform p).coeff k = logConcavitySequence p.coeff k := by
  rw [Branden.coeff_logConcavityTransform]
  by_cases hk : k ≤ p.natDegree
  · rw [ite_eq_left hk]
    rfl
  · rw [ite_eq_right hk]
    have hzero := coeff_eq_zero_of_natDegree_lt (p := p) (Nat.lt_of_not_ge hk)
    have hnext := coeff_eq_zero_of_natDegree_lt (p := p)
      (lt_trans (Nat.lt_of_not_ge hk) (Nat.lt_succ_self k))
    simp [logConcavitySequence, hzero, hnext]

/-- Polynomial iteration agrees coefficientwise with sequence iteration. -/
theorem coeff_iterate_logConcavityTransform (p : ℝ[X]) (m k : ℕ) :
    ((Branden.logConcavityTransform^[m]) p).coeff k =
      ((logConcavitySequence^[m]) p.coeff) k := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        coeff_logConcavityTransform_eq]
      simp only [logConcavitySequence, ih]

/-- The log-concavity transform is continuous for coefficientwise convergence. -/
theorem tendsto_logConcavitySequence {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (h : ∀ k, Tendsto (fun n => a n k) atTop (𝓝 (b k))) (k : ℕ) :
    Tendsto (fun n => logConcavitySequence (a n) k) atTop
      (𝓝 (logConcavitySequence b k)) := by
  by_cases hk : k = 0
  · simpa only [logConcavitySequence, ite_eq_left hk, zero_mul, sub_zero] using (h k).pow 2
  · simpa only [logConcavitySequence, ite_eq_right hk] using
      ((h k).pow 2).sub ((h (k - 1)).mul (h (k + 1)))

/-- Every finite log-concavity iterate respects coefficientwise convergence. -/
theorem tendsto_iterate_logConcavitySequence {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (h : ∀ k, Tendsto (fun n => a n k) atTop (𝓝 (b k))) (m k : ℕ) :
    Tendsto (fun n => ((logConcavitySequence^[m]) (a n)) k) atTop
      (𝓝 (((logConcavitySequence^[m]) b) k)) := by
  induction m generalizing k with
  | zero => exact h k
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      exact tendsto_logConcavitySequence ih k

/-- Every finite polynomial log-concavity iterate preserves the PF cone. -/
theorem IsPFPolynomial.iterate_logConcavityTransform {p : ℝ[X]}
    (hp : IsPFPolynomial p) (m : ℕ) :
    IsPFPolynomial ((Branden.logConcavityTransform^[m]) p) := by
  induction m with
  | zero => exact hp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Branden.IsPFPolynomial.logConcavityTransform ih

/-- All iterated log-concavity transforms of a coefficientwise PF polynomial
limit are PF sequences, so every Toeplitz minor of every iterate is nonnegative. -/
theorem isPolyaFreqSeq_iterate_logConcavitySequence_of_limit
    {p : ℕ → ℝ[X]} {a : ℕ → ℝ} (hp : ∀ n, IsPFPolynomial (p n))
    (hlim : ∀ k, Tendsto (fun n => (p n).coeff k) atTop (𝓝 (a k))) (m : ℕ) :
    IsPolyaFreqSeq ((logConcavitySequence^[m]) a) := by
  apply IsPolyaFreqSeq.of_tendsto (fun n => ((hp n).iterate_logConcavityTransform m).to_sequence)
  intro k
  simpa only [coeff_iterate_logConcavityTransform] using
    tendsto_iterate_logConcavitySequence hlim m k

/-- Newton's inequalities give a degree-independent lower bound for the
log-concavity transform of a PF polynomial. -/
theorem logConcavitySequence_coeff_lower_bound {p : ℝ[X]}
    (hp : IsPFPolynomial p) (k : ℕ) :
    p.coeff k ^ 2 ≤ (k + 1 : ℝ) * logConcavitySequence p.coeff k := by
  by_cases hk0 : k = 0
  · subst k
    simp [logConcavitySequence]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  by_cases hkd : k < p.natDegree
  · have hn := hasUltraLogConcaveCoeffs_of_eq_zero_or_splits (Or.inr hp.splits) k hkpos hkd
    have hB : 0 ≤ p.coeff (k - 1) * p.coeff (k + 1) :=
      mul_nonneg (hp.hasNonnegCoeffs _) (hp.hasNonnegCoeffs _)
    have hD : (0 : ℝ) < ((p.natDegree - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hkd
    have hdrop : p.coeff (k - 1) * p.coeff (k + 1) *
        ((k + 1 : ℝ) * ((p.natDegree - k : ℕ) : ℝ)) ≤
        p.coeff k ^ 2 * ((k : ℝ) * ((p.natDegree - k : ℕ) : ℝ)) := by
      calc
        _ ≤ p.coeff (k - 1) * p.coeff (k + 1) *
            ((k + 1 : ℝ) * (((p.natDegree - k : ℕ) : ℝ) + 1)) := by
          gcongr
          linarith
        _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using hn
    have hbase : p.coeff (k - 1) * p.coeff (k + 1) * (k + 1 : ℝ) ≤
        p.coeff k ^ 2 * k :=
      (mul_le_mul_iff_left₀ hD).mp (by simpa only [mul_assoc] using hdrop)
    simp only [logConcavitySequence, ite_eq_right hk0]
    nlinarith
  · have hnext : p.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
    simp only [logConcavitySequence, hnext, mul_zero, sub_zero]
    nlinarith [sq_nonneg (p.coeff k), Nat.cast_nonneg (α := ℝ) k]

/-- The degree-independent Newton lower bound passes to PF polynomial limits. -/
theorem logConcavitySequence_lower_bound_of_limit
    {p : ℕ → ℝ[X]} {a : ℕ → ℝ} (hp : ∀ n, IsPFPolynomial (p n))
    (hlim : ∀ k, Tendsto (fun n => (p n).coeff k) atTop (𝓝 (a k))) (k : ℕ) :
    a k ^ 2 ≤ (k + 1 : ℝ) * logConcavitySequence a k :=
  le_of_tendsto_of_tendsto ((hlim k).pow 2)
    ((tendsto_logConcavitySequence hlim k).const_mul (k + 1 : ℝ))
    (Filter.Eventually.of_forall fun n => logConcavitySequence_coeff_lower_bound (hp n) k)

/-- A positive entry in a PF polynomial limit remains positive after the
log-concavity transform. -/
theorem logConcavitySequence_pos_of_limit
    {p : ℕ → ℝ[X]} {a : ℕ → ℝ} (hp : ∀ n, IsPFPolynomial (p n))
    (hlim : ∀ k, Tendsto (fun n => (p n).coeff k) atTop (𝓝 (a k))) {k : ℕ}
    (ha : 0 < a k) : 0 < logConcavitySequence a k := by
  have h := logConcavitySequence_lower_bound_of_limit hp hlim k
  have hk : (0 : ℝ) < k + 1 := by positivity
  nlinarith [sq_pos_of_pos ha]

/-- A positive entry remains positive under every log-concavity iterate
for coefficientwise PF polynomial limits. -/
theorem iterate_logConcavitySequence_pos_of_limit
    {p : ℕ → ℝ[X]} {a : ℕ → ℝ} (hp : ∀ n, IsPFPolynomial (p n))
    (hlim : ∀ k, Tendsto (fun n => (p n).coeff k) atTop (𝓝 (a k)))
    (m k : ℕ) (ha : 0 < a k) : 0 < ((logConcavitySequence^[m]) a) k := by
  induction m with
  | zero => exact ha
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      apply logConcavitySequence_pos_of_limit
        (fun n => (hp n).iterate_logConcavityTransform m) ?_ ih
      intro j
      simpa only [coeff_iterate_logConcavityTransform] using
        tendsto_iterate_logConcavitySequence hlim m j

end RealRooted
