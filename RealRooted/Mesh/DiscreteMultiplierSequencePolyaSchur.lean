module

public import RealRooted.Mesh.DiscreteMultiplierSequence
public import RealRooted.MultiplierSequence
public import RealRooted.MultiplierSequence.Infinite
public import RealRooted.NarayanaTransformation.RootGeometry
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.Mesh.DiscreteMultiplier
import RealRooted.Mesh.FallingFactorial
import RealRooted.MultiplierSequence.PolyaSchur
import RealRooted.PFPolynomial

/-!
# Discrete multiplier sequences are multiplier sequences

Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in finite difference setting*,
Proc. AMS 144 (2016), Proposition 6: every discrete multiplier sequence is an (ordinary)
multiplier sequence.  The converse fails (Remark 2): see
`not_isDiscreteMultiplierSequence_geometric`.

The proof follows the paper.  For `p = ∑ γ_i x ^ i` with nonnegative roots and `ρ > 0`,
Brenti's lemma (`fallingFactorialMap_meshGE_one`) puts `∑ γ_i ρ ^ i [x]_i` in the mesh class, hence
so is its image `∑ γ_i a_i ρ ^ i [x]_i` under the discrete multiplier sequence.  Rescaling
`x ↦ x / ρ` gives `∑ γ_i a_i x (x - ρ) ⋯ (x - (i - 1) ρ)`, which splits, and as `ρ → 0` these
polynomials converge to `∑ γ_i a_i x ^ i`.  A sequence of nonnegative terms is then handled by the
Jensen polynomial characterization of multiplier sequences, and the sign by Corollary 3.
See RealRooted issue #2070.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- The polynomial `∑_{i ≤ N} c_i x (x - ρ) ⋯ (x - (i - 1) ρ)`, which tends to `∑ c_i x ^ i`
as `ρ → 0`. -/
private def stretched (c : ℕ → ℝ) (N : ℕ) (ρ : ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range (N + 1), C (c i) * ∏ j ∈ Finset.range i, (X - C ((j : ℝ) * ρ))

private theorem natDegree_stretched_le (c : ℕ → ℝ) (N : ℕ) (ρ : ℝ) :
    (stretched c N ρ).natDegree ≤ N := by
  unfold stretched
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

private theorem eval_stretched (c : ℕ → ℝ) (N : ℕ) (ρ x : ℝ) :
    (stretched c N ρ).eval x = ∑ i ∈ Finset.range (N + 1), c i * ∏ j ∈ Finset.range i,
      (x - (j : ℝ) * ρ) := by
  simp [stretched, eval_finsetSum, eval_prod]

/-- The rescaling `x ↦ x / ρ` of `∑ c_i ρ ^ i [x]_i` is `stretched c N ρ`. -/
private theorem stretched_eq_comp {c : ℕ → ℝ} {N : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    stretched c N ρ = (∑ i ∈ Finset.range (N + 1), C (c i * ρ ^ i) * descPochhammer ℝ i).comp
      (C ρ⁻¹ * X) := by
  apply Polynomial.funext
  intro x
  rw [eval_stretched, eval_comp, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_mul, eval_C, eval_X, descPochhammer_eval_eq_prod_range]
  rw [mul_assoc, show ρ ^ i = ∏ j ∈ Finset.range i, ρ by simp, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  field_simp

/-- A discrete multiplier sequence maps a polynomial with nonnegative roots to zero or to a
real-rooted polynomial (the heart of BKS 2016, Proposition 6). -/
theorem IsDiscreteMultiplierSequence.diagonalOperator_eq_zero_or_splits {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) {p : ℝ[X]} (hp : HasOnlyNonnegRoots p) :
    diagonalOperator a p = 0 ∨ (diagonalOperator a p).Splits := by
  obtain ⟨T, hT⟩ := exists_linearMap_descPochhammer a
  set N := p.natDegree with hN
  set c : ℕ → ℝ := fun i => a i * p.coeff i with hc
  have hsum : diagonalOperator a p = ∑ i ∈ Finset.range (N + 1), C (c i) * X ^ i := by
    ext k
    rw [coeff_diagonalOperator, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, hc]
    by_cases hk : k ≤ N
    · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 (by lia))]
      · simp
      · intro b _ hbk
        simp [Ne.symm hbk]
    · rw [Finset.sum_eq_zero, coeff_eq_zero_of_natDegree_lt (by lia), mul_zero]
      intro b hb
      have : b ≠ k := by
        have := Finset.mem_range.1 hb
        lia
      simp [Ne.symm this]
  -- the stretched polynomials split
  have hsplit : ∀ ρ : ℝ, 0 < ρ → (stretched c N ρ).Splits := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := hρ.ne'
    have hg : (C ρ * X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans natDegree_X_le
    have hinv : Invertible (C ρ * X : ℝ[X]).leadingCoeff := by
      rw [leadingCoeff_C_mul_X]
      exact invertibleOfNonzero hρ0
    -- the dilated polynomial has nonnegative roots
    have hpρ : HasOnlyNonnegRoots (p.comp (C ρ * X)) := by
      by_cases hp0 : p = 0
      · simp [hp0, HasOnlyNonnegRoots]
      obtain ⟨hs, hr⟩ := hp.resolve_left hp0
      refine Or.inr ⟨hs.comp_of_natDegree_le_one_of_invertible hg hinv, fun r hr' => ?_⟩
      have := roots_comp_C_mul_X_add_C p ρ 0 (isUnit_iff_ne_zero.2 hρ0)
      rw [show C ρ * X + C (0 : ℝ) = C ρ * X by simp] at this
      rw [this, Multiset.mem_map] at hr'
      obtain ⟨x, hx, rfl⟩ := hr'
      have := hr x hx
      simp only [Ring.inverse_eq_inv', sub_zero]
      positivity
    obtain ⟨h1, h2⟩ := fallingFactorialMap_meshGE_one hpρ
    obtain ⟨hU1, -⟩ := ha _ hT _ h1 h2
    have hdeg : (p.comp (C ρ * X)).natDegree < N + 1 := by
      have := natDegree_comp_le (p := p) (q := C ρ * X)
      have h2 : p.natDegree * (C ρ * X : ℝ[X]).natDegree ≤ p.natDegree * 1 :=
        Nat.mul_le_mul_left _ hg
      lia
    have hU : (T ∘ₗ fallingFactorialMap) (p.comp (C ρ * X)) =
        ∑ i ∈ Finset.range (N + 1), C (c i * ρ ^ i) * descPochhammer ℝ i := by
      rw [LinearMap.comp_apply, as_sum_range' _ (N + 1) hdeg]
      simp only [map_sum, fallingFactorialMap_monomial, map_smul, hT, comp_C_mul_X_coeff]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_C_mul, hc, map_mul, map_pow]
      ring
    rw [stretched_eq_comp hρ, ← hU]
    exact (hU1.1).comp_of_natDegree_le_one_of_invertible
      (by exact (natDegree_C_mul_le _ _).trans natDegree_X_le)
      (by rw [leadingCoeff_C_mul_X]; exact invertibleOfNonzero (inv_ne_zero hρ0))
  -- convergence as `ρ = 1 / (k + 1) → 0`
  refine Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    (p := fun k : ℕ => stretched c N (1 / ((k : ℝ) + 1))) (N := N)
    (fun k => natDegree_stretched_le _ _ _) (fun k => Or.inr (hsplit _ (by positivity)))
    fun z => ?_
  have hev : ∀ ρ : ℝ, ((stretched c N ρ).map Complex.ofRealHom).eval z =
      ∑ i ∈ Finset.range (N + 1), (c i : ℂ) * ∏ j ∈ Finset.range i, (z - (j : ℂ) * ρ) := by
    intro ρ
    simp [stretched, Polynomial.map_sum, Polynomial.map_prod, eval_finsetSum, eval_prod]
  simp only [hev]
  have hlim : ((diagonalOperator a p).map Complex.ofRealHom).eval z =
      ∑ i ∈ Finset.range (N + 1), (c i : ℂ) * ∏ j ∈ Finset.range i, (z - (j : ℂ) * (0 : ℝ)) := by
    rw [hsum]
    simp [Polynomial.map_sum, eval_finsetSum]
  rw [hlim]
  have hcont : Continuous fun ρ : ℝ =>
      ∑ i ∈ Finset.range (N + 1), (c i : ℂ) * ∏ j ∈ Finset.range i, (z - (j : ℂ) * (ρ : ℂ)) := by
    fun_prop
  exact (hcont.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat

/-- The negative of a discrete multiplier sequence is a discrete multiplier sequence. -/
theorem IsDiscreteMultiplierSequence.neg {a : ℕ → ℝ} (ha : IsDiscreteMultiplierSequence a) :
    IsDiscreteMultiplierSequence fun i => -a i := by
  intro T hT p hp hnn
  have hT' : ∀ i, (-T) (descPochhammer ℝ i) = a i • descPochhammer ℝ i := fun i => by
    simp [hT, neg_smul]
  obtain ⟨h1, h2⟩ := ha (-T) hT' p hp hnn
  rw [LinearMap.neg_apply] at h1 h2
  have e : -T p = C (-1) * T p := by simp
  rw [e] at h1 h2
  exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).1 h1,
    (HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).1 h2⟩

private theorem eval_pos_of_nonneg_coeff {q : ℝ[X]} (h : ∀ k, 0 ≤ q.coeff k) (hq : q ≠ 0)
    {r : ℝ} (hr : 0 < r) : 0 < q.eval r := by
  rw [eval_eq_sum_range]
  have hlc : 0 < q.coeff q.natDegree :=
    lt_of_le_of_ne (h _) (Ne.symm (leadingCoeff_ne_zero.mpr hq))
  exact lt_of_lt_of_le (mul_pos hlc (pow_pos hr _)) (Finset.single_le_sum
    (f := fun i => q.coeff i * r ^ i) (fun i _ => mul_nonneg (h i) (pow_nonneg hr.le i))
    (Finset.self_mem_range_succ _))

/-- The Jensen polynomials of a nonnegative discrete multiplier sequence are PF. -/
private theorem IsDiscreteMultiplierSequence.isPFPolynomial_jensenPolynomial {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) (h0 : ∀ k, 0 ≤ a k) (n : ℕ) :
    IsPFPolynomial (jensenPolynomial n a) := by
  have hX1 : (X + 1 : ℝ[X]).Splits := by
    simpa [sub_eq_add_neg] using Polynomial.Splits.X_sub_C (-1 : ℝ)
  have hsp : ((X + 1 : ℝ[X]) ^ n).Splits := hX1.pow n
  set p : ℝ[X] := ((X + 1 : ℝ[X]) ^ n).comp (-X) with hp
  have hp0 : p ≠ 0 := by
    intro h
    have := congrArg (fun q => q.comp (-X)) h
    simp only [hp, comp_neg_X_comp_neg_X, zero_comp] at this
    exact pow_ne_zero n (X_add_C_ne_zero (1 : ℝ)) (by simpa using this)
  have hpnn : HasOnlyNonnegRoots p := by
    refine Or.inr ⟨hsp.comp_neg_X, fun r hr => ?_⟩
    rw [hp, roots_comp_neg_X, Multiset.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hne : ((X + 1 : ℝ[X]) ^ n) ≠ 0 := pow_ne_zero n (X_add_C_ne_zero (1 : ℝ))
    have hroot := (mem_roots hne).1 hx
    simp only [IsRoot.def, eval_pow, eval_add, eval_X, eval_one] at hroot
    have : x + 1 = 0 := pow_eq_zero_iff'.mp hroot |>.1
    linarith
  have hJ : (jensenPolynomial n a).comp (-X) = diagonalOperator a p := by
    ext k
    rw [coeff_comp_neg_X, jensenPolynomial_eq_diagonalOperator_X_add_one_pow,
      coeff_diagonalOperator, coeff_diagonalOperator, hp, coeff_comp_neg_X]
    ring
  have hJ' : jensenPolynomial n a = (diagonalOperator a p).comp (-X) := by
    rw [← hJ, comp_neg_X_comp_neg_X]
  have hcoef : ∀ k, 0 ≤ (jensenPolynomial n a).coeff k := fun k => by
    rw [coeff_jensenPolynomial]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (h0 k)
    · exact le_rfl
  have hsplit : jensenPolynomial n a = 0 ∨ (jensenPolynomial n a).Splits := by
    rcases ha.diagonalOperator_eq_zero_or_splits hpnn with h | h
    · left
      rw [hJ', h, zero_comp]
    · right
      rw [hJ']
      exact h.comp_neg_X
  refine ⟨hcoef, hsplit, fun r hr => ?_⟩
  by_cases hJ0 : jensenPolynomial n a = 0
  · simp [hJ0] at hr
  by_contra hpos
  push Not at hpos
  have hroot := (mem_roots hJ0).1 hr
  exact (eval_pos_of_nonneg_coeff hcoef hJ0 hpos).ne' hroot

/-- BKS 2016, Proposition 6: every discrete multiplier sequence is a multiplier sequence.  The
converse fails: see `not_isDiscreteMultiplierSequence_geometric` (BKS 2016, Remark 2). -/
theorem IsDiscreteMultiplierSequence.isMultiplierSequence {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) : IsMultiplierSequence a := by
  rcases ha.nonneg_or_nonpos with h | h
  · exact (isMultiplierSequence_iff_jensenPolynomial_isPF h).2
      (ha.isPFPolynomial_jensenPolynomial h)
  · have hneg := ha.neg
    have hnn : ∀ k, 0 ≤ -a k := fun k => neg_nonneg.2 (h k)
    have := ((isMultiplierSequence_iff_jensenPolynomial_isPF hnn).2
      (hneg.isPFPolynomial_jensenPolynomial hnn)).const_mul (-1)
    simpa using this

/-- BKS 2016, Remark 2: the geometric sequence `ρ ^ i` with `0 < ρ < 1` is not a discrete
multiplier sequence, although it is a multiplier sequence. -/
theorem not_isDiscreteMultiplierSequence_geometric {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    ¬ IsDiscreteMultiplierSequence fun i : ℕ => ρ ^ i := fun h => by
  have := h.le_succ 0 (by positivity)
  simp at this
  linarith

end RealRooted

end
