import RealRooted.SymmetricDecomposition.DerangementTransform
import RealRooted.SymmetricDecomposition.EulerianTransform
import RealRooted.PFPolynomial

/-!
# Binder--Vecchi: refined Hodge--Poincar\'e polynomials of uniform matroids

Real-rootedness of the refined Hodge--Poincar\'e polynomial `\underline H^i_{r,n}` and of the
modified augmented refined Hodge--Poincar\'e polynomial `\widetilde H^i_{r,n}` of the uniform
matroid `U_{r,n}` for `1 ≤ i ≤ n - r` (Binder--Vecchi, Theorems 1.4 and 1.6). The geometry of
the singular cohomology rings is not formalized; we work with the explicit coefficient formulas
of the paper, with weights `W_{j,i}(r,n)` (see `weight`).

The proofs follow the paper. With `g = ∑_j W_{j,i} X^j` we show
`\underline H = I_{r-1}(D g)` for the deranged map `D` of Brändén--Solus and
`I_r(\widetilde H) = A°(g)` for Athanasiadis' Eulerian transformation `A°`, and that `g` has
a nonnegative expansion in the magic basis `X^p (1+X)^{r-1-p}` (an explicit Vandermonde-type
identity); real-rootedness then follows from the two magic-basis theorems.

The case `i = 0` (the Chow, respectively augmented Chow, polynomial of `U_{r,n}`) is outside the
scope of this file; the paper cites Brändén--Vecchi and Ferroni--Matherne--Stevens--Vecchi for
it.

The weight `W_{1,i}(r,n)` is the displayed coefficient formula, not the cardinality of the set
`W_1(U_{r,n})`, which equals that of `W_0`; since `d_1 = 0` this does not affect `\underline H`.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted
namespace BinderVecchi


/-- The negative-binomial convolution sum. -/
def convSum (a b m : ℕ) : ℕ :=
  ∑ p ∈ range (m + 1), (a + p).choose p * (b + m - p).choose (m - p)

private theorem convSum_zero_right (a b : ℕ) : convSum a b 0 = 1 := by
  simp [convSum]

private theorem convSum_succ_succ (a b m : ℕ) :
    convSum (a + 1) b (m + 1) = convSum (a + 1) b m + convSum a b (m + 1) := by
  unfold convSum
  rw [sum_range_succ' _ (m + 1), sum_range_succ' _ (m + 1)]
  have h : ∀ p ∈ range (m + 1),
      (a + 1 + (p + 1)).choose (p + 1) * (b + (m + 1) - (p + 1)).choose (m + 1 - (p + 1)) =
        (a + 1 + p).choose p * (b + m - p).choose (m - p) +
          (a + (p + 1)).choose (p + 1) * (b + (m + 1) - (p + 1)).choose (m + 1 - (p + 1)) := by
    intro p hp
    have h1 : a + 1 + (p + 1) = (a + 1 + p) + 1 := by lia
    have h2 : a + 1 + p = a + (p + 1) := by lia
    rw [h1, Nat.choose_succ_succ, h2, add_mul]
    have h3 : b + (m + 1) - (p + 1) = b + m - p := by lia
    have h4 : m + 1 - (p + 1) = m - p := by lia
    rw [h3, h4, ← h2]
  rw [sum_congr rfl h, sum_add_distrib]
  simp only [Nat.add_zero, Nat.choose_zero_right, one_mul]
  have h5 : ∀ p ∈ range (m + 1), (b + (m + 1) - (p + 1)) = b + m - p := fun p hp => by lia
  simp only [Nat.add_sub_add_right]
  ring

/-- The negative-binomial convolution identity. -/
theorem convSum_eq (a b m : ℕ) : convSum a b m = (a + b + m + 1).choose m := by
  induction a generalizing b m with
  | zero =>
    unfold convSum
    have h := Nat.sum_range_add_choose m b
    have h2 : ∀ p ∈ range (m + 1), (0 + p).choose p * (b + m - p).choose (m - p) =
        (m - p + b).choose b := by
      intro p hp
      have hp' : p ≤ m := by simpa [Nat.lt_succ_iff] using hp
      rw [zero_add, Nat.choose_self, one_mul, show b + m - p = (m - p) + b by lia,
        Nat.choose_symm_add]
    rw [sum_congr rfl h2]
    have h3 := sum_range_reflect (fun q => (q + b).choose b) (m + 1)
    simp only [Nat.add_sub_cancel] at h3
    rw [h3, h, zero_add, show m + b + 1 = b + m + 1 by lia]
    exact Nat.choose_symm_of_eq_add (by lia)
  | succ a ih =>
    induction m with
    | zero => simp [convSum_zero_right]
    | succ m ihm =>
      rw [convSum_succ_succ, ihm, ih b (m + 1)]
      rw [show a + 1 + b + (m + 1) + 1 = (a + b + m + 2) + 1 by lia,
        show a + 1 + b + m + 1 = a + b + m + 2 by lia,
        show a + b + (m + 1) + 1 = a + b + m + 2 by lia]
      exact (Nat.choose_succ_succ (a + b + m + 2) m).symm

/-- The coefficientwise form of the magic-basis expansion. -/
theorem sum_choose_mul_choose_mul_choose {N L d s : ℕ} (hL : 1 ≤ L) (hsd : s ≤ d)
    (hdN : d ≤ N) :
    ∑ p ∈ range (s + 1),
      (N - p).choose (d - p) * (L - 1 + p).choose p * (d - p).choose (s - p) =
        (N + L).choose s * (N - s).choose (d - s) := by
  have h1 : ∀ p ∈ range (s + 1),
      (N - p).choose (d - p) * (L - 1 + p).choose p * (d - p).choose (s - p) =
        ((L - 1 + p).choose p * (N - s + s - p).choose (s - p)) * (N - s).choose (d - s) := by
    intro p hp
    have hp' : p ≤ s := by simpa [Nat.lt_succ_iff] using hp
    have h := Nat.choose_mul (n := N - p) (k := d - p) (s := s - p) (by lia)
    have e1 : N - p - (s - p) = N - s := by lia
    have e2 : d - p - (s - p) = d - s := by lia
    have e3 : N - s + s - p = N - p := by lia
    rw [e1, e2] at h
    rw [e3]
    calc _ = (L - 1 + p).choose p * ((N - p).choose (d - p) * (d - p).choose (s - p)) := by ring
      _ = _ := by rw [h]; ring
  rw [sum_congr rfl h1, ← sum_mul]
  have h2 := convSum_eq (L - 1) (N - s) s
  unfold convSum at h2
  rw [h2, show L - 1 + (N - s) + s + 1 = N + L by lia]

/-- The magic-basis expansion of a binomial row. -/
theorem sum_choose_X_pow_eq {N L d : ℕ} (hL : 1 ≤ L) (hdN : d ≤ N) :
    ∑ s ∈ range (d + 1),
        C (((((N + L).choose s * (N - s).choose (d - s) : ℕ)) : ℝ)) * X ^ s =
      ∑ p ∈ range (d + 1),
        C ((((N - p).choose (d - p) * (L - 1 + p).choose p : ℕ)) : ℝ) *
          (X ^ p * (1 + X) ^ (d - p)) := by
  ext s
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul', mul_ite, mul_one,
    mul_zero]
  have hc : ∀ m k : ℕ, ((1 + X : ℝ[X]) ^ m).coeff k = (m.choose k : ℝ) := by
    intro m k
    rw [add_comm, coeff_X_add_one_pow]
  simp only [hc]
  rw [sum_ite_eq (range (d + 1)) s]
  by_cases hsd : s ≤ d
  · have hs : s ∈ range (d + 1) := by simpa [Nat.lt_succ_iff] using hsd
    simp only [hs, ↓reduceIte]
    have h := sum_choose_mul_choose_mul_choose hL hsd hdN
    have hsub : range (s + 1) ⊆ range (d + 1) := range_subset_range.mpr (by lia)
    rw [← sum_subset hsub (fun p _ hp => by
      have : ¬ p ≤ s := by simpa [Nat.lt_succ_iff] using hp
      simp [this])]
    have := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at this ⊢
    rw [← this]
    refine sum_congr rfl fun p hp => ?_
    have hp' : p ≤ s := by simpa [Nat.lt_succ_iff] using hp
    simp only [hp', ↓reduceIte]
  · have hs : s ∉ range (d + 1) := by simpa [Nat.lt_succ_iff] using hsd
    simp only [hs, ↓reduceIte]
    symm
    refine sum_eq_zero fun p hp => ?_
    have hp' : p ≤ d := by simpa [Nat.lt_succ_iff] using hp
    have hps : p ≤ s := by lia
    simp only [hps, ↓reduceIte]
    rw [Nat.choose_eq_zero_of_lt (n := d - p) (k := s - p) (by lia)]
    simp


/-! ## The weights and the two families -/

/-- The Eulerian polynomial `A_s`, with `A_0 = 1`. -/
def eulerian : ℕ → ℝ[X]
  | 0 => 1
  | s + 1 => generalizedEulerian 1 s

/-- The weight `W_{j,i}(r,n)` of Binder--Vecchi, Lemma 4.1: the displayed coefficient formula,
`C(n,j) ∑_ℓ C(n-j-ℓ, r-j-1) C(n-r-ℓ, i-1)` for `ℓ = 1, …, n-r-i+1`. For `j = 1` this is
the coefficient used by the transform, not the cardinality of `W_1(U_{r,n})`. -/
def weight (r n i j : ℕ) : ℕ :=
  n.choose j * ∑ l ∈ Icc 1 (n - r - i + 1),
    (n - j - l).choose (r - j - 1) * (n - r - l).choose (i - 1)

/-- The polynomial `∑_{j<r} W_{j,i}(r,n) X^j` (the polynomial `f_{r,n,i}` of Theorem 1.4 and
`g_{r,n,i}` of Theorem 1.6; the two coincide). -/
def weightPolynomial (r n i : ℕ) : ℝ[X] :=
  ∑ s ∈ range r, C (weight r n i s : ℝ) * X ^ s

/-- The refined Hodge--Poincaré polynomial `\underline H^i_{r,n}(x)` of the uniform matroid
`U_{r,n}`, `∑_{j<r} W_{j,i}(r,n) d_j(x) x^{r-j-1}` (for `i ≥ 1`). -/
def refinedHodgePoincare (r n i : ℕ) : ℝ[X] :=
  ∑ j ∈ range r, C (weight r n i j : ℝ) *
    (DerangementTransform.polynomial j * X ^ (r - 1 - j))

/-- The modified augmented refined Hodge--Poincaré polynomial `\widetilde H^i_{r,n}(x)`,
`∑_{s<r} W_{s,i}(r,n) A_s(x) x^{r-s}` (for `i ≥ 1`); the augmented weight
`C(n,s) ∑_ℓ C(n-s-ℓ, r-s-1) C(n-r-ℓ, i-1)` is `weight r n i s`. -/
def modifiedAugmentedHodgePoincare (r n i : ℕ) : ℝ[X] :=
  ∑ s ∈ range r, C (weight r n i s : ℝ) * (X ^ (r - s) * eulerian s)

/-- The coefficient of `X ^ p * (1 + X) ^ (r - 1 - p)` in `weightPolynomial`. -/
def magicCoeff (r n i p : ℕ) : ℝ :=
  ∑ l ∈ Icc 1 (n - r - i + 1), ((n - r - l).choose (i - 1) : ℝ) *
    (((n - l - p).choose (r - p - 1) * (l - 1 + p).choose p : ℕ) : ℝ)

theorem magicCoeff_nonneg (r n i p : ℕ) : 0 ≤ magicCoeff r n i p := by
  unfold magicCoeff
  positivity

/-- The first weight is positive. -/
theorem weight_zero_pos {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i) (hn : r + i ≤ n) :
    0 < weight r n i 0 := by
  unfold weight
  refine Nat.mul_pos (by simp) ?_
  have hmem : 1 ∈ Icc 1 (n - r - i + 1) := by simp only [mem_Icc]; lia
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun l =>
    (n - 0 - l).choose (r - 0 - 1) * (n - r - l).choose (i - 1)) (fun _ _ => Nat.zero_le _) hmem)
  exact Nat.mul_pos (Nat.choose_pos (by lia)) (Nat.choose_pos (by lia))

/-! ## The magic-basis expansion -/

private theorem sum_choose_X_pow_eq_of_le {n l d : ℕ} (hl : 1 ≤ l) (hdn : d + l ≤ n) :
    ∑ s ∈ range (d + 1), C (((n.choose s * (n - s - l).choose (d - s) : ℕ)) : ℝ) * X ^ s =
      ∑ p ∈ range (d + 1),
        C ((((n - l - p).choose (d - p) * (l - 1 + p).choose p : ℕ)) : ℝ) *
          (X ^ p * (1 + X) ^ (d - p)) := by
  have h := sum_choose_X_pow_eq (N := n - l) (L := l) (d := d) hl (by lia)
  rw [Nat.sub_add_cancel (by lia : l ≤ n)] at h
  rw [← h]
  refine sum_congr rfl fun s _ => ?_
  rw [show n - s - l = n - l - s by lia]

/-- The paper's magic-basis expansion of `g_{r,n,i}` (Eulerian magic positivity lemma), with
explicitly nonnegative coefficients. -/
theorem weightPolynomial_eq {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i) (hn : r + i ≤ n) :
    weightPolynomial r n i =
      ∑ p ∈ range r, C (magicCoeff r n i p) * (X ^ p * (1 + X) ^ (r - 1 - p)) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = d + 1 := ⟨r - 1, by lia⟩
  have e1 : ∀ s, d + 1 - s - 1 = d - s := fun s => by lia
  have e2 : ∀ p, d + 1 - 1 - p = d - p := fun p => by lia
  have e3 : ∀ p, d + 1 - p - 1 = d - p := fun p => by lia
  have hw : ∀ s, (weight (d + 1) n i s : ℝ) = ∑ l ∈ Icc 1 (n - (d + 1) - i + 1),
      (((n - (d + 1) - l).choose (i - 1) : ℕ) : ℝ) *
        (((n.choose s * (n - s - l).choose (d - s) : ℕ)) : ℝ) := by
    intro s
    unfold weight
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [e1]
    ring
  unfold weightPolynomial magicCoeff
  simp only [hw, e2, e3]
  have hper : ∀ l ∈ Icc 1 (n - (d + 1) - i + 1),
      ∑ s ∈ range (d + 1), C (((n.choose s * (n - s - l).choose (d - s) : ℕ)) : ℝ) * X ^ s =
        ∑ p ∈ range (d + 1),
          C ((((n - l - p).choose (d - p) * (l - 1 + p).choose p : ℕ)) : ℝ) *
            (X ^ p * (1 + X) ^ (d - p)) := by
    intro l hl
    rw [mem_Icc] at hl
    exact sum_choose_X_pow_eq_of_le hl.1 (by lia)
  calc ∑ s ∈ range (d + 1), C (∑ l ∈ Icc 1 (n - (d + 1) - i + 1),
        (((n - (d + 1) - l).choose (i - 1) : ℕ) : ℝ) *
          (((n.choose s * (n - s - l).choose (d - s) : ℕ)) : ℝ)) * X ^ s
      = ∑ l ∈ Icc 1 (n - (d + 1) - i + 1), C (((n - (d + 1) - l).choose (i - 1) : ℕ) : ℝ) *
          ∑ s ∈ range (d + 1),
            C (((n.choose s * (n - s - l).choose (d - s) : ℕ)) : ℝ) * X ^ s := by
        simp only [map_sum, sum_mul, mul_sum, map_mul]
        rw [sum_comm]
        refine sum_congr rfl fun l _ => sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ l ∈ Icc 1 (n - (d + 1) - i + 1), C (((n - (d + 1) - l).choose (i - 1) : ℕ) : ℝ) *
          ∑ p ∈ range (d + 1),
            C ((((n - l - p).choose (d - p) * (l - 1 + p).choose p : ℕ)) : ℝ) *
              (X ^ p * (1 + X) ^ (d - p)) := by
        exact sum_congr rfl fun l hl => by rw [hper l hl]
    _ = _ := by
        simp only [map_sum, sum_mul, mul_sum, map_mul]
        rw [sum_comm]
        refine sum_congr rfl fun p _ => sum_congr rfl fun l _ => ?_
        ring

/-! ## The deranged map and Theorem 1.4 -/

private theorem natDegree_derangement_le (j : ℕ) :
    (DerangementTransform.polynomial j).natDegree ≤ j := by
  cases j with
  | zero => simp
  | succ j => exact natDegree_le_sturmDerangementsExc (j + 1)

private theorem reflect_derangement (j : ℕ) :
    (DerangementTransform.polynomial j).reflect j = DerangementTransform.polynomial j := by
  cases j with
  | zero => simp
  | succ j => exact reflect_sturmDerangementsExc (j + 1)

private theorem reflect_derangement_of_le {j r : ℕ} (hj : j ≤ r) :
    (DerangementTransform.polynomial j).reflect r =
      DerangementTransform.polynomial j * X ^ (r - j) := by
  have h := reflect_add_right_of_reflect (r - j) (natDegree_derangement_le j)
    (reflect_derangement j)
  rwa [show j + (r - j) = r by lia] at h

/-- The deranged map applied to `weightPolynomial`. -/
theorem transform_weightPolynomial (r n i : ℕ) :
    DerangementTransform.transform (weightPolynomial r n i) =
      ∑ j ∈ range r, C (weight r n i j : ℝ) * DerangementTransform.polynomial j := by
  unfold weightPolynomial
  rw [map_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [DerangementTransform.transform_C_mul, DerangementTransform.transform_X_pow]

private theorem natDegree_transform_weightPolynomial_le (r n i : ℕ) :
    (DerangementTransform.transform (weightPolynomial r n i)).natDegree ≤ r - 1 := by
  rw [transform_weightPolynomial]
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hj' : j < r := mem_range.mp hj
  exact (natDegree_C_mul_le _ _).trans ((natDegree_derangement_le j).trans (by lia))

/-- The transform identity `\underline H = I_{r-1}(D g)`. -/
theorem refinedHodgePoincare_eq_reflect (r n i : ℕ) :
    refinedHodgePoincare r n i =
      (DerangementTransform.transform (weightPolynomial r n i)).reflect (r - 1) := by
  rw [transform_weightPolynomial, reflect_finset_sum_C_mul]
  refine sum_congr rfl fun j hj => ?_
  rw [reflect_derangement_of_le (by have := mem_range.mp hj; lia)]

/-- The constant coefficient of the deranged image is the first weight. -/
theorem coeff_zero_transform_weightPolynomial (r n i : ℕ) (hr : 1 ≤ r) :
    (DerangementTransform.transform (weightPolynomial r n i)).coeff 0 =
      (weight r n i 0 : ℝ) := by
  rw [transform_weightPolynomial, finsetSum_coeff, sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by lia⟩
    have h0 : (sturmDerangementsExc (m + 1)).coeff 0 = 0 :=
      Polynomial.X_dvd_iff.mp (X_dvd_sturmDerangementsExc (m + 1))
    simp [DerangementTransform.polynomial, h0]
  · intro h
    exact absurd (mem_range.mpr (by lia)) h

/-- **Binder--Vecchi, Theorem 1.4** (Pólya frequency form): the refined Hodge--Poincaré
polynomial of `U_{r,n}` has nonnegative coefficients and only real nonpositive roots, for
`1 ≤ i ≤ n - r`. -/
theorem isPFPolynomial_refinedHodgePoincare {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i)
    (hn : r + i ≤ n) : IsPFPolynomial (refinedHodgePoincare r n i) := by
  have hmagic : weightPolynomial r n i =
      DerangementTransform.magicExpansion (r - 1) (magicCoeff r n i) := by
    rw [weightPolynomial_eq hr hi hn, DerangementTransform.magicExpansion,
      Nat.sub_add_cancel hr]
  have hpf := DerangementTransform.transform_magicExpansion_isPF (d := r - 1)
    (c := magicCoeff r n i) (fun k _ => magicCoeff_nonneg r n i k)
  rw [← hmagic] at hpf
  rw [refinedHodgePoincare_eq_reflect]
  exact reciprocalShift_preserves_pf hpf (natDegree_transform_weightPolynomial_le r n i)

/-- The refined Hodge--Poincaré polynomial is nonzero. -/
theorem refinedHodgePoincare_ne_zero {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i)
    (hn : r + i ≤ n) : refinedHodgePoincare r n i ≠ 0 := by
  rw [refinedHodgePoincare_eq_reflect]
  intro h
  have h0 := Polynomial.reflect_eq_zero_iff.mp h
  have := coeff_zero_transform_weightPolynomial r n i hr
  rw [h0] at this
  have hpos : (0 : ℝ) < weight r n i 0 := by exact_mod_cast weight_zero_pos hr hi hn
  simp only [coeff_zero_eq_eval_zero, eval_zero] at this
  linarith

/-- **Binder--Vecchi, Theorem 1.4**: the refined Hodge--Poincaré polynomial
`\underline H^i_{r,n}` of the uniform matroid `U_{r,n}` is real-rooted for `1 ≤ i ≤ n - r`. -/
theorem isRealRooted_refinedHodgePoincare {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i)
    (hn : r + i ≤ n) :
    refinedHodgePoincare r n i ≠ 0 ∧ (refinedHodgePoincare r n i).Splits :=
  ⟨refinedHodgePoincare_ne_zero hr hi hn,
    ((isPFPolynomial_refinedHodgePoincare hr hi hn).ne_zero_and_splits
      (refinedHodgePoincare_ne_zero hr hi hn)).2⟩

/-! ## The Eulerian transformation and Theorem 1.6 -/

private theorem natDegree_eulerian_le (s : ℕ) : (eulerian s).natDegree ≤ s := by
  cases s with
  | zero => simp [eulerian]
  | succ s => exact (generalizedEulerian_natDegree 1 s).le.trans (Nat.le_succ s)

private theorem reflect_eulerian (s : ℕ) :
    (eulerian s).reflect s = EulerianTransform.image s := by
  cases s with
  | zero => simp [eulerian, EulerianTransform.image]
  | succ s =>
    simp only [eulerian, EulerianTransform.image]
    rw [reflect_add_right_of_reflect 1 (generalizedEulerian_natDegree 1 s).le
      (generalizedEulerian_one_reflect s), pow_one, mul_comm]

private theorem natDegree_image_le (s : ℕ) : (EulerianTransform.image s).natDegree ≤ s := by
  cases s with
  | zero => simp [EulerianTransform.image]
  | succ s =>
    have h1 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
    have h2 := (generalizedEulerian_natDegree 1 s).le
    rw [EulerianTransform.image]
    exact natDegree_mul_le.trans (by lia)

private theorem reflect_X_pow_mul_eulerian {s r : ℕ} (hs : s ≤ r) :
    (X ^ (r - s) * eulerian s).reflect r = EulerianTransform.image s := by
  have h := reflect_mul (X ^ (r - s)) (eulerian s) (F := r - s) (G := s) (natDegree_X_pow_le _)
    (natDegree_eulerian_le s)
  rw [show r - s + s = r by lia, reflect_monomial, revAt_le le_rfl, Nat.sub_self, pow_zero,
    reflect_eulerian, one_mul] at h
  exact h

/-- The Eulerian transformation applied to `weightPolynomial`. -/
theorem transform_weightPolynomial_eulerian (r n i : ℕ) :
    EulerianTransform.transform (weightPolynomial r n i) =
      ∑ s ∈ range r, C (weight r n i s : ℝ) * EulerianTransform.image s := by
  unfold weightPolynomial
  rw [map_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [EulerianTransform.transform_C_mul, EulerianTransform.transform_X_pow]

/-- The transform identity `I_r(\widetilde H) = A°(g)`. -/
theorem reflect_modifiedAugmentedHodgePoincare (r n i : ℕ) :
    (modifiedAugmentedHodgePoincare r n i).reflect r =
      EulerianTransform.transform (weightPolynomial r n i) := by
  rw [transform_weightPolynomial_eulerian, modifiedAugmentedHodgePoincare,
    reflect_finset_sum_C_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [reflect_X_pow_mul_eulerian (by have := mem_range.mp hs; lia)]

/-- `\widetilde H = I_r(A° g)`. -/
theorem modifiedAugmentedHodgePoincare_eq_reflect (r n i : ℕ) :
    modifiedAugmentedHodgePoincare r n i =
      (EulerianTransform.transform (weightPolynomial r n i)).reflect r := by
  rw [← reflect_modifiedAugmentedHodgePoincare, reflect_reflect]

private theorem natDegree_eulerianTransform_weightPolynomial_le (r n i : ℕ) :
    (EulerianTransform.transform (weightPolynomial r n i)).natDegree ≤ r := by
  rw [transform_weightPolynomial_eulerian]
  refine natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  have hs' : s < r := mem_range.mp hs
  exact (natDegree_C_mul_le _ _).trans ((natDegree_image_le s).trans hs'.le)

/-- The constant coefficient of the Eulerian image is the first weight. -/
theorem coeff_zero_eulerianTransform_weightPolynomial (r n i : ℕ) (hr : 1 ≤ r) :
    (EulerianTransform.transform (weightPolynomial r n i)).coeff 0 = (weight r n i 0 : ℝ) := by
  rw [transform_weightPolynomial_eulerian, finsetSum_coeff, sum_eq_single 0]
  · simp [EulerianTransform.image]
  · intro j _ hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by lia⟩
    simp [EulerianTransform.image]
  · intro h
    exact absurd (mem_range.mpr (by lia)) h

/-- **Binder--Vecchi, Theorem 1.6** (Pólya frequency form): the modified augmented refined
Hodge--Poincaré polynomial of `U_{r,n}` has nonnegative coefficients and only real nonpositive
roots, for `1 ≤ i ≤ n - r`. -/
theorem isPFPolynomial_modifiedAugmentedHodgePoincare {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i)
    (hn : r + i ≤ n) : IsPFPolynomial (modifiedAugmentedHodgePoincare r n i) := by
  have hmagic : weightPolynomial r n i =
      EulerianTransform.magicExpansion (r - 1) (magicCoeff r n i) := by
    rw [weightPolynomial_eq hr hi hn, EulerianTransform.magicExpansion, Nat.sub_add_cancel hr]
  have hpf := EulerianTransform.transform_magicExpansion_isPF (d := r - 1)
    (c := magicCoeff r n i) (fun k _ => magicCoeff_nonneg r n i k)
  rw [← hmagic] at hpf
  rw [modifiedAugmentedHodgePoincare_eq_reflect]
  exact reciprocalShift_preserves_pf hpf
    (natDegree_eulerianTransform_weightPolynomial_le r n i)

/-- The modified augmented refined Hodge--Poincaré polynomial is nonzero. -/
theorem modifiedAugmentedHodgePoincare_ne_zero {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i)
    (hn : r + i ≤ n) : modifiedAugmentedHodgePoincare r n i ≠ 0 := by
  rw [modifiedAugmentedHodgePoincare_eq_reflect]
  intro h
  have h0 := Polynomial.reflect_eq_zero_iff.mp h
  have := coeff_zero_eulerianTransform_weightPolynomial r n i hr
  rw [h0] at this
  have hpos : (0 : ℝ) < weight r n i 0 := by exact_mod_cast weight_zero_pos hr hi hn
  simp only [coeff_zero_eq_eval_zero, eval_zero] at this
  linarith

/-- **Binder--Vecchi, Theorem 1.6**: the modified augmented refined Hodge--Poincaré polynomial
`\widetilde H^i_{r,n}` of the uniform matroid `U_{r,n}` is real-rooted for `1 ≤ i ≤ n - r`. -/
theorem isRealRooted_modifiedAugmentedHodgePoincare {r n i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i)
    (hn : r + i ≤ n) :
    modifiedAugmentedHodgePoincare r n i ≠ 0 ∧ (modifiedAugmentedHodgePoincare r n i).Splits :=
  ⟨modifiedAugmentedHodgePoincare_ne_zero hr hi hn,
    ((isPFPolynomial_modifiedAugmentedHodgePoincare hr hi hn).ne_zero_and_splits
      (modifiedAugmentedHodgePoincare_ne_zero hr hi hn)).2⟩

end BinderVecchi
end RealRooted
