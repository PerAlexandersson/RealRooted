import RealRooted.EulerOperator.Darboux.NegativeRoots
import RealRooted.CombinatorialExamples.StirlingPermutations

/-!
# Jacobi–Stirling descent polynomials

S.-M. Ma and M.-X. Wang, *Binomial expansions of Jacobi–Stirling numbers and real-rootedness of
Jacobi–Stirling descent polynomials*, arXiv:2610.03111, Section 4.

Write `D_L f = (1 + L x) f + x (1 - x) f'` for the insertion operator, which is the Darboux
operator `darbouxOperator 1 (-L)`.  For `S ⊆ [k]` the descent polynomial `A_{k,S}` of the
Jacobi–Stirling permutations of `M_k ∖ S` satisfies `A_{0,∅} = 1` and, with
`L = 3 (k - 1) - |S ∩ [k - 1]|`,

* `A_{k,S} = D_L A_{k-1,S ∖ {k}}` if `k ∈ S`;
* `A_{k,S} = D_{L+1} D_L A_{k-1,S}` if `k ∉ S`

(Ma–Wang, eq. (9)).  The combinatorial model (descents of Jacobi–Stirling permutations,
Gessel–Lin–Zeng) is not formalized: these recurrences define the polynomials here, and the
real-rootedness below is derived from them rather than assumed.

The main results of this file are:

* `IsGood.insertion_and_strictInterl`: Ma–Wang Lemma 2.  If `f` has degree `d`, positive
  leading coefficient, nonnegative coefficients, `f(0) = 1` and simple real roots, and
  `d < L`, then `D_L f` has the same properties in degree `d + 1` and strictly interlaces
  with `f`.
* `isGood_descentPoly`, `coeff_zero_descentPoly`: for `S ⊆ [k]`, `A_{k,S}` has degree
  `2k - |S| - 1` (for `k ≥ 1`), `A_{k,S}(0) = 1`, and only simple negative zeros
  (Ma–Wang, eq. (11)).
* `X_mul_descentPoly_Icc`: `x A_{k,[k]}` is the second-order Eulerian polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace JacobiStirlingDescent

/-- The insertion operator `D_L f = (1 + L x) f + x (1 - x) f'`. -/
def insertion (L : ℕ) (f : ℝ[X]) : ℝ[X] :=
  darbouxOperator 1 (-(L : ℝ)) f

theorem insertion_eq (L : ℕ) (f : ℝ[X]) :
    insertion L f = (1 + C (L : ℝ) * X) * f + X * (1 - X) * f.derivative := by
  simp only [insertion, darbouxOperator, map_neg, map_one]
  ring

theorem coeff_insertion_succ (L : ℕ) (f : ℝ[X]) (k : ℕ) :
    (insertion L f).coeff (k + 1) = (k + 2) * f.coeff (k + 1) + ((L : ℝ) - k) * f.coeff k := by
  rw [insertion, coeff_darbouxOperator_succ]
  ring

theorem coeff_zero_insertion (L : ℕ) (f : ℝ[X]) :
    (insertion L f).coeff 0 = f.coeff 0 := by
  simp [insertion_eq, coeff_zero_eq_eval_zero]

/-- The Jacobi–Stirling descent polynomial `A_{k,S}`, defined by the insertion recurrence. -/
def descentPoly : ℕ → Finset ℕ → ℝ[X]
  | 0, _ => 1
  | k + 1, S =>
    if k + 1 ∈ S then insertion (3 * k - (S ∩ Finset.Icc 1 k).card)
        (descentPoly k (S ∩ Finset.Icc 1 k))
    else insertion (3 * k - (S ∩ Finset.Icc 1 k).card + 1)
        (insertion (3 * k - (S ∩ Finset.Icc 1 k).card) (descentPoly k (S ∩ Finset.Icc 1 k)))

/-- The invariant carried through the insertions: degree `d`, positive leading coefficient,
nonnegative coefficients, positive constant term, and simple real roots
(`RealRooted.SimpleNegRooted`). -/
abbrev IsGood (f : ℝ[X]) (d : ℕ) : Prop := SimpleNegRooted f d

/-- **Ma–Wang, Lemma 2.**  An insertion `D_L` with `L` larger than the degree raises the degree
by one, keeps the invariant, and strictly interlaces with its input.  This is the Darboux step
`SimpleNegRooted.darbouxOperator` with `a = 1` and `b = L`. -/
theorem IsGood.insertion_and_strictInterl {f : ℝ[X]} {d L : ℕ} (hf : IsGood f d) (hL : d < L) :
    IsGood (insertion L f) (d + 1) ∧ StrictInterl f (insertion L f) ∧
      ∀ r, f.IsRoot r → ¬ (insertion L f).IsRoot r :=
  hf.darbouxOperator one_pos (by exact_mod_cast hL)

theorem descentPoly_succ_of_mem {k : ℕ} {S : Finset ℕ} (h : k + 1 ∈ S) :
    descentPoly (k + 1) S = insertion (3 * k - (S ∩ Finset.Icc 1 k).card)
      (descentPoly k (S ∩ Finset.Icc 1 k)) := by
  simp [descentPoly, h]

theorem descentPoly_succ_of_not_mem {k : ℕ} {S : Finset ℕ} (h : k + 1 ∉ S) :
    descentPoly (k + 1) S = insertion (3 * k - (S ∩ Finset.Icc 1 k).card + 1)
      (insertion (3 * k - (S ∩ Finset.Icc 1 k).card) (descentPoly k (S ∩ Finset.Icc 1 k))) := by
  simp [descentPoly, h]

/-- **Ma–Wang, eq. (11).**  For `S ⊆ [k]`, the descent polynomial `A_{k,S}` has degree
`2k - |S| - 1` (read as `0` when `k = 0`), positive constant term, nonnegative coefficients,
and only simple real (hence negative) roots. -/
theorem isGood_descentPoly {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 k) :
    IsGood (descentPoly k S) (2 * k - S.card - 1) := by
  induction k generalizing S with
  | zero => simpa [descentPoly] using SimpleNegRooted.one
  | succ k ih =>
    have hT : S ∩ Finset.Icc 1 k ⊆ Finset.Icc 1 k := Finset.inter_subset_right
    have hTcard : (S ∩ Finset.Icc 1 k).card ≤ k := by
      simpa using Finset.card_le_card hT
    have hcard : S.card = (S ∩ Finset.Icc 1 k).card + if k + 1 ∈ S then 1 else 0 := by
      have hsplit : S = (S ∩ Finset.Icc 1 k) ∪ (S ∩ {k + 1}) := by
        ext x
        constructor
        · intro hx
          have := Finset.mem_Icc.mp (hS hx)
          rcases lt_or_eq_of_le this.2 with h | h
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, Finset.mem_Icc.mpr
              ⟨this.1, by lia⟩⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, by simp [h]⟩)
        · intro hx
          rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_inter.mp h).1
      conv_lhs => rw [hsplit]
      rw [Finset.card_union_of_disjoint]
      · split_ifs with h
        · simp [Finset.inter_singleton_of_mem h]
        · simp [Finset.inter_singleton_of_notMem h]
      · refine Finset.disjoint_left.mpr fun x hx hx' => ?_
        have h1 := Finset.mem_Icc.mp (Finset.mem_inter.mp hx).2
        have h2 := Finset.mem_singleton.mp (Finset.mem_inter.mp hx').2
        lia
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- `k + 1 = 1`: the base cases `A_{1,∅} = 1 + x` and `A_{1,{1}} = 1`.
      have hT0 : S ∩ Finset.Icc 1 0 = ∅ := by simp
      by_cases h1 : 1 ∈ S
      · rw [descentPoly_succ_of_mem h1, hT0]
        have hS1 : S.card = 1 := by simpa [hT0, h1] using hcard
        rw [hS1]
        simpa [descentPoly, insertion_eq] using SimpleNegRooted.one
      · rw [descentPoly_succ_of_not_mem h1, hT0]
        have hS0 : S.card = 0 := by simpa [hT0, h1] using hcard
        rw [hS0]
        have h0 : insertion (3 * 0 - (∅ : Finset ℕ).card) (descentPoly 0 ∅) = 1 := by
          simp [descentPoly, insertion_eq]
        rw [h0]
        exact (IsGood.insertion_and_strictInterl SimpleNegRooted.one (by norm_num)).1
    have hgood := ih hT
    set T := S ∩ Finset.Icc 1 k
    have hL : 2 * k - T.card - 1 < 3 * k - T.card := by lia
    obtain ⟨h1, -⟩ := hgood.insertion_and_strictInterl hL
    by_cases hmem : k + 1 ∈ S
    · rw [descentPoly_succ_of_mem hmem]
      have : 2 * (k + 1) - S.card - 1 = 2 * k - T.card - 1 + 1 := by
        rw [hcard]
        simp only [hmem, ↓reduceIte]
        lia
      rw [this]
      exact h1
    · rw [descentPoly_succ_of_not_mem hmem]
      have : 2 * (k + 1) - S.card - 1 = 2 * k - T.card - 1 + 1 + 1 := by
        rw [hcard]
        simp only [hmem, ↓reduceIte]
        lia
      rw [this]
      exact (h1.insertion_and_strictInterl (by lia)).1

/-- The roots of `A_{k,S}` are negative. -/
theorem isRoot_descentPoly_neg {k : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 k)
    {r : ℝ} (hr : (descentPoly k S).IsRoot r) : r < 0 :=
  (isGood_descentPoly hS).isRoot_neg hr

/-- `A_{k,S}(0) = 1`. -/
@[simp]
theorem coeff_zero_descentPoly (k : ℕ) (S : Finset ℕ) : (descentPoly k S).coeff 0 = 1 := by
  induction k generalizing S with
  | zero => simp [descentPoly]
  | succ k ih =>
    by_cases h : k + 1 ∈ S
    · rw [descentPoly_succ_of_mem h, coeff_zero_insertion, ih]
    · rw [descentPoly_succ_of_not_mem h, coeff_zero_insertion, coeff_zero_insertion, ih]

/-- With every barred letter deleted, `x A_{k,[k]}` is the second-order Eulerian polynomial
(the descent polynomial of Stirling permutations). -/
theorem X_mul_descentPoly_Icc (k : ℕ) :
    X * descentPoly (k + 1) (Finset.Icc 1 (k + 1)) = stirlingPermutations (k + 1) := by
  induction k with
  | zero => simp [descentPoly, insertion_eq, stirlingPermutations_one]
  | succ k ih =>
    have hT : Finset.Icc 1 (k + 1 + 1) ∩ Finset.Icc 1 (k + 1) = Finset.Icc 1 (k + 1) :=
      Finset.inter_eq_right.mpr (Finset.Icc_subset_Icc_right (by lia))
    rw [descentPoly_succ_of_mem (by simp), hT, Nat.card_Icc, stirlingPermutations_succ, ← ih,
      insertion_eq, stirlingPermutationsCoeffA, stirlingPermutationsCoeffB, derivative_mul,
      derivative_X, one_mul]
    have : ((3 * (k + 1) - (k + 1 + 1 - 1) : ℕ) : ℝ) = 2 * (k + 1) := by
      rw [show 3 * (k + 1) - (k + 1 + 1 - 1) = 2 * (k + 1) by lia]
      push_cast
      ring
    rw [this]
    push_cast
    simp only [map_add, map_mul, map_one, map_ofNat, map_natCast]
    ring

end JacobiStirlingDescent
end RealRooted
