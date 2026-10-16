module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.FieldDivision
public import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Reversal toolkit for degree-drop root-continuity

This file collects algebraic facts about `Polynomial.reverse` used by the
degree-drop endpoint behind issue #42.  The analytic endpoint concerns a family
`f + C μ * g` whose degree drops as `μ → 0`; after reversal, roots escaping to
infinity become ordinary roots near zero.
-/

public section

open Polynomial

namespace RealRooted.DegreeDropReversal

variable {K : Type*} [Field K]

/-- Predicate root-count transport across `reverse`: filtering roots of the
reverse by `q` counts exactly the original roots whose inverse satisfies `q`. -/
theorem card_filter_reverse_roots {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    (q : K → Prop) [DecidablePred q] :
    (p.reverse.roots.filter q).card = (p.roots.filter (fun r ↦ q r⁻¹)).card := by
  rw [Polynomial.roots_reverse_eq_map_inv hp h0]
  rw [Multiset.filter_map, Multiset.card_map]
  simp

/-- Total root count (with multiplicity) is preserved by reversal for a split
polynomial with nonzero constant coefficient.  This is the no-gap accounting
fact: reversal neither creates nor destroys roots. -/
theorem card_roots_reverse {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) :
    p.reverse.roots.card = p.roots.card := by
  rw [Polynomial.roots_reverse_eq_map_inv hp h0, Multiset.card_map]

/-- A polynomial with nonzero constant coefficient has nonzero reversal. -/
theorem reverse_ne_zero_of_coeff_zero_ne {p : K[X]} (h0 : p.coeff 0 ≠ 0) :
    p.reverse ≠ 0 :=
  fun hrev => h0 (by simp [Polynomial.reverse_eq_zero.mp hrev])

/-- Membership transport across reversal: the roots of `p.reverse` are exactly
the inverses of the roots of `p`. -/
theorem mem_roots_reverse_iff {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {x : K} : x ∈ p.reverse.roots ↔ ∃ r ∈ p.roots, r⁻¹ = x := by
  rw [Polynomial.roots_reverse_eq_map_inv hp h0, Multiset.mem_map]

/-- Reversal preserves `Splits` over a field. -/
@[deprecated Polynomial.Splits.reverse (since := "2026-10-21")]
theorem splits_reverse {p : K[X]} (h : p.Splits) :
    p.reverse.Splits :=
  h.reverse

/-- Reflecting a polynomial at a degree `N` at least its own `natDegree` factors
a power of `X` out of its reversal. -/
theorem reflect_eq_X_pow_mul_reverse {R : Type*} [Semiring R] (f : R[X]) {N : ℕ}
    (hN : f.natDegree ≤ N) :
    reflect N f = X ^ (N - f.natDegree) * f.reverse := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simp [Polynomial.reverse]
  | succ k ih =>
      rw [Nat.add_succ, Polynomial.reflect_succ f (Nat.le_add_right _ _),
        ih (Nat.le_add_right _ _),
        mul_assoc, ← Polynomial.commute_X, ← mul_assoc, ← pow_succ]
      rw [show f.natDegree + k - f.natDegree = k by lia,
        show f.natDegree + k + 1 - f.natDegree = k + 1 by lia]

/-- Reflection is linear on a polynomial family `f + C μ * g`. -/
theorem reflect_add_C_mul {R : Type*} [Semiring R] (f g : R[X]) (μ : R) (N : ℕ) :
    reflect N (f + C μ * g) = reflect N f + C μ * reflect N g := by simp

/-- If the constant coefficient is nonzero, reflecting at any degree bound
puts a nonzero coefficient in the top reflected degree. -/
theorem natDegree_reflect_eq_of_coeff_zero_ne {R : Type*} [Semiring R]
    {p : R[X]} {N : ℕ} (hN : p.natDegree ≤ N) (h0 : p.coeff 0 ≠ 0) :
    (reflect N p).natDegree = N := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact Polynomial.natDegree_reflect_le.trans <| by simp_all
  · simp_all

/-- Under the same hypotheses, the leading coefficient of the reflected
polynomial is the original constant coefficient. -/
theorem leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {N : ℕ} (hN : p.natDegree ≤ N) (h0 : p.coeff 0 ≠ 0) :
    (reflect N p).leadingCoeff = p.coeff 0 := by
  simp [Polynomial.leadingCoeff, natDegree_reflect_eq_of_coeff_zero_ne hN h0]

/-- Reflection at any degree at least `p.natDegree` preserves splitting. -/
@[deprecated Polynomial.Splits.reflect (since := "2026-10-21")]
theorem splits_reflect_of_splits {p : K[X]} (h : p.Splits) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p).Splits :=
  h.reflect hN

/-- For polynomials of degree at most `N`, reflection preserves and reflects
splitting. -/
@[deprecated Polynomial.splits_reflect_iff (since := "2026-10-21")]
theorem splits_reflect_iff {p : K[X]} {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).Splits ↔ p.Splits :=
  Polynomial.splits_reflect_iff hN

/-- Reflection sends a nonzero root to its inverse at any valid degree bound. -/
theorem isRoot_reflect_inv_iff {p : K[X]} {b : K} (hb : b ≠ 0)
    {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).IsRoot b⁻¹ ↔ p.IsRoot b := by
  let : Invertible b := invertibleOfNonzero hb
  change eval b⁻¹ (reflect N p) = 0 ↔ eval b p = 0
  simpa [Polynomial.eval₂_id, invOf_eq_inv] using
    (Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id K) b N p hN)

/-- Multiplying by a power of `X` does not change whether a polynomial splits. -/
theorem splits_X_pow_mul_iff {p : K[X]} (k : ℕ) :
    (X ^ k * p).Splits ↔ p.Splits := by
  rcases eq_or_ne p 0 with hp | hp
  · simp_all
  · rw [Polynomial.splits_mul (pow_ne_zero k Polynomial.X_ne_zero) hp,
      and_iff_right (Polynomial.Splits.X_pow k)]

/-- Multiplying by one factor of `X` does not change whether a polynomial
splits. -/
theorem splits_X_mul_iff {p : K[X]} : (X * p).Splits ↔ p.Splits := by simp

/-- A polynomial with zero constant coefficient is `X` times its `divX`
quotient. -/
theorem eq_X_mul_divX_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0) :
    p = X * p.divX :=
  by simpa [h0] using (Polynomial.X_mul_divX_add p).symm

/-- If the constant coefficient is zero, splitting is equivalent to splitting
after dividing by `X`. -/
theorem splits_iff_divX_splits_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0) :
    p.Splits ↔ p.divX.Splits := by
  conv_lhs => rw [eq_X_mul_divX_of_coeff_zero h0]
  simp

/-- If the constant coefficient is zero, splitting of `p.divX` lifts back to
splitting of `p`. -/
theorem splits_of_divX_splits_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0)
    (hdiv : p.divX.Splits) : p.Splits :=
  (splits_iff_divX_splits_of_coeff_zero h0).2 hdiv

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Inversion sends the positive half-line `(a, ∞)` to `(0, a⁻¹)`. -/
private theorem mem_Ioi_inv_iff {a r : K} (ha : 0 < a) :
    a < r⁻¹ ↔ (0 < r ∧ r < a⁻¹) := by
  by_cases hr : 0 < r
  · constructor <;> intro h <;> simp_all [lt_inv_comm₀]
    simpa using inv_strictAnti₀ h.1 h.2
  · refine iff_of_false (fun h ↦ hr ?_) (by simp_all)
    nlinarith [inv_mul_cancel₀ (show r ≠ 0 by grind),
      inv_pos.2 ha]

/-- Half-line root-count transport under reversal. -/
private theorem card_roots_reverse_Ioi {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {a : K} (ha : 0 < a) :
    (p.reverse.roots.filter (fun x => a < x)).card =
      (p.roots.filter (fun r => 0 < r ∧ r < a⁻¹)).card := by
  simpa [card_filter_reverse_roots hp h0 (fun x => a < x)] using
    congrArg Multiset.card
    (Multiset.filter_congr (fun r _ => mem_Ioi_inv_iff ha))

/-- Half-line root-count transport under reflection at a degree bound. -/
theorem card_roots_reflect_Ioi {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {N : ℕ} (hN : p.natDegree ≤ N) {a : K} (ha : 0 < a) :
    ((reflect N p).roots.filter (fun x => a < x)).card =
      (p.roots.filter (fun r => 0 < r ∧ r < a⁻¹)).card := by
  have hpad : Multiset.filter (fun x => a < x)
      ((N - p.natDegree) • ({0} : Multiset K)) = 0 := by
    rw [Multiset.filter_nsmul, Multiset.filter_singleton,
      ite_eq_right (not_lt_of_ge ha.le)]
    simp
  rw [reflect_eq_X_pow_mul_reverse p hN,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (reverse_ne_zero_of_coeff_zero_ne h0)),
    Multiset.filter_add, Multiset.card_add, Polynomial.roots_pow,
    Polynomial.roots_X, card_roots_reverse_Ioi hp h0 ha, hpad,
    Multiset.card_zero, zero_add]

/-- On the negative half-line, inversion reverses a strict-upper comparison. -/
private theorem mem_Ioi_inv_iff_of_neg {a r : K} (ha : a < 0) (hr : r < 0) :
    a < r⁻¹ ↔ r < a⁻¹ := by
  simpa using inv_lt_inv_of_neg (inv_lt_zero'.2 ha) hr

/-- Strict-upper root-count transport under reversal at a negative threshold,
assuming all original roots are strictly negative. -/
private theorem card_roots_reverse_Ioi_of_neg {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {a : K} (ha : a < 0)
    (hneg : ∀ r ∈ p.roots, r < 0) :
    (p.reverse.roots.filter (fun x => a < x)).card =
      (p.roots.filter (fun r => r < a⁻¹)).card := by
  rw [card_filter_reverse_roots hp h0]
  exact congrArg Multiset.card <|
    Multiset.filter_congr fun r hr => mem_Ioi_inv_iff_of_neg ha (hneg r hr)

/-- At a negative threshold, the reflected strict-upper count consists of all
degree-padding zeros together with the original roots lying below the inverse
threshold. -/
private theorem card_roots_reflect_Ioi_of_neg {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {N : ℕ} (hN : p.natDegree ≤ N)
    {a : K} (ha : a < 0) (hneg : ∀ r ∈ p.roots, r < 0) :
    ((reflect N p).roots.filter (fun x => a < x)).card =
      (N - p.natDegree) +
        (p.roots.filter (fun r => r < a⁻¹)).card := by
  rw [reflect_eq_X_pow_mul_reverse p hN,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (reverse_ne_zero_of_coeff_zero_ne h0)),
    Multiset.filter_add, Multiset.card_add, Polynomial.roots_pow,
    Polynomial.roots_X, card_roots_reverse_Ioi_of_neg hp h0 ha hneg]
  rw [Multiset.filter_nsmul, Multiset.filter_singleton, ite_eq_left ha]
  simp

/-- Complement form of negative-threshold root-count transport under
reflection. The number of original roots above `r < 0` is the complement in
the fixed reflection degree of the reflected roots above `r⁻¹`.

This is the endpoint bookkeeping needed when roots escape to `-∞`: the added
zero roots of the reflection are counted on the reflected strict-upper side
and hence disappear after taking the complement. -/
theorem card_roots_filter_gt_eq_reflect_compl {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {N : ℕ} (hN : p.natDegree ≤ N)
    {r : K} (hr : r < 0) (hrroot : ¬p.IsRoot r)
    (hneg : ∀ q ∈ p.roots, q < 0) :
    (p.roots.filter (fun q => r < q)).card =
      N - ((reflect N p).roots.filter (fun x => r⁻¹ < x)).card := by
  have hrmem : r ∉ p.roots := fun h => hrroot (Polynomial.isRoot_of_mem_roots h)
  have hpartition :
      (p.roots.filter (fun q => q < r)).card +
          (p.roots.filter (fun q => r < q)).card = p.roots.card := by
    have hfilter : p.roots.filter (fun q => ¬q < r) =
        p.roots.filter (fun q => r < q) :=
      Multiset.filter_congr fun q hq => by
      have hqr : q ≠ r := fun h => hrmem (h ▸ hq)
      grind
    rw [← Multiset.card_add, ← hfilter, Multiset.filter_add_not]
  have hreflect := card_roots_reflect_Ioi_of_neg hp h0 hN
    (inv_lt_zero'.2 hr) hneg
  rw [inv_inv] at hreflect
  have hcard : p.roots.card = p.natDegree :=
    hp.natDegree_eq_card_roots.symm
  lia

end Ordered

end RealRooted.DegreeDropReversal
