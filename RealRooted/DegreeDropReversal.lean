import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Reversal toolkit for degree-drop root-continuity

This file collects algebraic facts about `Polynomial.reverse` used by the
degree-drop endpoint behind issue #42.  The analytic endpoint concerns a family
`f + C μ * g` whose degree drops as `μ → 0`; after reversal, roots escaping to
infinity become ordinary roots near zero.
-/

open Polynomial

namespace RealRooted.DegreeDropReversal

variable {K : Type*} [Field K]

/-- Reversal sends a monic linear factor `X + C a` to a polynomial that still
splits. -/
theorem splits_reverse_X_add_C (a : K) :
    (X + C a).reverse.Splits :=
  Polynomial.Splits.of_natDegree_le_one <|
    (Polynomial.reverse_natDegree_le (X + C a)).trans <| by
      simp

/-- Reversal of a nonzero monic linear factor, normalized as a nonzero scalar
times another monic linear factor. -/
theorem reverse_X_sub_C_eq (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]).reverse = C (-r) * (X - C r⁻¹) := by
  ext n
  rcases n with _ | _ | n <;>
    simp [Polynomial.reverse, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_C, hr]

/-- Roots of the reverse of a nonzero monic linear factor. -/
theorem roots_reverse_X_sub_C (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]).reverse.roots = {r⁻¹} := by
  rw [reverse_X_sub_C_eq r hr, Polynomial.roots_C_mul]
  · simp
  · grind

/-- A product of monic linear factors is nonzero. -/
theorem prod_X_sub_C_ne_zero (s : Multiset K) :
    (Multiset.map (fun r => (X - C r : K[X])) s).prod ≠ 0 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons r s ih =>
      simp [ih, Polynomial.X_sub_C_ne_zero r]

/-- Roots of the reverse of a product of nonzero monic linear factors. -/
theorem roots_reverse_prod_X_sub_C (s : Multiset K) (hs : ∀ r ∈ s, r ≠ 0) :
    ((Multiset.map (fun r => (X - C r : K[X])) s).prod).reverse.roots =
      s.map (fun r => r⁻¹) := by
  induction s using Multiset.induction with
  | empty =>
      simp [Polynomial.reverse]
  | cons r s ih =>
      have hr : r ≠ 0 := hs r (by simp)
      have hs' : ∀ a ∈ s, a ≠ 0 := fun a ha => hs a (by simp [ha])
      have ih' := ih hs'
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [Polynomial.reverse_mul_of_domain]
      rw [Polynomial.roots_mul]
      · rw [roots_reverse_X_sub_C r hr, ih']
        simp
      · have hleft : (X - C r : K[X]).reverse ≠ 0 := by
          simpa [reverse_X_sub_C_eq r hr] using mul_ne_zero
            (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr hr))
            (Polynomial.X_sub_C_ne_zero r⁻¹)
        have hright :
            ((Multiset.map (fun r ↦ (X - C r : K[X])) s).prod).reverse ≠ 0 :=
          fun hzero ↦ by
          simp_all
        simp_all

/-- If `p` splits and has nonzero constant coefficient, the roots of
`p.reverse` are exactly the inverses of the roots of `p`, with multiplicity. -/
theorem roots_reverse_eq_map_inv_of_splits_coeff_zero_ne {p : K[X]}
    (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) :
    p.reverse.roots = p.roots.map (fun r ↦ r⁻¹) := by
  have hp_ne : p ≠ 0 := fun hp_zero ↦ by
    simp_all
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
  have hroots_ne : ∀ r ∈ p.roots, r ≠ 0 := fun r hr hr_zero ↦ by
    have hroot : p.IsRoot 0 := by simp_all
    exact h0 (by
      simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hroot)
  conv_lhs => rw [Polynomial.Splits.eq_prod_roots hp]
  rw [Polynomial.reverse_mul_of_domain]
  rw [Polynomial.reverse_C]
  rw [Polynomial.roots_C_mul]
  · exact roots_reverse_prod_X_sub_C p.roots hroots_ne
  · simp_all

/-- Predicate root-count transport across `reverse`: filtering roots of the
reverse by `q` counts exactly the original roots whose inverse satisfies `q`. -/
theorem card_filter_reverse_roots {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    (q : K → Prop) [DecidablePred q] :
    (p.reverse.roots.filter q).card = (p.roots.filter (fun r ↦ q r⁻¹)).card := by
  rw [roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hp h0]
  rw [Multiset.filter_map, Multiset.card_map]
  simp

/-- Total root count (with multiplicity) is preserved by reversal for a split
polynomial with nonzero constant coefficient.  This is the no-gap accounting
fact: reversal neither creates nor destroys roots. -/
theorem card_roots_reverse {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) :
    p.reverse.roots.card = p.roots.card := by
  rw [roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hp h0, Multiset.card_map]

/-- A polynomial with nonzero constant coefficient has nonzero reversal. -/
theorem reverse_ne_zero_of_coeff_zero_ne {p : K[X]} (h0 : p.coeff 0 ≠ 0) :
    p.reverse ≠ 0 :=
  fun hrev => h0 (by simp [Polynomial.reverse_eq_zero.mp hrev])

/-- Membership transport across reversal: the roots of `p.reverse` are exactly
the inverses of the roots of `p`. -/
theorem mem_roots_reverse_iff {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {x : K} : x ∈ p.reverse.roots ↔ ∃ r ∈ p.roots, r⁻¹ = x := by
  rw [roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hp h0, Multiset.mem_map]

/-- Every root of the reverse of a split polynomial with nonzero constant
coefficient is itself nonzero: reversal never introduces a zero root, which is
what keeps closed-segment endpoint arguments away from the point at infinity. -/
theorem ne_zero_of_mem_roots_reverse {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {x : K} (hx : x ∈ p.reverse.roots) : x ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := (mem_roots_reverse_iff hp h0).1 hx
  refine inv_ne_zero (fun hr0 ↦ h0 ?_)
  have hroot : p.IsRoot 0 := by simp_all
  simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hroot

/-- Pointwise multiplicity transport across reversal: the multiplicity of `x` as
a root of `p.reverse` equals the multiplicity of `x⁻¹` as a root of `p`.  This
refines `card_roots_reverse` to a per-point no-gap statement. -/
theorem count_roots_reverse [DecidableEq K] {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {x : K} :
    p.reverse.roots.count x = p.roots.count x⁻¹ := by
  rw [roots_reverse_eq_map_inv_of_splits_coeff_zero_ne hp h0]
  rw [show x = (x⁻¹)⁻¹ from (inv_inv x).symm,
    Multiset.count_map_eq_count' _ _ inv_injective, inv_inv]

/-- Reversal preserves `Splits` over a field. -/
theorem splits_reverse {p : K[X]} (h : p.Splits) :
    p.reverse.Splits := by
  induction h using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · simp
    · exact splits_reverse_X_add_C a
  | one =>
    exact Polynomial.Splits.of_natDegree_le_one <|
      (Polynomial.reverse_natDegree_le (1 : K[X])).trans <| by simp
  | mul x y _ _ ihx ihy =>
    simp_all

/-- Reflecting a polynomial at a degree `N` at least its own `natDegree` factors
a power of `X` out of its reversal. -/
theorem reflect_eq_X_pow_mul_reverse {R : Type*} [Semiring R] (f : R[X]) {N : ℕ}
    (hN : f.natDegree ≤ N) :
    reflect N f = X ^ (N - f.natDegree) * f.reverse := by
  ext n
  by_cases hn : n ≤ N
  · by_cases hNn : n ≥ N - f.natDegree
    · rw [coeff_reflect, revAt_le hn, Polynomial.coeff_mul,
        Finset.sum_eq_single (N - f.natDegree, n - (N - f.natDegree))]
      · dsimp only
        have h_sub : n - (N - f.natDegree) = f.natDegree - (N - n) := by lia
        rw [h_sub, Polynomial.coeff_reverse, revAt_le (by lia), Nat.sub_sub_self (by lia),
          Polynomial.coeff_X_pow, if_pos rfl, one_mul]
      · intro x hx hx_ne
        have : x.1 ≠ N - f.natDegree := by
          intro h_eq
          apply hx_ne
          ext
          · exact h_eq
          · have := Finset.mem_antidiagonal.mp hx
            lia
        rw [Polynomial.coeff_X_pow, if_neg this, zero_mul]
      · intro h
        exfalso
        apply h
        rw [Finset.mem_antidiagonal]
        lia
    · rw [coeff_reflect, revAt_le hn]
      have h_lt : f.natDegree < N - n := by lia
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt h_lt, Polynomial.coeff_mul]
      exact Eq.symm (Finset.sum_eq_zero fun x hx => by
        have h_eq : x.1 ≠ N - f.natDegree := by
          have := Finset.mem_antidiagonal.mp hx
          lia
        rw [Polynomial.coeff_X_pow, if_neg h_eq, zero_mul])
  · rw [coeff_reflect, revAt_eq_self_of_lt (by lia),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by lia), Polynomial.coeff_mul]
    exact Eq.symm (Finset.sum_eq_zero fun x hx => by
      by_cases hx1 : x.1 = N - f.natDegree
      · rw [hx1]
        have : x.2 > f.natDegree := by
          have := Finset.mem_antidiagonal.mp hx
          lia
        have : f.reverse.natDegree ≤ f.natDegree := Polynomial.reverse_natDegree_le _
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := f.reverse) (by lia), mul_zero]
      · rw [Polynomial.coeff_X_pow, if_neg hx1, zero_mul])

/-- Root-count accounting for reflection at a degree bound: reflecting at `N`
splits the roots into the `N - natDegree` padding zeros contributed by the
`X`-power and the reversed roots.  Useful for no-gap counting at the degree-drop
endpoint. -/
theorem card_roots_reflect {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).roots.card = (N - p.natDegree) + p.roots.card := by
  rw [reflect_eq_X_pow_mul_reverse p hN,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (reverse_ne_zero_of_coeff_zero_ne h0)),
    Multiset.card_add, Polynomial.roots_pow, Polynomial.roots_X, Multiset.card_nsmul,
    Multiset.card_singleton, mul_one, card_roots_reverse hp h0]

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
  rw [Polynomial.leadingCoeff, natDegree_reflect_eq_of_coeff_zero_ne hN h0]
  simp

/-- Degree-padded reversal form of a reflected affine polynomial family. -/
theorem reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_X_pow_mul_reverse
    {R : Type*} [Semiring R] (f g : R[X]) (μ : R) {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) :
    reflect N (f + C μ * g) =
      X ^ (N - f.natDegree) * f.reverse + C μ * (X ^ (N - g.natDegree) * g.reverse) := by
  rw [reflect_add_C_mul, reflect_eq_X_pow_mul_reverse f hfN,
    reflect_eq_X_pow_mul_reverse g hgN]

/-- When `g` has the reflecting degree exactly, the reflected family has only
the lower-degree member padded by a power of `X`. -/
theorem reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_reverse
    (f g : K[X]) (μ : K) {N : ℕ} (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    reflect N (f + C μ * g) = X ^ (N - f.natDegree) * f.reverse + C μ * g.reverse := by
  rw [reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_X_pow_mul_reverse f g μ hfN
    (le_of_eq hgN)]
  simp [hgN]

/-- Degree-padded reversal form of a reflected affine polynomial family, when
the second member has exactly the reflecting degree. -/
theorem reflect_add_C_mul_eq_X_pow_reverse_add_C_mul_reverse
    {R : Type*} [Semiring R] (f g : R[X]) (μ : R) {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    reflect N (f + C μ * g) = X ^ (N - f.natDegree) * f.reverse + C μ * g.reverse := by
  rw [reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_X_pow_mul_reverse f g μ hfN
    (le_of_eq hgN)]
  simp [hgN]

/-- Multiplying the reverse of a split polynomial by the degree-padding power
of `X` still splits. -/
theorem splits_X_pow_mul_reverse {p : K[X]} (h : p.Splits) (N : ℕ) :
    (X ^ (N - p.natDegree) * p.reverse).Splits :=
  (Polynomial.Splits.X_pow (N - p.natDegree)).mul (splits_reverse h)

/-- Interface-shaped version of `splits_X_pow_mul_reverse`; the degree bound is
not needed for the proof but is often available at call sites. -/
theorem splits_X_pow_mul_reverse_of_splits {p : K[X]} (h : p.Splits) {N : ℕ}
    (_hN : p.natDegree ≤ N) :
    (X ^ (N - p.natDegree) * p.reverse).Splits :=
  splits_X_pow_mul_reverse h N

/-- Reflection at any degree at least `p.natDegree` preserves splitting. -/
theorem splits_reflect_of_splits {p : K[X]} (h : p.Splits) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p).Splits := by
  simpa [reflect_eq_X_pow_mul_reverse p hN] using
    splits_X_pow_mul_reverse_of_splits h hN

/-- For polynomials of degree at most `N`, reflection preserves and reflects
splitting. -/
theorem splits_reflect_iff {p : K[X]} {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).Splits ↔ p.Splits := by
  refine ⟨?_, fun h ↦ splits_reflect_of_splits h hN⟩
  intro h
  have hreflect_deg : (reflect N p).natDegree ≤ N :=
    Polynomial.natDegree_reflect_le.trans <| by simp_all
  simpa using splits_reflect_of_splits h hreflect_deg

/-- Reversal preserves and reflects splitting over a field. -/
theorem splits_reverse_iff {p : K[X]} :
    p.reverse.Splits ↔ p.Splits := by
  simpa [Polynomial.reverse] using
    (splits_reflect_iff (p := p) (N := p.natDegree) le_rfl)

/-- If the reverse of a polynomial splits, then the original polynomial splits. -/
theorem splits_of_reverse {p : K[X]} (h : p.reverse.Splits) :
    p.Splits :=
  splits_reverse_iff.mp h

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
    p = X * p.divX := by
  have h := Polynomial.X_mul_divX_add p
  simp_all

/-- Reversal is blind to a vanishing constant term: if `p.coeff 0 = 0`, then
`p` and its `divX` quotient have the same reversal.

This is the reversal-side companion of `eq_X_mul_divX_of_coeff_zero`: on the
residual constant-term branch where the constant coefficient vanishes, the
reversal used by the degree-drop endpoint may be computed on the lower-degree
`divX` quotient, which is exactly the polynomial handled after removing the zero
root. -/
theorem reverse_divX_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0) :
    p.reverse = p.divX.reverse := by
  conv_lhs => rw [eq_X_mul_divX_of_coeff_zero h0]
  exact Polynomial.reverse_X_mul p.divX

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

/-- Alias for `reverse_divX_of_coeff_zero` matching the right-zero branch. -/
theorem reverse_eq_reverse_divX_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0) :
    p.reverse = p.divX.reverse :=
  reverse_divX_of_coeff_zero h0

/-- In the zero-constant branch, `p.reverse` splits iff `p.divX` splits. -/
theorem splits_reverse_iff_divX_splits_of_coeff_zero {p : K[X]}
    (h0 : p.coeff 0 = 0) :
    p.reverse.Splits ↔ p.divX.Splits := by
  rw [reverse_eq_reverse_divX_of_coeff_zero h0, splits_reverse_iff]

/-- The reflected degree-padded family splits if and only if the original
family splits. -/
theorem splits_reflected_family_iff {a b : K} {f g : K[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits ↔
      (C a * f + C b * g).Splits := by
  have hle : (C a * f + C b * g).natDegree ≤ N :=
    (Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_C_mul_le a f).trans hfN)
        ((Polynomial.natDegree_C_mul_le b g).trans hgN.le)
  have hreflect :
      reflect N (C a * f + C b * g) =
        C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse := by
    rw [Polynomial.reflect_add, Polynomial.reflect_C_mul, Polynomial.reflect_C_mul,
      reflect_eq_X_pow_mul_reverse f hfN, reflect_eq_X_pow_mul_reverse g hgN.le]
    simp [hgN]
  rw [← hreflect]
  exact splits_reflect_iff hle

/-- Additive right-zero degree-drop/reversal wrapper for the affine family. -/
theorem splits_reverse_family_iff_divX_add_of_coeff_zero {a b : K} {f g : K[X]}
    (h0 : (C a * f + C b * g).coeff 0 = 0) :
    (C a * f + C b * g).reverse.Splits ↔
      (C a * f.divX + C b * g.divX).Splits := by
  rw [splits_reverse_iff_divX_splits_of_coeff_zero h0, Polynomial.divX_add,
    Polynomial.divX_C_mul, Polynomial.divX_C_mul]

/-- Forward consumer for `splits_reverse_family_iff_divX_add_of_coeff_zero`. -/
theorem splits_divX_add_of_splits_reverse_family_of_coeff_zero
    {a b : K} {f g : K[X]}
    (h0 : (C a * f + C b * g).coeff 0 = 0)
    (h : (C a * f + C b * g).reverse.Splits) :
    (C a * f.divX + C b * g.divX).Splits :=
  (splits_reverse_family_iff_divX_add_of_coeff_zero h0).mp h

/-- Converse consumer for `splits_reverse_family_iff_divX_add_of_coeff_zero`. -/
theorem splits_reverse_family_of_splits_divX_add_of_coeff_zero
    {a b : K} {f g : K[X]}
    (h0 : (C a * f + C b * g).coeff 0 = 0)
    (h : (C a * f.divX + C b * g.divX).Splits) :
    (C a * f + C b * g).reverse.Splits :=
  (splits_reverse_family_iff_divX_add_of_coeff_zero h0).mpr h

/-- Reflected-family form of `splits_reverse_family_iff_divX_add_of_coeff_zero`. -/
theorem splits_reflected_family_iff_divX_add_of_coeff_zero
    {a b : K} {f g : K[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N)
    (h0 : (C a * f + C b * g).coeff 0 = 0) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits ↔
      (C a * f.divX + C b * g.divX).Splits := by
  rw [splits_reflected_family_iff hfN hgN]
  exact (splits_reverse_iff (p := C a * f + C b * g)).symm.trans
    (splits_reverse_family_iff_divX_add_of_coeff_zero h0)

/-- Forward-direction consumer of `splits_reflected_family_iff_divX_add_of_coeff_zero`. -/
theorem splits_divX_add_of_splits_reflected_family_of_coeff_zero
    {a b : K} {f g : K[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N)
    (h0 : (C a * f + C b * g).coeff 0 = 0)
    (h : (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits) :
    (C a * f.divX + C b * g.divX).Splits :=
  (splits_reflected_family_iff_divX_add_of_coeff_zero hfN hgN h0).mp h

/-- Converse-direction consumer of
`splits_reflected_family_iff_divX_add_of_coeff_zero`. -/
theorem splits_reflected_family_of_splits_divX_add_of_coeff_zero
    {a b : K} {f g : K[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N)
    (h0 : (C a * f + C b * g).coeff 0 = 0)
    (h : (C a * f.divX + C b * g.divX).Splits) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits :=
  (splits_reflected_family_iff_divX_add_of_coeff_zero hfN hgN h0).mpr h

/-- Direct routing between the reflected family and the reversed affine
family. -/
theorem splits_reflected_family_iff_splits_reverse {a b : K} {f g : K[X]}
    {N : ℕ} (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits ↔
      (C a * f + C b * g).reverse.Splits := by
  rw [splits_reverse_iff, splits_reflected_family_iff hfN hgN]

/-- Reverse-orientation routing between the reversed affine family and the
reflected family. -/
theorem splits_reverse_iff_splits_reflected_family {a b : K} {f g : K[X]}
    {N : ℕ} (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    (C a * f + C b * g).reverse.Splits ↔
      (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits :=
  (splits_reflected_family_iff_splits_reverse hfN hgN).symm

/-- Forward-direction consumer of `splits_reflected_family_iff_splits_reverse`. -/
theorem splits_reverse_of_splits_reflected_family {a b : K} {f g : K[X]}
    {N : ℕ} (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N)
    (h : (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits) :
    (C a * f + C b * g).reverse.Splits :=
  (splits_reflected_family_iff_splits_reverse hfN hgN).mp h

/-- Converse-direction consumer of `splits_reflected_family_iff_splits_reverse`. -/
theorem splits_reflected_family_of_splits_reverse {a b : K} {f g : K[X]}
    {N : ℕ} (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N)
    (h : (C a * f + C b * g).reverse.Splits) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits :=
  (splits_reflected_family_iff_splits_reverse hfN hgN).mpr h

/-- Orientation flip of `count_roots_reverse`: the multiplicity of `r⁻¹` as a
root of `p.reverse` equals the multiplicity of `r` as a root of `p`. -/
theorem count_roots_reverse_inv [DecidableEq K] {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {r : K} :
    p.reverse.roots.count r⁻¹ = p.roots.count r := by
  rw [count_roots_reverse hp h0, inv_inv]

/-- No-gap emptiness transport across reversal. -/
theorem card_filter_reverse_roots_eq_zero_iff {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) (q : K → Prop) [DecidablePred q] :
    (p.reverse.roots.filter q).card = 0 ↔
      (p.roots.filter (fun r => q r⁻¹)).card = 0 := by
  rw [card_filter_reverse_roots hp h0 q]

section Ordered

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Inversion sends a positive open interval `(a, b)` to `(b⁻¹, a⁻¹)`. -/
theorem mem_Ioo_inv_iff {a b r : K} (ha : 0 < a) (hb : 0 < b) :
    (a < r⁻¹ ∧ r⁻¹ < b) ↔ (b⁻¹ < r ∧ r < a⁻¹) := by
  constructor
  · intro h
    have hr_pos : 0 < r := inv_pos.mp (lt_trans ha h.1)
    exact ⟨inv_lt_of_inv_lt₀ hr_pos h.2, by simpa using inv_strictAnti₀ ha h.1⟩
  · intro h
    refine ⟨?_, ?_⟩ <;>
      nlinarith [inv_pos.2 ha, inv_pos.2 hb, mul_inv_cancel₀ (ne_of_gt ha),
        mul_inv_cancel₀ (ne_of_gt hb),
        mul_inv_cancel₀ (show r ≠ 0 by linarith [inv_pos.2 ha, inv_pos.2 hb])]

/-- Inversion sends the positive half-line `(a, ∞)` to `(0, a⁻¹)`. -/
theorem mem_Ioi_inv_iff {a r : K} (ha : 0 < a) :
    a < r⁻¹ ↔ (0 < r ∧ r < a⁻¹) := by
  by_cases hr : 0 < r
  · constructor <;> intro h <;> simp_all [lt_inv_comm₀]
    simpa using inv_strictAnti₀ h.1 h.2
  · refine iff_of_false (fun h ↦ hr ?_) (by simp_all)
    nlinarith [inv_mul_cancel₀ (show r ≠ 0 by grind),
      inv_pos.2 ha]

/-- Interval root-count transport under reversal. -/
theorem card_roots_reverse_Ioo {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {a b : K} (ha : 0 < a) (hb : 0 < b) :
    (p.reverse.roots.filter (fun x => a < x ∧ x < b)).card =
      (p.roots.filter (fun r => b⁻¹ < r ∧ r < a⁻¹)).card := by
  simpa [card_filter_reverse_roots hp h0 (fun x => a < x ∧ x < b)] using
    congrArg Multiset.card
    (Multiset.filter_congr (fun r _ => mem_Ioo_inv_iff ha hb))

/-- Half-line root-count transport under reversal. -/
theorem card_roots_reverse_Ioi {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
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
  have hpad :
      Multiset.filter (fun x => a < x)
        ((N - p.natDegree) • ({0} : Multiset K)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
    grind
  rw [reflect_eq_X_pow_mul_reverse p hN,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (reverse_ne_zero_of_coeff_zero_ne h0)),
    Multiset.filter_add, Multiset.card_add, Polynomial.roots_pow,
    Polynomial.roots_X, card_roots_reverse_Ioi hp h0 ha, hpad,
    Multiset.card_zero, zero_add]

/-- No-gap emptiness on a positive interval under reversal. -/
theorem card_roots_reverse_Ioo_eq_zero_iff {p : K[X]} (hp : p.Splits)
    (h0 : p.coeff 0 ≠ 0) {a b : K} (ha : 0 < a) (hb : 0 < b) :
    (p.reverse.roots.filter (fun x => a < x ∧ x < b)).card = 0 ↔
      (p.roots.filter (fun r => b⁻¹ < r ∧ r < a⁻¹)).card = 0 := by
  rw [card_roots_reverse_Ioo hp h0 ha hb]

/-- Interval root-count transport under reflection at a degree bound. -/
theorem card_roots_reflect_Ioo {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0)
    {N : ℕ} (hN : p.natDegree ≤ N) {a b : K} (ha : 0 < a) (hb : 0 < b) :
    ((reflect N p).roots.filter (fun x => a < x ∧ x < b)).card =
      (p.roots.filter (fun r => b⁻¹ < r ∧ r < a⁻¹)).card := by
  have hpad :
      Multiset.filter (fun x => a < x ∧ x < b)
        ((N - p.natDegree) • ({0} : Multiset K)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_nsmul, Multiset.mem_singleton] at hx
    grind
  rw [reflect_eq_X_pow_mul_reverse p hN,
    Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (reverse_ne_zero_of_coeff_zero_ne h0)),
    Polynomial.roots_pow, Polynomial.roots_X, Multiset.filter_add,
    Multiset.card_add, card_roots_reverse_Ioo hp h0 ha hb, hpad,
    Multiset.card_zero, zero_add]

end Ordered

end RealRooted.DegreeDropReversal
