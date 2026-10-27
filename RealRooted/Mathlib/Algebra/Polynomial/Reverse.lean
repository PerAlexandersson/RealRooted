/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.Mathlib.Algebra.Ring.Parity

/-!
# Roots of reversed polynomials

Root transport for `Polynomial.reverse`, including the zero-root case omitted
by the usual nonzero-constant-coefficient formulation, and the calculus of `reflect`:
`reflect N` is an involution on polynomials of degree at most `N`, and the derivative of
`reflect N r` is `reflect N (X (N r - X r'))`.
-/

public section

open Finset

noncomputable section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- Increasing a reflection bound by one multiplies the reflected polynomial by
`X`. -/
theorem reflect_succ (p : R[X]) {D : ℕ} (hdeg : p.natDegree ≤ D) :
    p.reflect (D + 1) = p.reflect D * X := by
  simpa [Nat.add_comm] using
    (Polynomial.reflect_mul (f := p) (g := (1 : R[X])) (F := D) (G := 1)
      hdeg (by simp))

theorem revAt_eq_ite (N i : ℕ) : revAt N i = if i ≤ N then N - i else i := by
  rw [← revAtFun_eq]
  rfl

theorem reflect_X (N : ℕ) : reflect N (X : R[X]) = X ^ revAt N 1 := by
  simpa using reflect_monomial (R := R) N 1

theorem reflect_ofNat_mul (N n : ℕ) [n.AtLeastTwo] (p : R[X]) :
    reflect N ((OfNat.ofNat n : R[X]) * p) = (OfNat.ofNat n : R[X]) * reflect N p := by
  rw [← C_ofNat, reflect_C_mul]

/-- Multiplying by `X ^ k` and reflecting `k` further leaves the reflection unchanged. -/
theorem reflect_X_pow_mul (q : R[X]) {N : ℕ} (k : ℕ) (hq : q.natDegree ≤ N) :
    reflect (N + k) (X ^ k * q) = reflect N q := by
  simpa [Nat.add_comm] using
    (reflect_mul (X ^ k : R[X]) q (F := k) (G := N) (natDegree_X_pow_le k) hq)

/-- Multiplying by a reflected polynomial is a reflection of a product:
`a * reflect N q = reflect (k + N) (reflect k a * q)` when `a` has degree at most `k` and `q`
degree at most `N`. -/
theorem mul_reflect_eq_reflect_mul {a q : R[X]} {k N : ℕ} (ha : a.natDegree ≤ k)
    (hq : q.natDegree ≤ N) : a * reflect N q = reflect (k + N) (reflect k a * q) := by
  rw [reflect_mul _ _ (natDegree_reflect_le.trans (max_le le_rfl ha)) hq, reflect_reflect]

section CommSemiring

variable {S : Type*} [CommSemiring S] [Nontrivial S]

/-- A degree bound on `X ^ k * f` gives one on `f`. -/
theorem natDegree_le_of_natDegree_X_pow_mul_le {f : S[X]} {k M : ℕ}
    (h : (X ^ k * f).natDegree ≤ M + k) : f.natDegree ≤ M := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [natDegree_X_pow_mul k hf] at h
    lia

/-- A factor `X ^ k` inside a product drops out of a reflection of length `M + k`. -/
theorem reflect_add_mul_X_pow_mul {a u : S[X]} {k M : ℕ}
    (h : (a * (X ^ k * u)).natDegree ≤ M + k) :
    reflect (M + k) (a * (X ^ k * u)) = reflect M (a * u) := by
  rw [mul_left_comm] at h ⊢
  exact reflect_X_pow_mul _ k (natDegree_le_of_natDegree_X_pow_mul_le h)

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A]

/-- Reflecting a polynomial after negating its variable introduces the sign of
the reflection bound. -/
theorem reflect_comp_neg_X_of_natDegree_le
    {n : ℕ} {p : A[X]} (hp : p.natDegree ≤ n) :
    reflect n (p.comp (-X)) =
      C ((-1 : A) ^ n) * (reflect n p).comp (-X) := by
  ext k
  rw [coeff_reflect, coeff_C_mul, coeff_comp_neg_X, coeff_comp_neg_X, coeff_reflect]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, ← Parity.neg_one_pow_mul_eq_neg_one_pow_sub hk]
    ring
  · have hlt : n < k := Nat.lt_of_not_le hk
    rw [revAt_eq_self_of_lt hlt,
      coeff_eq_zero_of_natDegree_lt (hp.trans_lt hlt)]
    simp

/-- The polynomial `X (N r - X r')`, whose reflection at `N` is the derivative of the
reflection of `r` (`derivative_reflect`), has degree at most `N`. -/
theorem natDegree_X_mul_C_mul_sub_X_mul_derivative_le {r : A[X]} {N : ℕ}
    (hr : r.natDegree ≤ N) :
    (X * (C (N : A) * r - X * derivative r)).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by lia⟩
  rw [coeff_X_mul, coeff_sub, coeff_C_mul]
  rcases m with _ | m
  · have hN : N = 0 := by lia
    subst hN
    simp
  · rw [coeff_X_mul, coeff_derivative]
    rcases Nat.lt_or_ge N (m + 1) with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (hr.trans_lt h)]
      ring
    · have hN : N = m + 1 := by lia
      subst hN
      push_cast
      ring

/-- The derivative of a reflection: `(X ^ N r (1 / X))' = X ^ N · (X (N r - X r'))(1 / X)`. -/
theorem derivative_reflect (r : A[X]) {N : ℕ} (hr : r.natDegree ≤ N) :
    derivative (reflect N r) = reflect N (X * (C (N : A) * r - X * derivative r)) := by
  ext j
  rw [coeff_derivative, coeff_reflect, coeff_reflect]
  rcases Nat.lt_or_ge N j with hj | hj
  · rw [revAt_eq_self_of_lt hj, revAt_eq_self_of_lt (by lia),
      coeff_eq_zero_of_natDegree_lt (by lia),
      coeff_eq_zero_of_natDegree_lt
        ((natDegree_X_mul_C_mul_sub_X_mul_derivative_le hr).trans_lt hj), zero_mul]
  · rw [revAt_le hj]
    rcases Nat.lt_or_ge j N with hj' | hj'
    · obtain ⟨s, hs⟩ : ∃ s, N - j = s + 1 := ⟨N - j - 1, by lia⟩
      have hN : (N : A) = s + 1 + j := by
        rw [show N = s + 1 + j by lia]
        push_cast
        ring
      rw [revAt_le (by lia : j + 1 ≤ N), show N - (j + 1) = s by lia, hs, coeff_X_mul,
        coeff_sub, coeff_C_mul, hN]
      rcases s with _ | s
      · simp
        ring
      · rw [coeff_X_mul, coeff_derivative]
        push_cast
        ring
    · obtain rfl : j = N := by lia
      rw [revAt_eq_self_of_lt (by lia), Nat.sub_self, coeff_X_mul_zero,
        coeff_eq_zero_of_natDegree_lt (by lia), zero_mul]

end CommRing

variable {K : Type*} [Field K]

namespace Splits

private theorem reverse_X_add_C (a : K) :
    (X + C a).reverse.Splits :=
  Splits.of_natDegree_le_one <|
    (reverse_natDegree_le (X + C a)).trans <| by simp

/-- Reversal preserves splitting over a field. -/
theorem reverse {p : K[X]} (h : p.Splits) : p.reverse.Splits := by
  induction h using Submonoid.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · simp
      · exact reverse_X_add_C a
  | one =>
      exact Splits.of_natDegree_le_one <|
        (reverse_natDegree_le (1 : K[X])).trans <| by simp
  | mul x y _ _ ihx ihy => simp_all

/-- Multiplying the reverse of a split polynomial by a power of `X` preserves
splitting. -/
theorem X_pow_mul_reverse {p : K[X]} (h : p.Splits) (N : ℕ) :
    (X ^ (N - p.natDegree) * p.reverse).Splits :=
  (Splits.X_pow (N - p.natDegree)).mul h.reverse

end Splits

/-- Reflecting at a degree bound factors through reversal and a power of `X`. -/
theorem reflect_eq_X_pow_mul_reverse (p : K[X]) {N : ℕ} (hN : p.natDegree ≤ N) :
    reflect N p = X ^ (N - p.natDegree) * p.reverse := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simp [Polynomial.reverse]
  | succ k ih =>
      rw [Nat.add_succ, reflect_succ p (Nat.le_add_right _ _),
        ih (Nat.le_add_right _ _), mul_assoc, ← commute_X, ← mul_assoc,
        ← pow_succ]
      rw [show p.natDegree + k - p.natDegree = k by lia,
        show p.natDegree + k + 1 - p.natDegree = k + 1 by lia]

namespace Splits

/-- Reflection at any degree bound preserves splitting. -/
theorem reflect {p : K[X]} (h : p.Splits) {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).Splits := by
  simpa [reflect_eq_X_pow_mul_reverse p hN] using h.X_pow_mul_reverse N

end Splits

/-- At a valid degree bound, reflection preserves and reflects splitting. -/
theorem splits_reflect_iff {p : K[X]} {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).Splits ↔ p.Splits := by
  refine ⟨?_, fun h ↦ h.reflect hN⟩
  intro h
  simpa using h.reflect <|
    (natDegree_reflect_le (N := N) (p := p)).trans (max_eq_left hN).le

/-- Reversal preserves and reflects splitting over a field. -/
theorem splits_reverse_iff {p : K[X]} : p.reverse.Splits ↔ p.Splits := by
  simpa [Polynomial.reverse] using
    (splits_reflect_iff (p := p) (N := p.natDegree) le_rfl)

namespace Splits

/-- If the reverse splits, then the original polynomial splits. -/
theorem of_reverse {p : K[X]} (h : p.reverse.Splits) : p.Splits :=
  splits_reverse_iff.mp h

end Splits

section CharZero

variable [CharZero K] {p : K[X]} {n : ℕ}

/-- Evaluation at `-1` of a polynomial fixed by reflection. -/
theorem eval_neg_one_mul_neg_one_pow_of_reflect_eq_self
    (hdeg : p.natDegree ≤ n) (hreflect : p.reflect n = p) :
    p.eval (-1) * (-1 : K) ^ n = p.eval (-1) := by
  let : Invertible (-1 : K) := invertibleOfNonzero (by simp)
  simpa [hreflect] using
    (Polynomial.eval₂_reflect_mul_pow (i := RingHom.id K) (x := (-1 : K)) n p hdeg)

/-- A polynomial fixed by reflection through an odd bound has `-1` as a root. -/
theorem isRoot_neg_one_of_reflect_eq_self_of_odd
    (hdeg : p.natDegree ≤ n) (hreflect : p.reflect n = p) (hn : Odd n) :
    p.IsRoot (-1) := by
  rw [Polynomial.IsRoot.def]
  have h := eval_neg_one_mul_neg_one_pow_of_reflect_eq_self hdeg hreflect
  rw [hn.neg_one_pow] at h
  exact CharZero.neg_eq_self_iff.mp (by simpa using h)

end CharZero

/-- The reversal of a nonzero monic linear factor is a nonzero scalar times
the monic factor at the inverse root. -/
theorem reverse_X_sub_C_eq (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]).reverse = C (-r) * (X - C r⁻¹) := by
  ext n
  rcases n with _ | _ | n <;>
    simp [Polynomial.reverse, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_C, hr]

/-- Reversal of a nonzero monic linear factor has the inverse root. -/
theorem roots_reverse_X_sub_C (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]).reverse.roots = {r⁻¹} := by
  rw [reverse_X_sub_C_eq r hr, Polynomial.roots_C_mul]
  · simp
  · grind

private theorem reverse_prod_X_sub_C_ne_zero (s : Multiset K) :
    ((s.map fun r => (X - C r : K[X])).prod).reverse ≠ 0 := by
  rw [Ne, Polynomial.reverse_eq_zero]
  exact (monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r).ne_zero

private theorem roots_reverse_prod_X_sub_C [DecidableEq K] (s : Multiset K) :
    ((s.map fun r => (X - C r : K[X])).prod).reverse.roots =
      (s.filter fun r => r ≠ 0).map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.reverse]
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.reverse_mul_of_domain]
      by_cases ha : a = 0
      · simp_all [Polynomial.reverse]
      · rw [Multiset.filter_cons_of_pos (p := fun r ↦ r ≠ 0) s ha, Multiset.map_cons]
        have hleft : (X - C a : K[X]).reverse ≠ 0 := by
          rw [reverse_X_sub_C_eq a ha]
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr ha))
            (Polynomial.X_sub_C_ne_zero a⁻¹)
        rw [Polynomial.roots_mul (mul_ne_zero hleft (reverse_prod_X_sub_C_ne_zero s)),
          roots_reverse_X_sub_C a ha, ih]
        simp

/-- If `p` splits over a field, the roots of `p.reverse` are the inverses of
the nonzero roots of `p`, retaining multiplicity. -/
theorem roots_reverse_eq_filter_map_inv [DecidableEq K] {p : K[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) :
    p.reverse.roots = (p.roots.filter fun r => r ≠ 0).map (·⁻¹) := by
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp_ne
  conv_lhs => rw [Polynomial.Splits.eq_prod_roots hp_splits]
  rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_C,
    Polynomial.roots_C_mul _ hlead, roots_reverse_prod_X_sub_C]

/-- If `p` splits over a field and `p 0 ≠ 0`, the roots of `p.reverse` are the inverses of the
roots of `p`, retaining multiplicity. -/
theorem roots_reverse_eq_map_inv {p : K[X]} (hp : p.Splits) (h0 : p.coeff 0 ≠ 0) :
    p.reverse.roots = p.roots.map (·⁻¹) := by
  classical
  have hp0 : p ≠ 0 := fun h => h0 (by simp [h])
  rw [roots_reverse_eq_filter_map_inv hp0 hp, Multiset.filter_eq_self.mpr]
  rintro r hr rfl
  exact h0 (by simpa [coeff_zero_eq_eval_zero] using isRoot_of_mem_roots hr)

/-- A product of monic linear factors over a field is nonzero. -/
theorem multiset_prod_X_sub_C_ne_zero (s : Multiset K) :
    (s.map fun r => (X - C r : K[X])).prod ≠ 0 :=
  (monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r).ne_zero

end Polynomial
