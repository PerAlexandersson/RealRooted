import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits

/-!
# Roots of reversed polynomials

Root transport for `Polynomial.reverse`, including the zero-root case omitted
by the usual nonzero-constant-coefficient formulation, and the calculus of `reflect`:
`reflect N` is an involution on polynomials of degree at most `N`, and the derivative of
`reflect N r` is `reflect N (X (N r - X r'))`.
-/

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
  ext j
  rw [coeff_reflect, coeff_reflect, coeff_X_pow_mul']
  rcases Nat.lt_or_ge (N + k) j with h1 | h1
  · rw [revAt_eq_self_of_lt h1, revAt_eq_self_of_lt (by lia),
      coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < j)]
    simp only [show k ≤ j by lia, ↓reduceIte]
    exact coeff_eq_zero_of_natDegree_lt (by lia)
  · rw [revAt_le h1]
    rcases Nat.lt_or_ge N j with h2 | h2
    · rw [revAt_eq_self_of_lt h2, coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < j)]
      simp only [show ¬k ≤ N + k - j by lia, ↓reduceIte]
    · rw [revAt_le h2, show N + k - j - k = N - j by lia]
      simp only [show k ≤ N + k - j by lia, ↓reduceIte]

section CommRing

variable {A : Type*} [CommRing A]

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

local instance : DecidableEq K := Classical.decEq K

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
  refine Multiset.prod_ne_zero ?_
  rw [Multiset.mem_map]
  rintro ⟨r, -, hr⟩
  exact X_sub_C_ne_zero r (by assumption)

private theorem roots_reverse_prod_X_sub_C (s : Multiset K) :
    ((s.map fun r => (X - C r : K[X])).prod).reverse.roots =
      (s.filter fun r => r ≠ 0).map (·⁻¹) := by
  classical
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
theorem roots_reverse_eq_filter_map_inv {p : K[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) :
    p.reverse.roots = (p.roots.filter fun r => r ≠ 0).map (·⁻¹) := by
  classical
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp_ne
  conv_lhs => rw [Polynomial.Splits.eq_prod_roots hp_splits]
  rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_C,
    Polynomial.roots_C_mul _ hlead, roots_reverse_prod_X_sub_C]

end Polynomial
