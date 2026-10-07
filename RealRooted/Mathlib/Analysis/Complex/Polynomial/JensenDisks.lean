import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Polynomial.GaussLucas

/-!
# Jensen disks

We prove Jensen's theorem (1913): every non-real root of the derivative of a real polynomial `p`
lies in a *Jensen disk* of `p`, that is, in the closed disk whose diameter is the segment joining
a non-real root `z` of `p` and its conjugate `conj z`. This disk is centred at `z.re` and has
radius `|z.im|`.

## Main statements

* `Polynomial.exists_mem_jensenDisk_of_isRoot_derivative`: Jensen's theorem.

## Proof

If `w` is a root of both `p'` and `p`, then `w` lies in its own Jensen disk. Otherwise
`∑ 1 / (w - z) = p'(w) / p(w) = 0`, the sum running over the complex roots of `p` with
multiplicity. Since this root multiset is invariant under conjugation, also
`∑ (1 / (w - z) + 1 / (w - conj z)) = 0`. If `w` lies strictly outside every Jensen disk, then
every summand has imaginary part of sign opposite to `w.im`, which is a contradiction.
-/

open scoped Polynomial ComplexConjugate

namespace Complex

/-- If `w` is non-real and lies strictly outside the closed disk centred at `z.re` with radius
`|z.im|`, then the imaginary part of `1 / (w - z) + 1 / (w - conj z)` has sign opposite to the
sign of `w.im`. -/
theorem im_mul_im_one_div_add_one_div_neg {w z : ℂ} (hw : w.im ≠ 0)
    (hz : |z.im| < dist w (z.re : ℂ)) :
    w.im * (1 / (w - z) + 1 / (w - conj z)).im < 0 := by
  have hd : z.im ^ 2 < (w.re - z.re) ^ 2 + w.im ^ 2 := by
    have h1 := mul_self_lt_mul_self (abs_nonneg _) hz
    rw [dist_eq, ← sq, ← sq, Complex.sq_norm, normSq_apply, sq_abs] at h1
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h1
    nlinarith
  have hb : 0 < w.im ^ 2 := by positivity
  have hD1 : 0 < (w.re - z.re) * (w.re - z.re) + (w.im - z.im) * (w.im - z.im) := by
    nlinarith [sq_nonneg (w.im + z.im)]
  have hD2 : 0 < (w.re - z.re) * (w.re - z.re) + (w.im - -z.im) * (w.im - -z.im) := by
    nlinarith [sq_nonneg (w.im - z.im)]
  simp only [one_div, add_im, inv_im, normSq_apply, sub_re, sub_im, conj_re, conj_im]
  rw [div_add_div _ _ hD1.ne' hD2.ne', mul_div_assoc']
  exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)

/-- If `c * (f a).im < 0` for every `a ∈ s`, then `c * (∑ a ∈ s, f a).im ≤ 0`. -/
theorem mul_im_multiset_sum_map_nonpos {α : Type*} {c : ℝ} {f : α → ℂ} (s : Multiset α)
    (h : ∀ a ∈ s, c * (f a).im < 0) : c * (s.map f).sum.im ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, add_im, mul_add]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun b hb ↦ h b (Multiset.mem_cons_of_mem hb)
    linarith

/-- If `s` is nonempty and `c * (f a).im < 0` for every `a ∈ s`, then
`c * (∑ a ∈ s, f a).im < 0`. -/
theorem mul_im_multiset_sum_map_neg {α : Type*} {c : ℝ} {f : α → ℂ} {s : Multiset α}
    (hs : s ≠ 0) (h : ∀ a ∈ s, c * (f a).im < 0) : c * (s.map f).sum.im < 0 := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.map_cons, Multiset.sum_cons, add_im, mul_add]
  have h1 := h a (Multiset.mem_cons_self a t)
  have h2 := mul_im_multiset_sum_map_nonpos t fun b hb ↦ h b (Multiset.mem_cons_of_mem hb)
  linarith

end Complex

namespace Polynomial

/-- The complex roots of a real polynomial, counted with multiplicity, are invariant under
complex conjugation. -/
theorem map_conj_roots_map_ofReal (p : ℝ[X]) :
    (p.map (algebraMap ℝ ℂ)).roots.map (starRingEnd ℂ) = (p.map (algebraMap ℝ ℂ)).roots := by
  rw [← (IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))).roots_map (starRingEnd ℂ), map_map]
  congr 2
  ext x
  simp

/-- *Jensen's theorem* (1913): every non-real root `w` of the derivative of a nonconstant real
polynomial `p` lies in a Jensen disk of `p`, i.e. there is a non-real root `z` of `p` such that
`w` lies in the closed disk whose diameter is the segment from `z` to `conj z`. -/
theorem exists_mem_jensenDisk_of_isRoot_derivative {p : ℝ[X]} (hp : 0 < p.degree) {w : ℂ}
    (hw : (p.derivative.map (algebraMap ℝ ℂ)).IsRoot w) (hwim : w.im ≠ 0) :
    ∃ z ∈ (p.map (algebraMap ℝ ℂ)).roots, z.im ≠ 0 ∧ dist w (z.re : ℂ) ≤ |z.im| := by
  have hP0 : p.map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero (ne_zero_of_degree_gt hp)
  by_cases hPw : (p.map (algebraMap ℝ ℂ)).eval w = 0
  · refine ⟨w, (mem_roots hP0).2 hPw, hwim, ?_⟩
    rw [Complex.dist_of_re_eq (by simp)]
    simp
  by_contra! h
  have hlt : ∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, |z.im| < dist w (z.re : ℂ) := by
    intro z hz
    by_cases hz0 : z.im = 0
    · rw [hz0, abs_zero, dist_pos]
      rintro rfl
      exact hwim (by simp)
    · exact h z hz hz0
  have hsplit := IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))
  have hsum : ((p.map (algebraMap ℝ ℂ)).roots.map fun z ↦ 1 / (w - z)).sum = 0 := by
    rw [← hsplit.eval_derivative_div_eval_of_ne_zero hPw, derivative_map, hw.eq_zero, zero_div]
  have hconj : ((p.map (algebraMap ℝ ℂ)).roots.map fun z ↦ 1 / (w - conj z)).sum = 0 := by
    rw [← hsum]
    conv_rhs => rw [← map_conj_roots_map_ofReal p]
    rw [Multiset.map_map]
    rfl
  have hne : (p.map (algebraMap ℝ ℂ)).roots ≠ 0 := by
    refine hsplit.roots_ne_zero ?_
    rw [natDegree_map]
    exact (natDegree_pos_iff_degree_pos.2 hp).ne'
  have key := Complex.mul_im_multiset_sum_map_neg hne
    fun z hz ↦ Complex.im_mul_im_one_div_add_one_div_neg hwim (hlt z hz)
  rw [Multiset.sum_map_add, hsum, hconj] at key
  simp at key

end Polynomial
