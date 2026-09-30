import RealRooted.Basic
import RealRooted.MaWang
import RealRooted.RootCountJump

/-!
# Liu x-subtraction splitting tools

This module contains reusable low-degree root-list splitting helpers used by
the normalized x-subtraction endpoint leaves.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- If `x` has opposite sign to `y` and the same sign as `z`, then `y` and
`z` have opposite signs. -/
lemma mul_neg_of_mul_neg_of_mul_pos_left {x y z : ℝ}
    (hxy : x * y < 0) (hxz : 0 < x * z) : y * z < 0 := by
  have hx_ne : x ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hxy)).1
  have hxx_pos : 0 < x * x := mul_self_pos.mpr hx_ne
  have hprod : (x * y) * (x * z) < 0 := mul_neg_of_neg_of_pos hxy hxz
  have hcalc : (x * y) * (x * z) = (x * x) * (y * z) := by ring
  rw [hcalc] at hprod
  have hneg_pos : 0 < (x * x) * (-(y * z)) := by
    rw [mul_neg]
    simpa [neg_pos] using hprod
  have : 0 < -(y * z) := (mul_pos_iff_of_pos_left hxx_pos).mp hneg_pos
  exact neg_pos.mp this

/-- Evaluate the x-subtraction pencil at a root of the left endpoint. -/
lemma eval_X_mul_sub_C_mul_of_left_isRoot
    {p q : ℝ[X]} {x μ : ℝ} (hx : p.IsRoot x) :
    (X * p - C μ * q).eval x = -μ * q.eval x := by
  have hpx : p.eval x = 0 := by simpa [Polynomial.IsRoot.def] using hx
  simp [Polynomial.eval_sub, Polynomial.eval_mul, hpx]

/-- The x-subtraction pencil does not vanish at a left root if the right
endpoint does not vanish there. -/
lemma not_isRoot_X_mul_sub_C_mul_of_left_isRoot
    {p q : ℝ[X]} {x μ : ℝ} (hx : p.IsRoot x) (hμ : μ ≠ 0)
    (hq : ¬ q.IsRoot x) :
    ¬ (X * p - C μ * q).IsRoot x := by
  intro hP
  have hprod : -μ * q.eval x = 0 := by
    simpa [Polynomial.IsRoot.def, eval_X_mul_sub_C_mul_of_left_isRoot hx] using hP
  have hqeval : q.eval x = 0 := (mul_eq_zero.mp hprod).resolve_left (neg_ne_zero.mpr hμ)
  exact hq (by simpa [Polynomial.IsRoot.def] using hqeval)

/-- Evaluate the x-subtraction pencil at a root of the right endpoint. -/
lemma eval_X_mul_sub_C_mul_of_right_isRoot
    {p q : ℝ[X]} {x μ : ℝ} (hx : q.IsRoot x) :
    (X * p - C μ * q).eval x = x * p.eval x := by
  have hqx : q.eval x = 0 := by simpa [Polynomial.IsRoot.def] using hx
  simp [Polynomial.eval_sub, Polynomial.eval_mul, hqx]

/-- A nonzero polynomial splits once a nodup list of roots is at least as long
as its natural degree.  This local helper packages the repeated
root-count-to-splitting argument used in low-degree endpoint leaves. -/
lemma splits_of_roots_list_of_natDegree_le {p : ℝ[X]} {rs : List ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ rs.length)
    (hnd : rs.Nodup) (hroot : ∀ r ∈ rs, p.IsRoot r) :
    p.Splits := by
  have hsub : (↑rs : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)]
    intro r hr
    exact (mem_roots hp_ne).mpr (hroot r (Multiset.mem_coe.mp hr))
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card hsub
    (by simpa using hdeg)

/-- A nonzero polynomial of degree at most three splits when it has three
ordered real roots. -/
lemma splits_of_three_ordered_roots_of_natDegree_le {p : ℝ[X]} {a b c : ℝ}
    (hp_ne : p ≠ 0) (hdeg : p.natDegree ≤ 3) (hab : a < b) (hbc : b < c)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hc : p.IsRoot c) :
    p.Splits := by
  have hac : a < c := lt_trans hab hbc
  exact splits_of_roots_list_of_natDegree_le (rs := [a, b, c]) hp_ne
    (by simpa using hdeg)
    (by simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt hbc])
    (by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc)

/-- If two roots of the left endpoint bracket a strict sign change of the
right endpoint, then the x-subtraction pencil has a root between them. -/
lemma exists_isRoot_between_X_mul_sub_C_mul_of_left_roots_right_eval_mul_neg
    {p q : ℝ[X]} {a b μ : ℝ}
    (hab : a < b) (ha : p.IsRoot a) (hb : p.IsRoot b)
    (hμ : μ ≠ 0) (hqsign : q.eval a * q.eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ (X * p - C μ * q).IsRoot c := by
  refine exists_isRoot_between_of_eval_mul_neg (p := X * p - C μ * q) hab ?_
  rw [eval_X_mul_sub_C_mul_of_left_isRoot ha,
    eval_X_mul_sub_C_mul_of_left_isRoot hb]
  nlinarith [mul_self_pos.mpr hμ, hqsign]

/-- If two roots of the left endpoint bracket an odd number of roots of a
nonzero splitting right endpoint, and the right endpoint is nonzero at both
bracket endpoints, then the x-subtraction pencil has a root between them. -/
lemma exists_isRoot_between_X_mul_sub_C_mul_of_left_roots_odd_right_roots
    {p q : ℝ[X]} (hq_ne : q ≠ 0) (hq : q.Splits) {a b μ : ℝ}
    (hab : a < b) (ha : p.IsRoot a) (hb : p.IsRoot b) (hμ : μ ≠ 0)
    (hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card)
    (hqa : ¬ q.IsRoot a) (hqb : ¬ q.IsRoot b) :
    ∃ c, a < c ∧ c < b ∧ (X * p - C μ * q).IsRoot c :=
  exists_isRoot_between_X_mul_sub_C_mul_of_left_roots_right_eval_mul_neg
    hab ha hb hμ
    (eval_mul_eval_neg_of_odd_card_roots_filter_Ioo
      hq_ne hq (le_of_lt hab) hodd hqa hqb)

/-- If a right-endpoint root `y` lies between two left-endpoint roots and the
two x-subtraction signs change across `y`, then the x-subtraction pencil has
one root on each side of `y`.  The assumption `y < 0` is load-bearing for
applications with nonnegative coefficients. -/
lemma exists_two_isRoot_between_X_mul_sub_C_mul_of_left_roots_right_root_signs
    {p q : ℝ[X]} {a b y μ : ℝ}
    (hay : a < y) (hyb : y < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hy : q.IsRoot y)
    (hμ : 0 < μ) (hy_neg : y < 0)
    (hay_sign : q.eval a * p.eval y < 0)
    (hyb_sign : p.eval y * q.eval b < 0) :
    ∃ c₁ c₂ : ℝ,
      a < c₁ ∧ c₁ < y ∧ y < c₂ ∧ c₂ < b ∧
        (X * p - C μ * q).IsRoot c₁ ∧ (X * p - C μ * q).IsRoot c₂ := by
  have hμ_neg : -μ < 0 := by linarith
  have hfactor : 0 < -μ * y := mul_pos_of_neg_of_neg hμ_neg hy_neg
  have hleft_sign :
      (X * p - C μ * q).eval a * (X * p - C μ * q).eval y < 0 := by
    rw [eval_X_mul_sub_C_mul_of_left_isRoot ha,
      eval_X_mul_sub_C_mul_of_right_isRoot hy]
    nlinarith
  have hright_sign :
      (X * p - C μ * q).eval y * (X * p - C μ * q).eval b < 0 := by
    rw [eval_X_mul_sub_C_mul_of_right_isRoot hy,
      eval_X_mul_sub_C_mul_of_left_isRoot hb]
    nlinarith
  obtain ⟨c₁, hac₁, hc₁y, hc₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hay hleft_sign
  obtain ⟨c₂, hyc₂, hc₂b, hc₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hyb hright_sign
  exact ⟨c₁, c₂, hac₁, hc₁y, hyc₂, hc₂b, hc₁_root, hc₂_root⟩

/-- If the right polynomial `q` has an even number of roots in `(a, b)`, counted
with multiplicity, then its values at `a` and `b` have the same sign when `b` is
not a root of `q`.  Hence one sign comparison between `q.eval a` and `p.eval y`
gives the two sign changes needed for one x-subtraction root on each side of the
right-polynomial root `y`. -/
lemma exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots_left_sign
    {p q : ℝ[X]} (hq_ne : q ≠ 0) (hq : q.Splits) {a b y μ : ℝ}
    (hay : a < y) (hyb : y < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hy : q.IsRoot y)
    (hμ : 0 < μ) (hy_neg : y < 0)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card)
    (hqb : ¬ q.IsRoot b) (hay_sign : q.eval a * p.eval y < 0) :
    ∃ c₁ c₂ : ℝ,
      a < c₁ ∧ c₁ < y ∧ y < c₂ ∧ c₂ < b ∧
        (X * p - C μ * q).IsRoot c₁ ∧ (X * p - C μ * q).IsRoot c₂ := by
  have hab : a ≤ b := le_of_lt (lt_trans hay hyb)
  have hqa : ¬ q.IsRoot a := by
    intro hroot
    have hzero : q.eval a = 0 := by simpa [Polynomial.IsRoot.def] using hroot
    rw [hzero, zero_mul] at hay_sign
    linarith
  have hqab_pos : 0 < q.eval a * q.eval b :=
    eval_mul_eval_pos_of_even_card_roots_filter_Ioo
      hq_ne hq hab heven hqa hqb
  have hright_sign : p.eval y * q.eval b < 0 :=
    mul_neg_of_mul_neg_of_mul_pos_left hay_sign hqab_pos
  exact
    exists_two_isRoot_between_X_mul_sub_C_mul_of_left_roots_right_root_signs
      hay hyb ha hb hy hμ hy_neg hay_sign hright_sign

end LiuOppositeSigns
end RealRooted
