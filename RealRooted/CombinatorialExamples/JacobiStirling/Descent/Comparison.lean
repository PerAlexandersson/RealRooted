import RealRooted.CombinatorialExamples.JacobiStirling.Descent.Basic
import RealRooted.MaWang.Strong
import RealRooted.Wronskian.Forward

/-!
# Comparison lemma for Jacobi–Stirling insertions

Ma–Wang (arXiv:2610.03111), Lemma 3: insertions preserve strict interleaving.  Write `f ≺ g`
(`StrictInterleave f g`) for `StrictInterl f g` together with the absence of common roots.

* `StrictInterleave.insertion_succ`: if `f ≺ g`, `deg g = deg f + 1` and `deg f < L`, then
  `D_L f ≺ D_{L+1} g`.
* `StrictInterleave.insertion_same`: if moreover `deg g < L`, then `D_L f ≺ D_L g`.

Instead of the partial-fraction expansion of `f / g` used in the paper, the proof uses the
Wronskian of the pair.  The polynomial identity
`g · D_L f - f · D_{L+1} g = -x · W(g, (x - 1) f)` and the positivity of `W(g, (x - 1) f)`,
checked at the roots of `g`, give the sign of `D_{L+1} g` at every root of `D_L f`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace JacobiStirlingDescent

/-- Strict interleaving `f ≺ g`: `StrictInterl f g` with no common real root. -/
def StrictInterleave (f g : ℝ[X]) : Prop :=
  StrictInterl f g ∧ ∀ r, f.IsRoot r → ¬ g.IsRoot r

/-- The Wronskian `g' f - g f'` of a strictly interleaving pair `f ≺ g` with
`deg g = deg f + 1` is positive. -/
theorem StrictInterleave.wronskian_pos {f g : ℝ[X]} {d : ℕ} (hfg : StrictInterleave f g)
    (hf : IsGood f d) (hg : IsGood g (d + 1)) (t : ℝ) :
    0 < g.derivative.eval t * f.eval t - g.eval t * f.derivative.eval t :=
  wronskian_pos_of_strictInterl_succ hg.pos hf.pos (by rw [hg.natDegree_eq, hf.natDegree_eq])
    hfg.1 hg.simple.roots_nodup hf.simple.roots_nodup (fun x hgx hfx => hfg.2 x hfx hgx) t

/-- From the sign of `F` at the roots of `D_L f`, conclude `D_L f ≺ F`. -/
private theorem strictInterleave_of_sign {f F : ℝ[X]} {d L : ℕ} (hf : IsGood f d)
    (hF : IsGood F (d + 2)) (hL : d < L)
    (hsign : ∀ p, (insertion L f).IsRoot p → F.eval p * f.eval p < 0) :
    StrictInterleave (insertion L f) F := by
  obtain ⟨h1, hstr, -⟩ := hf.insertion_and_strictInterl hL
  refine ⟨strictInterl_of_interlaces_eval_mul_neg_succ
    (hstr.toInterlaces (by rw [hf.natDegree_eq, h1.natDegree_eq])) hf.pos hF.pos
    (by rw [hF.natDegree_eq, h1.natDegree_eq]) hsign, fun p hp hFp => ?_⟩
  have := hsign p hp
  rw [hFp.eq_zero, zero_mul] at this
  exact lt_irrefl _ this

/-- **Ma–Wang, Lemma 2**, in interleaving form: `f ≺ D_L f` when `deg f < L`. -/
theorem IsGood.strictInterleave_insertion {f : ℝ[X]} {d L : ℕ} (hf : IsGood f d) (hL : d < L) :
    StrictInterleave f (insertion L f) :=
  ⟨(hf.insertion_and_strictInterl hL).2.1, (hf.insertion_and_strictInterl hL).2.2⟩

/-- **Ma–Wang, Lemma 3 (first part).**  If `f ≺ g` with `deg g = deg f + 1` and `deg f < L`,
then `D_L f ≺ D_{L+1} g`. -/
theorem StrictInterleave.insertion_succ {f g : ℝ[X]} {d L : ℕ} (hfg : StrictInterleave f g)
    (hf : IsGood f d) (hg : IsGood g (d + 1)) (hL : d < L) :
    StrictInterleave (insertion L f) (insertion (L + 1) g) := by
  have hW := hfg.wronskian_pos hf hg
  -- `Ψ = ((X - 1) f)' g - ((X - 1) f) g'` is positive on `ℝ`.
  have hΨ : ∀ t, 0 < ((X - 1) * f).derivative.eval t * g.eval t -
      ((X - 1) * f).eval t * g.derivative.eval t := by
    refine wronskian_pos_of_pos_at_roots hg.splits hg.natDegree_eq ?_ fun r hr => ?_
    · refine (natDegree_mul_le).trans ?_
      rw [hf.natDegree_eq]
      have : (X - 1 : ℝ[X]).natDegree ≤ 1 := by compute_degree
      lia
    · have hWr := hW r
      have hr0 := hg.isRoot_neg hr
      rw [hr.eq_zero] at hWr ⊢
      simp only [eval_mul, eval_sub, eval_X, eval_one, mul_zero, zero_sub, zero_mul] at hWr ⊢
      nlinarith
  refine strictInterleave_of_sign hf (hg.insertion_and_strictInterl (by lia)).1 hL
    fun p hp => ?_
  have hp0 : p < 0 := ((hf.insertion_and_strictInterl hL).1).isRoot_neg hp
  have hid : g.eval p * (insertion L f).eval p - f.eval p * (insertion (L + 1) g).eval p =
      -p * (((X - 1) * f).derivative.eval p * g.eval p -
        ((X - 1) * f).eval p * g.derivative.eval p) := by
    simp only [insertion_eq, derivative_mul, derivative_sub, derivative_X, derivative_one,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one, eval_zero, Nat.cast_add, Nat.cast_one]
    ring
  rw [hp.eq_zero, mul_zero, zero_sub] at hid
  have := hΨ p
  nlinarith

/-- **Ma–Wang, Lemma 3 (second part).**  If `f ≺ g` with `deg g = deg f + 1` and `deg g < L`,
then `D_L f ≺ D_L g`. -/
theorem StrictInterleave.insertion_same {f g : ℝ[X]} {d L : ℕ} (hfg : StrictInterleave f g)
    (hf : IsGood f d) (hg : IsGood g (d + 1)) (hL : d + 1 < L) :
    StrictInterleave (insertion L f) (insertion L g) := by
  have hW := hfg.wronskian_pos hf hg
  refine strictInterleave_of_sign hf (hg.insertion_and_strictInterl hL).1 (by lia)
    fun p hp => ?_
  have hp0 : p < 0 := ((hf.insertion_and_strictInterl (by lia)).1).isRoot_neg hp
  have hid : g.eval p * (insertion L f).eval p - f.eval p * (insertion L g).eval p =
      p * (1 - p) * -(g.derivative.eval p * f.eval p - g.eval p * f.derivative.eval p) := by
    simp only [insertion_eq, eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_one]
    ring
  rw [hp.eq_zero, mul_zero, zero_sub] at hid
  have := hW p
  have h1p : 0 < 1 - p := by linarith
  nlinarith [mul_pos (neg_pos.mpr hp0) h1p]

end JacobiStirlingDescent
end RealRooted
