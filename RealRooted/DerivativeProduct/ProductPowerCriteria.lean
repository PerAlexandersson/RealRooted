module

public import RealRooted.DerivativeProduct.ProductPower
public import RealRooted.RootLocation.Basic
import RealRooted.DerivativeProduct.ProductPowerRoots
import RealRooted.DerivativeProduct.KernelSufficiency
import Mathlib.Tactic

/-!
# Tests for real-rootedness of product powers

Let `⋆ = assocProduct a w` be an associative derivative product with `a > 0`, a quadratic weight
`w` and `A = w.coeff 2 ≥ 0`, and let `W = {r | w r ≤ 0}`.

* **Self-product lemma.**  For `q ≠ 0` we have `(q ⋆ q)(x) > 0` whenever `w x > 0`, since
  `(q ⋆ q)(x) = ∑ k, c k * w x ^ k * (q ^ (k) x) ^ 2` has nonnegative summands and a positive
  top summand.  Hence if `q ⋆ q` is real-rooted, all its roots lie in `W`
  (`isRealRootedIn_of_splits_assocProduct_self`).
* **Two-test criterion** (`assocProduct_self_splits_iff`,
  `forall_isRealRootedIn_derivProductPow_iff`):
  the second iterate `L_q ^ 2` of left multiplication preserves real-rootedness if and only if
  `q ⋆ q` is real-rooted, and every product power `q^{⋆n}` is real-rooted if and only if both
  `q` and `q ⋆ q` are.
* **Singleton sources** (`forall_isRealRootedIn_derivProductPowMap_singleton_iff`): the sequence map
  `S_g` sends every polynomial rooted in `{r}` to a real-rooted polynomial if and only if `g - r`
  and `(g - r) ⋆ (g - r)` are real-rooted.
* **Weights with `W = ℝ`**: then a source set `J` is mapped to real-rooted polynomials if and only
  if every level `g - r`, `r ∈ J`, is real-rooted.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

variable {a : ℝ} {w : ℝ[X]} {q : ℝ[X]}

theorem assocCoeff_pos {A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (k : ℕ) : 0 < assocCoeff a A k := by
  unfold assocCoeff
  positivity

/-- The top derivative of a nonzero polynomial does not vanish anywhere. -/
private theorem eval_iterate_derivative_natDegree_ne_zero (hq : q ≠ 0) (x : ℝ) :
    ((derivative^[q.natDegree]) q).eval x ≠ 0 := by
  have h0 : ((derivative^[q.natDegree]) q).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative q q.natDegree
    lia
  rw [eq_C_of_natDegree_le_zero h0, eval_C, coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (leadingCoeff_ne_zero.mpr hq)

/-- **Self-product lemma.**  For `q ≠ 0`, the product `q ⋆ q` is positive wherever the weight
is positive. -/
theorem eval_assocProduct_self_pos (ha : 0 < a) (hA : 0 ≤ w.coeff 2) (hq : q ≠ 0) {x : ℝ}
    (hx : 0 < w.eval x) : 0 < (assocProduct a w q q).eval x := by
  unfold assocProduct derivProduct
  rw [eval_finsetSum]
  refine Finset.sum_pos' (fun k _ ↦ ?_)
    ⟨q.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  · simp only [eval_mul, eval_C, eval_pow]
    rw [mul_assoc _ (eval x (derivative^[k] q)) (eval x (derivative^[k] q))]
    exact mul_nonneg (mul_nonneg (assocCoeff_pos ha hA k).le (pow_pos hx k).le)
      (mul_self_nonneg _)
  · simp only [eval_mul, eval_C, eval_pow]
    rw [mul_assoc _ (eval x (derivative^[q.natDegree] q)) (eval x (derivative^[q.natDegree] q))]
    exact mul_pos (mul_pos (assocCoeff_pos ha hA _) (pow_pos hx _))
      (mul_self_pos.mpr (eval_iterate_derivative_natDegree_ne_zero hq x))

/-- If `q ⋆ q` is real-rooted, then all its roots lie in `W = {r | w r ≤ 0}`. -/
theorem isRealRootedIn_of_splits_assocProduct_self (ha : 0 < a) (hw : w.natDegree ≤ 2)
    (hA : 0 ≤ w.coeff 2) (hq : q ≠ 0) (hs : (assocProduct a w q q).Splits) :
    IsRealRootedIn {r | w.eval r ≤ 0} (assocProduct a w q q) := by
  refine ⟨derivProduct_ne_zero hw hA (assocCoeff_zero _ _) (assocCoeff_nonneg ha.le hA) hq hq,
    hs, fun r hr ↦ ?_⟩
  have hne := derivProduct_ne_zero hw hA (assocCoeff_zero _ _) (assocCoeff_nonneg ha.le hA) hq hq
  have hroot := (mem_roots hne).1 hr
  by_contra hrW
  have := eval_assocProduct_self_pos ha hA hq (x := r) (lt_of_not_ge hrW)
  rw [IsRoot.def] at hroot
  exact this.ne' hroot

/-- **Two-test criterion, first form.**  For `q ≠ 0`, the second iterate of left multiplication
by `q` preserves real-rooted polynomials if and only if `q ⋆ q` is real-rooted. -/
theorem assocProduct_self_splits_iff (ha : 0 < a) (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2)
    (hq : q ≠ 0) :
    (assocProduct a w q q).Splits ↔ ∀ p : ℝ[X], IsRealRootedIn univ p →
      IsRealRootedIn univ (assocProduct a w q (assocProduct a w q p)) := by
  constructor
  · intro hs p hp
    rw [← assocProduct_assoc ha.le hw hA]
    exact assocProduct_isRealRootedIn_univ ha hw hA
      (isRealRootedIn_of_splits_assocProduct_self ha hw hA hq hs) hp
  · intro h
    have h1 : assocProduct a w q 1 = q :=
      derivProduct_one_right_of_zero_eq_one (assocCoeff_zero _ _) q
    simpa only [h1] using (h 1 IsRealRootedIn.one).splits

/-! ### All product powers -/

private theorem assocProduct_assoc' (ha : 0 < a) (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2)
    (f g h : ℝ[X]) :
    derivProduct w (assocCoeff a (w.coeff 2)) (derivProduct w (assocCoeff a (w.coeff 2)) f g) h =
      derivProduct w (assocCoeff a (w.coeff 2)) f
        (derivProduct w (assocCoeff a (w.coeff 2)) g h) :=
  assocProduct_assoc ha.le hw hA f g h

/-- The even product powers are the product powers of the square `q ⋆ q`. -/
private theorem derivProductPow_two_mul (ha : 0 < a) (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2)
    (m : ℕ) : derivProductPow w (assocCoeff a (w.coeff 2)) q (2 * m) =
      derivProductPow w (assocCoeff a (w.coeff 2)) (assocProduct a w q q) m := by
  have hc0 := assocCoeff_zero a (w.coeff 2)
  have hassoc := assocProduct_assoc' ha hw hA
  have h2 : derivProductPow w (assocCoeff a (w.coeff 2)) q 2 = assocProduct a w q q := by
    rw [derivProductPow_succ, derivProductPow_succ, derivProductPow_zero,
      derivProduct_one_right_of_zero_eq_one hc0]
    rfl
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 + 2 * m by ring, derivProductPow_add hc0 hassoc, ih, h2,
      derivProductPow_succ]

/-- **Two-test criterion for product powers.**  For `q ≠ 0`, every product power `q^{⋆n}` is
real-rooted if and only if both `q` and `q ⋆ q` are real-rooted. -/
theorem forall_isRealRootedIn_derivProductPow_iff (ha : 0 < a) (hw : w.natDegree ≤ 2)
    (hA : 0 ≤ w.coeff 2) (hq : q ≠ 0) :
    (∀ n : ℕ, IsRealRootedIn univ (derivProductPow w (assocCoeff a (w.coeff 2)) q n)) ↔
      q.Splits ∧ (assocProduct a w q q).Splits := by
  have hc0 := assocCoeff_zero a (w.coeff 2)
  have hassoc := assocProduct_assoc' ha hw hA
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [derivProductPow_one hc0] using (h 1).splits
    · have h2 := (h 2).splits
      rw [derivProductPow_succ, derivProductPow_succ, derivProductPow_zero,
        derivProduct_one_right_of_zero_eq_one hc0] at h2
      exact h2
  · rintro ⟨hqs, hQs⟩ n
    have hQW := isRealRootedIn_of_splits_assocProduct_self ha hw hA hq hQs
    have hL : ∀ (m : ℕ) (p : ℝ[X]), IsRealRootedIn univ p → IsRealRootedIn univ
        (((derivProductLinearMap w (assocCoeff a (w.coeff 2))
          (assocProduct a w q q)) ^ m) p) := by
      intro m
      induction m with
      | zero => exact fun p hp ↦ by simpa using hp
      | succ m ih =>
        intro p hp
        rw [pow_succ', Module.End.mul_apply, derivProductLinearMap_apply]
        exact assocProduct_isRealRootedIn_univ ha hw hA hQW (ih p hp)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [derivProductPow_two_mul ha hw hA]
      exact hL m 1 IsRealRootedIn.one
    · rw [derivProductPow_add hc0 hassoc, derivProductPow_one hc0,
        derivProductPow_two_mul ha hw hA,
        ← iterate_derivProductLinearMap_apply hc0 hassoc]
      exact hL m q ⟨hq, hqs, fun _ _ ↦ trivial⟩

/-! ### Source sets -/

/-- **Singleton sources.**  The sequence map `S_g` sends every polynomial rooted in `{r}` to a
real-rooted polynomial if and only if the level `g - r` and its self-product
`(g - r) ⋆ (g - r)` are real-rooted. -/
theorem forall_isRealRootedIn_derivProductPowMap_singleton_iff (ha : 0 < a)
    (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) {g : ℝ[X]} {r : ℝ} (hgr : g - C r ≠ 0) :
    (∀ p : ℝ[X], IsRealRootedIn {r} p →
      IsRealRootedIn univ (derivProductPowMap w (assocCoeff a (w.coeff 2)) g p)) ↔
      (g - C r).Splits ∧ (assocProduct a w (g - C r) (g - C r)).Splits := by
  have hc0 := assocCoeff_zero a (w.coeff 2)
  rw [← forall_isRealRootedIn_derivProductPow_iff ha hw hA hgr]
  constructor
  · intro h n
    have := h _ ((IsRealRootedIn.X_sub_C (mem_singleton r)).pow n)
    rwa [derivProductPowMap_X_sub_C_pow hc0] at this
  · intro h p hp
    obtain ⟨b, hb, n, rfl⟩ := exists_eq_C_mul_X_sub_C_pow_of_isRealRootedIn_singleton hp
    rw [← smul_eq_C_mul, map_smul, derivProductPowMap_X_sub_C_pow hc0, smul_eq_C_mul]
    exact (h n).C_mul hb

/-- **Weights with `W = ℝ`.**  If the weight is nonpositive everywhere, then `S_g` sends the
polynomials rooted in `J` to real-rooted polynomials if and only if every level `g - r`, `r ∈ J`,
is real-rooted. -/
theorem derivProductPowMap_realRooted_iff_of_nonpos (ha : 0 < a)
    (hw : w.natDegree ≤ 2) (hA : 0 ≤ w.coeff 2) (hW : ∀ x : ℝ, w.eval x ≤ 0) {J : Set ℝ}
    {g : ℝ[X]} :
    (∀ p : ℝ[X], IsRealRootedIn J p →
      IsRealRootedIn univ (derivProductPowMap w (assocCoeff a (w.coeff 2)) g p)) ↔
      ∀ r ∈ J, IsRealRootedIn univ (g - C r) :=
  forall_isRealRootedIn_derivProductPowMap_iff (assocCoeff_zero a (w.coeff 2))
    fun _ _ hf hq ↦ assocProduct_isRealRootedIn_univ ha hw hA (hf.mono fun x _ ↦ hW x) hq

end RealRooted
