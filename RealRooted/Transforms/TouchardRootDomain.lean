module

public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.PFPolynomial
public import RealRooted.RootLocation.Basic
public import RealRooted.Touchard
import RealRooted.Transforms.StirlingRootRegions
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
import RealRooted.CombinatorialExamples.Touchard
import RealRooted.Derivative.Algebra
import RealRooted.QuadraticRoot
import RealRooted.RootLocation.DerivativeSigns
import RealRooted.RootLocation.Pairing
import Mathlib.Tactic

/-!
# Sharp root domains for the Touchard transform

Let `T = basisTransform touchard` be the Touchard transform, `T (t falling n) = x ^ n`, which
turns ordinary multiplication into the Poisson product `⋆₁`.  We prove that `T` sends every
nonzero polynomial rooted in `J` to a real-rooted polynomial if and only if `J ⊆ (-∞, 1/4]`
(`forall_splits_basisTransform_touchard_iff`), and that the invariant upper rays of `T` are exactly
`(-∞, c]` with `0 ≤ c ≤ 1/4` (`forall_isRealRootedIn_Iic_basisTransform_touchard_iff`).

The proof pairs the positive roots.  For `0 ≤ r, s ≤ 1/4` the image of `(X - r) (X - s)` is
`X ^ 2 + (1 - r - s) X + r s`, which is PF; the images of the factors `X - r`, `r ≤ 0`, are PF as
well.  All these factors are combined first, at most one positive factor `X - r` remains, and
fixed Poisson multiplication by a PF polynomial preserves real-rootedness (Brändén, *On linear
transformations preserving the Pólya frequency property*, Theorem 3.11).  Necessity uses
`T ((X - r) ^ 2) = X ^ 2 + (1 - 2 r) X + r ^ 2`, whose discriminant is `1 - 4 r`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The Touchard transform of `X - r` is `X - r`. -/
theorem basisTransform_touchard_X_sub_C (r : ℝ) :
    basisTransform touchard (X - C r) = X - C r := by
  simpa [sub_eq_add_neg] using basisTransform_touchard_X_add_C (-r)

private theorem basisTransform_touchard_one : basisTransform touchard 1 = 1 := by
  simpa using basisTransform_C touchard 1

/-- The Touchard transform is linear over constants. -/
theorem basisTransform_touchard_C_mul (a : ℝ) (p : ℝ[X]) :
    basisTransform touchard (C a * p) = C a * basisTransform touchard p := by
  rw [C_mul', basisTransform_smul, C_mul']

/-- The Touchard transform of a product of two linear factors. -/
theorem basisTransform_touchard_X_sub_C_mul_X_sub_C (r s : ℝ) :
    basisTransform touchard ((X - C r) * (X - C s)) =
      X ^ 2 + C (1 - r - s) * X + C (r * s) := by
  rw [mul_comm, show X - C s = X + C (-s) by simp [sub_eq_add_neg],
    basisTransform_touchard_mul_X_add_C, basisTransform_touchard_X_sub_C]
  simp only [derivative_X, derivative_C, sub_zero, mul_one, map_sub, map_mul, map_neg, map_one]
  ring

/-- For `0 ≤ r, s ≤ 1 / 4` the Touchard transform of `(X - r) (X - s)` is PF. -/
theorem isPFPolynomial_basisTransform_touchard_X_sub_C_mul_X_sub_C {r s : ℝ} (hr0 : 0 ≤ r)
    (hs0 : 0 ≤ s) (hr : r ≤ 1 / 4) (hs : s ≤ 1 / 4) :
    IsPFPolynomial (basisTransform touchard ((X - C r) * (X - C s))) := by
  rw [basisTransform_touchard_X_sub_C_mul_X_sub_C]
  refine IsPFPolynomial.of_realRooted_nonneg
    (((hasNonnegCoeffs_X.pow 2).add (hasNonnegCoeffs_C_mul (by linarith) hasNonnegCoeffs_X)).add
      (hasNonnegCoeffs_C (mul_nonneg hr0 hs0))) ?_
  rw [monicQuadraticPoly_splits_iff_discrim_nonneg]
  nlinarith [sq_nonneg (r - s)]

/-- **Pairing for the Touchard transform.**  A polynomial rooted in `(-∞, 1/4]` is a nonzero
constant times `F * R`, where the Touchard transform of `F ≠ 0` is PF and `R` is either `1` or
a factor `X - r` for a positive root `r` of the polynomial. -/
theorem exists_eq_C_mul_mul_of_isRealRootedIn_Iic_quarter {p : ℝ[X]}
    (hp : IsRealRootedIn (Iic (1 / 4)) p) :
    ∃ (a : ℝ) (F R : ℝ[X]), a ≠ 0 ∧ p = C a * (F * R) ∧ F ≠ 0 ∧
      IsPFPolynomial (basisTransform touchard F) ∧
      (R = 1 ∨ ∃ r ∈ p.roots, 0 < r ∧ R = X - C r) := by
  classical
  have hT1 := basisTransform_touchard_one
  have hmul : ∀ f ∈ {q : ℝ[X] | IsPFPolynomial (basisTransform touchard q)},
      ∀ g ∈ {q : ℝ[X] | IsPFPolynomial (basisTransform touchard q)},
        f * g ∈ {q : ℝ[X] | IsPFPolynomial (basisTransform touchard q)} :=
    fun f hf g hg ↦ isPFPolynomial_basisTransform_touchard_mul hf hg
  -- the nonpositive roots
  have hneg : IsPFPolynomial (basisTransform touchard
      (rootPolynomial (p.roots.filter (· ≤ 0)))) :=
    rootPolynomial_mem_of_forall_X_sub_C_mem (K := {q : ℝ[X] | IsPFPolynomial
      (basisTransform touchard q)}) (by simpa [hT1] using IsPFPolynomial.one) hmul
      fun r hr ↦ by
        change IsPFPolynomial (basisTransform touchard (X - C r))
        rw [basisTransform_touchard_X_sub_C]
        exact IsPFPolynomial.of_realRooted_nonneg
          (hasNonnegCoeffs_X_sub_C (Multiset.mem_filter.mp hr).2) (Splits.X_sub_C r)
  have hmem : ∀ r ∈ p.roots.filter (fun r ↦ ¬ r ≤ 0), r ∈ Ioc (0 : ℝ) (1 / 4) := by
    intro r hr
    rw [Multiset.mem_filter] at hr
    exact ⟨not_le.mp hr.2, hp.mem_of_mem_roots hr.1⟩
  obtain ⟨F₂, R, hFR, hF₂, hR⟩ := exists_rootPolynomial_eq_mul_of_pairs
    (K := {q : ℝ[X] | IsPFPolynomial (basisTransform touchard q)}) (S := Ioc 0 (1 / 4))
    (by simpa [hT1] using IsPFPolynomial.one) hmul
    (fun r hr s hs ↦ isPFPolynomial_basisTransform_touchard_X_sub_C_mul_X_sub_C hr.1.le hs.1.le
      hr.2 hs.2) _ hmem
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  have hF₂0 : F₂ ≠ 0 := left_ne_zero_of_mul (hFR ▸ rootPolynomial_ne_zero _)
  refine ⟨p.leadingCoeff, rootPolynomial (p.roots.filter (· ≤ 0)) * F₂, R, hlc, ?_,
    mul_ne_zero (rootPolynomial_ne_zero _) hF₂0,
    hmul _ hneg _ hF₂, ?_⟩
  · conv_lhs => rw [hp.eq_C_mul_rootPolynomial, ← Multiset.filter_add_not (· ≤ 0) p.roots,
      rootPolynomial_add, hFR]
    ring
  · rcases hR with h | ⟨r, hr, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, (Multiset.mem_filter.mp hr).1, not_le.mp (Multiset.mem_filter.mp hr).2, h⟩

/-- **Touchard transform on `(-∞, 1/4]`.**  The Touchard transform sends every polynomial rooted
in `(-∞, 1/4]` to a nonzero real-rooted polynomial. -/
theorem IsRealRootedIn.basisTransform_touchard {p : ℝ[X]} (hp : IsRealRootedIn (Iic (1 / 4)) p) :
    IsRealRootedIn univ (basisTransform touchard p) := by
  obtain ⟨a, F, R, ha, rfl, hF0, hFPF, hR⟩ := exists_eq_C_mul_mul_of_isRealRootedIn_Iic_quarter hp
  have hne := basisTransform_ne_zero natDegree_touchard touchard_ne_zero hp.ne_zero
  refine IsRealRootedIn.univ_iff.mpr ⟨hne, ?_⟩
  rw [basisTransform_touchard_C_mul]
  refine Splits.C_mul ?_ a
  have hTF0 := basisTransform_ne_zero natDegree_touchard touchard_ne_zero hF0
  rcases hR with rfl | ⟨r, -, -, rfl⟩
  · rw [mul_one]
    exact (hFPF.ne_zero_and_splits hTF0).2
  · rw [basisTransform_touchard_mul, basisTransform_touchard_X_sub_C]
    have hadm := Poisson.IsPFPolynomial.isAdmissible zero_le_one hFPF hTF0
    have hne' : Poisson.starC 1 (basisTransform touchard F) (X - C r) ≠ 0 := by
      rw [← basisTransform_touchard_X_sub_C r, ← basisTransform_touchard_mul]
      exact basisTransform_ne_zero natDegree_touchard touchard_ne_zero
        (mul_ne_zero hF0 (X_sub_C_ne_zero r))
    exact (hadm.preservesRealRootedOrZero (X - C r)
      ⟨X_sub_C_ne_zero r, Splits.X_sub_C r⟩).resolve_left hne'

/-- The Touchard transform of `(X - r) ^ 2` does not split when `r > 1 / 4`: its discriminant is
`1 - 4 r`. -/
theorem not_splits_basisTransform_touchard_X_sub_C_sq {r : ℝ} (hr : 1 / 4 < r) :
    ¬ (basisTransform touchard ((X - C r) ^ 2)).Splits := by
  rw [sq, basisTransform_touchard_X_sub_C_mul_X_sub_C,
    monicQuadraticPoly_not_splits_iff_discrim_neg]
  nlinarith

/-- **Sharp source domain of the Touchard transform.**  For a set `J` of reals, the Touchard
transform sends every nonzero polynomial rooted in `J` to a real-rooted polynomial if and only if
`J ⊆ (-∞, 1/4]`.  Singletons and the empty set are included. -/
theorem forall_splits_basisTransform_touchard_iff (J : Set ℝ) :
    (∀ p : ℝ[X], IsRealRootedIn J p → (basisTransform touchard p).Splits) ↔ J ⊆ Iic (1 / 4) := by
  refine ⟨fun h r hr ↦ ?_, fun h p hp ↦ (hp.mono h).basisTransform_touchard.splits⟩
  by_contra hr'
  exact not_splits_basisTransform_touchard_X_sub_C_sq (not_le.mp hr')
    (h _ ((IsRealRootedIn.X_sub_C hr).pow 2))

/-- The Poisson product of a nonzero PF polynomial with `X - r` has no root to the right of the
positive number `r`. -/
private theorem eval_starC_one_X_sub_C_pos {G : ℝ[X]} (hG : IsPFPolynomial G) (hG0 : G ≠ 0)
    {r x : ℝ} (hr : 0 < r) (hx : r < x) : 0 < (Poisson.starC 1 G (X - C r)).eval x := by
  rw [Poisson.starC_comm, show X - C r = C (-r) + C 1 * X by simp [sub_eq_add_neg, add_comm],
    Poisson.starC_affine_left]
  have hx0 : 0 < x := hr.trans hx
  have h1 := eval_pos_of_hasNonnegCoeffs hG.hasNonnegCoeffs hG0 hx0
  have h2 := hG.hasNonnegCoeffs.derivative.eval_nonneg hx0.le
  simp only [eval_add, eval_mul, eval_C, eval_X]
  nlinarith [mul_pos (sub_pos.2 hx) h1, mul_nonneg hx0.le h2]

/-- **Invariant upper rays of the Touchard transform.**  For `0 ≤ c ≤ 1/4` the Touchard transform
sends polynomials rooted in `(-∞, c]` to polynomials rooted in `(-∞, c]`. -/
theorem IsRealRootedIn.basisTransform_touchard_Iic {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 4)
    {p : ℝ[X]} (hp : IsRealRootedIn (Iic c) p) :
    IsRealRootedIn (Iic c) (basisTransform touchard p) := by
  have hp' : IsRealRootedIn (Iic (1 / 4)) p := hp.mono fun x hx ↦ le_trans hx hc
  have huniv := hp'.basisTransform_touchard
  refine ⟨huniv.ne_zero, huniv.splits, fun x hx ↦ ?_⟩
  have hroot := (mem_roots huniv.ne_zero).1 hx
  obtain ⟨a, F, R, ha, hpeq, hF0, hFPF, hR⟩ := exists_eq_C_mul_mul_of_isRealRootedIn_Iic_quarter hp'
  have hTF0 := basisTransform_ne_zero natDegree_touchard touchard_ne_zero hF0
  have hTp : basisTransform touchard p =
      C a * basisTransform touchard (F * R) := by
    rw [hpeq, basisTransform_touchard_C_mul]
  rw [IsRoot.def, hTp, eval_mul, eval_C, mul_eq_zero] at hroot
  have hroot' := hroot.resolve_left ha
  rcases hR with rfl | ⟨r, hr, hr0, rfl⟩
  · rw [mul_one] at hroot'
    exact (hFPF.roots_nonpos x ((mem_roots hTF0).2 hroot')).trans hc0
  · rw [basisTransform_touchard_mul, basisTransform_touchard_X_sub_C] at hroot'
    by_contra hxc
    have hrc : r ≤ c := hp.mem_of_mem_roots hr
    exact (eval_starC_one_X_sub_C_pos hFPF hTF0 hr0 (lt_of_le_of_lt hrc (not_le.mp hxc))).ne' hroot'

/-- If the Touchard transform of `(X - c) ^ 2` is rooted in `(-∞, c]`, then `c ≥ 0`. -/
private theorem nonneg_of_isRealRootedIn_Iic_basisTransform_touchard_sq {c : ℝ}
    (h : IsRealRootedIn (Iic c) (basisTransform touchard ((X - C c) ^ 2))) : 0 ≤ c := by
  rw [sq, basisTransform_touchard_X_sub_C_mul_X_sub_C] at h
  have hmonic : (X ^ 2 + C (1 - c - c) * X + C (c * c) : ℝ[X]).Monic := by monicity!
  have := h.eval_nonneg_of_monic hmonic
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
  nlinarith

/-- **Invariant upper rays of the Touchard transform, sharp form.**  The Touchard transform sends
every polynomial rooted in `(-∞, c]` to a polynomial rooted in `(-∞, c]` if and only if
`0 ≤ c ≤ 1/4`. -/
theorem forall_isRealRootedIn_Iic_basisTransform_touchard_iff (c : ℝ) :
    (∀ p : ℝ[X], IsRealRootedIn (Iic c) p → IsRealRootedIn (Iic c) (basisTransform touchard p)) ↔
      0 ≤ c ∧ c ≤ 1 / 4 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h p hp ↦ hp.basisTransform_touchard_Iic h.1 h.2⟩
  · exact nonneg_of_isRealRootedIn_Iic_basisTransform_touchard_sq
      (h _ ((IsRealRootedIn.X_sub_C (mem_Iic.2 le_rfl)).pow 2))
  · exact (forall_splits_basisTransform_touchard_iff (Iic c)).1 (fun p hp ↦ (h p hp).splits)
      (mem_Iic.2 le_rfl)

/-- **Rows of a Touchard type recurrence.**  Let `P 0 = 1` and
`P (n + 1) = (X + a (n + 1)) * P n + X * (P n)'` with `a i ≥ -1 / 4` for all `i`.  Then every row
`P n` is rooted in `(-∞, 1/4]`.  (The row is the Touchard image of `∏ i ≤ n, (t + a i)`, whose
roots are `-a i ≤ 1/4`, and `(-∞, 1/4]` is invariant.) -/
theorem isRealRootedIn_Iic_quarter_of_touchard_recurrence {a : ℕ → ℝ} (ha : ∀ n, -(1 / 4) ≤ a n)
    {P : ℕ → ℝ[X]} (h0 : P 0 = 1)
    (hP : ∀ n, P (n + 1) = (X + C (a (n + 1))) * P n + X * derivative (P n)) (n : ℕ) :
    IsRealRootedIn (Iic (1 / 4)) (P n) := by
  have hT1 := basisTransform_touchard_one
  suffices h : ∀ n, ∃ q : ℝ[X], IsRealRootedIn (Iic (1 / 4)) q ∧
      P n = basisTransform touchard q by
    obtain ⟨q, hq, hPq⟩ := h n
    rw [hPq]
    exact hq.basisTransform_touchard_Iic (by norm_num) le_rfl
  intro n
  induction n with
  | zero => exact ⟨1, IsRealRootedIn.one, by rw [h0, hT1]⟩
  | succ n ih =>
    obtain ⟨q, hq, hPq⟩ := ih
    refine ⟨(X + C (a (n + 1))) * q, ?_, ?_⟩
    · rw [show (X + C (a (n + 1)) : ℝ[X]) = X - C (-a (n + 1)) by simp [sub_eq_add_neg]]
      exact (IsRealRootedIn.X_sub_C (mem_Iic.2 (by linarith [ha (n + 1)]))).mul hq
    · rw [hP, basisTransform_touchard_mul_X_add_C, hPq]

end RealRooted
