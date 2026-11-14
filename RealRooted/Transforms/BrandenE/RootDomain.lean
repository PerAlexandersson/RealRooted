module

public import RealRooted.RootLocation.Basic
public import RealRooted.Transforms.BrandenE.Basic
import RealRooted.DerivativeProduct.Diamond
import RealRooted.DerivativeProduct.DiamondIntervals
import RealRooted.QuadraticRoot
import RealRooted.RootLocation.DerivativeSigns
import RealRooted.RootLocation.Pairing
import Mathlib.Tactic

/-!
# Sharp root domains for Brändén's ordered Bell transform

Brändén's `E` transform sends `t ^ n` to the ordered Bell polynomial, `E (binomial t n) = x ^ n`,
and turns ordinary multiplication into the diamond product `⋄`.  Put
`L = -(1 + √2) / 2` and `U = (√2 - 1) / 2`.  We prove:

* `E` sends every nonzero polynomial rooted in `J` to a real-rooted polynomial if and only if
  `J ⊆ [L, U]` (`forall_splits_brandenE_iff`);
* the nonempty closed intervals `[A, B]` such that `E` sends polynomials rooted in `[A, B]` to
  polynomials rooted in `[A, B]` are exactly those with `L ≤ A ≤ -1` and `0 ≤ B ≤ U`
  (`forall_isRealRootedIn_Icc_brandenE_iff`).

The proof pairs the roots.  The images of the factors `X - r`, `r ∈ [-1, 0]`, are admissible
kernels for the diamond product (Brändén, Theorem 3.11), and so is the image
`2 X ^ 2 + (1 - r - s) X + r s` of `(X - r) (X - s)` for two roots `r, s ∈ (0, U]` or two roots
`r, s ∈ [L, -1)`.  After combining all admissible factors at most one positive and at most one
negative root remain, and their pair has a real-rooted image with roots between them.
Real-rootedness and the location of the product follow from
`RealRooted.betaProduct_one_isRealRootedIn_Icc`.  Necessity uses the discriminant
`1 - 4 r - 4 r ^ 2` of `E ((X - r) ^ 2)`.
-/

public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- The roots of the quadratic `4 r ^ 2 + 4 r - 1` are `L = -(1 + √2) / 2` and
`U = (√2 - 1) / 2`: `r ∈ [L, U]` iff `4 r ^ 2 + 4 r ≤ 1`. -/
theorem mem_Icc_neg_one_add_sqrt_two_iff {r : ℝ} :
    r ∈ Icc (-(1 + √2) / 2) ((√2 - 1) / 2) ↔ 4 * r ^ 2 + 4 * r ≤ 1 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  constructor
  · rintro ⟨h1, h3⟩
    nlinarith
  · intro h
    have habs : |2 * r + 1| ≤ √2 := Real.abs_le_sqrt (by nlinarith)
    rw [abs_le] at habs
    constructor <;> linarith [habs.1, habs.2]

private theorem brandenE_one_eq : brandenE (1 : ℝ[X]) = 1 := by
  simpa using brandenE_X_pow (R := ℝ) 0

/-- Brändén's `E` transform of a linear factor is the linear factor itself. -/
theorem brandenE_X_sub_C (r : ℝ) : brandenE (X - C r) = X - C r := by
  have h := brandenE_mul_X_add_C (-r) (1 : ℝ[X])
  rw [mul_one, brandenE_one_eq] at h
  rw [sub_eq_add_neg, ← C_neg, h]
  simp

/-- Brändén's `E` transform of a product of two linear factors. -/
theorem brandenE_X_sub_C_mul_X_sub_C (r s : ℝ) :
    brandenE ((X - C r) * (X - C s)) = C 2 * X ^ 2 + C (1 - r - s) * X + C (r * s) := by
  rw [mul_comm, show X - C s = X + C (-s) by simp [sub_eq_add_neg],
    brandenE_mul_X_add_C, brandenE_X_sub_C]
  simp only [derivative_X, derivative_C, sub_zero, mul_one, map_sub, map_mul, map_neg, map_one]
  rw [show (C 2 : ℝ[X]) = 2 from map_ofNat C 2]
  ring

/-! ### Roots of the pair images -/

private theorem natDegree_quadratic_two (b c : ℝ) :
    (C 2 * X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 :=
  natDegree_quadratic two_ne_zero

private theorem quadratic_two_ne_zero (b c : ℝ) : (C 2 * X ^ 2 + C b * X + C c : ℝ[X]) ≠ 0 :=
  ne_zero_of_natDegree_gt (n := 1) (by rw [natDegree_quadratic_two]; norm_num)

private theorem eval_quadratic_two (b c x : ℝ) :
    (C 2 * X ^ 2 + C b * X + C c : ℝ[X]).eval x = 2 * x ^ 2 + b * x + c := by
  simp

/-- A quadratic `2 X ^ 2 + b X + c` with `0 ≤ b ≤ 4`, `c ≥ 0`, nonnegative discriminant and
nonnegative value at `-1` is rooted in `[-1, 0]`. -/
private theorem isRealRootedIn_Icc_neg_one_zero_quadratic {b c : ℝ} (hb : 0 ≤ b) (hb4 : b ≤ 4)
    (hc : 0 ≤ c) (hd : 8 * c ≤ b ^ 2) (hk : b ≤ 2 + c) :
    IsRealRootedIn (Icc (-1) 0) (C 2 * X ^ 2 + C b * X + C c) := by
  refine ⟨quadratic_two_ne_zero b c, quadraticPoly_splits_of_le two_pos (by linarith), ?_⟩
  intro x hx
  have h0 : 2 * x ^ 2 + b * x + c = 0 := by
    have := (mem_roots (quadratic_two_ne_zero b c)).1 hx
    rwa [IsRoot.def, eval_quadratic_two] at this
  constructor
  · by_contra hx'
    have hx1 : x + 1 < 0 := by linarith [not_le.mp hx']
    nlinarith [mul_pos_of_neg_of_neg hx1 (show 2 * x - 2 + b < 0 by linarith [not_le.mp hx'])]
  · by_contra hx'
    nlinarith [not_le.mp hx']

/-- The numerical constraints on a root `r ∈ [L, U]` used below, from `4 r ^ 2 + 4 r ≤ 1`. -/
private theorem pair_disc {r s : ℝ} (hr : 4 * r ^ 2 + 4 * r ≤ 1) (hs : 4 * s ^ 2 + 4 * s ≤ 1) :
    8 * (r * s) ≤ (1 - r - s) ^ 2 := by
  nlinarith [sq_nonneg (r - s)]

/-- For two roots in `(0, U]`, the `E` image of the pair is rooted in `[-1, 0]`. -/
theorem isRealRootedIn_Icc_brandenE_X_sub_C_mul_X_sub_C_of_pos {r s : ℝ} (hr0 : 0 < r)
    (hs0 : 0 < s) (hr : 4 * r ^ 2 + 4 * r ≤ 1) (hs : 4 * s ^ 2 + 4 * s ≤ 1) :
    IsRealRootedIn (Icc (-1) 0) (brandenE ((X - C r) * (X - C s))) := by
  rw [brandenE_X_sub_C_mul_X_sub_C]
  refine isRealRootedIn_Icc_neg_one_zero_quadratic (by nlinarith) (by nlinarith)
    (by positivity) (pair_disc hr hs) (by nlinarith)

/-- For two roots in `[L, -1)`, the `E` image of the pair is rooted in `[-1, 0]`. -/
theorem BrandenE.isRealRootedIn_Icc_quadratic_of_lt_neg_one {r s : ℝ} (hr0 : r < -1)
    (hs0 : s < -1) (hr : 4 * r ^ 2 + 4 * r ≤ 1) (hs : 4 * s ^ 2 + 4 * s ≤ 1) :
    IsRealRootedIn (Icc (-1) 0) (brandenE ((X - C r) * (X - C s))) := by
  rw [brandenE_X_sub_C_mul_X_sub_C]
  have hr' : -5 / 4 ≤ r := by nlinarith
  have hs' : -5 / 4 ≤ s := by nlinarith
  have hrs : 0 < (r + 1) * (s + 1) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  refine isRealRootedIn_Icc_neg_one_zero_quadratic (by nlinarith) (by nlinarith)
    (by nlinarith) (pair_disc hr hs) (by nlinarith)

/-- For `r < -1 < 0 < s` in `[L, U]` the `E` image of `(X - r) (X - s)` is rooted in `[r, s]`;
its roots lie in `(r, -1)` and `(0, s)`. -/
theorem _root_.RealRooted.BrandenE.isRealRootedIn_Icc_quadratic_of_lt_neg_one_of_pos {r s : ℝ}
    (hr0 : r < -1) (hs0 : 0 < s) (hr : 4 * r ^ 2 + 4 * r ≤ 1) (hs : 4 * s ^ 2 + 4 * s ≤ 1) :
    IsRealRootedIn (Icc r s) (brandenE ((X - C r) * (X - C s))) := by
  rw [brandenE_X_sub_C_mul_X_sub_C]
  refine ⟨quadratic_two_ne_zero _ _, quadraticPoly_splits_of_le two_pos (by
    linarith [pair_disc hr hs]), ?_⟩
  intro x hx
  have h0 : 2 * x ^ 2 + (1 - r - s) * x + r * s = 0 := by
    have := (mem_roots (quadratic_two_ne_zero (1 - r - s) (r * s))).1 hx
    rwa [IsRoot.def, eval_quadratic_two] at this
  constructor
  · by_contra hx'
    have hx1 : x < r := not_le.mp hx'
    nlinarith [mul_pos_of_neg_of_neg (sub_neg.2 hx1)
      (show 2 * x + 2 * r + (1 - r - s) < 0 by linarith)]
  · by_contra hx'
    have hx1 : s < x := not_le.mp hx'
    nlinarith [mul_pos (sub_pos.2 hx1) (show 0 < 2 * x + 2 * s + (1 - r - s) by linarith)]

/-- If `E f` and `E g` are rooted in `[-1, 0]`, then so is `E (f * g)`. -/
theorem isRealRootedIn_Icc_brandenE_mul {f g : ℝ[X]}
    (hf : IsRealRootedIn (Icc (-1) 0) (brandenE f))
    (hg : IsRealRootedIn (Icc (-1) 0) (brandenE g)) :
    IsRealRootedIn (Icc (-1) 0) (brandenE (f * g)) := by
  rw [← betaProduct_one_brandenE]
  exact betaProduct_one_isRealRootedIn_Icc le_rfl le_rfl hf hg

/-! ### Pairing -/

/-- **Pairing for the `E` transform.**  A polynomial rooted in `[L, U]` is a nonzero constant
times `F * (Rp * Rn)`, where `E F` is rooted in `[-1, 0]`, `F ≠ 0`, and `Rp` and `Rn` are either
`1` or a linear factor `X - r` for a positive, respectively a `< -1`, root `r` of the
polynomial. -/
theorem exists_eq_C_mul_mul_of_isRealRootedIn_Icc {p : ℝ[X]}
    (hp : IsRealRootedIn (Icc (-(1 + √2) / 2) ((√2 - 1) / 2)) p) :
    ∃ (a : ℝ) (F Rp Rn : ℝ[X]), a ≠ 0 ∧ p = C a * (F * (Rp * Rn)) ∧ F ≠ 0 ∧
      IsRealRootedIn (Icc (-1) 0) (brandenE F) ∧
      (Rp = 1 ∨ ∃ r ∈ p.roots, 0 < r ∧ Rp = X - C r) ∧
      (Rn = 1 ∨ ∃ r ∈ p.roots, r < -1 ∧ Rn = X - C r) := by
  classical
  have hE1 := brandenE_one_eq
  set K : Set ℝ[X] := {q | IsRealRootedIn (Icc (-1) 0) (brandenE q)} with hK
  have h1 : (1 : ℝ[X]) ∈ K := by simpa [hK, hE1] using IsRealRootedIn.one
  have hmul : ∀ f ∈ K, ∀ g ∈ K, f * g ∈ K := fun f hf g hg ↦ isRealRootedIn_Icc_brandenE_mul hf hg
  have hroot : ∀ r ∈ p.roots, 4 * r ^ 2 + 4 * r ≤ 1 := fun r hr ↦
    mem_Icc_neg_one_add_sqrt_two_iff.1 (hp.mem_of_mem_roots hr)
  -- the roots in `[-1, 0]`
  have hmid : ∀ s : Multiset ℝ, (∀ r ∈ s, r ∈ Icc (-1 : ℝ) 0) → rootPolynomial s ∈ K :=
    fun s hs ↦ rootPolynomial_mem_of_forall_X_sub_C_mem h1 hmul fun r hr ↦ by
      simp only [hK, mem_ofPred_eq, brandenE_X_sub_C]
      exact IsRealRootedIn.X_sub_C (hs r hr)
  -- split the roots into `< -1`, `> 0` and the rest
  set mn := p.roots.filter (fun r ↦ r < -1) with hmn
  set mr := p.roots.filter (fun r ↦ ¬ r < -1) with hmr
  set mp := mr.filter (fun r ↦ 0 < r) with hmp
  set mm := mr.filter (fun r ↦ ¬ 0 < r) with hmm
  have hmn_mem : ∀ r ∈ mn, r ∈ Icc (-(1 + √2) / 2) (-1 : ℝ) := fun r hr ↦ by
    rw [hmn, Multiset.mem_filter] at hr
    refine ⟨(hp.mem_of_mem_roots hr.1).1, hr.2.le⟩
  have hmp_mem : ∀ r ∈ mp, 0 < r ∧ 4 * r ^ 2 + 4 * r ≤ 1 := fun r hr ↦ by
    rw [hmp, hmr, Multiset.mem_filter, Multiset.mem_filter] at hr
    exact ⟨hr.2, hroot r hr.1.1⟩
  have hmm_mem : ∀ r ∈ mm, r ∈ Icc (-1 : ℝ) 0 := fun r hr ↦ by
    rw [hmm, hmr, Multiset.mem_filter, Multiset.mem_filter] at hr
    exact ⟨not_lt.mp hr.1.2, not_lt.mp hr.2⟩
  obtain ⟨Fp, Rp, hFRp, hFp, hRp⟩ := exists_rootPolynomial_eq_mul_of_pairs (K := K)
    (S := {r | 0 < r ∧ 4 * r ^ 2 + 4 * r ≤ 1}) h1 hmul
    (fun r hr s hs ↦ isRealRootedIn_Icc_brandenE_X_sub_C_mul_X_sub_C_of_pos hr.1 hs.1 hr.2 hs.2)
    mp hmp_mem
  obtain ⟨Fn, Rn, hFRn, hFn, hRn⟩ := exists_rootPolynomial_eq_mul_of_pairs (K := K)
    (S := {r | r < -1 ∧ 4 * r ^ 2 + 4 * r ≤ 1}) h1 hmul
    (fun r hr s hs ↦
      RealRooted.BrandenE.isRealRootedIn_Icc_quadratic_of_lt_neg_one hr.1 hs.1 hr.2 hs.2)
    mn (fun r hr ↦ by
      rw [hmn, Multiset.mem_filter] at hr
      exact ⟨hr.2, hroot r hr.1⟩)
  have hFp0 : Fp ≠ 0 := left_ne_zero_of_mul (hFRp ▸ rootPolynomial_ne_zero _)
  have hFn0 : Fn ≠ 0 := left_ne_zero_of_mul (hFRn ▸ rootPolynomial_ne_zero _)
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  have hsplit : rootPolynomial p.roots =
      rootPolynomial mm * (rootPolynomial mp * rootPolynomial mn) := by
    have e1 : p.roots = mn + mr := (Multiset.filter_add_not _ _).symm
    have e2 : mr = mp + mm := (Multiset.filter_add_not _ _).symm
    rw [e1, rootPolynomial_add, e2, rootPolynomial_add]
    ring
  refine ⟨p.leadingCoeff, rootPolynomial mm * (Fp * Fn), Rp, Rn, hlc, ?_,
    mul_ne_zero (rootPolynomial_ne_zero _) (mul_ne_zero hFp0 hFn0),
    hmul _ (hmid mm hmm_mem) _ (hmul _ hFp _ hFn), ?_, ?_⟩
  · conv_lhs => rw [hp.eq_C_mul_rootPolynomial, hsplit, hFRp, hFRn]
    ring
  · rcases hRp with h | ⟨r, hr, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨r, ?_, (hmp_mem r hr).1, h⟩
      rw [hmp, hmr, Multiset.mem_filter, Multiset.mem_filter] at hr
      exact hr.1.1
  · rcases hRn with h | ⟨r, hr, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨r, ?_, ?_, h⟩
      · rw [hmn, Multiset.mem_filter] at hr
        exact hr.1
      · rw [hmn, Multiset.mem_filter] at hr
        exact hr.2

/-! ### Invariant intervals and sharp source domains -/

/-- The `E` image of a pair of roots is real-rooted with all roots in `[A, B]` whenever the two
linear factors have roots in `[A, B] ∩ ([L, -1) ∪ (0, U])`, one in each part; the other cases are
the linear factors. -/
private theorem isRealRootedIn_Icc_brandenE_residual {A B : ℝ} {Rp Rn : ℝ[X]} {m : Multiset ℝ}
    (hm : ∀ r ∈ m, r ∈ Icc A B) (hm' : ∀ r ∈ m, 4 * r ^ 2 + 4 * r ≤ 1)
    (hRp : Rp = 1 ∨ ∃ r ∈ m, 0 < r ∧ Rp = X - C r)
    (hRn : Rn = 1 ∨ ∃ r ∈ m, r < -1 ∧ Rn = X - C r) :
    IsRealRootedIn (Icc A B) (brandenE (Rp * Rn)) := by
  have hE1 := brandenE_one_eq
  rcases hRp with rfl | ⟨r, hr, hr0, rfl⟩ <;> rcases hRn with rfl | ⟨s, hs, hs0, rfl⟩
  · simpa [hE1] using IsRealRootedIn.one
  · rw [one_mul, brandenE_X_sub_C]
    exact IsRealRootedIn.X_sub_C (hm s hs)
  · rw [mul_one, brandenE_X_sub_C]
    exact IsRealRootedIn.X_sub_C (hm r hr)
  · rw [mul_comm]
    exact (RealRooted.BrandenE.isRealRootedIn_Icc_quadratic_of_lt_neg_one_of_pos hs0 hr0
      (hm' s hs) (hm' r hr)).mono (Icc_subset_Icc (hm s hs).1 (hm r hr).2)

/-- **Invariant intervals of the `E` transform.**  For `L ≤ A ≤ -1` and `0 ≤ B ≤ U` the `E`
transform sends polynomials rooted in `[A, B]` to polynomials rooted in `[A, B]`. -/
theorem IsRealRootedIn.brandenE_Icc {A B : ℝ} (hL : -(1 + √2) / 2 ≤ A) (hA : A ≤ -1)
    (hB : 0 ≤ B) (hU : B ≤ (√2 - 1) / 2) {p : ℝ[X]} (hp : IsRealRootedIn (Icc A B) p) :
    IsRealRootedIn (Icc A B) (brandenE p) := by
  have hp' : IsRealRootedIn (Icc (-(1 + √2) / 2) ((√2 - 1) / 2)) p :=
    hp.mono (Icc_subset_Icc hL hU)
  obtain ⟨a, F, Rp, Rn, ha, hpeq, hF0, hEF, hRp, hRn⟩ :=
    exists_eq_C_mul_mul_of_isRealRootedIn_Icc hp'
  have hres := isRealRootedIn_Icc_brandenE_residual (m := p.roots)
    (fun r hr ↦ hp.mem_of_mem_roots hr)
    (fun r hr ↦ mem_Icc_neg_one_add_sqrt_two_iff.1 (hp'.mem_of_mem_roots hr)) hRp hRn
  rw [hpeq, brandenE_C_mul, ← betaProduct_one_brandenE]
  exact IsRealRootedIn.C_mul ha (betaProduct_one_isRealRootedIn_Icc hA hB hEF hres)

/-- The constants `L ≤ -1` and `0 ≤ U`. -/
private theorem neg_one_add_sqrt_two_div_two_le : -(1 + √2) / 2 ≤ -1 := by
  have : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

private theorem zero_le_sqrt_two_sub_one_div_two : 0 ≤ (√2 - 1) / 2 := by
  have : 1 ≤ √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- The `E` image of `(X - r) ^ 2` is real-rooted iff `4 r ^ 2 + 4 r ≤ 1`, i.e. `r ∈ [L, U]`. -/
theorem splits_brandenE_X_sub_C_sq_iff (r : ℝ) :
    (brandenE ((X - C r) ^ 2)).Splits ↔ r ∈ Icc (-(1 + √2) / 2) ((√2 - 1) / 2) := by
  rw [sq, brandenE_X_sub_C_mul_X_sub_C, quadraticPoly_splits_iff_le two_pos,
    mem_Icc_neg_one_add_sqrt_two_iff]
  constructor <;> intro h <;> nlinarith

/-- **Sharp source domain of the `E` transform.**  For a set `J` of reals, Brändén's `E` transform
sends every nonzero polynomial rooted in `J` to a real-rooted polynomial if and only if
`J ⊆ [L, U]` with `L = -(1 + √2) / 2` and `U = (√2 - 1) / 2`.  Singletons and the empty set are
included. -/
theorem forall_splits_brandenE_iff (J : Set ℝ) :
    (∀ p : ℝ[X], IsRealRootedIn J p → (brandenE p).Splits) ↔
      J ⊆ Icc (-(1 + √2) / 2) ((√2 - 1) / 2) := by
  refine ⟨fun h r hr ↦ ?_, fun h p hp ↦ ?_⟩
  · exact (splits_brandenE_X_sub_C_sq_iff r).1 (h _ ((IsRealRootedIn.X_sub_C hr).pow 2))
  · exact ((hp.mono h).brandenE_Icc le_rfl neg_one_add_sqrt_two_div_two_le
      zero_le_sqrt_two_sub_one_div_two le_rfl).splits

/-- If `E ((X - c) ^ 2)` is rooted in `S`, then both of its (explicit) roots
`(2 c - 1 ± t) / 4` lie in `S`, where `t ^ 2 = 1 - 4 c - 4 c ^ 2`. -/
private theorem exists_sqrt_mem_of_isRealRootedIn_brandenE_X_sub_C_sq {S : Set ℝ} {c : ℝ}
    (h : IsRealRootedIn S (brandenE ((X - C c) ^ 2))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = 1 - 4 * c - 4 * c ^ 2 ∧ (2 * c - 1 - t) / 4 ∈ S ∧
      (2 * c - 1 + t) / 4 ∈ S := by
  rw [sq, brandenE_X_sub_C_mul_X_sub_C] at h
  have hd : 0 ≤ (1 - c - c) ^ 2 - 4 * 2 * (c * c) := by
    have := (quadraticPoly_splits_iff_le two_pos).1 h.splits
    nlinarith
  have hroots := roots_quadratic_posLead (a := 2) (b := 1 - c - c) (c := c * c) two_pos hd
  refine ⟨√((1 - c - c) ^ 2 - 4 * 2 * (c * c)), Real.sqrt_nonneg _, ?_, ?_, ?_⟩
  · rw [Real.sq_sqrt hd]
    ring
  · refine h.mem_of_mem_roots ?_
    rw [hroots]
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    left
    ring
  · refine h.mem_of_mem_roots ?_
    rw [hroots]
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    right
    ring

/-- **Invariant intervals of the `E` transform, sharp form.**  For `A ≤ B`, Brändén's `E` transform
sends every polynomial rooted in `[A, B]` to a polynomial rooted in `[A, B]` if and only if
`L ≤ A ≤ -1` and `0 ≤ B ≤ U`, with `L = -(1 + √2) / 2` and `U = (√2 - 1) / 2`. -/
theorem forall_isRealRootedIn_Icc_brandenE_iff {A B : ℝ} (hAB : A ≤ B) :
    (∀ p : ℝ[X], IsRealRootedIn (Icc A B) p → IsRealRootedIn (Icc A B) (brandenE p)) ↔
      -(1 + √2) / 2 ≤ A ∧ A ≤ -1 ∧ 0 ≤ B ∧ B ≤ (√2 - 1) / 2 := by
  refine ⟨fun h ↦ ?_, fun h p hp ↦ hp.brandenE_Icc h.1 h.2.1 h.2.2.1 h.2.2.2⟩
  have hsub := (forall_splits_brandenE_iff (Icc A B)).1 fun p hp ↦ (h p hp).splits
  have hAmem : A ∈ Icc A B := ⟨le_rfl, hAB⟩
  have hBmem : B ∈ Icc A B := ⟨hAB, le_rfl⟩
  obtain ⟨t, ht0, ht2, h1, -⟩ := exists_sqrt_mem_of_isRealRootedIn_brandenE_X_sub_C_sq
    (h _ ((IsRealRootedIn.X_sub_C hAmem).pow 2))
  obtain ⟨u, hu0, hu2, -, h2⟩ := exists_sqrt_mem_of_isRealRootedIn_brandenE_X_sub_C_sq
    (h _ ((IsRealRootedIn.X_sub_C hBmem).pow 2))
  refine ⟨(hsub hAmem).1, ?_, ?_, (hsub hBmem).2⟩
  · have h1' : t ≤ -1 - 2 * A := by linarith [h1.1]
    have := pow_le_pow_left₀ ht0 h1' 2
    by_contra hA
    nlinarith
  · have h2' : u ≤ 1 + 2 * B := by linarith [h2.2]
    have := pow_le_pow_left₀ hu0 h2' 2
    by_contra hB
    nlinarith

/-- **Rows of an ordered Bell type recurrence.**  Let `P 0 = 1` and
`P (n + 1) = (X + a (n + 1)) * P n + X * (X + 1) * (P n)'` with
`(1 - √2) / 2 ≤ a i ≤ (1 + √2) / 2` for all `i`.  Then every row `P n` is rooted in `[L, U]`.
(The row is the `E` image of `∏ i ≤ n, (t + a i)`, whose roots are `-a i ∈ [L, U]`.) -/
theorem isRealRootedIn_Icc_of_brandenE_recurrence {a : ℕ → ℝ}
    (ha : ∀ n, (1 - √2) / 2 ≤ a n ∧ a n ≤ (1 + √2) / 2) {P : ℕ → ℝ[X]} (h0 : P 0 = 1)
    (hP : ∀ n, P (n + 1) = (X + C (a (n + 1))) * P n + X * (X + 1) * derivative (P n)) (n : ℕ) :
    IsRealRootedIn (Icc (-(1 + √2) / 2) ((√2 - 1) / 2)) (P n) := by
  have hE1 := brandenE_one_eq
  suffices h : ∀ n, ∃ q : ℝ[X], IsRealRootedIn (Icc (-(1 + √2) / 2) ((√2 - 1) / 2)) q ∧
      P n = brandenE q by
    obtain ⟨q, hq, hPq⟩ := h n
    rw [hPq]
    exact hq.brandenE_Icc le_rfl neg_one_add_sqrt_two_div_two_le
      zero_le_sqrt_two_sub_one_div_two le_rfl
  intro n
  induction n with
  | zero => exact ⟨1, IsRealRootedIn.one, by rw [h0, hE1]⟩
  | succ n ih =>
    obtain ⟨q, hq, hPq⟩ := ih
    refine ⟨(X + C (a (n + 1))) * q, ?_, ?_⟩
    · rw [show (X + C (a (n + 1)) : ℝ[X]) = X - C (-a (n + 1)) by simp [sub_eq_add_neg]]
      refine (IsRealRootedIn.X_sub_C ?_).mul hq
      constructor <;> linarith [(ha (n + 1)).1, (ha (n + 1)).2]
    · rw [hP, brandenE_mul_X_add_C, hPq]
      ring

end RealRooted
