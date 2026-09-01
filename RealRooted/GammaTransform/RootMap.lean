import RealRooted.GammaTransform.Basic

/-!
# Gamma-transform root maps

The Hoster--Stump root map and the multiplicity transport from a gamma
polynomial to its transform.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The root map `ρ ↦ ρ / (1 + ρ)²` in Hoster--Stump, Proposition 2.5,
equation (2.1). Reciprocal roots of a palindromic polynomial have the same
image under this map. -/
def gammaRootMap (x : ℝ) : ℝ := x / (1 + x) ^ 2

/-- The surjectivity part of Hoster--Stump equation (2.1) on the preferred
reciprocal branch. For `y < 0`, the polynomial `x - y * (1 + x)^2` has
opposite signs at `-1` and `0`, so the intermediate value theorem supplies the
required representative in `(-1, 0)`. -/
theorem exists_mem_Ioo_gammaRootMap_eq {y : ℝ} (hy : y < 0) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 0, gammaRootMap x = y := by
  let q : ℝ[X] := X - C y * (X + 1) ^ 2
  have hzero : (0 : ℝ) ∈ Set.Icc (q.eval (-1)) (q.eval 0) := by simpa [q] using le_of_lt hy
  obtain ⟨x, hx, hxzero⟩ :=
    intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 0)
      q.continuous.continuousOn hzero
  have hx_ne_left : x ≠ -1 := by
    intro h
    subst x
    dsimp [q] at hxzero
    norm_num at hxzero
  have hx_ne_right : x ≠ 0 := by
    intro h
    subst x
    dsimp [q] at hxzero
    simp at hxzero
    linarith
  have hxmem : x ∈ Set.Ioo (-1 : ℝ) 0 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx_ne_left),
      lt_of_le_of_ne hx.2 hx_ne_right⟩
  refine ⟨x, hxmem, ?_⟩
  have hone : 1 + x ≠ 0 := by linarith [hxmem.1]
  dsimp [q] at hxzero
  simp only [eval_sub, eval_X, eval_mul, eval_C, eval_pow, eval_add, eval_one] at hxzero
  unfold gammaRootMap
  field_simp [hone]
  nlinarith

/-- The gamma root map identifies a nonzero real number with its reciprocal. -/
lemma gammaRootMap_inv {x : ℝ} (hx : x ≠ 0) :
    gammaRootMap x⁻¹ = gammaRootMap x := by
  by_cases h1x : 1 + x = 0
  · have hxneg : x = -1 := by linarith
    simp [gammaRootMap, hxneg]
  · unfold gammaRootMap
    have hone : 1 + x⁻¹ = (1 + x) / x := by
      field_simp [hx]
      ring
    rw [hone, div_pow]
    field_simp [hx, h1x]

/-- Hoster--Stump, Proposition 2.5: the gamma root map is strictly increasing
on the interval `(-1, 0)`. -/
theorem strictMonoOn_gammaRootMap :
    StrictMonoOn gammaRootMap (Set.Ioo (-1) 0) := by
  intro a ha b hb hab
  have ha1 : 0 < 1 + a := by linarith [ha.1]
  have hb1 : 0 < 1 + b := by linarith [hb.1]
  have hab_pos : 0 < b - a := sub_pos.mpr hab
  have hone : 0 < 1 - a * b := by
    have hproduct : 0 < (1 + a) * (1 - b) :=
      mul_pos ha1 (by linarith [hb.2])
    nlinarith
  have hfactor := mul_pos hab_pos hone
  simp only [gammaRootMap]
  rw [div_lt_div_iff₀ (sq_pos_of_pos ha1) (sq_pos_of_pos hb1)]
  nlinarith

/-- The monotone root-map step in Hoster--Stump, Proposition 2.5:
mapping roots in `(-1, 0)` by equation (2.1) preserves and reflects their
weak interleaving order. See https://arxiv.org/abs/2508.15538. -/
theorem interleaves_map_gammaRootMap_iff :
    ∀ {ss rs : List ℝ}
      (_ : ∀ x ∈ ss, x ∈ Set.Ioo (-1) 0)
      (_ : ∀ x ∈ rs, x ∈ Set.Ioo (-1) 0),
      List.Interleaves (fun x y : ℝ => x ≤ y)
          (ss.map gammaRootMap) (rs.map gammaRootMap) ↔
        List.Interleaves (fun x y : ℝ => x ≤ y) ss rs
  | [], rs, _, _ => by
      cases rs <;> simp
  | _ :: _, [], _, _ => by simp
  | s :: ss, r :: rs, hss, hrs => by
      rw [List.map_cons, List.map_cons, List.interleaves_cons_cons,
        List.interleaves_cons_cons,
        strictMonoOn_gammaRootMap.le_iff_le
          (hrs r (by simp)) (hss s (by simp))]
      apply and_congr_right
      intro _
      simpa only [List.map_cons] using
        interleaves_map_gammaRootMap_iff
          (ss := rs) (rs := s :: ss)
          (fun x hx => hrs x (List.mem_cons_of_mem r hx)) hss
termination_by ss rs => ss.length + rs.length

/-- The quadratic reciprocal-pair factor in Hoster--Stump, Proposition 2.5,
equation (2.1). See https://arxiv.org/abs/2508.15538. -/
lemma gammaQuadraticFactor_eq_mul_reciprocal {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ≠ -1) :
    X - C (gammaRootMap x) * (X + 1) ^ 2 =
      C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹) := by
  have h1x : 1 + x ≠ 0 := by
    intro h
    apply hx1
    linarith
  apply Polynomial.funext
  intro y
  simp only [eval_sub, eval_X, eval_mul, eval_C, eval_pow, eval_add, eval_one]
  unfold gammaRootMap
  field_simp [hx0, h1x]
  ring

lemma eval_gammaTransform_eq_mul_eval_gammaUntransform {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) {x : ℝ} (hx : x ≠ -1) :
    (gammaTransform d γ).eval x = (1 + x) ^ d * γ.eval (x / (1 + x) ^ 2) := by
  have h1x_ne : 1 + x ≠ 0 := by grind
  unfold gammaTransform
  rw [Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hγdeg)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h2k_le : 2 * k ≤ d := by lia
  calc
    (C (γ.coeff k) * gammaBasisTerm d k).eval x
        = γ.coeff k * x ^ k * (x + 1) ^ (d - 2 * k) := by simp [gammaBasisTerm, mul_assoc]
    _ = γ.coeff k * x ^ k * (1 + x) ^ (d - 2 * k) := by grind
    _ = γ.coeff k * (x ^ k * (1 + x) ^ (d - 2 * k)) := by grind
    _ = γ.coeff k * ((1 + x) ^ d * (x / (1 + x) ^ 2) ^ k) := by
          have hterm :
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k = x ^ k * (1 + x) ^ (d - 2 * k) := by
            calc
              (1 + x) ^ d * (x / (1 + x) ^ 2) ^ k
                  = (1 + x) ^ d * (x ^ k * (((1 + x) ^ 2) ^ k)⁻¹) := by
                      rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * (((1 + x) ^ 2) ^ k)⁻¹) := by grind
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ (2 * k))⁻¹) := by rw [pow_mul]
              _ = x ^ k * (1 + x) ^ (d - 2 * k) := by rw [← pow_sub₀ (1 + x) h1x_ne h2k_le]
          lia
    _ = (1 + x) ^ d * (γ.coeff k * (x / (1 + x) ^ 2) ^ k) := by ring

lemma gammaUntransform_nonpos {x : ℝ} (hx0 : x ≤ 0) (hx : x ≠ -1) :
    x / (1 + x) ^ 2 ≤ 0 := by
  have h1x_ne : 1 + x ≠ 0 := by grind
  have hsq_pos : 0 < (1 + x) ^ 2 := by positivity
  have hinv_nonneg : 0 ≤ ((1 + x) ^ 2)⁻¹ := inv_nonneg.mpr hsq_pos.le
  simpa [div_eq_mul_inv] using mul_nonpos_of_nonpos_of_nonneg hx0 hinv_nonneg

lemma hasRootsNonpos_of_dvd {p q : ℝ[X]}
    (hp_nonpos : HasRootsNonpos p) (hp0 : p ≠ 0)
    (hqp : q ∣ p) (hq0 : q ≠ 0) :
    HasRootsNonpos q := by
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq0).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact hp_nonpos r ((mem_roots hp0).mpr hrp)

lemma HasRootsNonpos.mul {p q : ℝ[X]}
    (hp : HasRootsNonpos p) (hq : HasRootsNonpos q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    HasRootsNonpos (p * q) := by
  intro r hr
  have hrpq : (p * q).IsRoot r := (mem_roots (mul_ne_zero hp0 hq0)).mp hr
  rw [Polynomial.IsRoot.def, eval_mul] at hrpq
  exact (mul_eq_zero.mp hrpq).elim
    (fun hpr => hp r ((mem_roots hp0).mpr hpr))
    (fun hqr => hq r ((mem_roots hq0).mpr hqr))

lemma hasRootsNonpos_X_sub_C {r : ℝ} (hr : r ≤ 0) :
    HasRootsNonpos (X - C r) := by
  intro s hs
  simp_all

lemma isRoot_gamma_of_isRoot_gammaTransform {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) {x : ℝ} (hx : x ≠ -1)
    (hroot : (gammaTransform d γ).IsRoot x) :
    γ.IsRoot (x / (1 + x) ^ 2) := by
  rw [Polynomial.IsRoot.def] at hroot ⊢
  rw [eval_gammaTransform_eq_mul_eval_gammaUntransform hγdeg hx] at hroot
  have h1x_ne : 1 + x ≠ 0 := by grind
  simp_all

lemma rootPullback_nonpos_of_gammaTransform {x : ℝ}
    (hx : x ≠ -1) (hx0 : x ≤ 0) :
    (x / (1 + x) ^ 2) ≤ 0 :=
  gammaUntransform_nonpos hx0 hx

lemma gammaTransform_X_sub_C_mul_two {d : ℕ} {γ : ℝ[X]}
    (hγ : γ.natDegree ≤ d / 2) (r : ℝ) :
    gammaTransform (d + 2) ((X - C r) * γ) =
      (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by
  have hmul : (X - C r) * γ = X * γ + C (-r) * γ := by simp [sub_eq_add_neg, add_mul]
  calc
    gammaTransform (d + 2) ((X - C r) * γ)
      = gammaTransform (d + 2) (X * γ + C (-r) * γ) := by lia
    _ = gammaTransform (d + 2) (X * γ) + C (-r) * gammaTransform (d + 2) γ := by
          rw [gammaTransform_add, gammaTransform_C_mul]
    _ = X * gammaTransform d γ + C (-r) * ((X + 1) ^ 2 * gammaTransform d γ) := by
          rw [gammaTransform_X_mul_two, gammaTransform_pad_two hγ]
    _ = X * gammaTransform d γ - (C r * (X + 1) ^ 2) * gammaTransform d γ := by
          simp [sub_eq_add_neg, mul_assoc]
    _ = (X - C r * (X + 1) ^ 2) * gammaTransform d γ := by grind

/-- Iterated form of the quadratic factor in Hoster--Stump, Proposition 2.5,
equation (2.1). -/
lemma gammaTransform_X_sub_C_pow_mul_two
    {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) (r : ℝ) :
    ∀ m : ℕ,
      gammaTransform (d + 2 * m) ((X - C r) ^ m * γ) =
        (X - C r * (X + 1) ^ 2) ^ m * gammaTransform d γ
  | 0 => by simp
  | m + 1 => by
      have hdeg :
          ((X - C r) ^ m * γ).natDegree ≤ (d + 2 * m) / 2 := by
        calc
          ((X - C r) ^ m * γ).natDegree
              ≤ ((X - C r) ^ m).natDegree + γ.natDegree :=
            natDegree_mul_le
          _ ≤ m * (X - C r).natDegree + γ.natDegree :=
            Nat.add_le_add_right natDegree_pow_le _
          _ ≤ m * 1 + d / 2 :=
            Nat.add_le_add (Nat.mul_le_mul_left m (natDegree_X_sub_C_le r)) hγ
          _ ≤ (d + 2 * m) / 2 := by lia
      calc
        gammaTransform (d + 2 * (m + 1)) ((X - C r) ^ (m + 1) * γ) =
            gammaTransform ((d + 2 * m) + 2)
              ((X - C r) * ((X - C r) ^ m * γ)) := by
                rw [show d + 2 * (m + 1) = (d + 2 * m) + 2 by lia]
                congr 1
                rw [pow_succ]
                ring
        _ = (X - C r * (X + 1) ^ 2) *
              gammaTransform (d + 2 * m) ((X - C r) ^ m * γ) :=
          gammaTransform_X_sub_C_mul_two hdeg r
        _ = (X - C r * (X + 1) ^ 2) *
              ((X - C r * (X + 1) ^ 2) ^ m * gammaTransform d γ) := by
          rw [gammaTransform_X_sub_C_pow_mul_two hγ r m]
        _ = (X - C r * (X + 1) ^ 2) ^ (m + 1) *
              gammaTransform d γ := by
          rw [pow_succ]
          ring

/-- Algebraic reciprocal-pair factorization away from `0` and `-1`. -/
lemma gammaTransform_X_sub_C_pow_gammaRootMap_of_ne
    {d m : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) {x : ℝ}
    (hx0 : x ≠ 0) (hx1 : x ≠ -1) :
    gammaTransform (d + 2 * m) ((X - C (gammaRootMap x)) ^ m * γ) =
      (C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹)) ^ m *
        gammaTransform d γ := by
  rw [gammaTransform_X_sub_C_pow_mul_two hγ,
    gammaQuadraticFactor_eq_mul_reciprocal hx0 hx1]

/-- A gamma root of multiplicity `m` yields reciprocal transform roots, each
with the same extracted multiplicity, in Hoster--Stump equation (2.1). -/
lemma gammaTransform_X_sub_C_pow_gammaRootMap
    {d m : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 0) :
    gammaTransform (d + 2 * m) ((X - C (gammaRootMap x)) ^ m * γ) =
      (C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹)) ^ m *
        gammaTransform d γ :=
  gammaTransform_X_sub_C_pow_gammaRootMap_of_ne hγ
    (ne_of_lt hx.2) (ne_of_gt hx.1)

/-- Extracting one gamma root produces the reciprocal transform-root pair in
Hoster--Stump, Proposition 2.5, equation (2.1). -/
lemma gammaTransform_X_sub_C_gammaRootMap
    {d : ℕ} {γ : ℝ[X]} (hγ : γ.natDegree ≤ d / 2) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 0) :
    gammaTransform (d + 2) ((X - C (gammaRootMap x)) * γ) =
      (C (-gammaRootMap x) * (X - C x) * (X - C x⁻¹)) *
        gammaTransform d γ := by
  simpa using
    (gammaTransform_X_sub_C_pow_gammaRootMap (m := 1) hγ hx)

/-- Multiplicity form of Hoster--Stump, Proposition 2.5, equation (2.1), on
both reciprocal halves of the negative real axis. -/
theorem rootMultiplicity_gammaTransform_of_neg
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) {x : ℝ} (hx : x < 0) (hx1 : x ≠ -1) :
    (gammaTransform d γ).rootMultiplicity x =
      γ.rootMultiplicity (gammaRootMap x) := by
  let r := gammaRootMap x
  let m := γ.rootMultiplicity r
  obtain ⟨q, hγq, hq_not_dvd⟩ :=
    γ.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hγ r
  change γ = (X - C r) ^ m * q at hγq
  have hq : q ≠ 0 := by
    intro hzero
    apply hγ
    rw [hγq, hzero, mul_zero]
  have hdeg_eq : γ.natDegree = m + q.natDegree := by
    rw [hγq, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero r)) hq,
      natDegree_pow, natDegree_X_sub_C, mul_one]
  have hm : 2 * m ≤ d := by
    have hbound : m + q.natDegree ≤ d / 2 := hdeg_eq ▸ hγdeg
    lia
  have hqdeg : q.natDegree ≤ (d - 2 * m) / 2 := by
    have hbound : m + q.natDegree ≤ d / 2 := hdeg_eq ▸ hγdeg
    lia
  have hx0 : x ≠ 0 := ne_of_lt hx
  have htransform :=
    gammaTransform_X_sub_C_pow_gammaRootMap_of_ne
      (d := d - 2 * m) (m := m) hqdeg hx0 hx1
  have hambient : d - 2 * m + 2 * m = d := by lia
  have hfull := htransform
  rw [hambient, ← hγq] at hfull
  have h1x : 1 + x ≠ 0 := by
    intro h
    apply hx1
    linarith
  have hr0 : r ≠ 0 := by
    dsimp [r, gammaRootMap]
    exact div_ne_zero hx0 (pow_ne_zero _ h1x)
  have hxxinv : x ≠ x⁻¹ := by
    intro heq
    have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    rw [← heq] at hmul
    rcases lt_or_gt_of_ne hx1 with hlt | hgt <;> nlinarith
  have hcore_not_root :
      ¬(gammaTransform (d - 2 * m) q).IsRoot x := by
    intro hroot
    apply hq_not_dvd
    rw [dvd_iff_isRoot]
    simpa [r, gammaRootMap] using
      isRoot_gamma_of_isRoot_gammaTransform hqdeg hx1 hroot
  have hcore_eval : (gammaTransform (d - 2 * m) q).eval x ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hcore_not_root
  let p :=
    (C (-r) * (X - C x⁻¹)) ^ m * gammaTransform (d - 2 * m) q
  have hp_eval : p.eval x ≠ 0 := by
    dsimp [p]
    simp only [eval_mul, eval_pow, eval_C, eval_sub, eval_X]
    exact mul_ne_zero
      (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr hr0)
        (sub_ne_zero.mpr hxxinv)))
      hcore_eval
  have hp : p ≠ 0 := by
    intro hzero
    apply hp_eval
    simp [hzero]
  have hp_not_root : ¬p.IsRoot x := by
    rw [Polynomial.IsRoot.def]
    exact hp_eval
  have hfactor :
      gammaTransform d γ = p * (X - C x) ^ m := by
    rw [hfull]
    dsimp [p, r]
    simp only [mul_pow]
    ring
  change (gammaTransform d γ).rootMultiplicity x = m
  rw [hfactor, rootMultiplicity_mul_X_sub_C_pow hp,
    rootMultiplicity_eq_zero hp_not_root, zero_add]

/-- Multiplicity form of Hoster--Stump equation (2.1) on the preferred branch
`(-1, 0)`. -/
theorem rootMultiplicity_gammaTransform_of_mem_Ioo
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ : γ ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 0) :
    (gammaTransform d γ).rootMultiplicity x =
      γ.rootMultiplicity (gammaRootMap x) :=
  rootMultiplicity_gammaTransform_of_neg hγdeg hγ hx.2 (ne_of_gt hx.1)



end RealRooted
