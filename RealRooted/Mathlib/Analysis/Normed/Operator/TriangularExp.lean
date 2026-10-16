/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import Mathlib

/-!
# A normalized triangular exponential converges to the top eigenvector

Let `T` be a continuous linear endomorphism of a finite-dimensional real normed space with a
basis `b` indexed by `Fin (n + 1)`, upper triangular in that basis, whose last diagonal entry
`a` is strictly larger than every other diagonal entry.  For every `x` whose last coordinate is
`1`, `exp(-t a) • exp(t T) x` converges as `t → ∞` to the unique
eigenvector `y` of `T` for `a` with last coordinate `1`.

Proof idea: upper triangularity makes `V = span {b 0, …, b (n-1)}` invariant (with the
convention `A i j = 0` for `j < i`); the eigenvector `y` is obtained by back substitution since
`a - A i i ≠ 0` for `i < n`; `x - y ∈ V` and `exp(t (T - a)) ` restricted to `V` decays to zero
because all eigenvalues of `T|V - a` are negative (e.g. via a triangular bound, or the spectral
radius / Gelfand formula).  The uniqueness part follows from uniqueness of limits.

The proof was found by Aristotle (Harmonic).
-/

public section

open Filter Topology

namespace TriExp

open Matrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section General

variable {m : Type*} [Fintype m] [DecidableEq m]

private lemma exp_mulVec_of_mulVec_eq_zero (X : Matrix m m ℝ) (v : m → ℝ)
    (h : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) X
  let L : Matrix m m ℝ →ₗ[ℝ] (m → ℝ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun _ _ => Matrix.add_mulVec _ _ _
      map_smul' := fun _ _ => Matrix.smul_mulVec _ _ _ }
  have := (hs.hasSum.map L (LinearMap.continuous_of_finiteDimensional L)).tsum_eq
  calc
    L (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • X ^ n) =
        ∑' n : ℕ, L ((n.factorial : ℝ)⁻¹ • X ^ n) := by
      change L _ = ∑' n : ℕ,
        (⇑L ∘ fun k : ℕ => (k.factorial : ℝ)⁻¹ • X ^ k) n
      exact this.symm
    _ = v := by
      rw [tsum_eq_single 0]
      · simp [L]
      · intro k hk
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_mulVec,
          pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]

private lemma norm_one_add_smul_le (M : Matrix m m ℝ) (c h : ℝ) (hh : 0 ≤ h)
    (hch : c * h ≤ 1)
    (hdiag : ∀ i, h * |M i i| ≤ 1)
    (hrow : ∀ i, M i i + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ -c) :
    ‖(1 : Matrix m m ℝ) + h • M‖ ≤ 1 - c * h := by
  have hnn : 0 ≤ 1 - c * h := by linarith
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : m => ∑ j : m, ‖((1 : Matrix m m ℝ) + h • M) i j‖₊) ≤
      ⟨1 - c * h, hnn⟩ := by
    refine Finset.sup_le fun i _ => ?_
    apply NNReal.coe_le_coe.mp
    have hi : (∑ j : m, ‖((1 : Matrix m m ℝ) + h • M) i j‖) ≤
        1 - c * h := by
      simp only [Real.norm_eq_abs]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have h1 : |((1 : Matrix m m ℝ) + h • M) i i| = 1 + h * M i i := by
        simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
        rw [abs_of_nonneg (by nlinarith [hdiag i, neg_abs_le (M i i)])]
      have h2 : ∑ j ∈ Finset.univ.erase i, |((1 : Matrix m m ℝ) + h • M) i j| =
          h * ∑ j ∈ Finset.univ.erase i, |M i j| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [Matrix.one_apply_ne (Finset.ne_of_mem_erase hj).symm, abs_mul, abs_of_nonneg hh]
      rw [h1, h2]
      nlinarith [hrow i]
    convert hi using 1
    · rw [NNReal.coe_sum]
      simp only [coe_nnnorm]
    · rfl
  exact_mod_cast this

private lemma exists_norm_exp_lt_one (M : Matrix m m ℝ) (c : ℝ) (hc : 0 < c)
    (hrow : ∀ i, M i i + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ -c) :
    ∃ h : ℝ, 0 < h ∧ ‖NormedSpace.exp (h • M)‖ < 1 := by
  have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) M (0 : ℝ)
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hd
  have he := hd.def (half_pos hc)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 he
  have hS : 0 ≤ ∑ i, |M i i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  set R : ℝ := c + 1 + ∑ i, |M i i|
  have hRpos : 0 < R := by linarith
  set h : ℝ := min (ε / 2) (1 / R) with hh
  have hpos : 0 < h := lt_min (half_pos hε) (by positivity)
  have hhR : h * R ≤ 1 := by
    have : h ≤ 1 / R := min_le_right _ _
    rwa [le_div_iff₀ hRpos] at this
  have hsum : ∀ i, |M i i| ≤ ∑ j, |M j j| := fun i =>
    Finset.single_le_sum (f := fun j => |M j j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hdiag : ∀ i, h * |M i i| ≤ 1 := fun i =>
    (mul_le_mul_of_nonneg_left (by linarith [hsum i]) hpos.le).trans hhR
  have hch : c * h ≤ 1 := by nlinarith
  have h1 := norm_one_add_smul_le M c h hpos.le hch hdiag hrow
  have h2 := hball (y := h) (by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul, Real.norm_eq_abs,
    abs_of_pos hpos] at h2
  refine ⟨h, hpos, ?_⟩
  rw [show NormedSpace.exp (h • M) =
    (1 + h • M) + (NormedSpace.exp (h • M) - 1 - h • M) by abel]
  calc _ ≤ ‖(1 : Matrix m m ℝ) + h • M‖ + ‖NormedSpace.exp (h • M) - 1 - h • M‖ :=
        norm_add_le _ _
    _ ≤ (1 - c * h) + c / 2 * h := add_le_add h1 h2
    _ < 1 := by nlinarith

private lemma tendsto_exp_of_norm_exp_lt_one (M : Matrix m m ℝ) (h : ℝ)
    (hh : 0 < h)
    (hq : ‖NormedSpace.exp (h • M)‖ < 1) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • M)) atTop (𝓝 0) := by
  set q := ‖NormedSpace.exp (h • M)‖
  have hcont : Continuous fun s : ℝ => NormedSpace.exp (s • M) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) M s).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := h)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hk : Tendsto (fun t : ℝ => ⌊t / h⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hh)
  have hlim : Tendsto (fun t : ℝ => C * q ^ ⌊t / h⌋₊) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq).comp hk).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop h] with t ht
  set k := ⌊t / h⌋₊ with hkdef
  have hk1 : 1 ≤ k := by
    rw [hkdef, Nat.one_le_floor_iff, one_le_div hh]; exact ht
  set s := t - k * h with hs
  have hk_le : (k : ℝ) * h ≤ t := by
    have := Nat.floor_le (div_nonneg (hh.le.trans ht) hh.le)
    rw [← hkdef, le_div_iff₀ hh] at this; exact this
  have hlt : t < (k + 1) * h := by
    have := Nat.lt_floor_add_one (t / h)
    rw [← hkdef, div_lt_iff₀ hh] at this; exact this
  have hs0 : s ∈ Set.Icc 0 h := ⟨by linarith, by nlinarith⟩
  have hdecomp : t • M = k • (h • M) + s • M := by
    rw [hs, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← add_smul]; ring_nf
  have hcomm : Commute (k • (h • M)) (s • M) :=
    (((Commute.refl M).smul_left h).smul_right s).smul_left k
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm, Matrix.exp_nsmul]
  calc ‖NormedSpace.exp (h • M) ^ k * NormedSpace.exp (s • M)‖
      ≤ ‖NormedSpace.exp (h • M) ^ k‖ * ‖NormedSpace.exp (s • M)‖ := norm_mul_le _ _
    _ ≤ q ^ k * C := by
        apply mul_le_mul (norm_pow_le' _ (by lia)) (hC s hs0) (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) _)
    _ = C * q ^ k := mul_comm _ _

end General

private lemma tendsto_exp_of_upperTriangular {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : M.IsUpperTriangular) (hdiag : ∀ i, M i i < 0) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • M)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hci⟩ : ∃ c > (0 : ℝ), ∀ i, M i i ≤ -c := by
    rcases isEmpty_or_nonempty (Fin k) with hk | hk
    · exact ⟨1, one_pos, fun i => hk.elim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => M i i)
      exact ⟨-M i0 i0, by linarith [hdiag i0], fun i => by linarith [hi0 i]⟩
  set R : ℝ := ∑ i, ∑ j, |M i j| with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set K : ℝ := 1 + 2 * R / c with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    exact le_add_of_nonneg_right (by positivity)
  have hKpos : 0 < K := by linarith
  have hRK : R / K ≤ c / 2 := by
    rw [div_le_iff₀ hKpos, hK]
    field_simp
    nlinarith
  let d : Fin k → ℝ := fun i => K ^ (i : ℕ)
  have hd : ∀ i, d i ≠ 0 := fun i => pow_ne_zero _ hKpos.ne'
  let u : (Matrix (Fin k) (Fin k) ℝ)ˣ :=
    ⟨Matrix.diagonal d, Matrix.diagonal d⁻¹, by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; simp [hd i], by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; simp [hd i]⟩
  set M' : Matrix (Fin k) (Fin k) ℝ := u.val * M * (u⁻¹).val with hM'
  have hentry : ∀ i j, M' i j = d i * M i j * (d j)⁻¹ := by
    intro i j
    simp [hM', u, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hoff : ∀ i j, i ≠ j → |M' i j| ≤ |M i j| / K := by
    intro i j hij
    rw [hentry]
    rcases lt_or_gt_of_ne hij with h | h
    · have hdj : d j = d i * K ^ ((j : ℕ) - i) := by
        simp only [d, ← pow_add]; congr 1; lia
      have hpow : K ≤ K ^ ((j : ℕ) - i) := by
        simpa using pow_le_pow_right₀ hK1 (show 1 ≤ (j : ℕ) - i by lia)
      have hKp : 0 < K ^ ((j : ℕ) - i) := pow_pos hKpos _
      have heq : d i * M i j * (d j)⁻¹ = M i j / K ^ ((j : ℕ) - i) := by
        rw [hdj]; field_simp [hd i]
      rw [heq, abs_div, abs_of_pos hKp]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hKpos hpow
    · rw [hM h]; simp
  have hrow : ∀ i, M' i i + ∑ j ∈ Finset.univ.erase i, |M' i j| ≤ -(c / 2) := by
    intro i
    have hii : M' i i = M i i := by rw [hentry]; field_simp [hd i]
    have h1 : ∑ j ∈ Finset.univ.erase i, |M' i j| ≤
        ∑ j ∈ Finset.univ.erase i, |M i j| / K :=
      Finset.sum_le_sum fun j hj => hoff i j (Finset.ne_of_mem_erase hj).symm
    have h2 : ∑ j ∈ Finset.univ.erase i, |M i j| ≤ R :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun j _ _ => abs_nonneg _).trans <|
          Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [← Finset.sum_div] at h1
    have h4 : (∑ j ∈ Finset.univ.erase i, |M i j|) / K ≤ R / K :=
      div_le_div_of_nonneg_right h2 hKpos.le
    linarith [hci i]
  obtain ⟨h, hh, hq⟩ := exists_norm_exp_lt_one M' (c / 2) (half_pos hc) hrow
  have hlim := tendsto_exp_of_norm_exp_lt_one M' h hh hq
  have hconj : ∀ t : ℝ, NormedSpace.exp (t • M) =
      (u⁻¹).val * NormedSpace.exp (t • M') * u.val := by
    intro t
    have : t • M' = u.val * (t • M) * (u⁻¹).val := by
      rw [hM', Matrix.mul_smul, Matrix.smul_mul]
    rw [this, Matrix.exp_units_conj]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have := (hlim.const_mul (u⁻¹).val).mul_const u.val
  rw [mul_zero, zero_mul] at this
  exact this.congr fun t => (hconj t).symm

private lemma exists_kernel_vec {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hS : S.IsUpperTriangular) (hlast : S (Fin.last n) (Fin.last n) = 0)
    (hdiag : ∀ i : Fin n, S i.castSucc i.castSucc ≠ 0) :
    ∃ η : Fin (n + 1) → ℝ, S *ᵥ η = 0 ∧ η (Fin.last n) = 1 := by
  have hdet : S.det = 0 := by
    rw [Matrix.det_of_isUpperTriangular hS]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) hlast
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : (Finset.univ.filter fun j => v j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
    refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    simpa only [Pi.zero_apply] using hj
  set i := (Finset.univ.filter fun j => v j ≠ 0).max' hne with hidef
  have hi : v i ≠ 0 := by
    simpa only [← hidef] using (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  have hgt : ∀ j, i < j → v j = 0 := fun j hj => by
    by_contra h
    exact not_le.2 hj (Finset.le_max' _ j (by simp [h]))
  have hSi : S i i * v i = 0 := by
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i] at this
    · exact this
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · change j < i at h
        rw [@hS i j h, zero_mul]
      · rw [hgt j h, mul_zero]
    · simp
  have hii : S i i = 0 := (mul_eq_zero.1 hSi).resolve_right hi
  have hil : i = Fin.last n := by
    by_contra h
    obtain ⟨i', hi'⟩ := Fin.exists_castSucc_eq.2 h
    rw [← hi'] at hii
    exact hdiag i' hii
  refine ⟨(v (Fin.last n))⁻¹ • v, by rw [Matrix.mulVec_smul, hv, smul_zero], ?_⟩
  rw [← hil, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hi]

private lemma matrix_main {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.IsUpperTriangular)
    (hgap : ∀ i : Fin n, A i.castSucc i.castSucc < A (Fin.last n) (Fin.last n)) :
    ∃ η : Fin (n + 1) → ℝ,
      A *ᵥ η = A (Fin.last n) (Fin.last n) • η ∧ η (Fin.last n) = 1 ∧
      ∀ ξ : Fin (n + 1) → ℝ, ξ (Fin.last n) = 1 →
        Tendsto (fun t : ℝ => Real.exp (-t * A (Fin.last n) (Fin.last n)) •
          (NormedSpace.exp (t • A) *ᵥ ξ)) atTop (𝓝 η) := by
  set a := A (Fin.last n) (Fin.last n) with hadef
  set S := A - a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) with hSdef
  have hSe : ∀ i j, S i j = A i j - if i = j then a else 0 := by
    intro i j; simp [hSdef, Matrix.one_apply]
  have hSU : S.IsUpperTriangular := fun i j h => by
    change j < i at h
    rw [hSe, hA h]
    simp [h.ne']
  have hSl : S (Fin.last n) (Fin.last n) = 0 := by simp [hSe, hadef]
  have hSd : ∀ i : Fin n, S i.castSucc i.castSucc ≠ 0 := fun i => by
    simpa [hSe] using sub_ne_zero.2 (hgap i).ne
  obtain ⟨η, hη, hηl⟩ := exists_kernel_vec S hSU hSl hSd
  have hrow : ∀ j, S (Fin.last n) j = 0 := by
    intro j
    rcases (Fin.le_last j).lt_or_eq with h | h
    · exact hSU h
    · simpa [h] using hSl
  refine ⟨η, ?_, hηl, ?_⟩
  · have : A = S + a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by simp [hSdef]
    rw [this, Matrix.add_mulVec, hη, Matrix.smul_mulVec, Matrix.one_mulVec, zero_add]
  intro ξ hξ
  have hexp : ∀ t : ℝ, Real.exp (-t * a) • NormedSpace.exp (t • A) =
      NormedSpace.exp (t • S) := by
    intro t
    have h1 : t • A =
        t • S + algebraMap ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t * a) := by
      rw [Algebra.algebraMap_eq_smul_one, hSdef, smul_sub, smul_smul, sub_add_cancel]
    rw [h1, Matrix.exp_add_of_commute _ _ (Algebra.commute_algebraMap_right (t * a) (t • S))]
    have hscalar :
        NormedSpace.exp
            (algebraMap ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t * a)) =
          algebraMap ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            (Real.exp (t * a)) := by
      calc
        _ = algebraMap ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
            (NormedSpace.exp (t * a)) :=
          (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ)
            (𝔸 := Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t * a)).symm
        _ = _ := by rw [Real.exp_eq_exp_ℝ]
    rw [hscalar, ← Algebra.commutes, ← Algebra.smul_def, smul_smul,
      ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero, one_smul]
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => if j = Fin.last n then η i else 0 with hPdef
  set N := S - P with hNdef
  have hSP : S * P = 0 := by
    ext i j
    by_cases hj : j = Fin.last n
    · simpa [Matrix.mul_apply, hPdef, hj, Matrix.mulVec, dotProduct] using congrFun hη i
    · simp [Matrix.mul_apply, hPdef, hj]
  have hPS : P * S = 0 := by
    ext i j
    simp [Matrix.mul_apply, hPdef, hrow]
  have hPP : P * P = P := by
    ext i j
    by_cases hj : j = Fin.last n <;> simp [Matrix.mul_apply, hPdef, hj, hηl]
  have hcomm : Commute N P := by
    change N * P = P * N
    rw [hNdef, sub_mul, mul_sub, hSP, hPS, hPP]
  have hNU : N.IsUpperTriangular := fun i j h => by
    change j < i at h
    have hj : j ≠ Fin.last n := fun hj => by
      rw [hj] at h; exact absurd (Fin.le_last i) (not_le.2 h)
    simp [hNdef, hPdef, hj, hSU h]
  have hNd : ∀ i, N i i < 0 := by
    intro i
    by_cases hi : i = Fin.last n
    · subst hi; simp [hNdef, hPdef, hSl, hηl]
    · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hi
      simpa [hNdef, hPdef, hSe, hi] using sub_neg.mpr (hgap i')
  have hlimN := tendsto_exp_of_upperTriangular N hNU hNd
  set v := ξ - η with hvdef
  have hPv : P *ᵥ v = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, hPdef, hvdef, hξ, hηl]
  have hfun : ∀ t : ℝ, Real.exp (-t * a) • (NormedSpace.exp (t • A) *ᵥ ξ) =
      η + NormedSpace.exp (t • N) *ᵥ v := by
    intro t
    rw [← Matrix.smul_mulVec, hexp]
    have hξv : ξ = η + v := by rw [hvdef]; abel
    have hS' : t • S = t • N + t • P := by rw [← smul_add, hNdef, sub_add_cancel]
    rw [hξv, Matrix.mulVec_add, exp_mulVec_of_mulVec_eq_zero (t • S) η (by
      rw [Matrix.smul_mulVec, hη, smul_zero]), hS',
      Matrix.exp_add_of_commute _ _ ((hcomm.smul_left t).smul_right t),
      ← Matrix.mulVec_mulVec, exp_mulVec_of_mulVec_eq_zero (t • P) v (by
      rw [Matrix.smul_mulVec, hPv, smul_zero])]
  have hlimv : Tendsto (fun t : ℝ => NormedSpace.exp (t • N) *ᵥ v) atTop (𝓝 0) := by
    have := ((continuous_id.matrix_mulVec (continuous_const (y := v))).tendsto
      (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).comp hlimN
    simpa [Function.comp_def] using this
  simpa only [add_zero] using
    ((tendsto_const_nhds (x := η)).add hlimv).congr fun t => (hfun t).symm

private lemma repr_exp_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (b : Module.Basis (Fin (n + 1)) ℝ E) (T : E →L[ℝ] E) (t : ℝ) (z : E) :
    ⇑(b.repr (NormedSpace.exp (t • T) z)) =
      NormedSpace.exp (t • LinearMap.toMatrix b b T.toLinearMap) *ᵥ ⇑(b.repr z) := by
  let f : (E →L[ℝ] E) →+* Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  have hfl : ∀ S, f S =
      (LinearMap.toMatrix b b).toLinearMap ((ContinuousLinearMap.coeLM ℝ) S) := by
    intro S; ext i j; simp [f, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hf : Continuous f := by
    have := LinearMap.continuous_of_finiteDimensional
      ((LinearMap.toMatrix b b).toLinearMap ∘ₗ
        (ContinuousLinearMap.coeLM ℝ : (E →L[ℝ] E) →ₗ[ℝ] (E →ₗ[ℝ] E)))
    exact this.congr fun S => (hfl S).symm
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) f hf (t • T)
    ((NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _)
  rw [hfl, hfl] at h
  simp only [LinearEquiv.coe_coe, ContinuousLinearMap.coeLM_apply, map_smul] at h
  calc
    ⇑(b.repr (NormedSpace.exp (t • T) z)) =
        LinearMap.toMatrix b b (NormedSpace.exp (t • T)).toLinearMap *ᵥ
          ⇑(b.repr z) :=
      (LinearMap.toMatrix_mulVec_repr b b
        (NormedSpace.exp (t • T)).toLinearMap z).symm
    _ = NormedSpace.exp (t • LinearMap.toMatrix b b T.toLinearMap) *ᵥ
        ⇑(b.repr z) := congrArg (fun M => M *ᵥ ⇑(b.repr z)) h

private lemma continuous_main {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (b : Module.Basis (Fin (n + 1)) ℝ E) (T : E →L[ℝ] E)
    (hT : (LinearMap.toMatrix b b T.toLinearMap).IsUpperTriangular)
    (hgap : ∀ i : Fin n, LinearMap.toMatrix b b T.toLinearMap i.castSucc i.castSucc <
      LinearMap.toMatrix b b T.toLinearMap (Fin.last n) (Fin.last n)) :
    ∃ y : E,
      T y = LinearMap.toMatrix b b T.toLinearMap (Fin.last n) (Fin.last n) • y ∧
      b.repr y (Fin.last n) = 1 ∧
      ∀ x : E, b.repr x (Fin.last n) = 1 →
        Tendsto (fun t : ℝ =>
          Real.exp (-t * LinearMap.toMatrix b b T.toLinearMap
            (Fin.last n) (Fin.last n)) • NormedSpace.exp (t • T) x)
          atTop (𝓝 y) := by
  set A := LinearMap.toMatrix b b T.toLinearMap with hAdef
  set a := A (Fin.last n) (Fin.last n)
  obtain ⟨eta, heta, hetal, hlim⟩ := matrix_main A hT hgap
  let y := b.equivFunL.symm eta
  have hrep : ⇑(b.repr y) = eta := b.equivFunL.apply_symm_apply eta
  have heigen : T y = a • y := by
    apply b.repr.injective
    ext i
    have hmul := congrFun (LinearMap.toMatrix_mulVec_repr b b T.toLinearMap y) i
    rw [ContinuousLinearMap.coe_coe, ← hAdef, hrep, heta] at hmul
    simpa [map_smul, Finsupp.smul_apply, hrep] using hmul.symm
  refine ⟨y, heigen, by rw [hrep, hetal], ?_⟩
  intro x hx
  have hkey : ∀ t : ℝ,
      b.equivFunL (Real.exp (-t * a) • NormedSpace.exp (t • T) x) =
        Real.exp (-t * a) • (NormedSpace.exp (t • A) *ᵥ ⇑(b.repr x)) := by
    intro t
    rw [map_smul]
    congr 1
    exact repr_exp_smul b T t x
  refine ((b.equivFunL.symm.continuous.tendsto eta).comp (hlim (⇑(b.repr x)) hx)).congr
    fun t => ?_
  rw [Function.comp_apply, ← hkey t, ContinuousLinearEquiv.symm_apply_apply]

end TriExp

namespace ContinuousLinearMap

open TriExp Matrix

/-- A normalized upper-triangular flow converges to its uniquely normalized
top-eigenvalue eigenvector. The proof was found by Aristotle (Harmonic). -/
theorem tendsto_exp_neg_mul_smul_exp_of_isUpperTriangular {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (b : Module.Basis (Fin (n + 1)) ℝ E) (T : E →L[ℝ] E)
    (hT : (LinearMap.toMatrix b b T.toLinearMap).IsUpperTriangular)
    (hgap : ∀ i : Fin n, LinearMap.toMatrix b b T.toLinearMap i.castSucc i.castSucc <
      LinearMap.toMatrix b b T.toLinearMap (Fin.last n) (Fin.last n))
    (x : E) (hx : b.repr x (Fin.last n) = 1) :
    ∃! y : E,
      T y = LinearMap.toMatrix b b T.toLinearMap (Fin.last n) (Fin.last n) • y ∧
      b.repr y (Fin.last n) = 1 ∧
      Tendsto
        (fun t : ℝ =>
          Real.exp (-t * LinearMap.toMatrix b b T.toLinearMap (Fin.last n) (Fin.last n)) •
            NormedSpace.exp (t • T) x)
        atTop (𝓝 y) := by
  obtain ⟨y, heigen, hy, hlim⟩ := continuous_main b T hT hgap
  refine ⟨y, ⟨heigen, hy, hlim x hx⟩, ?_⟩
  exact fun _ ⟨_, _, hz⟩ => tendsto_nhds_unique hz (hlim x hx)

/-- An upper-triangular flow with a strict top diagonal gap has a normalized
top eigenvector, and every vector with top coordinate one converges to it
under the normalized flow. The proof was found by Aristotle (Harmonic). -/
theorem exists_eigenvector_tendsto_of_isUpperTriangular {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (b : Module.Basis (Fin (n + 1)) ℝ E)
    (T : E →L[ℝ] E)
    (hT : (LinearMap.toMatrix b b T.toLinearMap).IsUpperTriangular)
    (hgap : ∀ i : Fin n,
      LinearMap.toMatrix b b T.toLinearMap i.castSucc i.castSucc <
        LinearMap.toMatrix b b T.toLinearMap (Fin.last n) (Fin.last n)) :
    ∃ y : E,
      T y = LinearMap.toMatrix b b T.toLinearMap
          (Fin.last n) (Fin.last n) • y ∧
      b.repr y (Fin.last n) = 1 ∧
      ∀ x : E, b.repr x (Fin.last n) = 1 →
        Tendsto (fun t : ℝ =>
          Real.exp (-t * LinearMap.toMatrix b b T.toLinearMap
            (Fin.last n) (Fin.last n)) • NormedSpace.exp (t • T) x)
          atTop (𝓝 y) :=
  continuous_main b T hT hgap

end ContinuousLinearMap
