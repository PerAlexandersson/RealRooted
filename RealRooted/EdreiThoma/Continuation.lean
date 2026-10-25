module

public import RealRooted.EdreiThoma.Identities
public import RealRooted.Mathlib.Analysis.Complex.EntireExponentialType

/-!
# Edrei--Thoma continuation

Edrei’s coefficient-growth argument produces an entire numerator after multiplying the
generating function by the limiting denominator product.  A separate quotient argument
then factors the resulting zero-free quotient as an exponential.
-/

@[expose] public section

open Polynomial Filter Topology Complex

noncomputable section

namespace RealRooted.EdreiThoma

private lemma summable_norm_genFun {a : ℕ → ℝ} (h : IsPolyaFreqSeq a) (h0 : a 0 = 1) {z : ℂ}
    (hz : a 1 * ‖z‖ < 1) : Summable fun n => ‖(a n : ℂ) * z ^ n‖ := by
  have := (IsPolyaFreqSeq.summable_genFun h h0 (by simpa using hz)).norm
  refine this.congr fun n => ?_
  simp [norm_pow, abs_of_nonneg (IsPolyaFreqSeq.nonneg h n)]

private lemma eventually_disc (c : ℝ) : ∀ᶠ z in 𝓝 (0 : ℂ), c * ‖z‖ < 1 := by
  exact (continuous_const.mul continuous_norm).continuousAt.eventually_lt continuousAt_const
    (by simp)

namespace E7

/-- Coefficient `k` of the formal product `(∑ a_n z^n) * P(z)`. -/
private def cp (a : ℕ → ℝ) (P : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), P.coeff l * a (k - l)

private lemma cp_add (a : ℕ → ℝ) (P P' : ℝ[X]) (k : ℕ) :
    cp a (P + P') k = cp a P k + cp a P' k := by
  simp [cp, add_mul, Finset.sum_add_distrib]

private lemma cp_sub (a : ℕ → ℝ) (P P' : ℝ[X]) (k : ℕ) :
    cp a (P - P') k = cp a P k - cp a P' k := by
  simp [cp, sub_mul, Finset.sum_sub_distrib]

private lemma cp_C_mul (a : ℕ → ℝ) (c : ℝ) (P : ℝ[X]) (k : ℕ) :
    cp a (C c * P) k = c * cp a P k := by
  simp [cp, Finset.mul_sum, mul_assoc]

private lemma cp_sum (a : ℕ → ℝ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) (k : ℕ) :
    cp a (∑ i ∈ s, P i) k = ∑ i ∈ s, cp a (P i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cp]
  | insert i s hi ih => simp only [Finset.sum_insert hi, cp_add, ih]

private lemma cp_X_mul_succ (a : ℕ → ℝ) (P : ℝ[X]) (k : ℕ) :
    cp a (X * P) (k + 1) = cp a P k := by
  simp [cp, Finset.sum_range_succ', coeff_X_mul]

private lemma cp_X_mul_zero (a : ℕ → ℝ) (P : ℝ[X]) : cp a (X * P) 0 = 0 := by
  simp [cp]

private lemma cp_one (a : ℕ → ℝ) (k : ℕ) : cp a 1 k = a k := by
  simp only [cp, coeff_one]
  rw [Finset.sum_eq_single 0] <;> simp_all

private lemma cp_C_mul_X_pow (a : ℕ → ℝ) (c : ℝ) (j k : ℕ) :
    cp a (C c * X ^ j) k = c * tc a ((k : ℤ) - j) := by
  simp only [cp, coeff_C_mul_X_pow]
  by_cases hj : j ≤ k
  · rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      unfold tc
      rw [ite_eq_left (by lia)]
      congr 2
      lia
    · intro b _ hb; simp [hb]
    · intro h; simp at h; lia
  · rw [Finset.sum_eq_zero]
    · unfold tc; rw [ite_eq_right (by lia)]; simp
    · intro b hb
      simp at hb
      rw [ite_eq_right (by lia)]; simp

/-- The `n × n` real matrix obtained from Edrei's matrix by deleting row `0` and column `j`. -/
private def subM (a : ℕ → ℝ) (m n : ℕ) (j : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j' =>
    tc a ((m : ℤ) + ((i.succ : Fin (n + 1)) : ℕ) -
      ((j.succAbove j' : Fin (n + 1)) : ℕ))

/-- The real matrix whose first row is `(a_{k-j})_j` and whose later rows are
`(a_{m+i-j})_j`. -/
private def Mk (a : ℕ → ℝ) (m n k : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 then tc a ((k : ℤ) - j) else tc a ((m : ℤ) + i - j)

private lemma det_QX (a : ℕ → ℝ) (m n : ℕ) :
    Matrix.det (Matrix.of fun (i j : Fin (n + 1)) =>
      if (i : ℕ) = 0 then (X : ℝ[X]) ^ (j : ℕ) else C (tc a ((m : ℤ) + i - j))) =
    ∑ j : Fin (n + 1), C ((-1) ^ (j : ℕ) * Matrix.det (subM a m n j)) * X ^ (j : ℕ) := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : (Matrix.of fun (i j : Fin (n + 1)) =>
      if (i : ℕ) = 0 then (X : ℝ[X]) ^ (j : ℕ) else C (tc a ((m : ℤ) + i - j))).submatrix
        Fin.succ j.succAbove = (C : ℝ →+* ℝ[X]).mapMatrix (subM a m n j) := by
    ext i j'
    simp [subM, Fin.succ_ne_zero]
  rw [hsub, ← RingHom.map_det]
  simp only [Matrix.of_apply, Fin.val_zero, ite_true, map_mul, map_pow, map_neg, map_one]
  ring

private lemma det_Mk (a : ℕ → ℝ) (m n k : ℕ) :
    Matrix.det (Mk a m n k) =
    ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * Matrix.det (subM a m n j) * tc a ((k : ℤ) - j) := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : (Mk a m n k).submatrix Fin.succ j.succAbove = subM a m n j := by
    ext i j'
    simp [subM, Mk, Fin.succ_ne_zero]
  rw [hsub]
  simp only [Mk, Matrix.of_apply, Fin.val_zero, ite_true]
  ring

/-- Coefficient `k` of `f · Q^{(m,n)}`. -/
private def pc (a : ℕ → ℝ) (m n k : ℕ) : ℝ := cp a (Q a m n) k

private lemma pc_eq_det (a : ℕ → ℝ) (m n k : ℕ) :
    pc a m n k = (1 / A a n m) * Matrix.det (Mk a m n k) := by
  rw [pc, Q, cp_C_mul, det_QX, cp_sum, det_Mk]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cp_C_mul_X_pow]

private lemma toeplitz_eq_tc (a : ℕ → ℝ) (i j : ℕ) :
    (toeplitz a) i j = tc a ((i : ℤ) - j) := by
  rw [toeplitz_apply]
  simp only [tc]
  split_ifs <;> congr 1 <;> lia

private lemma det_Mk_nonneg {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    {m n k : ℕ} (hk : k ≤ m) :
    0 ≤ Matrix.det (Mk a m n k) := by
  set r : Fin (n + 1) → ℕ := fun i => if (i : ℕ) = 0 then k else m + i with hr
  have hrm : StrictMono r := by
    intro i i' hii'
    have : (i : ℕ) < i' := hii'
    simp only [hr]
    split_ifs <;> lia
  have hcm : StrictMono (fun j : Fin (n + 1) => (j : ℕ)) := fun _ _ h => h
  have h := hpf (rows := r) (cols := fun j => (j : ℕ)) hrm hcm
  convert h using 2
  ext i j
  simp only [Mk, Matrix.of_apply, Matrix.submatrix_apply, toeplitz_eq_tc, hr]
  split_ifs <;> push_cast <;> ring_nf

private lemma pc_nonneg {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    (hP : ∀ n m, 0 < A a n m) {m n k : ℕ}
    (hk : k ≤ m) : 0 ≤ pc a m n k := by
  rw [pc_eq_det]
  exact mul_nonneg (div_nonneg zero_le_one (hP n m).le) (det_Mk_nonneg hpf hk)

private lemma pc_succ_eq_zero (a : ℕ → ℝ) (m n : ℕ) : pc a m (n + 1) (m + 1) = 0 := by
  rw [pc_eq_det, Matrix.det_zero_of_row_eq (i := 0) (j := 1) (by simp)
    (by funext j; simp [Mk]), mul_zero]

private lemma Q_eq_S_comp (a : ℕ → ℝ) (m n : ℕ) : Q a m n = (S a m n).comp (-X) := by
  rw [S, comp_neg_X_comp_neg_X]

private lemma coeff_comp_neg_X (P : ℝ[X]) (l : ℕ) :
    (P.comp (-X)).coeff l = (-1) ^ l * P.coeff l := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq]; ring
  | monomial i c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, ← mul_assoc,
      show ((-1 : ℝ[X]) ^ i) = C ((-1) ^ i) by simp, ← C_mul, coeff_C_mul_X_pow,
      coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

private lemma Q_succ_sub (a : ℕ → ℝ) (hA : ∀ n m, A a n m ≠ 0) (m n : ℕ) :
    Q a (m + 1) (n + 1) - Q a m (n + 1) = C (gam a m n) * X * Q a m n := by
  have h := congrArg (fun P => P.comp (-X)) (S_succ_shift_sub_eq hA m n)
  simp only [sub_comp, neg_comp, mul_comp, C_comp, X_comp] at h
  rw [Q_eq_S_comp, Q_eq_S_comp, Q_eq_S_comp, h]
  ring

private lemma pc_succ_sub (a : ℕ → ℝ) (hA : ∀ n m, A a n m ≠ 0) (m n k : ℕ) :
    pc a (m + 1) (n + 1) (k + 1) - pc a m (n + 1) (k + 1) = gam a m n * pc a m n k := by
  rw [pc, pc, ← cp_sub, Q_succ_sub a hA, mul_assoc, cp_C_mul, cp_X_mul_succ, pc]

private lemma pc_succ_sub_zero (a : ℕ → ℝ) (hA : ∀ n m, A a n m ≠ 0) (m n : ℕ) :
    pc a (m + 1) (n + 1) 0 = pc a m (n + 1) 0 := by
  rw [← sub_eq_zero, pc, pc, ← cp_sub, Q_succ_sub a hA, mul_assoc, cp_C_mul,
    cp_X_mul_zero, mul_zero]

private lemma A_zero (a : ℕ → ℝ) (m : ℕ) : A a 0 m = 1 := by
  simp [A]

private lemma A_one (a : ℕ → ℝ) (m : ℕ) : A a 1 m = a m := by
  simp [A, Matrix.det_unique, tc]

private lemma Q_zero (a : ℕ → ℝ) (m : ℕ) : Q a m 0 = 1 := by
  simp [Q, A_zero, Matrix.det_unique]

private lemma pc_zero (a : ℕ → ℝ) (m k : ℕ) : pc a m 0 k = a k := by
  rw [pc, Q_zero, cp_one]

/-- `w_n(m) = A^{(n+1)}_m / A^{(n)}_m`. -/
private def w (a : ℕ → ℝ) (n m : ℕ) : ℝ := A a (n + 1) m / A a n m

private lemma w_pos {a : ℕ → ℝ} (hP : ∀ n m, 0 < A a n m) (n m : ℕ) : 0 < w a n m :=
  div_pos (hP _ _) (hP _ _)

private lemma w_zero (a : ℕ → ℝ) (m : ℕ) : w a 0 m = a m := by
  simp [w, A_zero, A_one]

private lemma rr_eq {a : ℕ → ℝ} (hP : ∀ n m, 0 < A a n m) (m n : ℕ) :
    rr a m n = w a n (m + 1) / w a n m := by
  simp only [rr, w]
  field_simp [ne_of_gt (hP _ _)]

private lemma gam_eq {a : ℕ → ℝ} (hP : ∀ n m, 0 < A a n m) (m n : ℕ) :
    gam a m n = w a (n + 1) (m + 1) / w a n m := by
  simp only [gam, w]
  field_simp [ne_of_gt (hP _ _)]

private lemma gam_pos {a : ℕ → ℝ} (hP : ∀ n m, 0 < A a n m) (m n : ℕ) :
    0 < gam a m n := by
  rw [gam_eq hP]; exact div_pos (w_pos hP _ _) (w_pos hP _ _)

/-- `u k ≤ C (L + δ)^k` for every `δ > 0`. -/
private def GrowthBound (u : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ δ > 0, ∃ C, ∀ k, u k ≤ C * (L + δ) ^ k

private lemma ratio_limit_nonneg {w : ℕ → ℝ} (hw : ∀ m, 0 < w m) {L : ℝ}
    (h : Tendsto (fun m => w (m + 1) / w m) atTop (𝓝 L)) : 0 ≤ L :=
  ge_of_tendsto' h fun _ => (div_pos (hw _) (hw _)).le

private lemma growth_upper {w : ℕ → ℝ} (hw : ∀ m, 0 < w m) {L : ℝ}
    (h : Tendsto (fun m => w (m + 1) / w m) atTop (𝓝 L)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 < C ∧ ∀ m, w m ≤ C * (L + δ) ^ m := by
  have hL := ratio_limit_nonneg hw h
  have hq : 0 < L + δ := by linarith
  obtain ⟨M, hM⟩ :=
    eventually_atTop.1 (h.eventually (gt_mem_nhds (show L < L + δ by linarith)))
  set C := ∑ m ∈ Finset.range (M + 1), w m / (L + δ) ^ m with hC
  have hle : ∀ m ≤ M, w m / (L + δ) ^ m ≤ C := fun m hm =>
    Finset.single_le_sum (f := fun m => w m / (L + δ) ^ m)
      (fun i _ => (div_pos (hw i) (pow_pos hq i)).le) (Finset.mem_range.2 (by lia))
  have hCpos : 0 < C := lt_of_lt_of_le (div_pos (hw 0) (pow_pos hq 0)) (hle 0 (Nat.zero_le _))
  refine ⟨C, hCpos, fun m => ?_⟩
  rcases le_or_gt m M with hm | hm
  · have := hle m hm
    rwa [div_le_iff₀ (pow_pos hq m)] at this
  · induction m, hm.le using Nat.le_induction with
    | base => have := hle M le_rfl; rwa [div_le_iff₀ (pow_pos hq M)] at this
    | succ m hMm ih =>
      have h1 := hM m hMm
      rw [div_lt_iff₀ (hw m)] at h1
      have ih' : w m ≤ C * (L + δ) ^ m := by
        rcases eq_or_lt_of_le hMm with h | h
        · have := hle m h.ge; rwa [div_le_iff₀ (pow_pos hq m)] at this
        · exact ih h
      calc w (m + 1) ≤ (L + δ) * w m := h1.le
        _ ≤ (L + δ) * (C * (L + δ) ^ m) := mul_le_mul_of_nonneg_left ih' hq.le
        _ = C * (L + δ) ^ (m + 1) := by ring

private lemma growth_lower {w : ℕ → ℝ} (hw : ∀ m, 0 < w m) {L : ℝ}
    (h : Tendsto (fun m => w (m + 1) / w m) atTop (𝓝 L))
    {δ : ℝ} (hδ : 0 < δ) (hLδ : 0 < L - δ) :
    ∃ c, 0 < c ∧ ∀ m, c * (L - δ) ^ m ≤ w m := by
  have hq := hLδ
  obtain ⟨M, hM⟩ :=
    eventually_atTop.1 (h.eventually (lt_mem_nhds (show L - δ < L by linarith)))
  set S := ∑ m ∈ Finset.range (M + 1), (L - δ) ^ m / w m with hS
  have hle : ∀ m ≤ M, (L - δ) ^ m / w m ≤ S := fun m hm =>
    Finset.single_le_sum (f := fun m => (L - δ) ^ m / w m)
      (fun i _ => (div_pos (pow_pos hq i) (hw i)).le) (Finset.mem_range.2 (by lia))
  have hSpos : 0 < S := lt_of_lt_of_le (div_pos (pow_pos hq 0) (hw 0)) (hle 0 (Nat.zero_le _))
  have key : ∀ m ≤ M, S⁻¹ * (L - δ) ^ m ≤ w m := by
    intro m hm
    have := hle m hm
    rw [div_le_iff₀ (hw m)] at this
    rw [inv_mul_le_iff₀ hSpos]
    linarith [mul_comm S (w m)]
  refine ⟨S⁻¹, inv_pos.2 hSpos, fun m => ?_⟩
  rcases le_or_gt m M with hm | hm
  · exact key m hm
  · induction m, hm.le using Nat.le_induction with
    | base => exact key M le_rfl
    | succ m hMm ih =>
      have h1 := hM m hMm
      rw [lt_div_iff₀ (hw m)] at h1
      have ih' : S⁻¹ * (L - δ) ^ m ≤ w m := by
        rcases eq_or_lt_of_le hMm with h | h
        · exact key m h.ge
        · exact ih h
      calc S⁻¹ * (L - δ) ^ (m + 1) = (L - δ) * (S⁻¹ * (L - δ) ^ m) := by ring
        _ ≤ (L - δ) * w m := mul_le_mul_of_nonneg_left ih' hq.le
        _ ≤ w (m + 1) := h1.le

private lemma tail_geom {g : ℕ → ℝ} (hg0 : ∀ m, 0 ≤ g m) {D θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hg : ∀ m, g m ≤ D * θ ^ m) (j : ℕ) : ∑' μ, g (μ + j) ≤ D / (1 - θ) * θ ^ j := by
  have hgeo : Summable fun μ : ℕ => D * θ ^ j * θ ^ μ :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left _
  have hle : ∀ μ, g (μ + j) ≤ D * θ ^ j * θ ^ μ := fun μ => by
    rw [mul_assoc, ← pow_add, add_comm j]; exact hg _
  calc ∑' μ, g (μ + j) ≤ ∑' μ : ℕ, D * θ ^ j * θ ^ μ :=
        Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun μ => hg0 _) hle hgeo) hgeo
    _ = D / (1 - θ) * θ ^ j := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1]; ring

private lemma growth_step {u v γ W0 W1 : ℕ → ℝ} {b b' : ℝ}
    (hu : GrowthBound u b) (hu0 : ∀ k, 0 ≤ u k) (hvu : ∀ k, v k ≤ u k)
    (hvT : ∀ k, v (k + 1) ≤ u k * ∑' μ, γ (μ + k))
    (hγ0 : ∀ m, 0 ≤ γ m) (hW0 : ∀ m, 0 < W0 m) (hW1 : ∀ m, 0 < W1 m)
    (hγ : ∀ m, γ m = W1 (m + 1) / W0 m)
    (h0 : Tendsto (fun m => W0 (m + 1) / W0 m) atTop (𝓝 b))
    (h1 : Tendsto (fun m => W1 (m + 1) / W1 m) atTop (𝓝 b')) :
    GrowthBound v b' := by
  have hb := ratio_limit_nonneg hW0 h0
  have hb' := ratio_limit_nonneg hW1 h1
  intro δ hδ
  rcases le_or_gt b b' with hbb | hbb
  · obtain ⟨C, hC⟩ := hu δ hδ
    have hC0 : 0 ≤ C := by have := hC 0; simp at this; linarith [hu0 0]
    exact ⟨C, fun k => (hvu k).trans ((hC k).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) k) hC0))⟩
  · have hbpos : 0 < b := by linarith
    set η := min (δ * b / (2 * b + 2 * b' + δ)) ((b - b') / 4) with hηdef
    have hη0 : 0 < η := lt_min (by positivity) (by linarith)
    have hη1 : η ≤ δ * b / (2 * b + 2 * b' + δ) := min_le_left _ _
    have hη2 : η ≤ (b - b') / 4 := min_le_right _ _
    have hηb : η < b := by linarith
    set θ := (b' + η) / (b - η) with hθdef
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
    have hθ1 : θ < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have hkey : (b + η) * θ ≤ b' + δ := by
      rw [hθdef, mul_div_assoc', div_le_iff₀ (by linarith)]
      have : η * (2 * b + 2 * b' + δ) ≤ δ * b := by
        rw [le_div_iff₀ (by positivity)] at hη1; linarith
      nlinarith [mul_le_mul_of_nonneg_left hηb.le hη0.le]
    obtain ⟨C1, hC1, hC1b⟩ := growth_upper hW1 h1 hη0
    obtain ⟨c0, hc0, hc0b⟩ := growth_lower hW0 h0 hη0 (by linarith)
    set D := C1 * (b' + η) / c0 with hD
    have hD0 : 0 ≤ D := div_nonneg (mul_nonneg hC1.le (by linarith)) hc0.le
    have hγb : ∀ m, γ m ≤ D * θ ^ m := by
      intro m
      rw [hγ m, div_le_iff₀ (hW0 m)]
      have hbη : 0 < b - η := by linarith
      calc W1 (m + 1) ≤ C1 * (b' + η) ^ (m + 1) := hC1b _
        _ = D * θ ^ m * (c0 * (b - η) ^ m) := by
            rw [hD, hθdef, div_pow]; field_simp; ring
        _ ≤ D * θ ^ m * W0 m := mul_le_mul_of_nonneg_left (hc0b m) (by positivity)
    obtain ⟨C2, hC2⟩ := hu η hη0
    have hC20 : 0 ≤ C2 := by have := hC2 0; simp at this; linarith [hu0 0]
    set E := C2 * (D / (1 - θ)) with hE
    have hE0 : 0 ≤ E := mul_nonneg hC20 (div_nonneg hD0 (by linarith))
    have hv1 : ∀ k, v (k + 1) ≤ E * (b' + δ) ^ k := by
      intro k
      calc v (k + 1) ≤ u k * ∑' μ, γ (μ + k) := hvT k
        _ ≤ (C2 * (b + η) ^ k) * (D / (1 - θ) * θ ^ k) :=
            mul_le_mul (hC2 k) (tail_geom hγ0 hθ0 hθ1 hγb k) (tsum_nonneg fun μ => hγ0 _)
              (mul_nonneg hC20 (pow_nonneg (by linarith) _))
        _ = E * ((b + η) * θ) ^ k := by rw [hE, mul_pow]; ring
        _ ≤ E * (b' + δ) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hkey k) hE0
    refine ⟨max (u 0) (E / (b' + δ)), fun k => ?_⟩
    cases k with
    | zero => simpa using (hvu 0).trans (le_max_left _ _)
    | succ k =>
      have hpos : 0 < b' + δ := by linarith
      calc v (k + 1) ≤ E * (b' + δ) ^ k := hv1 k
        _ = E / (b' + δ) * (b' + δ) ^ (k + 1) := by field_simp; ring
        _ ≤ max (u 0) (E / (b' + δ)) * (b' + δ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

section Limits

variable {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a) (hP : ∀ n m, 0 < A a n m)
  {Sinf : ℕ → ℝ[X]} {β : ℕ → ℝ} (hS0 : Sinf 0 = 1)
  (hSlim : ∀ n k, Tendsto (fun m => (S a m n).coeff k) atTop (𝓝 ((Sinf n).coeff k)))
  (hβ : ∀ n, 0 ≤ β n) (hSrec : ∀ n, Sinf (n + 1) = (1 + C (β n) * X) * Sinf n)

include hSlim in
private lemma pc_tendsto (n k : ℕ) :
    Tendsto (fun m => pc a m n k) atTop (𝓝 (cp a ((Sinf n).comp (-X)) k)) := by
  simp only [pc, cp]
  refine tendsto_finsetSum _ fun l _ => ?_
  refine Tendsto.mul_const _ ?_
  simp only [Q_eq_S_comp, coeff_comp_neg_X]
  exact (hSlim n l).const_mul _

include hS0 in
private lemma pn_zero (k : ℕ) : cp a ((Sinf 0).comp (-X)) k = a k := by
  rw [hS0, one_comp, cp_one]

private lemma comp_rec (n : ℕ) (hSrec : ∀ n, Sinf (n + 1) = (1 + C (β n) * X) * Sinf n) :
    (Sinf (n + 1)).comp (-X) = (Sinf n).comp (-X) - C (β n) * (X * (Sinf n).comp (-X)) := by
  rw [hSrec, mul_comp, add_comp, one_comp, mul_comp, C_comp, X_comp]
  ring

include hSrec in
private lemma pn_succ_succ (n k : ℕ) :
    cp a ((Sinf (n + 1)).comp (-X)) (k + 1) =
      cp a ((Sinf n).comp (-X)) (k + 1) - β n * cp a ((Sinf n).comp (-X)) k := by
  rw [comp_rec n hSrec, cp_sub, cp_C_mul, cp_X_mul_succ]

include hSrec in
private lemma pn_succ_zero (n : ℕ) :
    cp a ((Sinf (n + 1)).comp (-X)) 0 = cp a ((Sinf n).comp (-X)) 0 := by
  rw [comp_rec n hSrec, cp_sub, cp_C_mul, cp_X_mul_zero, mul_zero, sub_zero]

include hpf hP hSlim in
private lemma pn_nonneg (n k : ℕ) : 0 ≤ cp a ((Sinf n).comp (-X)) k := by
  refine ge_of_tendsto (pc_tendsto hSlim n k) ?_
  filter_upwards [eventually_ge_atTop k] with m hm
  exact pc_nonneg hpf hP hm

include hpf hP hSlim hβ hSrec in
private lemma pn_succ_le (n k : ℕ) :
    cp a ((Sinf (n + 1)).comp (-X)) k ≤ cp a ((Sinf n).comp (-X)) k := by
  cases k with
  | zero => rw [pn_succ_zero hSrec]
  | succ k =>
    rw [pn_succ_succ hSrec]
    linarith [mul_nonneg (hβ n) (pn_nonneg hpf hP hSlim n k)]

include hpf hP hS0 hSlim in
private lemma pc_le_pn {μ n k : ℕ} (hk : k ≤ μ) :
    pc a μ n k ≤ cp a ((Sinf n).comp (-X)) k := by
  have hA : ∀ n m, A a n m ≠ 0 := fun n m => (hP n m).ne'
  cases n with
  | zero => rw [pc_zero, pn_zero hS0]
  | succ n =>
    set g : ℕ → ℝ := fun i => pc a (i + k) (n + 1) k with hg
    have hmono : Monotone g := by
      refine monotone_nat_of_le_succ fun i => ?_
      simp only [hg, show i + 1 + k = (i + k) + 1 by ring]
      cases k with
      | zero => simp only [add_zero]; rw [pc_succ_sub_zero a hA]
      | succ k =>
        have h1 := pc_succ_sub a hA (i + (k + 1)) n k
        have h2 := mul_nonneg (gam_pos hP (i + (k + 1)) n).le
          (pc_nonneg hpf hP (m := i + (k + 1)) (n := n) (k := k) (by lia))
        linarith
    have ht : Tendsto g atTop (𝓝 (cp a ((Sinf (n + 1)).comp (-X)) k)) :=
      (tendsto_add_atTop_iff_nat k).2 (pc_tendsto hSlim (n + 1) k)
    have := hmono.ge_of_tendsto ht (μ - k)
    simpa [hg, Nat.sub_add_cancel hk] using this

include hP in
private lemma pc_telescope (n k : ℕ) : ∀ M, k ≤ M →
    pc a M (n + 1) (k + 1) = ∑ μ ∈ Finset.Ico k M, gam a μ n * pc a μ n k := by
  have hA : ∀ n m, A a n m ≠ 0 := fun n m => (hP n m).ne'
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp [pc_succ_eq_zero]
  | succ M hkM ih =>
    rw [Finset.sum_Ico_succ_top hkM, ← ih]
    linarith [pc_succ_sub a hA M n k]

include hpf hP hS0 hSlim in
private lemma pn_succ_le_T (n k : ℕ) (sγ : Summable fun m => gam a m n) :
    cp a ((Sinf (n + 1)).comp (-X)) (k + 1) ≤
      cp a ((Sinf n).comp (-X)) k * ∑' μ, gam a (μ + k) n := by
  have sγ' : Summable fun μ => gam a (μ + k) n := (summable_nat_add_iff k).2 sγ
  have hT : ∀ M, k ≤ M → pc a M (n + 1) (k + 1) ≤
      cp a ((Sinf n).comp (-X)) k * ∑' μ, gam a (μ + k) n := by
    intro M hM
    rw [pc_telescope hP n k M hM]
    calc ∑ μ ∈ Finset.Ico k M, gam a μ n * pc a μ n k
        ≤ ∑ μ ∈ Finset.Ico k M, gam a μ n * cp a ((Sinf n).comp (-X)) k :=
          Finset.sum_le_sum fun μ hμ => mul_le_mul_of_nonneg_left
            (pc_le_pn hpf hP hS0 hSlim (Finset.mem_Ico.1 hμ).1) (gam_pos hP μ n).le
      _ = cp a ((Sinf n).comp (-X)) k * ∑ μ ∈ Finset.Ico k M, gam a μ n := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ cp a ((Sinf n).comp (-X)) k * ∑' μ, gam a (μ + k) n := by
          refine mul_le_mul_of_nonneg_left ?_ (pn_nonneg hpf hP hSlim n k)
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [add_comm k]
          exact sγ'.sum_le_tsum _ fun i _ => (gam_pos hP _ n).le
  exact le_of_tendsto (pc_tendsto hSlim (n + 1) (k + 1)) ((eventually_ge_atTop k).mono hT)

end Limits

private lemma hasSum_cp (a : ℕ → ℝ) {z : ℂ} {f : ℂ}
    (hf : HasSum (fun n => (a n : ℂ) * z ^ n) f)
    (P : ℝ[X]) : HasSum (fun k => (cp a P k : ℂ) * z ^ k) (f * aeval z P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [cp_add, Complex.ofReal_add, add_mul, map_add, mul_add]
    exact hp.add hq
  | monomial j c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [cp_C_mul_X_pow]
    refine (hasSum_nat_add_iff' j).1 ?_
    have hz : ∑ i ∈ Finset.range j, ((c * tc a ((i : ℤ) - j) : ℝ) : ℂ) * z ^ i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : (i : ℤ) - j < 0 := by simp at hi; lia
      have h2 : ¬ (0 ≤ (i : ℤ) - j) := by lia
      simp only [tc, h2, ite_false, mul_zero, Complex.ofReal_zero, zero_mul]
    rw [hz, sub_zero]
    have := hf.mul_left ((c : ℂ) * z ^ j)
    convert this using 1
    · funext k
      have : tc a (((k + j : ℕ) : ℤ) - j) = a k := by simp [tc]
      rw [this]; push_cast; ring
    · simp [map_mul]; ring

section Growth

variable {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a) (hP : ∀ n m, 0 < A a n m)
  {Sinf : ℕ → ℝ[X]} {β : ℕ → ℝ} (hS0 : Sinf 0 = 1)
  (hSlim : ∀ n k, Tendsto (fun m => (S a m n).coeff k) atTop (𝓝 ((Sinf n).coeff k)))
  (hβ : ∀ n, 0 ≤ β n) (hSrec : ∀ n, Sinf (n + 1) = (1 + C (β n) * X) * Sinf n)
  (hrr : ∀ n, Tendsto (fun m => rr a m n) atTop (𝓝 (β n)))
  (sγ : ∀ n, Summable fun m => gam a m n)

include hP hrr in
private lemma w_ratio_tendsto (n : ℕ) :
    Tendsto (fun m => w a n (m + 1) / w a n m) atTop (𝓝 (β n)) := by
  simpa only [rr_eq hP] using hrr n

include hpf hP hS0 hSlim hβ hSrec hrr sγ in
private lemma pn_growth (n : ℕ) : GrowthBound (fun k => cp a ((Sinf n).comp (-X)) k) (β n) := by
  induction n with
  | zero =>
    intro δ hδ
    obtain ⟨C, -, hC⟩ := growth_upper (w_pos hP 0) (w_ratio_tendsto hP hrr 0) hδ
    refine ⟨C, fun k => ?_⟩
    simpa only [pn_zero hS0, w_zero] using hC k
  | succ n ih =>
    exact growth_step ih (pn_nonneg hpf hP hSlim n) (pn_succ_le hpf hP hSlim hβ hSrec n)
      (fun k => pn_succ_le_T hpf hP hS0 hSlim n k (sγ n)) (fun m => (gam_pos hP m n).le)
      (w_pos hP n) (w_pos hP (n + 1)) (fun m => gam_eq hP m n)
      (w_ratio_tendsto hP hrr n) (w_ratio_tendsto hP hrr (n + 1))

include hSrec in
private lemma aeval_Qinf (z : ℂ) (n : ℕ) :
    aeval z ((Sinf n).comp (-X)) = (aeval z ((Sinf 0).comp (-X))) *
      ∏ j ∈ Finset.range n, (1 - (β j : ℂ) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [comp_rec n hSrec, Finset.prod_range_succ]
    simp only [map_sub, map_mul, aeval_C, aeval_X, ih]
    simp only [Complex.coe_algebraMap]
    ring

end Growth

end E7
/-- **Stage E7 (Edrei's coefficient-growth continuation).**  Let `a` be a PF sequence with `a 0 = 1`
and property (P).  Then there are `β ≥ 0` summable (Edrei's `β_n`, the limits of the `r_{mn}` of
`coeff_S_antitone_and_exists_limit`) and an everywhere convergent power series `∑ p_k z^k`
with nonnegative
coefficients such that near `0` it equals `(∑ a_n z^n) * ∏ (1 - β_j z)`.  In other words
`F = f * Q` is an entire function with nonnegative Taylor coefficients.

Proof route: Edrei (1953), pp. 89--92, assertions (vi)--(vii). -/
theorem exists_entire_series_mul_tprod {a : ℕ → ℝ} (hpf : IsPolyaFreqSeq a)
    (h0 : a 0 = 1) (hP : ∀ n m, 0 < A a n m) :
    ∃ (β p : ℕ → ℝ), (∀ j, 0 ≤ β j) ∧ Summable β ∧ (∀ k, 0 ≤ p k) ∧
      (∀ z : ℂ, Summable fun k => (p k : ℂ) * z ^ k) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), ∑' k, (p k : ℂ) * z ^ k =
        (∑' n, (a n : ℂ) * z ^ n) * ∏' j, (1 - (β j : ℂ) * z) := by
  obtain ⟨-, sγ, Sinf, β, hS0, hSlim, hβ, hrr, hSrec, sβ, -⟩ :=
    coeff_S_antitone_and_exists_limit hpf h0 hP
  set pn : ℕ → ℕ → ℝ := fun n k => E7.cp a ((Sinf n).comp (-X)) k with hpn
  have pn_nn : ∀ n k, 0 ≤ pn n k := E7.pn_nonneg hpf hP hSlim
  have pn_anti : ∀ k, Antitone (fun n => pn n k) := fun k =>
    antitone_nat_of_succ_le fun n => E7.pn_succ_le hpf hP hSlim hβ hSrec n k
  have pn_le_a : ∀ n k, pn n k ≤ a k := fun n k =>
    (pn_anti k (Nat.zero_le n)).trans (le_of_eq (E7.pn_zero hS0 k))
  have hbdd : ∀ k, BddBelow (Set.range fun n => pn n k) := fun k =>
    ⟨0, by rintro _ ⟨n, rfl⟩; exact pn_nn n k⟩
  set p : ℕ → ℝ := fun k => ⨅ n, pn n k with hp
  have hp_le : ∀ n k, p k ≤ pn n k := fun n k => ciInf_le (hbdd k) n
  have hp_nn : ∀ k, 0 ≤ p k := fun k => le_ciInf fun n => pn_nn n k
  have hp_t : ∀ k, Tendsto (fun n => pn n k) atTop (𝓝 (p k)) := fun k =>
    tendsto_atTop_ciInf (pn_anti k) (hbdd k)
  have hgrowth := E7.pn_growth hpf hP hS0 hSlim hβ hSrec hrr sγ
  refine ⟨β, p, hβ, sβ, hp_nn, fun z => ?_, ?_⟩
  · set δ : ℝ := 1 / (2 * (‖z‖ + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨n, hn⟩ := (sβ.tendsto_atTop_zero.eventually (gt_mem_nhds hδpos)).exists
    obtain ⟨C, hC⟩ := hgrowth n δ hδpos
    set ρ := (β n + δ) * ‖z‖ with hρ
    have hρ0 : 0 ≤ ρ := mul_nonneg (by linarith [hβ n]) (norm_nonneg _)
    have hρ1 : ρ < 1 := by
      have h1 : β n + δ < 2 * δ := by linarith
      have h2 : 2 * δ * ‖z‖ < 1 := by
        rw [hδ]; field_simp; linarith [norm_nonneg z]
      calc ρ ≤ 2 * δ * ‖z‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
        _ < 1 := h2
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left C)
      fun k => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hp_nn k)]
    calc p k * ‖z‖ ^ k ≤ pn n k * ‖z‖ ^ k :=
          mul_le_mul_of_nonneg_right (hp_le n k) (by positivity)
      _ ≤ C * (β n + δ) ^ k * ‖z‖ ^ k := mul_le_mul_of_nonneg_right (hC k) (by positivity)
      _ = C * ρ ^ k := by rw [hρ, mul_pow]; ring
  · filter_upwards [eventually_disc (a 1)] with z hz
    have hf := (IsPolyaFreqSeq.summable_genFun hpf h0 hz).hasSum
    have hpoly : ∀ n, HasSum (fun k => (pn n k : ℂ) * z ^ k)
        ((∑' n, (a n : ℂ) * z ^ n) * ∏ j ∈ Finset.range n, (1 - (β j : ℂ) * z)) := by
      intro n
      have := E7.hasSum_cp a hf ((Sinf n).comp (-X))
      rwa [E7.aeval_Qinf hSrec z n, hS0, one_comp, map_one, one_mul] at this
    have hdom := summable_norm_genFun hpf h0 hz
    have h1 : Tendsto (fun n => ∑' k, (pn n k : ℂ) * z ^ k) atTop
        (𝓝 (∑' k, (p k : ℂ) * z ^ k)) := by
      refine tendsto_tsum_of_dominated_convergence hdom (fun k => ?_)
        (Eventually.of_forall fun n k => ?_)
      · exact ((Complex.continuous_ofReal.tendsto _).comp (hp_t k)).mul_const _
      · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (pn_nn n k), Real.norm_of_nonneg (IsPolyaFreqSeq.nonneg hpf k)]
        exact mul_le_mul_of_nonneg_right (pn_le_a n k) (norm_nonneg _)
    have hmult : Multipliable fun j => (1 - (β j : ℂ) * z) := by
      have hs : Summable fun j => ‖((-β j : ℝ) : ℂ) * z‖ := by
        simpa [norm_mul, Complex.norm_real] using sβ.neg.norm.mul_right ‖z‖
      have := multipliable_one_add_of_summable hs
      convert this using 2 with j
      push_cast; ring
    have h2 : Tendsto (fun n => ∑' k, (pn n k : ℂ) * z ^ k) atTop
        (𝓝 ((∑' n, (a n : ℂ) * z ^ n) * ∏' j, (1 - (β j : ℂ) * z))) := by
      have e : (fun n => ∑' k, (pn n k : ℂ) * z ^ k) = fun n =>
          (∑' n, (a n : ℂ) * z ^ n) * ∏ j ∈ Finset.range n, (1 - (β j : ℂ) * z) :=
        funext fun n => (hpoly n).tsum_eq
      rw [e]
      exact hmult.hasProd.tendsto_prod_nat.const_mul _
    exact tendsto_nhds_unique h1 h2

/-- **Abstract quotient lemma (E8).** If `F, G, Q, N` are entire with
`F(z) G(-z) = Q(z) N(z)`, every zero of `N` is a non-zero of `G(-·)`, and every zero of `Q`
is a non-zero of `F`, then `F / N` is entire and zero-free, so
`F = e^φ N` and `G(-z) = e^{-φ} Q`. -/
theorem exists_exp_factorization_of_mul_neg_eq {F G Q N : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hQ : Differentiable ℂ Q) (hN : Differentiable ℂ N)
    (hFG : ∀ z, F z * G (-z) = Q z * N z)
    (hNz : ∀ z, N z = 0 → G (-z) ≠ 0) (hQz : ∀ z, Q z = 0 → F z ≠ 0) :
    ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ (∀ z, F z = Complex.exp (φ z) * N z) ∧
      ∀ z, G (-z) = Complex.exp (-φ z) * Q z := by
  classical
  set K : ℂ → ℂ := fun z => if N z ≠ 0 then F z / N z else Q z / G (-z) with hKdef
  have hGm : Differentiable ℂ (fun z => G (-z)) := hG.comp differentiable_neg
  have hFnz : ∀ z, N z ≠ 0 → F z ≠ 0 := by
    intro z hn hf
    apply hQz z ?_ hf
    exact (mul_eq_zero.mp (by rw [← hFG z, hf, zero_mul])).resolve_right hn
  have hQnz : ∀ z, N z = 0 → Q z ≠ 0 := by
    intro z hn hq
    have hg := hNz z hn
    apply hQz z hq
    exact (mul_eq_zero.mp (by rw [hFG z, hq, zero_mul])).resolve_right hg
  have hK : Differentiable ℂ K := by
    intro w
    by_cases hw : N w ≠ 0
    · have hev : ∀ᶠ z in 𝓝 w, N z ≠ 0 := (hN w).continuousAt.eventually_ne hw
      have : K =ᶠ[𝓝 w] fun z => F z / N z := hev.mono fun z hz => by simp [K, hz]
      exact (((hF w).div (hN w) hw)).congr_of_eventuallyEq this
    · push Not at hw
      have hg : G (-w) ≠ 0 := hNz w hw
      have hev : ∀ᶠ z in 𝓝 w, G (-z) ≠ 0 := (hGm w).continuousAt.eventually_ne hg
      have : K =ᶠ[𝓝 w] fun z => Q z / G (-z) := hev.mono fun z hz => by
        by_cases hn : N z ≠ 0
        · simp only [K, ite_eq_left hn]
          rw [div_eq_div_iff hn hz, hFG z]
        · simp [K, hn]
      exact ((hQ w).div (hGm w) hg).congr_of_eventuallyEq this
  have hK0 : ∀ z, K z ≠ 0 := by
    intro z
    by_cases hn : N z ≠ 0
    · simp only [K, ite_eq_left hn]
      exact div_ne_zero (hFnz z hn) hn
    · push Not at hn
      simp only [K, hn, ne_eq, not_true_eq_false, ite_false]
      exact div_ne_zero (hQnz z hn) (hNz z hn)
  obtain ⟨φ, hφ, hexp⟩ := hK.exists_log_of_ne_zero hK0
  refine ⟨φ, hφ, fun z => ?_, fun z => ?_⟩
  · rw [hexp z]
    by_cases hn : N z ≠ 0
    · simp only [K, ite_eq_left hn]; field_simp
    · push Not at hn
      have hg := hNz z hn
      have : F z * G (-z) = 0 := by rw [hFG z, hn, mul_zero]
      rw [hn, mul_zero]
      exact (mul_eq_zero.1 this).resolve_right hg
  · rw [Complex.exp_neg, hexp z]
    by_cases hn : N z ≠ 0
    · simp only [K, ite_eq_left hn]
      field_simp [hFnz z hn]
      linear_combination hFG z
    · push Not at hn
      have hg := hNz z hn
      simp only [K, hn, ne_eq, not_true_eq_false, ite_false]
      field_simp [hQnz z hn]


end RealRooted.EdreiThoma

