import RealRooted.FolkloreLemma
import RealRooted.SymmetricDecomposition.Definitions

/-!
# The `f`-polynomial transform

The Brändén--Solus coefficient transform, its root-coordinate transport, and
its real-rootedness equivalences for nonnegative-coefficient polynomials.
-/

open Polynomial Finset

noncomputable section

namespace RealRooted

/-- The `f`-polynomial transform from equation (2.2), written in coefficient
form to avoid rational-function substitution. -/
def fPolynomial (d : ℕ) (h : ℝ[X]) : ℝ[X] :=
  Finset.sum (Finset.range (d + 1))
    (fun k => C (h.coeff k) * X ^ k * (X + 1) ^ (d - k))

@[simp] lemma fPolynomial_zero (d : ℕ) :
    fPolynomial d 0 = 0 := by
  simp [fPolynomial]

@[simp] lemma fPolynomial_add (d : ℕ) (p q : ℝ[X]) :
    fPolynomial d (p + q) = fPolynomial d p + fPolynomial d q := by
  unfold fPolynomial
  have hterm :
      (fun x => C ((p + q).coeff x) * X ^ x * (X + 1) ^ (d - x)) =
        (fun x => C (p.coeff x) * X ^ x * (X + 1) ^ (d - x) +
          C (q.coeff x) * X ^ x * (X + 1) ^ (d - x)) := by
    funext x
    simp [coeff_add, add_mul]
  rw [hterm, Finset.sum_add_distrib]

@[simp] lemma fPolynomial_C_mul (d : ℕ) (a : ℝ) (p : ℝ[X]) :
    fPolynomial d (C a * p) = C a * fPolynomial d p := by
  unfold fPolynomial
  calc
    ∑ k ∈ Finset.range (d + 1),
        C ((C a * p).coeff k) * X ^ k * (X + 1) ^ (d - k)
      = ∑ k ∈ Finset.range (d + 1),
          C a * (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by grind
    _ = C a * ∑ k ∈ Finset.range (d + 1),
          C (p.coeff k) * X ^ k * (X + 1) ^ (d - k) := by rw [Finset.mul_sum]

lemma fPolynomial_succ_of_natDegree_le {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) p = (X + 1) * fPolynomial d p := by
  unfold fPolynomial
  rw [Finset.sum_range_succ]
  have htop : p.coeff (d + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (Nat.lt_succ_self d))
  rw [htop]
  simp only [map_zero, zero_mul, tsub_self, pow_zero, mul_one, add_zero]
  calc
    ∑ k ∈ Finset.range (d + 1),
        C (p.coeff k) * X ^ k * (X + 1) ^ (d + 1 - k)
      = ∑ k ∈ Finset.range (d + 1),
          (X + 1) * (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hsub : d + 1 - k = (d - k) + 1 := by lia
            grind
    _ = (X + 1) * ∑ k ∈ Finset.range (d + 1),
          C (p.coeff k) * X ^ k * (X + 1) ^ (d - k) := by rw [Finset.mul_sum]

lemma hasNonnegCoeffs_fPolynomial {d : ℕ} {h : ℝ[X]} (hh : HasNonnegCoeffs h) :
    HasNonnegCoeffs (fPolynomial d h) := by
  classical
  unfold fPolynomial
  refine Finset.induction_on (Finset.range (d + 1)) ?base ?step
  · exact hasNonnegCoeffs_zero
  · intro k s hk hs
    have hterm : HasNonnegCoeffs (C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)) := by
      have hXk : HasNonnegCoeffs (X ^ k) := hasNonnegCoeffs_X.pow k
      have hXp : HasNonnegCoeffs ((X + 1) ^ (d - k)) :=
        hasNonnegCoeffs_X_add_one.pow (d - k)
      have hprod : HasNonnegCoeffs (X ^ k * (X + 1) ^ (d - k)) := hXk.mul hXp
      simpa [mul_assoc] using nonnegCoeffs_C_mul (hh k) hprod
    simpa [Finset.sum_insert, hk] using hterm.add hs

lemma fPolynomial_monomial (d n : ℕ) (a : ℝ) :
    fPolynomial d (monomial n a) =
      if n ≤ d then C a * X ^ n * (X + 1) ^ (d - n) else 0 := by
  by_cases h : n ≤ d
  · have hn : n ∈ Finset.range (d + 1) := by simp_all
    unfold fPolynomial
    rw [Finset.sum_eq_single n]
    · simp_all
    · intro k hk hkn
      have hcoeff : (monomial n a).coeff k = 0 := by simp [coeff_monomial, mt Eq.symm hkn]
      simp_all
    · lia
  · unfold fPolynomial
    have hsum :
        ∑ k ∈ Finset.range (d + 1),
          C (((monomial n a).coeff k)) * X ^ k * (X + 1) ^ (d - k) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hklt : k < d + 1 := Finset.mem_range.mp hk
      have hkn : k ≠ n := by lia
      have hcoeff : (monomial n a).coeff k = 0 := by simp [coeff_monomial, mt Eq.symm hkn]
      simp_all
    lia

lemma fPolynomial_natDegree_le (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).natDegree ≤ d := by
  unfold fPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.range (d + 1))
    (f := fun k => C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)) ?_
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hleft : (C (h.coeff k) * X ^ k).natDegree ≤ k :=
    (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le k)
  have hright : ((X + 1) ^ (d - k) : ℝ[X]).natDegree ≤ d - k := by
    rw [show (X + 1 : ℝ[X]) = X + C (1 : ℝ) by simp]
    exact le_of_eq (Polynomial.natDegree_pow_X_add_C (n := d - k) (r := (1 : ℝ)))
  calc
    (C (h.coeff k) * X ^ k * (X + 1) ^ (d - k)).natDegree
        ≤ k + (d - k) := by
          simpa [mul_assoc] using
            (Polynomial.natDegree_mul_le_of_le hleft hright)
    _ = d := by lia

lemma coeff_fPolynomial_top (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).coeff d = ∑ k ∈ Finset.range (d + 1), h.coeff k := by
  unfold fPolynomial
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show C (h.coeff k) * X ^ k = Polynomial.monomial k (h.coeff k) by
    rw [Polynomial.C_mul_X_pow_eq_monomial]]
  have hdk : d = (d - k) + k := by lia
  rw [hdk, Polynomial.coeff_monomial_mul, Polynomial.coeff_X_add_one_pow]
  simp

lemma eval_one_eq_sum_coeffs_of_natDegree_le {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) :
    h.eval 1 = ∑ k ∈ Finset.range (d + 1), h.coeff k := by
  simp [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hd)]

lemma coeff_fPolynomial_top_eq_eval_one {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) :
    (fPolynomial d h).coeff d = h.eval 1 := by
  rw [coeff_fPolynomial_top]
  exact (eval_one_eq_sum_coeffs_of_natDegree_le hd).symm

lemma eval_neg_one_fPolynomial (d : ℕ) (h : ℝ[X]) :
    (fPolynomial d h).eval (-1) = h.coeff d * (-1) ^ d := by
  unfold fPolynomial
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single d]
  · simp
  · intro k hk hkd
    have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk_lt : k < d := lt_of_le_of_ne hk_le hkd
    have hsub_pos : 0 < d - k := Nat.sub_pos_of_lt hk_lt
    simp [Polynomial.eval_mul, hsub_pos.ne']
  · simp

lemma eval_one_pos_of_hasNonnegCoeffs {h : ℝ[X]}
    (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) :
    0 < h.eval 1 := by
  have heval :
      h.eval 1 = ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i := by
    simpa [one_pow, mul_one] using (Polynomial.eval_eq_sum_range (p := h) (x := (1 : ℝ)))
  rw [heval]
  have htop_coeff : 0 < h.coeff h.natDegree := by
    rw [coeff_natDegree]
    exact hh.pos_leadingCoeff h0
  have hle :
      h.coeff h.natDegree ≤
        ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i :=
    Finset.single_le_sum
      (fun i hi => hh i)
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  grind

lemma eval_pos_of_hasNonnegCoeffs_of_pos {h : ℝ[X]}
    (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) {x : ℝ} (hx : 0 < x) :
    0 < h.eval x := by
  have heval :
      h.eval x = ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i * x ^ i :=
    Polynomial.eval_eq_sum_range (p := h) (x := x)
  rw [heval]
  have hpow_pos : 0 < x ^ h.natDegree := pow_pos hx _
  have htop_coeff : 0 < h.leadingCoeff := hh.pos_leadingCoeff h0
  have htop_term : 0 < h.leadingCoeff * x ^ h.natDegree :=
    mul_pos htop_coeff hpow_pos
  have hle :
      h.leadingCoeff * x ^ h.natDegree ≤
        ∑ i ∈ Finset.range (h.natDegree + 1), h.coeff i * x ^ i :=
    Finset.single_le_sum
      (s := Finset.range (h.natDegree + 1))
      (f := fun i => h.coeff i * x ^ i)
      (fun i hi => mul_nonneg (hh i) (pow_nonneg hx.le _))
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  grind

lemma fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) :
    (fPolynomial d h).natDegree = d := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (fPolynomial_natDegree_le d h)
  rw [coeff_fPolynomial_top_eq_eval_one hd]
  exact ne_of_gt (eval_one_pos_of_hasNonnegCoeffs hh h0)

lemma leadingCoeff_fPolynomial_eq_eval_one {d : ℕ} {h : ℝ[X]}
    (hd : h.natDegree ≤ d) (hh : HasNonnegCoeffs h) (h0 : h ≠ 0) :
    (fPolynomial d h).leadingCoeff = h.eval 1 := by
  rw [Polynomial.leadingCoeff, fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero hd hh h0]
  exact coeff_fPolynomial_top_eq_eval_one hd

lemma fPolynomial_X_mul_succ (d : ℕ) (p : ℝ[X]) :
    fPolynomial (d + 1) (X * p) = X * fPolynomial d p := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [show X * (p + q) = X * p + X * q by grind]
    rw [fPolynomial_add, fPolynomial_add, hp, hq]
    ring
  · intro n a
    by_cases h : n ≤ d
    · have hs : n + 1 ≤ d + 1 := Nat.succ_le_succ h
      have hf : fPolynomial d (monomial n a) = C a * X ^ n * (X + 1) ^ (d - n) := by
        simpa [h] using (fPolynomial_monomial d n a)
      rw [Polynomial.X_mul_monomial, fPolynomial_monomial, hf]
      grind
    · have hs : ¬ n + 1 ≤ d + 1 := by lia
      rw [Polynomial.X_mul_monomial, fPolynomial_monomial]
      rw [show fPolynomial d (monomial n a) = 0 by simpa [h] using (fPolynomial_monomial d n a)]
      lia

lemma fPolynomial_pad_by_X_add_one_pow {m d : ℕ} {p : ℝ[X]}
    (hm : p.natDegree ≤ m) (hmd : m ≤ d) :
    fPolynomial d p = (X + 1) ^ (d - m) * fPolynomial m p := by
  have hpad : ∀ n : ℕ, fPolynomial (m + n) p = (X + 1) ^ n * fPolynomial m p := by
    intro n
    induction n with
    | zero =>
        lia
    | succ n ih =>
        have hm' : p.natDegree ≤ m + n := le_trans hm (Nat.le_add_right _ _)
        rw [show m + n.succ = (m + n) + 1 by lia]
        rw [fPolynomial_succ_of_natDegree_le hm', ih]
        grind
  grind

lemma fPolynomial_X_sub_C_mul_succ (d : ℕ) (r : ℝ) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      (C (1 - r) * X - C r) * fPolynomial d p := by
  have hmul : (X - C r) * p = X * p + C (-r) * p := by grind
  calc
    fPolynomial (d + 1) ((X - C r) * p)
      = fPolynomial (d + 1) (X * p + C (-r) * p) := by lia
    _ = X * fPolynomial d p + C (-r) * fPolynomial (d + 1) p := by
          rw [fPolynomial_add, fPolynomial_X_mul_succ, fPolynomial_C_mul]
    _ = X * fPolynomial d p + C (-r) * ((X + 1) * fPolynomial d p) := by
          rw [fPolynomial_succ_of_natDegree_le hp]
    _ = (C (1 - r) * X - C r) * fPolynomial d p := by grind

lemma transformedRoot_nonpos {r : ℝ} (hr : r ≤ 0) :
    r / (1 - r) ≤ 0 := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1r_inv_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr h1r_pos.le
  have hmul_nonpos : r * (1 - r)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hr h1r_inv_nonneg
  lia

/-- Inverse Möbius map to `r ↦ r / (1-r)` on `(-1, ∞)`. -/
def untransformRoot (x : ℝ) : ℝ := x / (1 + x)

lemma untransformRoot_nonpos {x : ℝ} (hx1 : -1 < x) (hx0 : x ≤ 0) :
    untransformRoot x ≤ 0 := by
  have h1x_pos : 0 < 1 + x := by linarith
  have h1x_inv_nonneg : 0 ≤ (1 + x)⁻¹ := inv_nonneg.mpr h1x_pos.le
  simpa [untransformRoot, div_eq_mul_inv] using
    mul_nonpos_of_nonpos_of_nonneg hx0 h1x_inv_nonneg

lemma transformedRoot_untransformRoot {x : ℝ} (hx1 : -1 < x) :
    untransformRoot x / (1 - untransformRoot x) = x := by
  have h1x_ne : 1 + x ≠ 0 := by linarith
  have hden : 1 - x / (1 + x) = (1 : ℝ) / (1 + x) := by grind
  rw [untransformRoot, hden]
  simp_all

lemma untransformRoot_transformedRoot {r : ℝ} (hr : r ≤ 0) :
    untransformRoot (r / (1 - r)) = r := by
  have h1r_ne : 1 - r ≠ 0 := by linarith
  have hden : 1 + r / (1 - r) = (1 : ℝ) / (1 - r) := by grind
  rw [untransformRoot, hden]
  simp_all

lemma eval_fPolynomial_eq_mul_eval_untransform {d : ℕ} {p : ℝ[X]}
    (hd : p.natDegree ≤ d) {x : ℝ} (hx : x ≠ -1) :
    (fPolynomial d p).eval x = (1 + x) ^ d * p.eval (untransformRoot x) := by
  have h1x_ne : 1 + x ≠ 0 := by grind
  unfold fPolynomial
  rw [Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hd)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc
    (C (p.coeff k) * X ^ k * (X + 1) ^ (d - k)).eval x
        = p.coeff k * x ^ k * (x + 1) ^ (d - k) := by simp
    _ = p.coeff k * x ^ k * (1 + x) ^ (d - k) := by grind
    _ = p.coeff k * (x ^ k * (1 + x) ^ (d - k)) := by grind
    _ = p.coeff k * ((1 + x) ^ d * (untransformRoot x) ^ k) := by
          have hterm :
              (1 + x) ^ d * (untransformRoot x) ^ k = x ^ k * (1 + x) ^ (d - k) := by
            calc
              (1 + x) ^ d * (untransformRoot x) ^ k
                  = (1 + x) ^ d * (x / (1 + x)) ^ k := by simp [untransformRoot]
              _ = (1 + x) ^ d * (x ^ k * ((1 + x) ^ k)⁻¹) := by
                    rw [div_eq_mul_inv, mul_pow, inv_pow]
              _ = x ^ k * ((1 + x) ^ d * ((1 + x) ^ k)⁻¹) := by grind
              _ = x ^ k * (1 + x) ^ (d - k) := by rw [← pow_sub₀ (1 + x) h1x_ne hk_le]
          lia
    _ = (1 + x) ^ d * (p.coeff k * (untransformRoot x) ^ k) := by ring

lemma neg_one_lt_transformedRoot {r : ℝ} (hr : r ≤ 0) :
    -1 < r / (1 - r) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have hmul : (-1 : ℝ) * (1 - r) < r := by simp
  exact (lt_div_iff₀ h1r_pos).2 hmul

lemma untransformRoot_mono_of_neg_one_lt {x y : ℝ}
    (hxy : x ≤ y) (hx1 : -1 < x) :
    untransformRoot x ≤ untransformRoot y := by
  have hy1 : -1 < y := lt_of_lt_of_le hx1 hxy
  have h1x_pos : 0 < 1 + x := by linarith
  have h1y_pos : 0 < 1 + y := by linarith
  rw [untransformRoot, untransformRoot, div_le_div_iff₀ h1x_pos h1y_pos]
  nlinarith

lemma transformedRoot_mono_of_nonpos {r s : ℝ}
    (hrs : r ≤ s) (hs : s ≤ 0) :
    r / (1 - r) ≤ s / (1 - s) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1s_pos : 0 < 1 - s := by linarith
  rw [div_le_div_iff₀ h1r_pos h1s_pos]
  nlinarith

lemma pairwise_map_transformedRoot_of_nonpos :
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) →
      (∀ r ∈ rs, r ≤ 0) →
      (rs.map (fun r : ℝ => r / (1 - r))).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | r :: rs, hrs, hnonpos => by
      rw [List.pairwise_cons] at hrs
      rw [List.map, List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact transformedRoot_mono_of_nonpos (hrs.1 z hz) (hnonpos z (by simp_all))
      · exact pairwise_map_transformedRoot_of_nonpos hrs.2 (fun z hz => hnonpos z (by simp_all))

lemma listInterlaces_map_transformedRoot_of_nonpos :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ r ∈ rs, r ≤ 0) →
      ListInterlaces (ss.map (fun r : ℝ => r / (1 - r)))
        (rs.map (fun r : ℝ => r / (1 - r)))
  | [], [], _, _ => by simp_all
  | [], [_], _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hnonpos => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      have hs_nonpos : s ≤ 0 := le_trans hsr₂ (hnonpos r₂ (by simp))
      refine ⟨?_, ?_, ?_⟩
      · exact transformedRoot_mono_of_nonpos hr₁s hs_nonpos
      · exact transformedRoot_mono_of_nonpos hsr₂ (hnonpos r₂ (by simp))
      · exact listInterlaces_map_transformedRoot_of_nonpos htail
          (fun r hr => hnonpos r (by simp_all))
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_transformedRoot_of_nonpos :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ r ∈ rs, r ≤ 0) →
      ListAlternates (ss.map (fun r : ℝ => r / (1 - r)))
        (rs.map (fun r : ℝ => r / (1 - r)))
  | [], [], _, _ => by simp_all
  | s :: ss, r :: rs, h, hnonpos => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨transformedRoot_mono_of_nonpos hsr (hnonpos r (by simp)),
        listInterlaces_map_transformedRoot_of_nonpos htail (fun t ht => hnonpos t (by lia))⟩
  | [], _ :: _, h, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _ => by simp [ListAlternates] at h

lemma listAlternates_neg_one_cons_map_of_listInterlaces_of_nonpos
    {ss : List ℝ} {r₁ : ℝ} {rs : List ℝ}
    (hint : ListInterlaces ss (r₁ :: rs))
    (hnonpos : ∀ r ∈ (r₁ :: rs), r ≤ 0) :
    ListAlternates ((-1) :: ss.map (fun r : ℝ => r / (1 - r)))
      ((r₁ :: rs).map (fun r : ℝ => r / (1 - r))) := by
  refine ⟨le_of_lt (neg_one_lt_transformedRoot (hnonpos r₁ (by simp))), ?_⟩
  exact listInterlaces_map_transformedRoot_of_nonpos hint hnonpos

lemma pairwise_map_untransformRoot_of_neg_one_lt :
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) →
      (∀ r ∈ rs, -1 < r) →
      (rs.map untransformRoot).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | r :: rs, hrs, hgt => by
      rw [List.pairwise_cons] at hrs
      rw [List.map, List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact untransformRoot_mono_of_neg_one_lt (hrs.1 z hz) (hgt r (by simp))
      · exact pairwise_map_untransformRoot_of_neg_one_lt hrs.2 (fun z hz => hgt z (by simp_all))

lemma listInterlaces_map_untransformRoot_of_neg_one_lt :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      (∀ s ∈ ss, -1 < s) →
      (∀ r ∈ rs, -1 < r) →
      ListInterlaces (ss.map untransformRoot) (rs.map untransformRoot)
  | [], [], _, _, _ => by simp_all
  | [], [_], _, _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, hss, hrs => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      refine ⟨?_, ?_, ?_⟩
      · exact untransformRoot_mono_of_neg_one_lt hr₁s (hrs r₁ (by simp))
      · exact untransformRoot_mono_of_neg_one_lt hsr₂ (hss s (by simp))
      · exact listInterlaces_map_untransformRoot_of_neg_one_lt htail
          (fun s hs => hss s (by simp_all))
          (fun r hr => hrs r (by simp_all))
  | [], _ :: _ :: _, h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_untransformRoot_of_neg_one_lt :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      (∀ s ∈ ss, -1 < s) →
      (∀ r ∈ rs, -1 < r) →
      ListAlternates (ss.map untransformRoot) (rs.map untransformRoot)
  | [], [], _, _, _ => by simp_all
  | s :: ss, r :: rs, h, hss, hrs => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨untransformRoot_mono_of_neg_one_lt hsr (hss s (by simp)),
        listInterlaces_map_untransformRoot_of_neg_one_lt htail
          (fun t ht => hss t (by simp_all))
          (fun t ht => hrs t (by lia))⟩
  | [], _ :: _, h, _, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _, _ => by simp [ListAlternates] at h

lemma transformedLinearFactor_eq_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    C (1 - r) * X - C r = C (1 - r) * (X - C (r / (1 - r))) := by
  grind

lemma transformedLinearFactor_eq {r : ℝ} (h1r_ne : 1 - r ≠ 0) :
    C (1 - r) * X - C r = C (1 - r) * (X - C (r / (1 - r))) := by
  grind

lemma fPolynomial_X_sub_C_mul_succ' (d : ℕ) {r : ℝ} (hr : r ≤ 0) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      C (1 - r) * (X - C (r / (1 - r))) * fPolynomial d p := by
  rw [fPolynomial_X_sub_C_mul_succ d r hp, transformedLinearFactor_eq_of_nonpos hr]

lemma fPolynomial_X_sub_C_mul_succ_of_ne_one (d : ℕ) {r : ℝ} (hr1 : r ≠ 1) {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    fPolynomial (d + 1) ((X - C r) * p) =
      C (1 - r) * (X - C (r / (1 - r))) * fPolynomial d p := by
  have h1r_ne : 1 - r ≠ 0 := by grind
  rw [fPolynomial_X_sub_C_mul_succ d r hp, transformedLinearFactor_eq h1r_ne]

lemma fPolynomial_natDegree_factor_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    ∃ q, p = (X - C r) * q ∧
      fPolynomial p.natDegree p =
        C (1 - r) * (X - C (r / (1 - r))) * fPolynomial q.natDegree q := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hq' : p = (X - C r) * q := by lia
  have hq_ne : q ≠ 0 := by simp_all
  have hr_mem : r ∈ p.roots := (mem_roots hp_ne).mpr hr
  have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp_splits hpnn r hr_mem
  have hdeg_eq : p.natDegree = q.natDegree + 1 := by
    simpa [Nat.add_comm] using
      (show p.natDegree = 1 + q.natDegree by
        rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C])
  refine ⟨q, hq', ?_⟩
  rw [hdeg_eq, hq']
  simpa using fPolynomial_X_sub_C_mul_succ' q.natDegree hr_nonpos (p := q) le_rfl

lemma isRoot_transformedRoot_fPolynomial_natDegree_of_isRoot
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    (fPolynomial p.natDegree p).IsRoot (r / (1 - r)) := by
  rcases fPolynomial_natDegree_factor_of_isRoot hp_ne hp_splits hpnn hr with ⟨q, _, hfac⟩
  simp_all

lemma isRoot_transformedRoot_fPolynomial_of_isRoot
    {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) {r : ℝ}
    (hr : p.IsRoot r) :
    (fPolynomial d p).IsRoot (r / (1 - r)) := by
  have hroot_min :
      (fPolynomial p.natDegree p).IsRoot (r / (1 - r)) :=
    isRoot_transformedRoot_fPolynomial_natDegree_of_isRoot hp_ne hp_splits hpnn hr
  rw [Polynomial.IsRoot.def, fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) le_rfl hd]
  simp_all

lemma isRoot_neg_one_fPolynomial_of_natDegree_lt
    {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree < d) :
    (fPolynomial d p).IsRoot (-1) := by
  simp [Polynomial.IsRoot.def, eval_neg_one_fPolynomial,
    Polynomial.coeff_eq_zero_of_natDegree_lt hpd]

lemma not_isRoot_neg_one_fPolynomial_of_natDegree_eq_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hdeg : p.natDegree = d)
    (hp0 : p ≠ 0) :
    ¬ (fPolynomial d p).IsRoot (-1) := by
  rw [Polynomial.IsRoot.def, eval_neg_one_fPolynomial]
  have hcoeff_ne : p.coeff d ≠ 0 := by
    have hcoeff_eq : p.coeff d = p.leadingCoeff := by simpa [hdeg] using (coeff_natDegree (p := p))
    simp_all
  simp_all

private lemma isRealRooted_transformed_linear {r : ℝ} (hr : r ≤ 0) :
    ((C (1 - r) * X - C r) ≠ 0 ∧ (C (1 - r) * X - C r).Splits) := by
  have h1r_pos : 0 < 1 - r := by linarith
  have h1r_ne : 1 - r ≠ 0 := ne_of_gt h1r_pos
  have hmul : (1 - r) * (r / (1 - r)) = r := by grind
  have hfac :
      C (1 - r) * X - C r =
        C (1 - r) * (X - C (r / (1 - r))) := by
    grind
  rw [hfac]
  exact isRealRooted_C_mul (isRealRooted_X_sub_C (r / (1 - r))).1
    (isRealRooted_X_sub_C (r / (1 - r))).2 h1r_ne

/-- The Brändén--Solus `f`-polynomial transform preserves real-rootedness on
nonnegative-coefficient inputs of degree at most `d`. -/
theorem isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hpdeg : p.natDegree ≤ d)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    ((fPolynomial d p) ≠ 0 ∧ (fPolynomial d p).Splits) := by
  induction d generalizing p with
  | zero =>
      have hpC : p = C (p.coeff 0) := by simpa using (Polynomial.eq_C_of_natDegree_le_zero hpdeg)
      rw [hpC]
      have hfp : fPolynomial 0 (C (p.coeff 0)) = C (p.coeff 0) := by simp [fPolynomial]
      lia
  | succ d ih =>
      by_cases hpd : p.natDegree ≤ d
      · rw [fPolynomial_succ_of_natDegree_le hpd]
        have hX1 : ((X + 1 : ℝ[X]) ≠ 0 ∧ (X + 1 : ℝ[X]).Splits) := by
          simpa using (isRealRooted_X_sub_C (-1 : ℝ))
        simp_all
      · have hpdeg_eq : p.natDegree = d + 1 := by lia
        have hroots_pos : 0 < p.roots.card := by
          rw [card_roots_of_splits hp_splits, hpdeg_eq]
          lia
        obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hr_root : p.IsRoot r := (mem_roots hp_ne).mp hr_mem
        have hr_nonpos : r ≤ 0 :=
          roots_nonpos_of_nonneg_coeffs hp_splits hpnn r hr_mem
        obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
        have hq' : p = (X - C r) * q := by lia
        have hq_dvd : q ∣ p := ⟨X - C r, by grind⟩
        have hq_ne : q ≠ 0 := by simp_all
        have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hp_ne hp_splits hq_ne hq_dvd
        have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp_ne
        have hq_pos : HasPosLeadingCoeff q := by
          apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
          lia
        have hq_nonneg : HasNonnegCoeffs q :=
          hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
            hp_ne hp_splits hpnn hq_rr.1 hq_rr.2 hq_pos hq_dvd
        have hqdeg : q.natDegree ≤ d := by
          have hmuldeg : p.natDegree = 1 + q.natDegree := by
            rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          lia
        rw [hq', fPolynomial_X_sub_C_mul_succ d r hqdeg]
        have hlin := isRealRooted_transformed_linear hr_nonpos
        simp_all

theorem roots_fPolynomial_natDegree_eq_map_of_isRealRooted_of_hasNonnegCoeffs
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    (fPolynomial p.natDegree p).roots =
      p.roots.map (fun r : ℝ => r / (1 - r)) := by
  have hP :
      ∀ n (p : ℝ[X]), p.natDegree = n → (p ≠ 0 ∧ p.Splits) → HasNonnegCoeffs p →
        (fPolynomial p.natDegree p).roots =
          p.roots.map (fun r : ℝ => r / (1 - r)) := by
    intro n
    exact Nat.strong_induction_on n (fun n ih =>
      show ∀ (p : ℝ[X]), p.natDegree = n → (p ≠ 0 ∧
        p.Splits) → HasNonnegCoeffs p →
        (fPolynomial p.natDegree p).roots =
          p.roots.map (fun r : ℝ => r / (1 - r)) from by
        intro p hpdeg hp hpnn
        by_cases hn : n = 0
        · have hp0 : p.natDegree = 0 := by lia
          have hpC : p = C (p.coeff 0) := by
            simpa [hp0] using
              (Polynomial.eq_C_of_natDegree_le_zero (show p.natDegree ≤ 0 by lia))
          have hcoeff0_ne : p.coeff 0 ≠ 0 := by grind
          rw [hpC]
          simp [fPolynomial]
        · have hroots_pos : 0 < p.roots.card := by
            rw [card_roots_of_splits hp.2, hpdeg]
            lia
          obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
          have hr_root : p.IsRoot r := (mem_roots hp.1).mp hr_mem
          obtain ⟨q, hq', hfac⟩ :=
            fPolynomial_natDegree_factor_of_isRoot hp.1 hp.2 hpnn hr_root
          have hq_dvd : q ∣ p := ⟨X - C r, by grind⟩
          have hq_ne : q ≠ 0 := by simp_all
          have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hp.2 hpnn r hr_mem
          have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hp.1 hp.2 hq_ne hq_dvd
          have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp.1
          have hq_pos : HasPosLeadingCoeff q := by
            apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
            lia
          have hq_nonneg : HasNonnegCoeffs q :=
            hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
              hp.1 hp.2 hpnn hq_rr.1 hq_rr.2 hq_pos hq_dvd
          have hmuldeg : n = q.natDegree + 1 := by
            rw [← hpdeg, hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
            lia
          have hqdeg_lt : q.natDegree < n := by lia
          have hqdeg_eq : q.natDegree = n - 1 := by lia
          have ihq :
              (fPolynomial q.natDegree q).roots =
                q.roots.map (fun s : ℝ => s / (1 - s)) :=
            ih q.natDegree hqdeg_lt q rfl hq_rr hq_nonneg
          have h1r_ne : 1 - r ≠ 0 := by linarith
          have hqf_rr :
              ((fPolynomial q.natDegree q) ≠ 0 ∧ (fPolynomial q.natDegree q).Splits) :=
            isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs le_rfl hq_rr.1 hq_rr.2
              hq_nonneg
          have hroots_f :
              (fPolynomial p.natDegree p).roots =
                ({r / (1 - r)} : Multiset ℝ) + (fPolynomial q.natDegree q).roots := by
            rw [hfac, mul_assoc, roots_C_mul _ h1r_ne,
              roots_mul (mul_ne_zero (X_sub_C_ne_zero (r / (1 - r))) hqf_rr.1), roots_X_sub_C]
          have hp_roots : p.roots = ({r} : Multiset ℝ) + q.roots := by
            rw [hq', roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hq_ne), roots_X_sub_C]
          calc
            (fPolynomial p.natDegree p).roots
                = ({r / (1 - r)} : Multiset ℝ) + (fPolynomial q.natDegree q).roots := hroots_f
            _ = ({r / (1 - r)} : Multiset ℝ) + q.roots.map (fun s : ℝ => s / (1 - s)) := by lia
            _ = ({r} : Multiset ℝ).map (fun s : ℝ => s / (1 - s)) +
                  q.roots.map (fun s : ℝ => s / (1 - s)) := by simp
            _ = (({r} : Multiset ℝ) + q.roots).map (fun s : ℝ => s / (1 - s)) := by simp
            _ = p.roots.map (fun s : ℝ => s / (1 - s)) := by lia)
  simp_all

theorem roots_fPolynomial_eq_padding_map_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hd : p.natDegree ≤ d)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    (fPolynomial d p).roots =
      Multiset.replicate (d - p.natDegree) (-1) +
        p.roots.map (fun r : ℝ => r / (1 - r)) := by
  let n := p.natDegree
  have hpad : fPolynomial d p = (X + 1) ^ (d - n) * fPolynomial n p := by
    simpa [n] using fPolynomial_pad_by_X_add_one_pow (m := n) (p := p) le_rfl hd
  have hfp_rr : ((fPolynomial n p) ≠ 0 ∧ (fPolynomial n p).Splits) :=
    isRealRooted_fPolynomial_of_isRealRooted_of_hasNonnegCoeffs le_rfl hp_ne hp_splits hpnn
  have hpow_ne : (X + 1 : ℝ[X]) ^ (d - n) ≠ 0 :=
    pow_ne_zero _ (by simpa [sub_eq_add_neg, add_comm] using (X_sub_C_ne_zero (-1 : ℝ)))
  have hroots_pow : ((X + 1 : ℝ[X]) ^ (d - n)).roots = Multiset.replicate (d - n) (-1) := by
    calc
      ((X + 1 : ℝ[X]) ^ (d - n)).roots = ((X - C (-1) : ℝ[X]) ^ (d - n)).roots := by simp
      _ = (d - n) • ({-1} : Multiset ℝ) := by rw [roots_pow, roots_X_sub_C]
      _ = Multiset.replicate (d - n) (-1) := by rw [Multiset.nsmul_singleton]
  rw [hpad, roots_mul (mul_ne_zero hpow_ne hfp_rr.1), hroots_pow,
    roots_fPolynomial_natDegree_eq_map_of_isRealRooted_of_hasNonnegCoeffs hp_ne hp_splits hpnn]

private theorem isRealRooted_of_fPolynomial_natDegree_roots_gt_neg_one
    {p : ℝ[X]}
    (hfpdeg : (fPolynomial p.natDegree p).natDegree = p.natDegree)
    (hfp_ne : (fPolynomial p.natDegree p) ≠ 0)
    (hfp_splits : (fPolynomial p.natDegree p).Splits)
    (hgt : ∀ x ∈ (fPolynomial p.natDegree p).roots, -1 < x) : (p ≠ 0 ∧ p.Splits) := by
  have hP :
      ∀ n : ℕ, ∀ p : ℝ[X],
        p.natDegree = n →
        (fPolynomial n p).natDegree = n →
        ((fPolynomial n p) ≠ 0 ∧ (fPolynomial n p).Splits) →
        (∀ x ∈ (fPolynomial n p).roots, -1 < x) →
        (p ≠ 0 ∧ p.Splits) := by
    intro n
    exact Nat.strong_induction_on n (fun n ih p hpdeg hqdeg hq_rr hq_gt => by
      have hp0 : p ≠ 0 := fun hpz => by simp_all
      by_cases hn : n = 0
      · exact isRealRooted_of_deg_zero hp0 (by lia)
      · have hroots_pos : 0 < (fPolynomial n p).roots.card := by
          rw [card_roots_of_splits hq_rr.2, hqdeg]
          lia
        obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hx_root : (fPolynomial n p).IsRoot x := (mem_roots hq_rr.1).mp hx_mem
        have hx_gt : -1 < x := hq_gt x hx_mem
        have hx_ne : x ≠ -1 := by linarith
        let r : ℝ := untransformRoot x
        have hr_root : p.IsRoot r := by
          rw [Polynomial.IsRoot.def] at hx_root ⊢
          rw [eval_fPolynomial_eq_mul_eval_untransform (d := n) (p := p)
            (by lia) hx_ne] at hx_root
          have hpow_ne : (1 + x) ^ n ≠ 0 :=
            pow_ne_zero _ (by linarith)
          grind
        obtain ⟨u, hu_dvd⟩ := dvd_iff_isRoot.mpr hr_root
        have hpu : p = (X - C r) * u := by lia
        have hu0 : u ≠ 0 := by simp_all
        have hudeg_succ : p.natDegree = u.natDegree + 1 := by
          simpa [Nat.add_comm] using
            (show p.natDegree = 1 + u.natDegree by
              rw [hpu, natDegree_mul (X_sub_C_ne_zero r) hu0, natDegree_X_sub_C])
        have hu_lt : u.natDegree < n := by lia
        have h1r_ne : 1 - r ≠ 0 := by
          intro hzero
          have h1x_ne : 1 + x ≠ 0 := by linarith
          dsimp [r, untransformRoot] at hzero
          grind
        have hq_fac0 :
            fPolynomial n p =
              (C (1 - r) * X - C r) * fPolynomial u.natDegree u := by
          have hdeg_eq : n = u.natDegree + 1 := by lia
          rw [hdeg_eq, hpu]
          simpa using fPolynomial_X_sub_C_mul_succ u.natDegree r (p := u) le_rfl
        have hq_fac :
            fPolynomial n p =
              (X - C x) * (C (1 - r) * fPolynomial u.natDegree u) := by
          calc
            fPolynomial n p
                = (C (1 - r) * X - C r) * fPolynomial u.natDegree u := hq_fac0
            _ = (C (1 - r) * (X - C (r / (1 - r)))) * fPolynomial u.natDegree u := by grind
            _ = (C (1 - r) * (X - C x)) * fPolynomial u.natDegree u := by
                  rw [transformedRoot_untransformRoot (x := x) hx_gt]
            _ = (X - C x) * (C (1 - r) * fPolynomial u.natDegree u) := by grind
        have hscaled_ne : C (1 - r) * fPolynomial u.natDegree u ≠ 0 := by simp_all
        have hscaled_rr : ((C (1 - r) * fPolynomial u.natDegree u) ≠ 0 ∧
          (C (1 - r) * fPolynomial u.natDegree u).Splits) := by
          apply isRealRooted_of_dvd hq_rr.1 hq_rr.2 hscaled_ne
          simp_all
        have hfu0 : fPolynomial u.natDegree u ≠ 0 := by simp_all
        have hfu_rr :
            ((fPolynomial u.natDegree u) ≠ 0 ∧
              (fPolynomial u.natDegree u).Splits) := by
          apply isRealRooted_of_dvd hscaled_rr.1 hscaled_rr.2 hfu0
          simp
        have hfu_deg : (fPolynomial u.natDegree u).natDegree = u.natDegree := by
          have htmp : n = 1 + (C (1 - r) * fPolynomial u.natDegree u).natDegree := by
            rw [← hqdeg, hq_fac, natDegree_mul (X_sub_C_ne_zero x) hscaled_ne, natDegree_X_sub_C]
          rw [natDegree_C_mul h1r_ne] at htmp
          lia
        have hgt_u : ∀ y ∈ (fPolynomial u.natDegree u).roots, -1 < y := by simp_all
        have hu_rr : (u ≠ 0 ∧ u.Splits) :=
          ih u.natDegree hu_lt u rfl hfu_deg hfu_rr hgt_u
        simp_all)
  simp_all

lemma root_gt_neg_one_of_mem_roots_fPolynomial_natDegree_of_isRealRooted_of_hasNonnegCoeffs
    {p : ℝ[X]} (hfp_ne : (fPolynomial p.natDegree p) ≠ 0)
    (hpnn : HasNonnegCoeffs p)
    {x : ℝ} (hx : x ∈ (fPolynomial p.natDegree p).roots) :
    -1 < x := by
  have hp0 : p ≠ 0 := fun hpz => by simp_all
  by_cases hxm1 : x = -1
  · subst hxm1
    exfalso
    exact not_isRoot_neg_one_fPolynomial_of_natDegree_eq_of_hasNonnegCoeffs rfl hp0
      ((mem_roots hfp_ne).mp hx)
  · by_cases hxlt : x < -1
    · exfalso
      have hx_root : (fPolynomial p.natDegree p).IsRoot x := (mem_roots hfp_ne).mp hx
      rw [Polynomial.IsRoot.def] at hx_root
      have hux_pos : 0 < untransformRoot x := by
        have h1x_neg : 1 + x < 0 := by linarith
        have hx_neg : x < 0 := by linarith
        have hdiv_pos : 0 < x / (1 + x) := div_pos_of_neg_of_neg hx_neg h1x_neg
        simpa [untransformRoot] using hdiv_pos
      have hpx_pos : 0 < p.eval (untransformRoot x) :=
        eval_pos_of_hasNonnegCoeffs_of_pos hpnn hp0 hux_pos
      rw [eval_fPolynomial_eq_mul_eval_untransform (d := p.natDegree) (p := p)
        le_rfl hxm1] at hx_root
      have hpow_ne : (1 + x) ^ p.natDegree ≠ 0 :=
        pow_ne_zero _ (by linarith)
      simp_all
    · grind

theorem isRealRooted_of_isRealRooted_fPolynomial_natDegree_of_hasNonnegCoeffs
    {p : ℝ[X]} (hfp_ne : (fPolynomial p.natDegree p) ≠ 0)
    (hfp_splits : (fPolynomial p.natDegree p).Splits)
    (hpnn : HasNonnegCoeffs p) : (p ≠ 0 ∧ p.Splits) := by
  have hp0 : p ≠ 0 := fun hpz => by simp_all
  have hfpdeg : (fPolynomial p.natDegree p).natDegree = p.natDegree :=
    fPolynomial_natDegree_eq_of_hasNonnegCoeffs_of_ne_zero le_rfl hpnn hp0
  have hgt : ∀ x ∈ (fPolynomial p.natDegree p).roots, -1 < x :=
    fun _ hx =>
      root_gt_neg_one_of_mem_roots_fPolynomial_natDegree_of_isRealRooted_of_hasNonnegCoeffs
        hfp_ne hpnn hx
  exact
    isRealRooted_of_fPolynomial_natDegree_roots_gt_neg_one hfpdeg hfp_ne hfp_splits hgt

theorem isRealRooted_of_isRealRooted_fPolynomial_of_hasNonnegCoeffs
    {d : ℕ} {p : ℝ[X]} (hpd : p.natDegree ≤ d)
    (hfp_ne : (fPolynomial d p) ≠ 0) (hfp_splits : (fPolynomial d p).Splits)
    (hpnn : HasNonnegCoeffs p) : (p ≠ 0 ∧ p.Splits) := by
  have hmin0 : fPolynomial p.natDegree p ≠ 0 := by
    intro hzero
    apply hfp_ne
    rw [fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) (p := p) le_rfl hpd, hzero, mul_zero]
  have hdiv : fPolynomial p.natDegree p ∣ fPolynomial d p := by
    refine ⟨(X + 1) ^ (d - p.natDegree), ?_⟩
    rw [fPolynomial_pad_by_X_add_one_pow (m := p.natDegree) (p := p) le_rfl hpd]
    grind
  have hmin_rr : ((fPolynomial p.natDegree p) ≠ 0 ∧ (fPolynomial p.natDegree p).Splits) :=
    isRealRooted_of_dvd hfp_ne hfp_splits hmin0 hdiv
  exact isRealRooted_of_isRealRooted_fPolynomial_natDegree_of_hasNonnegCoeffs
    hmin_rr.1 hmin_rr.2 hpnn


end RealRooted
