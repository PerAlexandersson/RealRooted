module

public import RealRooted.Hadamard.KostovMap

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Kostov

/-- The linear part of Kostov's affine coefficient map. -/
def linearPart (n : ℕ) (v : Fin (n - 1) → ℝ) : Fin (n - 1) → ℝ :=
  coeffMap n v - coeffMap n 0

/-- The `k`th candidate eigenvalue (zero-indexed) of Kostov's linear part:
`eigenvalue n k = n^k / ((n-1)(n-2)⋯(n-k))`, i.e. `λ_{k+1}` of the issue. -/
def eigenvalue (n k : ℕ) : ℝ :=
  (n : ℝ) ^ k / ((n - 1).descFactorial k : ℕ)

/-! ## Sanity checks (exact) -/

/-! Hint (not part of the statements): in tangent-polynomial coordinates
`T = (X+1) * ∑ v_i X^(n-2-i) = monicPolynomial n v - monicPolynomial n 0`, the eigen-equation
`linearPart n v = λ v` reads, for `k = 1..n-1`,
`[X^k] T = λ * C(n,k) ((n-k)/n)^n * T(k/(n-k))`.
Writing `G(y) = (1-y)^n T(y/(1-y))`, i.e. `T(x) = (1+x)^n G(x/(1+x))`, this is exactly
`B_n G = λ⁻¹ G` for the Bernstein operator `B_n G = ∑_k G(k/n) C(n,k) y^k (1-y)^(n-k)`
(`G ∈ P_{n-1}`, `G(1) = 0`).  `B_n` is triangular on monomials with diagonal
`n!/((n-m)! n^m)`, so the eigenvalue `λ_{m} = 1/μ_m` (`m = k`) has a monic eigenpolynomial
`G_m` of degree `m`; for `m ≥ 2`, `G_m(0) = G_m(1) = 0`, so `G_m = y (1-y) H`, and
`T(x) = x (1+x)^(n-m) Q(x)` with `Q(x) = (1+x)^(m-2) H(x/(1+x))` of degree `m-2`.
The symmetry `y ↦ 1-y` of `B_n` gives `G_m(1-y) = (-1)^m G_m(y)`, hence reciprocity. -/

/-! ## Auxiliary theory

The Bernstein operator, its eigenpolynomials (existence, uniqueness, simple zeros at the
endpoints via a variation-diminishing argument, reciprocity), and the dictionary between
Kostov's linear part and the Bernstein operator. -/

/-- The (unnormalised) Bernstein basis polynomial `X^k (1-X)^(n-k)`. -/
def bb (n k : ℕ) : ℝ[X] := X ^ k * (1 - X) ^ (n - k)

/-- The Bernstein operator `B_n G = ∑_k G(k/n) C(n,k) X^k (1-X)^(n-k)`. -/
def bernOp (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    (Polynomial.leval ((k : ℝ) / n)).smulRight (C (n.choose k : ℝ) * bb n k)

lemma bernOp_apply (n : ℕ) (G : ℝ[X]) :
    bernOp n G = ∑ k ∈ Finset.range (n + 1),
      C (G.eval ((k : ℝ) / n) * n.choose k) * bb n k := by
  simp only [bernOp, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    Polynomial.leval_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, C_mul, mul_assoc]

lemma sum_desc_bb (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), C ((k.descFactorial j : ℝ) * n.choose k) * bb n k =
      C (n.descFactorial j : ℝ) * X ^ j := by
  by_cases hj : n < j
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hj]
    simp only [Nat.cast_zero, map_zero, zero_mul]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by lia)]
    simp
  push Not at hj
  have hsplit : n + 1 = j + (n - j + 1) := by lia
  rw [hsplit, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range j, C ((x.descFactorial j : ℝ) * n.choose x) * bb n x = 0 :=
    Finset.sum_eq_zero fun k hk => by
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hk)]
    simp
  rw [h1, zero_add]
  have h2 : ∀ i ∈ Finset.range (n - j + 1),
      C (((j + i).descFactorial j : ℝ) * n.choose (j + i)) * bb n (j + i) =
      C (n.descFactorial j : ℝ) * X ^ j *
        (X ^ i * (1 - X) ^ (n - j - i) * C ((n - j).choose i : ℝ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have key : (j + i).descFactorial j * n.choose (j + i) =
        n.descFactorial j * (n - j).choose i := by
      have hc := Nat.choose_mul (n := n) (k := j + i) (s := j) (by lia)
      rw [show j + i - j = i by lia] at hc
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
        mul_assoc, mul_assoc, mul_comm ((j + i).choose j), hc]
    have key' : ((j + i).descFactorial j : ℝ) * n.choose (j + i) =
        n.descFactorial j * (n - j).choose i := by exact_mod_cast key
    rw [key', bb, show n - (j + i) = n - j - i by lia]
    simp only [map_mul, pow_add]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  have h3 : ∑ i ∈ Finset.range (n - j + 1), X ^ i * (1 - X) ^ (n - j - i) *
      C ((n - j).choose i : ℝ) = (1 : ℝ[X]) := by
    rw [show ∑ i ∈ Finset.range (n - j + 1), X ^ i * (1 - X) ^ (n - j - i) *
        C ((n - j).choose i : ℝ) = (X + (1 - X)) ^ (n - j) by
      rw [add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_natCast C]]
    rw [add_sub_cancel, one_pow]
  rw [h3, mul_one]

/-- The diagonal entries `μ_m = n(n-1)⋯(n-m+1)/n^m` of the Bernstein operator. -/
def mu (n m : ℕ) : ℝ := (n.descFactorial m : ℝ) / (n : ℝ) ^ m

/-- `(nX)(nX-1)⋯(nX-j+1)`. -/
def descPoly (n j : ℕ) : ℝ[X] := (descPochhammer ℝ j).comp (C (n : ℝ) * X)

lemma descPoly_eval (n j k : ℕ) (hn : n ≠ 0) :
    (descPoly n j).eval ((k : ℝ) / n) = (k.descFactorial j : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [descPoly, eval_comp, eval_mul, eval_C, eval_X, mul_div_cancel₀ _ hn',
    descPochhammer_eval_eq_descFactorial]

lemma descPoly_natDegree (n j : ℕ) (hn : n ≠ 0) :
    (descPoly n j).natDegree = j ∧ (descPoly n j).coeff j = (n : ℝ) ^ j := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 : (C (n : ℝ) * X).natDegree = 1 := natDegree_C_mul_X _ hn'
  have hd : (descPoly n j).natDegree = j := by
    rw [descPoly, natDegree_comp, h1, descPochhammer_natDegree, mul_one]
  refine ⟨hd, ?_⟩
  have := leadingCoeff_comp (p := descPochhammer ℝ j) (q := C (n : ℝ) * X)
    (by rw [h1]; norm_num)
  rw [leadingCoeff,
    show ((descPochhammer ℝ j).comp (C (n : ℝ) * X)).natDegree = j from hd] at this
  rw [descPoly, this, (monic_descPochhammer ℝ j).leadingCoeff, descPochhammer_natDegree,
    leadingCoeff_C_mul_X]
  simp

lemma bernOp_descPoly (n j : ℕ) (hn : n ≠ 0) :
    bernOp n (descPoly n j) = C (n.descFactorial j : ℝ) * X ^ j := by
  rw [bernOp_apply, ← sum_desc_bb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [descPoly_eval n j k hn]

lemma bernOp_deg_step (n m : ℕ) (hn : n ≠ 0)
    (h : ∀ r : ℝ[X], r.natDegree ≤ m → r.coeff m = 0 →
      (bernOp n r).natDegree ≤ m ∧ (bernOp n r).coeff m = 0)
    (G : ℝ[X]) (hG : G.natDegree ≤ m) :
    (bernOp n G).natDegree ≤ m ∧ (bernOp n G).coeff m = mu n m * G.coeff m := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨hd, hc⟩ := descPoly_natDegree n m hn
  set c : ℝ := G.coeff m / (n : ℝ) ^ m with hc_def
  set r : ℝ[X] := G - C c * descPoly n m with hr_def
  have hrd : r.natDegree ≤ m := by
    refine (natDegree_sub_le _ _).trans (max_le hG ?_)
    exact (natDegree_C_mul_le _ _).trans hd.le
  have hrc : r.coeff m = 0 := by
    rw [hr_def, coeff_sub, coeff_C_mul, hc, hc_def]
    field_simp
    ring
  obtain ⟨h1, h2⟩ := h r hrd hrc
  have hG' : G = r + C c * descPoly n m := by rw [hr_def]; ring
  have hB : bernOp n G = bernOp n r + C (c * n.descFactorial m) * X ^ m := by
    rw [hG', map_add, ← smul_eq_C_mul, map_smul, bernOp_descPoly n m hn, smul_eq_C_mul,
      ← mul_assoc, ← C_mul]
  rw [hB]
  refine ⟨(natDegree_add_le _ _).trans (max_le h1 (natDegree_C_mul_X_pow_le _ _)), ?_⟩
  rw [coeff_add, h2, coeff_C_mul_X_pow, ite_eq_left rfl, mu, hc_def, zero_add]
  field_simp

/-- **Triangularity of the Bernstein operator.** -/
lemma bernOp_deg (n : ℕ) (hn : n ≠ 0) (m : ℕ) (G : ℝ[X]) (hG : G.natDegree ≤ m) :
    (bernOp n G).natDegree ≤ m ∧ (bernOp n G).coeff m = mu n m * G.coeff m := by
  induction m generalizing G with
  | zero =>
    refine bernOp_deg_step n 0 hn (fun r hr hr0 => ?_) G hG
    have : r = 0 := by
      rw [eq_C_of_natDegree_le_zero hr, hr0, map_zero]
    simp [this]
  | succ m ih =>
    refine bernOp_deg_step n (m + 1) hn (fun r hr hr0 => ?_) G hG
    have hr' : r.natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero] at hr ⊢
      intro k hk
      rcases Nat.lt_or_ge (m + 1) k with h | h
      · exact hr k h
      · obtain rfl : k = m + 1 := by lia
        exact hr0
    obtain ⟨h1, -⟩ := ih r hr'
    exact ⟨h1.trans (Nat.le_succ m), coeff_eq_zero_of_natDegree_lt (by lia)⟩

lemma mu_zero (n : ℕ) : mu n 0 = 1 := by simp [mu]

lemma mu_one (n : ℕ) (hn : n ≠ 0) : mu n 1 = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [mu, hn']

lemma mu_pos (n m : ℕ) (hm : m ≤ n) : 0 < mu n m := by
  have h1 : (0 : ℝ) < n.descFactorial m := by exact_mod_cast Nat.descFactorial_pos.mpr hm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : m = 0 := by lia
    simp [mu]
  · exact div_pos h1 (pow_pos (by exact_mod_cast hn) _)

lemma mu_succ (n m : ℕ) (hm : m < n) : mu n (m + 1) = mu n m * (((n : ℝ) - m) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by lia)
  rw [mu, mu, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hm.le]
  field_simp
  ring

lemma mu_succ_lt (n m : ℕ) (hm1 : 1 ≤ m) (hm : m < n) : mu n (m + 1) < mu n m := by
  rw [mu_succ n m hm]
  have hp := mu_pos n m hm.le
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  have : ((n : ℝ) - m) / n < 1 := by
    rw [div_lt_one hn]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  nlinarith

lemma mu_lt_of_lt (n d m : ℕ) (hd : 1 ≤ d) (hdm : d < m) (hmn : m ≤ n) : mu n m < mu n d := by
  induction m, hdm using Nat.le_induction with
  | base => exact mu_succ_lt n d hd (by lia)
  | succ m hdm ih =>
    exact (mu_succ_lt n m (by lia) (by lia)).trans (ih (by lia))

lemma mu_lt_one (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) : mu n m < 1 := by
  have := mu_lt_of_lt n 1 m le_rfl (by lia) hmn
  rwa [mu_one n (by lia)] at this

/-- `μ` is injective on the relevant range. -/
lemma mu_inj (n d m : ℕ) (hd : d ≤ n) (hm : 2 ≤ m) (hmn : m ≤ n) (h : mu n d = mu n m) :
    d = m := by
  have h1 := mu_lt_one n m hm hmn
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · interval_cases d
    · rw [mu_zero] at h; linarith
    · rw [mu_one n (by lia)] at h; linarith
  rcases lt_trichotomy d m with h2 | h2 | h2
  · have := mu_lt_of_lt n d m (by lia) h2 hmn; linarith
  · exact h2
  · have := mu_lt_of_lt n m d (by lia) h2 hd; linarith

lemma mu_eq_one_iff (n d : ℕ) (hd : d ≤ n) (h : mu n d = 1) : d ≤ 1 := by
  by_contra h'
  have := mu_lt_one n d (by lia) hd
  linarith

/-! ### Evaluation at the endpoints -/

lemma bb_eval_zero (n k : ℕ) : (bb n k).eval 0 = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [bb]
  · simp [bb, zero_pow hk.ne', hk.ne']

lemma bernOp_eval_zero (n : ℕ) (G : ℝ[X]) : (bernOp n G).eval 0 = G.eval 0 := by
  rw [bernOp_apply, eval_finsetSum, Finset.sum_eq_single 0]
  · simp [bb]
  · intro k _ hk
    rw [eval_mul, bb_eval_zero, ite_eq_right hk, mul_zero]
  · intro h; simp at h

lemma bernOp_eval_one (n : ℕ) (hn : n ≠ 0) (G : ℝ[X]) : (bernOp n G).eval 1 = G.eval 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [bernOp_apply, eval_finsetSum, Finset.sum_eq_single n]
  · simp [bb, hn']
  · intro k hk hkn
    rw [Finset.mem_range] at hk
    have : n - k ≠ 0 := by lia
    simp [bb, zero_pow this]
  · intro h; simp at h

lemma bernOp_one (n : ℕ) (hn : n ≠ 0) : bernOp n 1 = 1 := by
  obtain ⟨h1, h2⟩ := bernOp_deg n hn 0 1 (by simp)
  rw [eq_C_of_natDegree_le_zero h1, h2, mu_zero]
  simp

lemma bernOp_X (n : ℕ) (hn : n ≠ 0) : bernOp n X = X := by
  obtain ⟨h1, h2⟩ := bernOp_deg n hn 1 X (by simp)
  rw [eq_X_add_C_of_natDegree_le_one h1, h2, mu_one n hn, coeff_zero_eq_eval_zero,
    bernOp_eval_zero]
  simp

/-! ### Solving `(B - μ) R = S` on polynomials of degree `< m` -/

lemma bernOp_surj (n : ℕ) (hn : n ≠ 0) (μ : ℝ) :
    ∀ m : ℕ, (∀ d < m, mu n d ≠ μ) → ∀ S : ℝ[X], S.degree < m →
      ∃ R : ℝ[X], R.degree < m ∧ bernOp n R - μ • R = S := by
  intro m
  induction m with
  | zero =>
    intro _ S hS
    have : S = 0 := by
      ext k
      rw [degree_lt_iff_coeff_zero] at hS
      simpa using hS k (Nat.zero_le k)
    exact ⟨0, by simp, by simp [this]⟩
  | succ m ih =>
    intro hmu S hS
    set μ' : ℝ := mu n m - μ with hμ'
    have hμ'0 : μ' ≠ 0 := sub_ne_zero.mpr (hmu m (Nat.lt_succ_self m))
    set P : ℝ[X] := bernOp n (X ^ m) - μ • X ^ m with hP
    obtain ⟨hPd, hPc⟩ := bernOp_deg n hn m (X ^ m) (by simp)
    set c : ℝ := S.coeff m with hc
    set S' : ℝ[X] := S - (c / μ') • P with hS'
    have hS'd : S'.degree < m := by
      rw [degree_lt_iff_coeff_zero] at hS ⊢
      intro k hk
      rcases eq_or_lt_of_le hk with rfl | hk'
      · rw [hS', coeff_sub, coeff_smul, hP, coeff_sub, hPc, coeff_smul]
        simp only [coeff_X_pow_self, mul_one, smul_eq_mul]
        rw [← hc]
        field_simp
        ring
      · rw [hS', coeff_sub, coeff_smul, hP, coeff_sub, coeff_smul,
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPd hk'), coeff_X_pow,
          ite_eq_right (by lia), hS k (by lia)]
        simp
    obtain ⟨R', hR'd, hR'⟩ := ih (fun d hd => hmu d (by lia)) S' hS'd
    refine ⟨R' + (c / μ') • X ^ m, ?_, ?_⟩
    · rw [degree_lt_iff_coeff_zero]
      intro k hk
      rw [degree_lt_iff_coeff_zero] at hR'd
      rw [coeff_add, coeff_smul, hR'd k (by lia), coeff_X_pow, ite_eq_right (by lia)]
      simp
    · rw [map_add, map_smul]
      calc bernOp n R' + (c / μ') • bernOp n (X ^ m) - μ • (R' + (c / μ') • X ^ m)
          = (bernOp n R' - μ • R') + (c / μ') • P := by rw [hP]; module
        _ = S := by rw [hR', hS']; module

/-- **Existence of eigenpolynomials.** For `2 ≤ m ≤ n` there is a monic polynomial of degree
`m` which is an eigenvector of the Bernstein operator with eigenvalue `μ_m`. -/
lemma exists_eigPoly (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ G : ℝ[X], G.Monic ∧ G.natDegree = m ∧ bernOp n G = mu n m • G := by
  have hn : n ≠ 0 := by lia
  have hmu : ∀ d < m, mu n d ≠ mu n m := by
    intro d hd h
    have := mu_inj n d m (by lia) hm hmn h
    lia
  obtain ⟨hPd, hPc⟩ := bernOp_deg n hn m (X ^ m) (by simp)
  set S : ℝ[X] := -(bernOp n (X ^ m) - mu n m • X ^ m) with hS
  have hSd : S.degree < m := by
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hk'
    · simp [hS, hPc]
    · rw [hS, coeff_neg, coeff_sub, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPd hk'),
        coeff_smul, coeff_X_pow, ite_eq_right (by lia)]
      simp
  obtain ⟨R, hRd, hR⟩ := bernOp_surj n hn (mu n m) m hmu S hSd
  refine ⟨X ^ m + R, monic_X_pow_add hRd, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · apply sub_eq_zero.mp
    rw [map_add]
    calc bernOp n (X ^ m) + bernOp n R - mu n m • (X ^ m + R)
        = (bernOp n (X ^ m) - mu n m • X ^ m) + (bernOp n R - mu n m • R) := by module
      _ = 0 := by rw [hR, hS]; module

/-- The canonical monic eigenpolynomial of degree `m` (junk value `0` outside `2 ≤ m ≤ n`). -/
def eigPoly (n m : ℕ) : ℝ[X] :=
  if h : 2 ≤ m ∧ m ≤ n then Classical.choose (exists_eigPoly n m h.1 h.2) else 0

lemma eigPoly_spec (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (eigPoly n m).Monic ∧ (eigPoly n m).natDegree = m ∧
      bernOp n (eigPoly n m) = mu n m • eigPoly n m := by
  rw [eigPoly, dite_eq_left ⟨hm, hmn⟩]
  exact Classical.choose_spec (exists_eigPoly n m hm hmn)

/-- Eigenvectors vanish at the endpoints when the eigenvalue is not `1`. -/
lemma eigen_eval_zero (n : ℕ) (G : ℝ[X]) (μ : ℝ) (hμ : μ ≠ 1)
    (hG : bernOp n G = μ • G) :
    G.eval 0 = 0 := by
  have := bernOp_eval_zero n G
  rw [hG, eval_smul, smul_eq_mul] at this
  exact (mul_eq_zero.mp (by nlinarith : (μ - 1) * G.eval 0 = 0)).resolve_left
    (sub_ne_zero.mpr hμ)

lemma eigen_eval_one (n : ℕ) (hn : n ≠ 0) (G : ℝ[X]) (μ : ℝ) (hμ : μ ≠ 1)
    (hG : bernOp n G = μ • G) : G.eval 1 = 0 := by
  have := bernOp_eval_one n hn G
  rw [hG, eval_smul, smul_eq_mul] at this
  exact (mul_eq_zero.mp (by nlinarith : (μ - 1) * G.eval 1 = 0)).resolve_left
    (sub_ne_zero.mpr hμ)

/-- The degree of an eigenvector determines its eigenvalue. -/
lemma mu_natDegree_of_eigen (n : ℕ) (hn : n ≠ 0) (G : ℝ[X]) (μ : ℝ) (hG0 : G ≠ 0)
    (hG : bernOp n G = μ • G) : mu n G.natDegree = μ := by
  obtain ⟨-, h2⟩ := bernOp_deg n hn G.natDegree G le_rfl
  rw [hG, coeff_smul, smul_eq_mul] at h2
  have hl : G.coeff G.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hG0
  exact (mul_right_cancel₀ hl h2).symm

/-- **Uniqueness of eigenpolynomials** for `μ_m`, `2 ≤ m ≤ n`. -/
lemma eigen_unique (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) (G₁ G₂ : ℝ[X]) (h1 : G₁ ≠ 0)
    (hd1 : G₁.natDegree ≤ n) (hd2 : G₂.natDegree ≤ n)
    (hG₁ : bernOp n G₁ = mu n m • G₁) (hG₂ : bernOp n G₂ = mu n m • G₂) :
    ∃ c : ℝ, G₂ = c • G₁ := by
  have hn : n ≠ 0 := by lia
  have hdeg : ∀ G : ℝ[X], G ≠ 0 → G.natDegree ≤ n → bernOp n G = mu n m • G →
      G.natDegree = m := fun G hG hd hGe =>
    mu_inj n _ m hd hm hmn (mu_natDegree_of_eigen n hn G _ hG hGe)
  have e1 := hdeg G₁ h1 hd1 hG₁
  set c : ℝ := G₂.coeff m / G₁.coeff m with hc
  have hl1 : G₁.coeff m ≠ 0 := by rw [← e1]; exact leadingCoeff_ne_zero.mpr h1
  refine ⟨c, ?_⟩
  by_contra hne
  set D : ℝ[X] := G₂ - c • G₁ with hD
  have hD0 : D ≠ 0 := sub_ne_zero.mpr hne
  have hDe : bernOp n D = mu n m • D := by
    rw [hD, map_sub, map_smul, hG₁, hG₂]; module
  have hDd : D.natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le hd2 ((natDegree_smul_le _ _).trans hd1))
  have eD := hdeg D hD0 hDd hDe
  have hDc : D.coeff m = 0 := by
    rw [hD, coeff_sub, coeff_smul, smul_eq_mul, hc]
    field_simp
    ring
  rw [← eD] at hDc
  exact hD0 (leadingCoeff_eq_zero.mp hDc)

/-- Eigenvectors for eigenvalue `1` of degree `≤ n-1` vanishing at `1` are multiples of
`1 - X`. -/
lemma eigen_one_form (n : ℕ) (hn : n ≠ 0) (G : ℝ[X]) (hd : G.natDegree ≤ n)
    (hG : bernOp n G = (1 : ℝ) • G) (h1 : G.eval 1 = 0) : G = C (G.coeff 0) * (1 - X) := by
  have hle : G.natDegree ≤ 1 := by
    by_cases hG0 : G = 0
    · simp [hG0]
    · exact mu_eq_one_iff n _ hd (mu_natDegree_of_eigen n hn G 1 hG0 hG)
  have hform := eq_X_add_C_of_natDegree_le_one hle
  have : G.coeff 1 = -G.coeff 0 := by
    rw [hform] at h1
    simp at h1
    linarith
  calc G = C (G.coeff 1) * X + C (G.coeff 0) := hform
    _ = C (G.coeff 0) * (1 - X) := by rw [this, map_neg]; ring


end Kostov
end RealRooted
