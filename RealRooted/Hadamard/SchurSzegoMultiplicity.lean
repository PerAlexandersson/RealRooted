import RealRooted.Hadamard.Basic

/-!
# Exact root multiplicity for the finite Schur–Szegő composition

For real polynomials `f = ∑ C(n,k) αₖ Xᵏ` and `g = ∑ C(n,k) βₖ Xᵏ`, the Schur–Szegő composition
is `f *ₙ g = ∑ C(n,k) αₖ βₖ Xᵏ`.  We prove the result of Kostov and Shapiro
(*On the Schur–Szegő composition of polynomials*, C. R. Acad. Sci. Paris 343 (2006),
Prop. 4/5; with the nonzero-root hypothesis of Kostov 2010, Prop. 6): if `f` and `g` have
degree `n`, `a ≠ 0` is a root of `f` of multiplicity `m`, `b ≠ 0` is a root of `g` of
multiplicity `l`, and `n ≤ m + l`, then `-(a * b)` is a root of `f *ₙ g` of multiplicity
exactly `m + l - n`.

## Proof outline

* `schurSzegoComp_X_mul`: `(X * f) *ₙ₊₁ g = (n + 1)⁻¹ • X * (f *ₙ g')`.
* `schurSzegoComp_X_sub_C_pow`: `(X - a)ⁿ *ₙ g = (-a)ⁿ g(-X / a)`.
* Hence `(X - a)ⁿ⁻ʲ Xʲ *ₙ g = K Xʲ g⁽ʲ⁾(-X / a)` with `K ≠ 0`, which has `-(a * b)` as a root
  of multiplicity exactly `l - j` when `j ≤ l`.
* Splitting `q = c X^(d+1) + (X - a) q'` with `c = q(a) / a^(d+1)`, induction on `d` shows
  that `(X - a)ⁿ⁻ᵈ q *ₙ g = (X + a b)ˡ⁻ᵈ R` with `R(-(a * b)) ≠ 0` whenever `q(a) ≠ 0`.
-/

open Polynomial

namespace RealRooted

/-- Coefficients of the Schur–Szegő composition (for `k > n` both sides vanish). -/
theorem coeff_schurSzegoComp_eq_div (n : ℕ) (f g : ℝ[X]) (k : ℕ) :
    (schurSzegoComp n f g).coeff k = f.coeff k * g.coeff k / (n.choose k : ℝ) := by
  rw [schurSzegoComp, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero, div_zero]

/-- Multiplying the first argument by `X` raises the degree index and differentiates `g`. -/
theorem schurSzegoComp_X_mul (N : ℕ) (f g : ℝ[X]) :
    schurSzegoComp (N + 1) (X * f) g =
      C ((N + 1 : ℝ)⁻¹) * (X * schurSzegoComp N f (derivative g)) := by
  ext k
  rcases k with _ | k
  · simp [coeff_schurSzegoComp_eq_div]
  · rw [coeff_C_mul, coeff_X_mul, coeff_schurSzegoComp_eq_div, coeff_schurSzegoComp_eq_div,
      coeff_X_mul, coeff_derivative]
    have h := Nat.add_one_mul_choose_eq N k
    have hc : ((N + 1).choose (k + 1) : ℝ) * (k + 1) = (N + 1) * N.choose k := by
      exact_mod_cast h.symm
    rcases eq_or_ne (N.choose k : ℝ) 0 with h0 | h0
    · have : ((N + 1).choose (k + 1) : ℝ) = 0 := by
        rw [h0, mul_zero] at hc
        rcases mul_eq_zero.mp hc with h1 | h1
        · exact h1
        · exact absurd h1 (by positivity)
      rw [this, h0]
      simp
    · have : ((N + 1).choose (k + 1) : ℝ) ≠ 0 := by
        intro h1
        rw [h1, zero_mul] at hc
        exact mul_ne_zero (by positivity) h0 hc.symm
      field_simp
      linear_combination (-(f.coeff k * g.coeff (k + 1))) * hc

/-- Composition with `(X - a) ^ n` rescales `g`: `(X - a)ⁿ *ₙ g = (-a)ⁿ g(-X / a)`. -/
theorem schurSzegoComp_X_sub_C_pow {n : ℕ} {a : ℝ} (ha : a ≠ 0) {g : ℝ[X]}
    (hg : g.natDegree ≤ n) :
    schurSzegoComp n ((X - C a) ^ n) g = C ((-a) ^ n) * g.comp (C (-a⁻¹) * X) := by
  ext k
  rw [coeff_schurSzegoComp_eq_div, coeff_C_mul, comp_C_mul_X_coeff, sub_eq_add_neg, ← C_neg,
    coeff_X_add_C_pow]
  rcases le_or_gt k n with hk | hk
  · have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    have hpow : (-a) ^ n = (-a) ^ (n - k) * (-a) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have hak : (-a) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr ha)
    rw [hpow, neg_inv, inv_pow]
    field_simp
  · rw [coeff_eq_zero_of_natDegree_lt (by lia)]
    simp

/-- Composition with the basis polynomial `(X - a) ^ (n - j) * X ^ j` is a nonzero multiple
of `X ^ j * g⁽ʲ⁾(-X / a)`. -/
theorem schurSzegoComp_X_sub_C_pow_mul_X_pow {a : ℝ} (ha : a ≠ 0) (j : ℕ) :
    ∀ (n : ℕ) (g : ℝ[X]), j ≤ n → g.natDegree ≤ n →
      ∃ K : ℝ, K ≠ 0 ∧ schurSzegoComp n ((X - C a) ^ (n - j) * X ^ j) g =
        C K * X ^ j * (derivative^[j] g).comp (C (-a⁻¹) * X) := by
  induction j with
  | zero =>
    intro n g _ hg
    refine ⟨(-a) ^ n, pow_ne_zero _ (neg_ne_zero.mpr ha), ?_⟩
    rw [Nat.sub_zero, pow_zero, mul_one, mul_one, Function.iterate_zero_apply]
    exact schurSzegoComp_X_sub_C_pow ha hg
  | succ j ih =>
    intro n g hj hg
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by lia⟩
    obtain ⟨K, hK, hEq⟩ := ih N (derivative g) (by lia)
      ((natDegree_derivative_le g).trans (by lia))
    refine ⟨(N + 1 : ℝ)⁻¹ * K, mul_ne_zero (inv_ne_zero (by positivity)) hK, ?_⟩
    have hsplit : (X - C a) ^ (N + 1 - (j + 1)) * X ^ (j + 1) =
        X * ((X - C a) ^ (N - j) * X ^ j) := by
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [hsplit, schurSzegoComp_X_mul, hEq, Function.iterate_succ_apply, C_mul, pow_succ]
    ring

/-- If `b` is a root of `(X - b) ^ l * v` of multiplicity exactly `l`, then it is a root of the
`j`-th derivative of multiplicity exactly `l - j`, for `j ≤ l`. -/
private theorem exists_iterate_derivative_X_sub_C_pow_mul {b : ℝ} {l : ℕ} {v : ℝ[X]}
    (hv : v.eval b ≠ 0) (j : ℕ) (hj : j ≤ l) :
    ∃ w : ℝ[X], derivative^[j] ((X - C b) ^ l * v) = (X - C b) ^ (l - j) * w ∧
      w.eval b ≠ 0 := by
  induction j with
  | zero => exact ⟨v, by rw [Function.iterate_zero_apply, Nat.sub_zero], hv⟩
  | succ j ih =>
    obtain ⟨w, hw, hwb⟩ := ih (by lia)
    refine ⟨C ((l - j : ℕ) : ℝ) * w + (X - C b) * derivative w, ?_, ?_⟩
    · obtain ⟨r, hr⟩ : ∃ r, l - j = r + 1 := ⟨l - j - 1, by lia⟩
      rw [Function.iterate_succ_apply', hw, derivative_mul, derivative_X_sub_C_pow, hr,
        show l - (j + 1) = r by lia, Nat.add_sub_cancel]
      ring
    · rw [eval_add, eval_mul, eval_mul, eval_C, eval_sub, eval_X, eval_C, sub_self, zero_mul,
        add_zero]
      exact mul_ne_zero (by exact_mod_cast (show l - j ≠ 0 by lia)) hwb

/-- Rescaling `X ↦ -X / a` moves the factor `(X - b) ^ r` to `(X + a * b) ^ r`. -/
private theorem X_sub_C_pow_mul_comp_C_mul_X {a b : ℝ} (ha : a ≠ 0) (r : ℕ) (w : ℝ[X]) :
    ((X - C b) ^ r * w).comp (C (-a⁻¹) * X) =
      (X - C (-(a * b))) ^ r * (C ((-a⁻¹) ^ r) * w.comp (C (-a⁻¹) * X)) := by
  have h : C (-a⁻¹) * X - C b = C (-a⁻¹) * (X - C (-(a * b))) := by
    rw [mul_sub, ← C_mul, show -a⁻¹ * -(a * b) = b by field_simp]
  rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, h, mul_pow, C_pow]
  ring

/-- The composition of `(X - a) ^ (n - j) * X ^ j` with `(X - b) ^ l * v` has `-(a * b)` as a
root of multiplicity exactly `l - j`. -/
theorem exists_schurSzegoComp_X_sub_C_pow_mul_X_pow {n l j : ℕ} {a b : ℝ} {v : ℝ[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hv : v.eval b ≠ 0) (hg : ((X - C b) ^ l * v).natDegree ≤ n)
    (hjn : j ≤ n) (hjl : j ≤ l) :
    ∃ R : ℝ[X], schurSzegoComp n ((X - C a) ^ (n - j) * X ^ j) ((X - C b) ^ l * v) =
      (X - C (-(a * b))) ^ (l - j) * R ∧ R.eval (-(a * b)) ≠ 0 := by
  obtain ⟨K, hK, hEq⟩ := schurSzegoComp_X_sub_C_pow_mul_X_pow ha j n _ hjn hg
  obtain ⟨w, hw, hwb⟩ := exists_iterate_derivative_X_sub_C_pow_mul hv j hjl
  refine ⟨C K * X ^ j * (C ((-a⁻¹) ^ (l - j)) * w.comp (C (-a⁻¹) * X)), ?_, ?_⟩
  · rw [hEq, hw, X_sub_C_pow_mul_comp_C_mul_X ha]
    ring
  · have hs : -a⁻¹ * -(a * b) = b := by field_simp
    rw [eval_mul, eval_mul, eval_mul, eval_C, eval_C, eval_pow, eval_X, eval_comp, eval_mul,
      eval_C, eval_X, hs]
    have hab : -(a * b) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha hb)
    have hs0 : -a⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ha)
    exact mul_ne_zero (mul_ne_zero hK (pow_ne_zero _ hab)) (mul_ne_zero (pow_ne_zero _ hs0) hwb)

/-- Splitting `q = c X ^ (d + 1) + (X - a) q'` with `c = q(a) / a ^ (d + 1)`. -/
private theorem exists_eq_C_mul_X_pow_add_X_sub_C_mul {a : ℝ} (ha : a ≠ 0) {d : ℕ} {q : ℝ[X]}
    (hq : q.natDegree ≤ d + 1) :
    ∃ q' : ℝ[X], q'.natDegree ≤ d ∧
      q = C (q.eval a / a ^ (d + 1)) * X ^ (d + 1) + (X - C a) * q' := by
  set r := q - C (q.eval a / a ^ (d + 1)) * X ^ (d + 1) with hr
  have hroot : r.IsRoot a := by
    rw [IsRoot, hr, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    field_simp
    ring
  refine ⟨r /ₘ (X - C a), ?_, ?_⟩
  · rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]
    have : r.natDegree ≤ d + 1 :=
      (natDegree_sub_le _ _).trans (max_le hq (natDegree_C_mul_X_pow_le _ _))
    lia
  · rw [mul_divByMonic_eq_iff_isRoot.mpr hroot, hr]
    ring

/-- Main induction: `(X - a) ^ (n - d) * q *ₙ (X - b) ^ l * v` is divisible by
`(X + a * b) ^ (l - d)`, with a cofactor not vanishing at `-(a * b)` when `q(a) ≠ 0`. -/
theorem exists_schurSzegoComp_X_sub_C_pow_mul {n l : ℕ} {a b : ℝ} {v : ℝ[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hv : v.eval b ≠ 0) (hg : ((X - C b) ^ l * v).natDegree ≤ n)
    (d : ℕ) (hdn : d ≤ n) (hdl : d ≤ l) (q : ℝ[X]) (hq : q.natDegree ≤ d) :
    ∃ R : ℝ[X], schurSzegoComp n ((X - C a) ^ (n - d) * q) ((X - C b) ^ l * v) =
      (X - C (-(a * b))) ^ (l - d) * R ∧ (q.eval a ≠ 0 → R.eval (-(a * b)) ≠ 0) := by
  induction d generalizing q with
  | zero =>
    obtain ⟨R₁, hR₁, hR₁x⟩ :=
      exists_schurSzegoComp_X_sub_C_pow_mul_X_pow (j := 0) ha hb hv hg hdn hdl
    rw [eq_C_of_natDegree_le_zero hq]
    refine ⟨C (q.coeff 0) * R₁, ?_, fun hqa => ?_⟩
    · rw [mul_comm, schurSzegoComp_C_mul_left]
      rw [pow_zero, mul_one] at hR₁
      rw [hR₁]
      ring
    · rw [eval_mul, eval_C]
      rw [eval_C] at hqa
      exact mul_ne_zero hqa hR₁x
  | succ d ih =>
    obtain ⟨q', hq'd, hq'⟩ := exists_eq_C_mul_X_pow_add_X_sub_C_mul ha hq
    obtain ⟨R', hR', -⟩ := ih (by lia) (by lia) q' hq'd
    obtain ⟨R₁, hR₁, hR₁x⟩ :=
      exists_schurSzegoComp_X_sub_C_pow_mul_X_pow (j := d + 1) ha hb hv hg hdn hdl
    set c := q.eval a / a ^ (d + 1) with hc
    have hsplit : (X - C a) ^ (n - (d + 1)) * q =
        C c * ((X - C a) ^ (n - (d + 1)) * X ^ (d + 1)) + (X - C a) ^ (n - d) * q' := by
      rw [hq', show n - d = n - (d + 1) + 1 by lia, pow_succ]
      ring
    refine ⟨C c * R₁ + (X - C (-(a * b))) * R', ?_, fun hqa => ?_⟩
    · rw [hsplit, schurSzegoComp_add_left, schurSzegoComp_C_mul_left, hR₁, hR',
        show l - d = l - (d + 1) + 1 by lia, pow_succ]
      ring
    · rw [eval_add, eval_mul, eval_mul, eval_C, eval_sub, eval_X, eval_C, sub_self, zero_mul,
        add_zero]
      exact mul_ne_zero (div_ne_zero hqa (pow_ne_zero _ ha)) hR₁x

/-- Factorization form of the Kostov–Shapiro theorem: `f *ₙ g = (X + a b) ^ (m + l - n) * R`
with `R(-(a * b)) ≠ 0`. -/
theorem exists_schurSzegoComp_eq_X_sub_C_pow_mul {n m l : ℕ} {f g : ℝ[X]} {a b : ℝ}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hf : f.natDegree = n) (hg : g.natDegree = n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hm : f.rootMultiplicity a = m) (hl : g.rootMultiplicity b = l)
    (hn : n ≤ m + l) :
    ∃ R : ℝ[X], schurSzegoComp n f g = (X - C (-(a * b))) ^ (m + l - n) * R ∧
      R.eval (-(a * b)) ≠ 0 := by
  obtain ⟨u, hfu, hu⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf0 a
  obtain ⟨v, hgv, hv⟩ := g.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hg0 b
  rw [hm] at hfu
  rw [hl] at hgv
  rw [dvd_iff_isRoot, IsRoot] at hu hv
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu eval_zero
  have hdeg : f.natDegree = m + u.natDegree := by
    rw [hfu, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hu0, natDegree_pow,
      natDegree_X_sub_C, mul_one]
  obtain ⟨R, hR, hRx⟩ := exists_schurSzegoComp_X_sub_C_pow_mul ha hb hv
    (by rw [← hgv, hg]) (n - m) (by lia) (by lia) u (by lia)
  refine ⟨R, ?_, hRx hu⟩
  rw [show n - (n - m) = m by lia, show l - (n - m) = m + l - n by lia, ← hfu, ← hgv] at hR
  exact hR

private theorem rootMultiplicity_X_sub_C_pow_mul_of_eval_ne_zero {x : ℝ} {R : ℝ[X]}
    (hR : R.eval x ≠ 0) (k : ℕ) : ((X - C x) ^ k * R).rootMultiplicity x = k := by
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hR eval_zero
  rw [mul_comm, rootMultiplicity_mul_X_sub_C_pow hR0, rootMultiplicity_eq_zero hR, zero_add]

/-- **Kostov–Shapiro.** Let `f` and `g` be real polynomials of degree `n`, and let `a` and `b`
be nonzero reals that are roots of `f` and `g` of multiplicities `m` and `l` with
`n ≤ m + l`.  Then `-(a * b)` is a root of the Schur–Szegő composition `f *ₙ g` of
multiplicity exactly `m + l - n`. -/
theorem rootMultiplicity_schurSzegoComp {n m l : ℕ} {f g : ℝ[X]} {a b : ℝ}
    (hf : f.natDegree = n) (hg : g.natDegree = n) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : f.rootMultiplicity a = m) (hl : g.rootMultiplicity b = l) (hn : n ≤ m + l) :
    (schurSzegoComp n f g).rootMultiplicity (-(a * b)) = m + l - n := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have hn0 : n = 0 := by rw [← hf, natDegree_zero]
    subst hn0
    have hl0 : l = 0 := by rw [← hl, eq_C_of_natDegree_eq_zero hg, rootMultiplicity_C]
    rw [rootMultiplicity_zero] at hm
    simp [← hm, hl0, schurSzegoComp_zero_left]
  rcases eq_or_ne g 0 with rfl | hg0
  · have hn0 : n = 0 := by rw [← hg, natDegree_zero]
    subst hn0
    have hm0 : m = 0 := by rw [← hm, eq_C_of_natDegree_eq_zero hf, rootMultiplicity_C]
    rw [rootMultiplicity_zero] at hl
    simp [← hl, hm0, schurSzegoComp_zero_right]
  obtain ⟨R, hR, hRx⟩ := exists_schurSzegoComp_eq_X_sub_C_pow_mul hf0 hg0 hf hg ha hb hm hl hn
  rw [hR]
  exact rootMultiplicity_X_sub_C_pow_mul_of_eval_ne_zero hRx _

/-- Under the hypotheses of `rootMultiplicity_schurSzegoComp`, with `f` and `g` nonzero, the
Schur–Szegő composition `f *ₙ g` is a nonzero polynomial. -/
theorem schurSzegoComp_ne_zero {n m l : ℕ} {f g : ℝ[X]} {a b : ℝ}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hf : f.natDegree = n) (hg : g.natDegree = n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hm : f.rootMultiplicity a = m) (hl : g.rootMultiplicity b = l)
    (hn : n ≤ m + l) : schurSzegoComp n f g ≠ 0 := by
  obtain ⟨R, hR, hRx⟩ := exists_schurSzegoComp_eq_X_sub_C_pow_mul hf0 hg0 hf hg ha hb hm hl hn
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hRx eval_zero
  rw [hR]
  exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) hR0

/-- In the extremal case `m + l = n` of `rootMultiplicity_schurSzegoComp`, `-(a * b)` is not a
root of the Schur–Szegő composition of the nonzero polynomials `f` and `g`. -/
theorem not_isRoot_schurSzegoComp {n m l : ℕ} {f g : ℝ[X]} {a b : ℝ}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hf : f.natDegree = n) (hg : g.natDegree = n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hm : f.rootMultiplicity a = m) (hl : g.rootMultiplicity b = l)
    (hn : m + l = n) : ¬ (schurSzegoComp n f g).IsRoot (-(a * b)) := by
  obtain ⟨R, hR, hRx⟩ :=
    exists_schurSzegoComp_eq_X_sub_C_pow_mul hf0 hg0 hf hg ha hb hm hl hn.ge
  rw [hR, hn, Nat.sub_self, pow_zero, one_mul]
  exact hRx

end RealRooted
