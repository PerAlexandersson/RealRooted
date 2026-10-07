import Mathlib

/-!
# Gurvits' univariate inequality

For a real-rooted real polynomial `q` with nonnegative coefficients and `natDegree q ≤ d`, if
`c * t ≤ q.eval t` for every `t > 0`, then `c * gurvitsFactor d ≤ q.coeff 1`, where
`gurvitsFactor d = ((d - 1) / d) ^ (d - 1)`; and `∏ i < n, gurvitsFactor (i + 1) = n! / nⁿ`.
These are the univariate ingredients of Gurvits' proof of the van der Waerden bound
(L. Gurvits, *Van der Waerden/Schrijver-Valiant like conjectures and stable (aka hyperbolic)
homogeneous polynomials*, Electron. J. Combin. 15 (2008)).
-/

noncomputable section

namespace RealRooted.Gurvits

section Inequality

open Polynomial Filter Topology


/-- Two-point AM–GM with weights `1 / (n + 1)` and `n / (n + 1)`, in power form. -/
theorem mul_pow_le_add_div_pow {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    u * v ^ n ≤ ((u + n * v) / (n + 1)) ^ (n + 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  rcases hv.eq_or_lt with rfl | hv
  · rw [zero_pow hn.ne', mul_zero]
    positivity
  obtain ⟨w, hw⟩ : ∃ w, w = (u + n * v) / (n + 1) := ⟨_, rfl⟩
  rw [← hw]
  have hw0 : 0 < w := hw ▸ by positivity
  have hb := one_add_mul_le_pow (a := w / v - 1) (by
    have : 0 ≤ w / v := by positivity
    linarith) (n + 1)
  rw [add_sub_cancel, div_pow, le_div_iff₀ (by positivity)] at hb
  have hwn : ((n : ℝ) + 1) * w = u + n * v := by
    rw [hw]
    field_simp
  calc u * v ^ n = (1 + ((n + 1 : ℕ) : ℝ) * (w / v - 1)) * v ^ (n + 1) := by
        push_cast
        field_simp
        linear_combination (-v ^ (n + 1)) * hwn
    _ ≤ w ^ (n + 1) := hb

/-- AM–GM for the factors `1 + x`, `x ∈ m`, padded to `d ≥ card m` factors:
`∏ (1 + x) ≤ (1 + (∑ x) / d) ^ d`. -/
theorem multiset_prod_one_add_le_pow (m : Multiset ℝ) (hm : ∀ x ∈ m, 0 ≤ x) (d : ℕ)
    (hd : m.card ≤ d) : (m.map (1 + ·)).prod ≤ (1 + m.sum / d) ^ d := by
  induction m using Multiset.induction_on generalizing d with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.card_cons] at hd
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by lia⟩
    have ha : 0 ≤ a := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ x ∈ m, 0 ≤ x := fun x hx => hm x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ m.sum := Multiset.sum_nonneg hm'
    have hv : 0 ≤ 1 + m.sum / e := by positivity
    have heS : (e : ℝ) * (1 + m.sum / e) = e + m.sum := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · have : m = 0 := Multiset.card_eq_zero.mp (by lia)
        simp [this]
      · field_simp
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    calc (1 + a) * (m.map (1 + ·)).prod ≤ (1 + a) * (1 + m.sum / e) ^ e := by
          gcongr
          exact ih hm' e (by lia)
      _ ≤ ((1 + a + e * (1 + m.sum / e)) / (e + 1)) ^ (e + 1) :=
          mul_pow_le_add_div_pow (by linarith) hv e
      _ = (1 + (a + m.sum) / ((e + 1 : ℕ) : ℝ)) ^ (e + 1) := by
          rw [heS]
          push_cast
          field_simp
          ring

/-- If `c * t ≤ A + B * t` for all `t > 0`, with `0 ≤ A`, then `c ≤ B`. -/
theorem le_of_forall_mul_le_add {A B c : ℝ} (hA : 0 ≤ A)
    (h : ∀ t > 0, c * t ≤ A + B * t) : c ≤ B := by
  by_contra! hc
  have hcB : 0 < c - B := by linarith
  have := h ((A + 1) / (c - B)) (by positivity)
  have h2 : (c - B) * ((A + 1) / (c - B)) = A + 1 := by field_simp
  nlinarith

/-- The optimisation step of Gurvits' argument: if `c * t ≤ a * (1 + s * t / d) ^ d` for all
`t > 0`, then `c * ((d - 1) / d) ^ (d - 1) ≤ a * s`. -/
theorem mul_pow_le_of_forall_mul_le {a s c : ℝ} {d : ℕ} (hd : 1 ≤ d) (ha : 0 ≤ a)
    (hs : 0 ≤ s) (h : ∀ t > 0, c * t ≤ a * (1 + s * t / d) ^ d) :
    c * (((d : ℝ) - 1) / d) ^ (d - 1) ≤ a * s := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hg0 : 0 ≤ ((d : ℝ) - 1) / d := div_nonneg (by linarith) (by linarith)
  rcases hs.eq_or_lt with rfl | hs
  · have hc : c ≤ 0 := le_of_forall_mul_le_add ha (B := 0) fun t ht => by simpa using h t ht
    rw [mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg hg0 _)
  obtain rfl | ⟨e, rfl⟩ : d = 1 ∨ ∃ e, d = e + 2 :=
    (Nat.lt_or_ge d 2).imp (by lia) fun h => ⟨d - 2, by lia⟩
  · norm_num
    refine le_of_forall_mul_le_add ha fun t ht => ?_
    have := h t ht
    norm_num at this
    linarith
  · rw [show e + 2 - 1 = e + 1 by lia]
    push_cast at h ⊢
    rw [show (e : ℝ) + 2 - 1 = e + 1 by ring]
    have he1 : (0 : ℝ) < e + 1 := by positivity
    have hx : 1 + s * ((e + 2) / (e + 1) / s) / (e + 2) = ((e : ℝ) + 2) / (e + 1) := by
      field_simp
      ring
    have hxy : ((e : ℝ) + 2) / (e + 1) * ((e + 1) / (e + 2)) = 1 := by
      field_simp
    have key := h ((e + 2) / (e + 1) / s) (by positivity)
    rw [hx] at key
    have hy0 : 0 ≤ ((e : ℝ) + 1) / (e + 2) := by positivity
    generalize ((e : ℝ) + 2) / (e + 1) = x at key hxy
    generalize ((e : ℝ) + 1) / (e + 2) = y at key hxy hy0 ⊢
    calc c * y ^ (e + 1) = c * (x / s) * (s * y ^ (e + 2)) := by
          field_simp
          linear_combination (-c * y ^ (e + 1)) * hxy
      _ ≤ a * x ^ (e + 2) * (s * y ^ (e + 2)) :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = a * s * (x * y) ^ (e + 2) := by ring
      _ = a * s := by rw [hxy, one_pow, mul_one]

/-- The constant and linear coefficients of `∏ (1 + c X)`. -/
theorem coeff_prod_one_add_C_mul_X (cs : Multiset ℝ) :
    (cs.map fun c => 1 + C c * X).prod.coeff 0 = 1 ∧
      (cs.map fun c => 1 + C c * X).prod.coeff 1 = cs.sum := by
  induction cs using Multiset.induction_on with
  | empty => simp [coeff_one]
  | cons a cs ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, add_mul, one_mul,
      mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul_zero, ih.1, ih.2]
    refine ⟨by simp, ?_⟩
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, ih.1]
    ring

/-- A polynomial with nonnegative coefficients is at least its constant term on `[0, ∞)`. -/
theorem coeff_zero_le_eval {q : ℝ[X]} (hq : ∀ n, 0 ≤ q.coeff n) {t : ℝ} (ht : 0 ≤ t) :
    q.coeff 0 ≤ q.eval t := by
  rw [eval_eq_sum_range]
  calc q.coeff 0 = q.coeff 0 * t ^ 0 := by simp
    _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * t ^ i :=
      Finset.single_le_sum (f := fun i => q.coeff i * t ^ i)
        (fun i _ => mul_nonneg (hq i) (pow_nonneg ht i)) (by simp)

/-- A split real polynomial with nonnegative coefficients and positive constant term factors as
`q = q(0) * ∏ (1 + c X)` with `c = -r⁻¹ ≥ 0` running over the roots `r` of `q`. -/
theorem eq_C_mul_prod_of_splits {q : ℝ[X]} (hs : q.Splits) (hq : ∀ n, 0 ≤ q.coeff n)
    (h0 : 0 < q.coeff 0) :
    (∀ c ∈ q.roots.map (fun r => -r⁻¹), 0 ≤ c) ∧
      q = C (q.coeff 0) * ((q.roots.map fun r => -r⁻¹).map fun c => 1 + C c * X).prod := by
  have hq0 : q ≠ 0 := fun h => by simp [h] at h0
  have hneg : ∀ r ∈ q.roots, r < 0 := by
    intro r hr
    by_contra! hr0
    have h1 := coeff_zero_le_eval hq hr0
    rw [((mem_roots hq0).1 hr).eq_zero] at h1
    linarith
  refine ⟨?_, ?_⟩
  · simp only [Multiset.mem_map]
    rintro c ⟨r, hr, rfl⟩
    have := hneg r hr
    have : r⁻¹ < 0 := inv_lt_zero.2 this
    linarith
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (splits_iff_card_roots.1 hs)
  have hX : ∀ r ∈ q.roots, X - C r = C (-r) * (1 + C (-r⁻¹) * X) := by
    intro r hr
    have hr0 : r ≠ 0 := (hneg r hr).ne
    rw [mul_add, mul_one, ← mul_assoc, ← C_mul]
    rw [show -r * -r⁻¹ = 1 by field_simp]
    simp only [C_1, one_mul, C_neg]
    ring
  rw [Multiset.map_congr rfl hX, Multiset.prod_map_mul,
    show (q.roots.map fun r => C (-r)) = (q.roots.map fun r => -r).map C by
      simp [Multiset.map_map],
    ← map_multiset_prod, ← mul_assoc, ← C_mul] at hfac
  rw [Multiset.map_map]
  set Q := (q.roots.map fun r => 1 + C (-r⁻¹) * X).prod with hQ
  have hQ0 : Q.coeff 0 = 1 := by
    have := (coeff_prod_one_add_C_mul_X (q.roots.map fun r => -r⁻¹)).1
    rwa [Multiset.map_map] at this
  have hb : q.coeff 0 = q.leadingCoeff * (q.roots.map fun r => -r).prod := by
    conv_lhs => rw [← hfac]
    rw [coeff_C_mul, hQ0, mul_one]
  rw [hb]
  exact hfac.symm

/-- **Gurvits' univariate inequality.** Let `q` be a real-rooted (split) real polynomial with
nonnegative coefficients and `q.natDegree ≤ d`, where `1 ≤ d`. If `c * t ≤ q.eval t` for all
`t > 0`, then `c * ((d - 1) / d) ^ (d - 1) ≤ q.coeff 1`. -/
theorem mul_le_coeff_one_of_splits {q : ℝ[X]} (hs : q.Splits) (hq : ∀ n, 0 ≤ q.coeff n)
    {d : ℕ} (hdeg : q.natDegree ≤ d) (hd : 1 ≤ d) {c : ℝ}
    (h : ∀ t > 0, c * t ≤ q.eval t) :
    c * (((d : ℝ) - 1) / d) ^ (d - 1) ≤ q.coeff 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hg0 : 0 ≤ ((d : ℝ) - 1) / d := div_nonneg (by linarith) (by linarith)
  have hg1 : ((d : ℝ) - 1) / d ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hgp0 := pow_nonneg hg0 (d - 1)
  have hgp1 := pow_le_one₀ (n := d - 1) hg0 hg1
  rcases (hq 0).eq_or_lt with h0 | h0
  · obtain ⟨r, rfl⟩ := X_dvd_iff.2 h0.symm
    have h1 : (X * r).coeff 1 = r.eval 0 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_zero_eq_eval_zero]
    have hk : 0 ≤ r.eval 0 := h1 ▸ hq 1
    have hle : c ≤ r.eval 0 := by
      have hlim : Tendsto (fun t => r.eval t) (𝓝[>] 0) (𝓝 (r.eval 0)) :=
        (r.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto hlim (eventually_of_mem self_mem_nhdsWithin fun t ht => ?_)
      have ht : (0 : ℝ) < t := ht
      have := h t ht
      rw [eval_mul, eval_X, mul_comm t] at this
      exact le_of_mul_le_mul_right this ht
    rw [h1]
    nlinarith
  · obtain ⟨hcs, hfac⟩ := eq_C_mul_prod_of_splits hs hq h0
    have hcard : (q.roots.map fun r => -r⁻¹).card ≤ d := by
      rw [Multiset.card_map]
      exact (card_roots' q).trans hdeg
    generalize q.roots.map (fun r => -r⁻¹) = cs at hcs hfac hcard
    have hcoeff1 : q.coeff 1 = q.coeff 0 * cs.sum := by
      conv_lhs => rw [hfac]
      rw [coeff_C_mul, (coeff_prod_one_add_C_mul_X cs).2]
    have heval : ∀ t > 0, c * t ≤ q.coeff 0 * (1 + cs.sum * t / d) ^ d := by
      intro t ht
      have hm : ∀ x ∈ cs.map (· * t), 0 ≤ x := by
        simp only [Multiset.mem_map]
        rintro x ⟨y, hy, rfl⟩
        exact mul_nonneg (hcs y hy) ht.le
      calc c * t ≤ q.eval t := h t ht
        _ = q.coeff 0 * ((cs.map (· * t)).map (1 + ·)).prod := by
            conv_lhs => rw [hfac]
            rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
            congr 2
            exact Multiset.map_congr rfl fun x _ => by simp
        _ ≤ q.coeff 0 * (1 + (cs.map (· * t)).sum / d) ^ d :=
            mul_le_mul_of_nonneg_left
              (multiset_prod_one_add_le_pow _ hm d (by rwa [Multiset.card_map])) h0.le
        _ = q.coeff 0 * (1 + cs.sum * t / d) ^ d := by simp [Multiset.sum_map_mul_right]
    rw [hcoeff1]
    exact mul_pow_le_of_forall_mul_le hd h0.le (Multiset.sum_nonneg hcs) heval

end Inequality

section Factor

/-- The constant `((d - 1) / d) ^ (d - 1)` in Gurvits' inequality. -/
noncomputable def gurvitsFactor (d : ℕ) : ℝ := (((d : ℝ) - 1) / d) ^ (d - 1)

@[simp]
theorem gurvitsFactor_zero : gurvitsFactor 0 = 1 := by simp [gurvitsFactor]

theorem gurvitsFactor_succ (n : ℕ) :
    gurvitsFactor (n + 1) = ((n : ℝ) / (n + 1)) ^ n := by
  simp [gurvitsFactor]

@[simp]
theorem gurvitsFactor_one : gurvitsFactor 1 = 1 := by simp [gurvitsFactor_succ]

theorem gurvitsFactor_nonneg (d : ℕ) : 0 ≤ gurvitsFactor d := by
  rcases d with _ | n
  · simp
  rw [gurvitsFactor_succ]
  positivity

/-- `gurvitsFactor` is antitone on `ℕ` (it decreases from `1` towards `1 / e`). -/
theorem gurvitsFactor_antitone : Antitone gurvitsFactor := by
  refine antitone_nat_of_succ_le fun d => ?_
  rcases d with _ | e
  · simp [gurvitsFactor]
  rcases e with _ | e
  · norm_num [gurvitsFactor_succ]
  rw [gurvitsFactor_succ, gurvitsFactor_succ]
  have key := mul_pow_le_add_div_pow zero_le_one (v := ((e : ℝ) + 2) / (e + 1))
    (by positivity) (e + 1)
  have h1 : (1 + ((e + 1 : ℕ) : ℝ) * ((e + 2) / (e + 1))) / ((e + 1 : ℕ) + 1)
      = ((e : ℝ) + 3) / (e + 2) := by
    push_cast
    field_simp
    ring
  rw [h1, one_mul] at key
  have hA : ((e + 1 + 1 : ℕ) : ℝ) / ((e + 1 + 1 : ℕ) + 1)
      = (((e : ℝ) + 3) / (e + 2))⁻¹ := by
    rw [inv_div]
    push_cast
    ring
  have hB : ((e + 1 : ℕ) : ℝ) / ((e + 1 : ℕ) + 1) = (((e : ℝ) + 2) / (e + 1))⁻¹ := by
    rw [inv_div]
    push_cast
    ring
  rw [hA, hB, inv_pow, inv_pow]
  exact inv_anti₀ (by positivity) key

theorem gurvitsFactor_le_one (d : ℕ) : gurvitsFactor d ≤ 1 :=
  gurvitsFactor_zero ▸ gurvitsFactor_antitone (Nat.zero_le d)

/-- The product of the Gurvits constants: `∏ i ∈ range n, gurvitsFactor (i + 1) = n! / n ^ n`.
This holds for every `n`, including `n = 0` (both sides equal `1`). -/
theorem prod_range_gurvitsFactor (n : ℕ) :
    ∏ i ∈ Finset.range n, gurvitsFactor (i + 1) = n.factorial / (n : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, gurvitsFactor_succ]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.factorial_succ, div_pow]
    push_cast
    field_simp
    ring

end Factor

end RealRooted.Gurvits
