module

public import RealRooted.BorceaBranden.Transcendental.JensenMultiplier
public import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization.Derivative
public import RealRooted.BoundarySpecializationGeneral

@[expose] public noncomputable section

open Filter Topology

namespace RealRooted.BorceaBranden

variable {σ : Type*} [Fintype σ]

/-! ## Auxiliary lemmas -/

omit [Fintype σ] in
open _root_.MvPolynomial in
private lemma hasDerivAt_eval_update [DecidableEq σ] (i : σ) (z : σ → ℂ)
    (p : MvPolynomial σ ℂ) (x : ℂ) :
    HasDerivAt (fun y : ℂ => eval (Function.update z i y) p)
      (eval (Function.update z i x) (pderiv i p)) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const x c
  | add p q hp hq => simpa using hp.fun_add hq
  | mul_X p j hp =>
    have hj : HasDerivAt (fun y : ℂ => Function.update z i y j)
        (Pi.single (M := fun _ => ℂ) i 1 j) x := by
      by_cases hji : j = i
      · subst hji; simpa using hasDerivAt_id' x
      · simpa [Function.update_of_ne hji, Pi.single_apply, hji] using
          hasDerivAt_const x (z j)
    have heq :
        eval (Function.update z i x) (pderiv i (p * X j)) =
          eval (Function.update z i x) (pderiv i p) * Function.update z i x j +
            eval (Function.update z i x) p *
              Pi.single (M := fun _ => ℂ) i 1 j := by
      rw [pderiv_mul]
      simp only [map_add, map_mul, eval_X]
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    convert hp.fun_mul hj using 1
    · funext y
      simp

omit [Fintype σ] in
private lemma norm_eval_le_specializeZero_add [Finite σ]
    (i : σ) (p : MvPolynomial σ ℂ) {r M : ℝ}
    (hM : ∀ w : σ → ℂ, (∀ j, ‖w j‖ ≤ r) →
      ‖MvPolynomial.eval w (MvPolynomial.pderiv i p)‖ ≤ M)
    (z : σ → ℂ) (hz : ∀ j, ‖z j‖ ≤ r) :
    ‖MvPolynomial.eval z p‖ ≤
      ‖MvPolynomial.eval z (MvPolynomial.specializeZero i p)‖ + r * M := by
  classical
  let := Fintype.ofFinite σ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  set h : ℝ → ℂ := fun t =>
    MvPolynomial.eval (Function.update z i ((t : ℂ) * z i)) p with hh
  have hd : ∀ t : ℝ, HasDerivAt h
      (MvPolynomial.eval (Function.update z i ((t : ℂ) * z i))
        (MvPolynomial.pderiv i p) * z i) t := by
    intro t
    have h1 := hasDerivAt_eval_update i z p ((t : ℂ) * z i)
    have h2 : HasDerivAt (fun y : ℂ => y * z i) (1 * z i) (t : ℂ) :=
      (hasDerivAt_id (t : ℂ)).mul_const (z i)
    have h3 := (h1.comp (t : ℂ) h2).comp_ofReal
    simpa using h3
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := h) (a := 0) (b := 1)
    (C := M * r) (fun t _ => (hd t).hasDerivWithinAt) ?_ 1 (by simp)
  · have e1 : h 1 = MvPolynomial.eval z p := by simp [hh]
    have e0 : h 0 = MvPolynomial.eval z (MvPolynomial.specializeZero i p) := by
      simp [hh, MvPolynomial.eval_specializeZero]
    rw [e1, e0] at key
    have := norm_sub_norm_le (MvPolynomial.eval z p)
      (MvPolynomial.eval z (MvPolynomial.specializeZero i p))
    nlinarith
  · intro t ht
    rw [norm_mul]
    apply mul_le_mul _ (hz i) (norm_nonneg _) hM0
    apply hM
    intro j
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      nlinarith [hz j, norm_nonneg (z j), abs_nonneg t]
    · simp [Function.update_of_ne hji, hz j]

private def UniformBound (a : (σ →₀ ℕ) → ℂ) : Prop :=
  ∀ (κ : ℕ → (σ →₀ ℕ) → ℝ) (f : ℕ → MvPolynomial σ ℂ),
    (∀ m α, (f m).coeff α = (κ m α : ℂ) * a α) →
    (∀ α, Tendsto (fun m => κ m α) atTop (𝓝 1)) →
    (∀ m, MvUpperHalfPlaneStable (f m) ∨ f m = 0) →
    ∃ (B C : ℝ) (m₀ : ℕ),
      ∀ m ≥ m₀, ∀ r : ℝ, 0 ≤ r → ∀ z : σ → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ‖MvPolynomial.eval z (f m)‖ ≤ B * Real.exp (C * r ^ 2)

omit [Fintype σ] in
private lemma uniformBound_zero (a : (σ →₀ ℕ) → ℂ) (ha : ∀ α, a α = 0) :
    UniformBound a := by
  intro κ f hcoef _ _
  refine ⟨0, 0, 0, fun m _ r _ z _ => ?_⟩
  have : f m = 0 := by
    ext α; simp [hcoef, ha]
  simp [this]

private lemma le_exp_sq (r : ℝ) : r ≤ Real.exp (r ^ 2) := by
  have := Real.add_one_le_exp (r ^ 2)
  nlinarith [sq_nonneg (r - 1)]

omit [Fintype σ] in
private lemma uniformBound_step [Finite σ] (a : (σ →₀ ℕ) → ℂ) (i : σ)
    (h1 : UniformBound (fun α => if α i = 0 then a α else 0))
    (h2 : UniformBound (fun α => ((α i : ℂ) + 1) * a (α + Finsupp.single i 1))) :
    UniformBound a := by
  classical
  let := Fintype.ofFinite σ
  intro κ f hcoef hκ hst
  obtain ⟨B1, C1, m1, hb1⟩ := h1 κ
    (fun m => MvPolynomial.specializeZero i (f m))
    (fun m α => by
      rw [MvPolynomial.coeff_specializeZero, hcoef]
      by_cases h : α i = 0 <;> simp [h])
    hκ
    (fun m => by
      rcases hst m with h | h
      · rcases h.specializeZero_zero_or_general i with hzero | hstable
        · exact Or.inr hzero
        · exact Or.inl hstable
      · right
        rw [h, MvPolynomial.specializeZero_zero])
  obtain ⟨B2, C2, m2, hb2⟩ := h2 (fun m α => κ m (α + Finsupp.single i 1))
    (fun m => MvPolynomial.pderiv i (f m))
    (fun m α => by rw [MvPolynomial.coeff_pderiv, hcoef]; ring)
    (fun α => hκ _)
    (fun m => by
      rcases hst m with h | h
      · rcases h.pderiv_zero_or_of_finite i with hzero | hstable
        · exact Or.inr hzero
        · exact Or.inl hstable
      · right; show MvPolynomial.pderiv i (f m) = 0; rw [h, map_zero])
  refine ⟨max B1 0 + max B2 0, max C1 (C2 + 1), max m1 m2, fun m hm r hr z hz => ?_⟩
  have hm1 : m ≥ m1 := le_trans (le_max_left _ _) hm
  have hm2 : m ≥ m2 := le_trans (le_max_right _ _) hm
  have key := norm_eval_le_specializeZero_add i (f m) (hb2 m hm2 r hr) z hz
  have e1 := hb1 m hm1 r hr z hz
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have x1 : B1 * Real.exp (C1 * r ^ 2) ≤ max B1 0 * Real.exp (max C1 (C2 + 1) * r ^ 2) := by
    apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le (le_max_right _ _)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hr2)
  have x2 : r * (B2 * Real.exp (C2 * r ^ 2)) ≤
      max B2 0 * Real.exp (max C1 (C2 + 1) * r ^ 2) := by
    have h3 : r * (B2 * Real.exp (C2 * r ^ 2)) ≤ r * (max B2 0 * Real.exp (C2 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) hr
    have h4 : r * (max B2 0 * Real.exp (C2 * r ^ 2)) ≤
        Real.exp (r ^ 2) * (max B2 0 * Real.exp (C2 * r ^ 2)) :=
      mul_le_mul_of_nonneg_right (le_exp_sq r)
        (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
    have h5 : Real.exp (r ^ 2) * (max B2 0 * Real.exp (C2 * r ^ 2)) =
        max B2 0 * Real.exp ((C2 + 1) * r ^ 2) := by
      rw [add_mul, one_mul, Real.exp_add]; ring
    have h6 : max B2 0 * Real.exp ((C2 + 1) * r ^ 2) ≤
        max B2 0 * Real.exp (max C1 (C2 + 1) * r ^ 2) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hr2))
        (le_max_right _ _)
    linarith
  rw [add_mul]
  linarith

omit [Fintype σ] in
private lemma uniformBound_const [Finite σ] (a : (σ →₀ ℕ) → ℂ) (ha : a 0 ≠ 0) :
    UniformBound a := by
  let _ := Fintype.ofFinite σ
  intro κ f hcoef hκ hst
  set K : (σ →₀ ℕ) → ℝ := fun α => 4 * ‖a α‖ / ‖a 0‖ with hKdef
  set Cst : ℝ := 6 * Real.exp 1 ^ 2 * (∑ i, K (Finsupp.single i 1)) ^ 2 +
    4 * Real.exp 1 ^ 2 * ∑ i, ∑ j, K (Finsupp.single i 1 + Finsupp.single j 1) with hCst
  set B0 : ℝ := (2 : ℝ) ^ (Fintype.card σ) *
    (Real.sqrt (2 * Real.exp 1 ^ 2 - Real.exp 1) / (Real.exp 1 - 1)) with hB0
  have hB0nn : 0 ≤ B0 := by
    have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact mul_nonneg (by positivity) (div_nonneg (Real.sqrt_nonneg _) (by linarith))
  have hb : ∀ α, ∀ᶠ m in atTop, κ m α ∈ Set.Ioo (1 / 2 : ℝ) 2 := fun α =>
    (hκ α).eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have ev1 := Filter.eventually_all.2 fun i => hb (Finsupp.single i 1)
  have ev2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    hb (Finsupp.single i 1 + Finsupp.single j 1)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 ((hb 0).and (ev1.and ev2))
  refine ⟨2 * ‖a 0‖ * B0, Cst, m₀, fun m hm r hr z hz => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hm₀ m hm
  set c := (f m).coeff 0 with hcdef
  have hc : c = (κ m 0 : ℂ) * a 0 := hcoef m 0
  have hκ0 : (κ m 0 : ℂ) ≠ 0 := by
    have := h0.1; exact_mod_cast (show κ m 0 ≠ 0 by linarith)
  have hc0 : c ≠ 0 := by rw [hc]; exact mul_ne_zero hκ0 ha
  have hfm : f m ≠ 0 := by
    intro h; apply hc0; rw [hcdef, h]; simp
  have hstab : MvUpperHalfPlaneStable (f m) := (hst m).resolve_right hfm
  set g := MvPolynomial.C c⁻¹ * f m with hgdef
  have hgcoeff : ∀ α, g.coeff α = c⁻¹ * (f m).coeff α := fun α =>
    MvPolynomial.coeff_C_mul _ _ _
  have hg0 : g.coeff 0 = 1 := by rw [hgcoeff, ← hcdef, inv_mul_cancel₀ hc0]
  have hgstab : MvUpperHalfPlaneStable g := by
    intro w hw
    rw [hgdef, map_mul, MvPolynomial.eval_C]
    exact mul_ne_zero (inv_ne_zero hc0) (hstab w hw)
  have hJ : ∀ β, MvUpperHalfPlaneStable (MvPolynomial.jensenOp β g) := fun β =>
    (jensenOp_stableOrZero β hgstab).resolve_left (fun h => by
      have hcoeff : (MvPolynomial.jensenOp β g).coeff 0 = 0 := by
        rw [h]
        simp
      rw [MvPolynomial.coeff_jensenOp] at hcoeff
      have hj : MvPolynomial.jensen 0 β = 1 := by
        simp [MvPolynomial.jensen]
      rw [hj, Complex.ofReal_one, one_mul, hg0] at hcoeff
      exact one_ne_zero hcoeff)
  have hsz := MvPolynomial.norm_eval_le_of_forall_jensenOp_stable g hg0 hJ hr z hz
  have hK : ∀ α, κ m α ∈ Set.Ioo (1 / 2 : ℝ) 2 → ‖g.coeff α‖ ≤ K α := by
    intro α hα
    rw [hgcoeff, hcoef, hc, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith [h0.1]),
      abs_of_pos (by linarith [hα.1])]
    have ha0 : 0 < ‖a 0‖ := norm_pos_iff.2 ha
    have e : (κ m 0 * ‖a 0‖)⁻¹ * (κ m α * ‖a α‖) =
        (κ m α / κ m 0) * (‖a α‖ / ‖a 0‖) := by
      field_simp
    rw [e, hKdef]
    have hq : κ m α / κ m 0 ≤ 4 := by
      rw [div_le_iff₀ (by linarith [h0.1])]; nlinarith [hα.2, h0.1]
    calc κ m α / κ m 0 * (‖a α‖ / ‖a 0‖) ≤ 4 * (‖a α‖ / ‖a 0‖) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = 4 * ‖a α‖ / ‖a 0‖ := by ring
  have hC : MvPolynomial.szaszC g ≤ Cst := by
    unfold MvPolynomial.szaszC
    rw [hCst]
    gcongr with i _ i _ j _
    · exact hK _ (h1 i)
    · exact hK _ (h2 i j)
  have hfeq : MvPolynomial.eval z (f m) = c * MvPolynomial.eval z g := by
    rw [hgdef, map_mul, MvPolynomial.eval_C, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hcn : ‖c‖ ≤ 2 * ‖a 0‖ := by
    rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [h0.1])]
    exact mul_le_mul_of_nonneg_right h0.2.le (norm_nonneg _)
  rw [hfeq, norm_mul]
  calc ‖c‖ * ‖MvPolynomial.eval z g‖
      ≤ (2 * ‖a 0‖) * (B0 * Real.exp (MvPolynomial.szaszC g * r ^ 2)) :=
        mul_le_mul hcn hsz (norm_nonneg _) (by positivity)
    _ ≤ (2 * ‖a 0‖) * (B0 * Real.exp (Cst * r ^ 2)) := by
        gcongr
    _ = 2 * ‖a 0‖ * B0 * Real.exp (Cst * r ^ 2) := by ring

open Classical in
private def nvars (a : (σ →₀ ℕ) → ℂ) : ℕ :=
  (Finset.univ.filter fun i => ∃ α, a α ≠ 0 ∧ α i ≠ 0).card

private lemma nvars_slice_lt (a : (σ →₀ ℕ) → ℂ) (i : σ)
    (α₀ : σ →₀ ℕ) (h0 : a α₀ ≠ 0)
    (hi : α₀ i ≠ 0) : nvars (fun α => if α i = 0 then a α else 0) < nvars a := by
  classical
  unfold nvars
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨α₀, h0, hi⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro β hβ
      split_ifs at hβ with h
      · exact fun h' => h' h
      · exact absurd rfl hβ
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨β, hβ, hj⟩ := hj
    split_ifs at hβ with h
    · exact ⟨β, hβ, hj⟩
    · exact absurd rfl hβ

private lemma nvars_pderiv_le (a : (σ →₀ ℕ) → ℂ) (i : σ) :
    nvars (fun α => ((α i : ℂ) + 1) * a (α + Finsupp.single i 1)) ≤ nvars a := by
  classical
  unfold nvars
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨β, hβ, hj⟩ := hj
  refine ⟨β + Finsupp.single i 1, right_ne_zero_of_mul hβ, ?_⟩
  simp only [Finsupp.add_apply]
  lia

private lemma sum_sub_single_add_one (α : σ →₀ ℕ) (i : σ) (hi : α i ≠ 0) :
    ∑ j, (α - Finsupp.single i 1 : σ →₀ ℕ) j + 1 = ∑ j, α j := by
  classical
  have hle : Finsupp.single i 1 ≤ α := by rw [Finsupp.single_le_iff]; lia
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  simp [Finsupp.single_apply]

private lemma uniformBound_of_nvars :
    ∀ n, ∀ a : (σ →₀ ℕ) → ℂ, nvars a = n → UniformBound a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have inner : ∀ d, ∀ a : (σ →₀ ℕ) → ℂ, nvars a ≤ n →
      (∃ α, a α ≠ 0 ∧ ∑ j, α j ≤ d) → UniformBound a := by
    intro d
    induction d with
    | zero =>
      rintro a - ⟨α, hα, hd⟩
      have : α = 0 := by
        ext j
        have := Finset.single_le_sum (f := fun j => α j) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ j)
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        lia
      subst this
      exact uniformBound_const a hα
    | succ d ihd =>
      rintro a hn ⟨α, hα, hd⟩
      by_cases hlow : ∃ α', a α' ≠ 0 ∧ ∑ j, α' j ≤ d
      · exact ihd a hn hlow
      push Not at hlow
      have hdeg : ∑ j, α j = d + 1 := by have := hlow α hα; lia
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h
        push Not at h
        simp [h] at hdeg
      classical
      apply uniformBound_step a i
      · exact ih _ (lt_of_lt_of_le (nvars_slice_lt a i α hα hi) hn) _ rfl
      · apply ihd _ (le_trans (nvars_pderiv_le a i) hn)
        have hle : Finsupp.single i 1 ≤ α := by rw [Finsupp.single_le_iff]; lia
        refine ⟨(α - Finsupp.single i 1 : σ →₀ ℕ), ?_, ?_⟩
        · rw [tsub_add_cancel_of_le hle]
          refine mul_ne_zero ?_ hα
          norm_cast
        · have := sum_sub_single_add_one α i hi
          lia
  intro a ha
  by_cases h : ∃ α, a α ≠ 0
  · obtain ⟨α, hα⟩ := h
    exact inner _ a ha.le ⟨α, hα, le_rfl⟩
  · push Not at h
    exact uniformBound_zero a h

/-! ## Target -/

omit [Fintype σ] in
/-- **Uniform multivariate Szász growth bound** (Borcea--Brändén,
arXiv:0809.0401, Theorem 5.6, in the form needed for Theorem 5.1).
This version is proved by induction on the number of variables
occurring in the support of `a` and the minimal total degree of the support of `a`.  This avoids
the paper's invalid claim that partial differentiation always lowers the largest degree among
minimal support elements by one.

Let `a : (σ →₀ ℕ) → ℂ` be a fixed coefficient family and let `κ m α → 1`
for each `α`.
Suppose the polynomial `f m` with coefficients `κ m α * a α` is stable or zero for every `m`.
In the application, `f m = ∑_{α ≤ β_m} J(α, β_m) P_α z^α` for `β_m = (m,…,m)`.
Then there are `B`, `C`, and `m₀` with `|f m (z)| ≤ B e^{C r²}` for all `m ≥ m₀` and all
`z` with `|z_i| ≤ r`.

Proof sketch.  If `a = 0` every `f m` is zero.  Otherwise let `d` be the minimal total degree in the
support of `a` and `μ` the number of variables occurring in the support of `a`.  Induct
lexicographically on `(μ, d)`, over all `(a, κ, f)` satisfying the hypotheses (the statement is
closed under the two operations below, which is why it is quantified over all of them):
* If `d = 0`, then `a 0 ≠ 0` and `f m 0 = κ m 0 * a 0 → a 0 ≠ 0`.  Thus the constant term is
  nonzero for large `m`.  The normalized polynomial `g m = f m / f m 0` has constant
  coefficient `1`, and all `MvPolynomial.jensenOp β (g m)` are stable by Lemma 5.2.
  The zero alternative is impossible because `MvPolynomial.jensen 0 β = 1`.
  Theorem 5.5 gives `‖g m z‖ ≤ B' e^{C_m r²}`, where
  `C_m = MvPolynomial.szaszC (g m)` and `B'` is independent of
  `m`.  Since `coeff α (g m) = κ m α a α / (κ m 0 a 0)` converges,
  `C_m` is bounded for `m ≥ m₀`
  (a convergent real sequence is bounded) and `‖f m 0‖` is bounded.
* If `d ≥ 1`, pick `α₀` in the support of `a` with `|α₀| = d` and `i` with `α₀ i > 0`.
  Write `f m (z) = specializeZero i (f m) (z) +
  z_i ∫₀¹ (pderiv i (f m)) (z_i t, z') dt` by the
  fundamental theorem of calculus for `t ↦ f m (z with z_i := t z_i)` on `[0,1]`.  Thus, with
  `|g|_r = sup_{|z_j| ≤ r} |g(z)|`:
  `|f m|_r ≤ |specializeZero i (f m)|_r + r |pderiv i (f m)|_r`.
  Both are in the class.  The polynomial `pderiv i (f m)` has coefficients
  `κ m (α + e_i) * ((α i + 1) * a (α + e_i))`
  (multipliers `κ'_m α = κ m (α + e_i) → 1`), minimal
  degree of its family `d - 1` (it contains `α₀ - e_i` and nothing below
  degree `d - 1`) and at most
  `μ` variables.  The polynomial `specializeZero i (f m)` has coefficients
  `κ m α * (if α i = 0 then a α else 0)` and at most `μ - 1` variables.
  The induction hypothesis gives
  `B₁ e^{C₁ r²}` and `B₂ e^{C₂ r²}`.  Use `r ≤ e^{r²}` to combine the bounds. -/
theorem exists_norm_eval_le_exp_sq [Finite σ] (a : (σ →₀ ℕ) → ℂ)
    (κ : ℕ → (σ →₀ ℕ) → ℝ)
    (f : ℕ → MvPolynomial σ ℂ)
    (hcoef : ∀ m α, (f m).coeff α = (κ m α : ℂ) * a α)
    (hκ : ∀ α, Tendsto (fun m => κ m α) atTop (𝓝 1))
    (hst : ∀ m, MvUpperHalfPlaneStable (f m) ∨ f m = 0) :
    ∃ (B C : ℝ) (m₀ : ℕ),
      ∀ m ≥ m₀, ∀ r : ℝ, 0 ≤ r → ∀ z : σ → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ‖MvPolynomial.eval z (f m)‖ ≤ B * Real.exp (C * r ^ 2) := by
  let _ := Fintype.ofFinite σ
  exact uniformBound_of_nvars _ a rfl κ f hcoef hκ hst

end RealRooted.BorceaBranden
