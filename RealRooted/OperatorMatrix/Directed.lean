import RealRooted.Derivative.SimpleRoots
import RealRooted.EulerOperator.Pencil
import RealRooted.Interlacing.OuterDifference
import RealRooted.QuadraticInterlacingClosure

/-!
# Directed differential comparisons for PF polynomials

Directed (zero-aware) comparisons between a PF polynomial `p` and `p'`, `θ p = X p'` and `X p`,
`X`-duality, and the mixed differential lemma `p' + q' ≤ q + X p'` for coprime strictly
interlacing inputs.  These are the differential facts behind the `{1, θ, X}` block
classification of operator matrices (issue #1741).
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem eval_sub_X_mul_derivative_mul_eval_pos
    {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree = g.natDegree)
    (hfdeg : 2 ≤ f.natDegree)
    (hf_simple : HasSimpleRoots f)
    (hno : ∀ x, f.IsRoot x → ¬ g.IsRoot x)
    (hf_roots_neg : ∀ x, f.IsRoot x → x < 0)
    (hf_zero : 0 < f.eval 0) (hg_zero : 0 < g.eval 0)
    {r : ℝ} (hr : f.derivative.IsRoot r) :
    0 < (g - X * g.derivative).eval r * f.eval r := by
  have hf_ne : f ≠ 0 := hf_pos.ne_zero
  have hg_ne : g ≠ 0 := hg_pos.ne_zero
  have hf_nodup : f.roots.Nodup := hf_simple.roots_nodup
  let a : ℝ := g.leadingCoeff / f.leadingCoeff
  let u : ℝ[X] := g - C a * f
  have hu_degree : u.degree < f.natDegree := by
    dsimp [u, a]
    exact degree_sub_c₀_mul_lt hf_ne hg_ne hdeg.symm hf_pos
  have hu_lagrange : lagInterp f u = u :=
    lagInterp_eq_g hfg.1.2 hf_nodup (by lia) hu_degree
  have hr_not_root : ¬ f.IsRoot r := by
    intro hfr
    exact (hf_simple.eval_derivative_ne_zero hfr) hr
  have hfr_ne : f.eval r ≠ 0 := by
    simpa [Polynomial.IsRoot.def] using hr_not_root
  have hfr_der : f.derivative.eval r = 0 := hr
  have hroot (s : ℝ) (hs : s ∈ f.roots.toFinset) : f.IsRoot s :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
  have hroot_data (s : ℝ) (hs : s ∈ f.roots.toFinset) :
      s < 0 ∧ r - s ≠ 0 ∧
        u.eval s / f.derivative.eval s = g.eval s / f.derivative.eval s := by
    refine ⟨hf_roots_neg s (hroot s hs), sub_ne_zero.mpr ?_, ?_⟩
    · intro hrs
      subst r
      exact hr_not_root (hroot s hs)
    · simp [u, Polynomial.IsRoot.def.mp (hroot s hs)]
  have hquot_eval (x s : ℝ) (hs : s ∈ f.roots.toFinset) (hxs : x - s ≠ 0) :
      (f /ₘ (X - C s)).eval x = f.eval x / (x - s) := by
    have hfactor := congrArg (Polynomial.eval x)
      (mul_divByMonic_eq_iff_isRoot.mpr (hroot s hs))
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hfactor
    exact (eq_div_iff hxs).mpr (by simpa [mul_comm] using hfactor)
  have hquot_derivative_eval (s : ℝ) (hs : s ∈ f.roots.toFinset) :
      (f /ₘ (X - C s)).derivative.eval r =
        -f.eval r / (r - s) ^ 2 := by
    have hfactor := congrArg (fun p : ℝ[X] ↦ p.derivative.eval r)
      (mul_divByMonic_eq_iff_isRoot.mpr (hroot s hs))
    have hrs := (hroot_data s hs).2.1
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C] at hfactor
    rw [hfr_der] at hfactor
    calc
      (f /ₘ (X - C s)).derivative.eval r =
          -(f /ₘ (X - C s)).eval r / (r - s) := by
        rw [eq_div_iff hrs]
        linarith
      _ = -(f.eval r / (r - s)) / (r - s) := by
        rw [hquot_eval r s hs (hroot_data s hs).2.1]
      _ = -f.eval r / (r - s) ^ 2 := by field_simp
  have hu_eval :
      u.eval r = ∑ s ∈ f.roots.toFinset,
        (g.eval s / f.derivative.eval s) * (f.eval r / (r - s)) := by
    rw [← hu_lagrange]
    simp only [lagInterp, eval_finsetSum, eval_mul, eval_C]
    apply Finset.sum_congr rfl; intro s hs
    rw [(hroot_data s hs).2.2, hquot_eval r s hs (hroot_data s hs).2.1]
  have hu_derivative_eval :
      u.derivative.eval r = ∑ s ∈ f.roots.toFinset,
        (g.eval s / f.derivative.eval s) *
          (-f.eval r / (r - s) ^ 2) := by
    rw [← hu_lagrange]
    simp only [lagInterp, map_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C]
    apply Finset.sum_congr rfl; intro s hs
    rw [(hroot_data s hs).2.2, hquot_derivative_eval s hs]
  have hu_zero :
      u.eval 0 = ∑ s ∈ f.roots.toFinset,
        (g.eval s / f.derivative.eval s) * (f.eval 0 / (0 - s)) := by
    rw [← hu_lagrange]
    simp only [lagInterp, eval_finsetSum, eval_mul, eval_C]
    apply Finset.sum_congr rfl; intro s hs
    rw [(hroot_data s hs).2.2]
    have hs_ne : 0 - s ≠ 0 := by linarith [(hroot_data s hs).1]
    rw [hquot_eval 0 s hs hs_ne]
  have ha_zero :
      a = g.eval 0 / f.eval 0 +
        ∑ s ∈ f.roots.toFinset,
          (g.eval s / f.derivative.eval s) / s := by
    have hform : g.eval 0 = a * f.eval 0 + u.eval 0 := by simp [u]
    calc
      a = (a * f.eval 0) / f.eval 0 := by
        rw [mul_div_cancel_right₀ a hf_zero.ne']
      _ = (g.eval 0 - u.eval 0) / f.eval 0 := by rw [hform]; ring
      _ = g.eval 0 / f.eval 0 - u.eval 0 / f.eval 0 := by rw [sub_div]
      _ = g.eval 0 / f.eval 0 +
          ∑ s ∈ f.roots.toFinset,
            (g.eval s / f.derivative.eval s) / s := by
        rw [hu_zero, Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl; intro s hs
        have hs_ne : s ≠ 0 := by linarith [(hroot_data s hs).1]
        field_simp; ring
  have hmain :
      g.eval r - r * g.derivative.eval r =
        f.eval r * (g.eval 0 / f.eval 0 +
          ∑ s ∈ f.roots.toFinset,
            (g.eval s / f.derivative.eval s) * r ^ 2 /
              (s * (r - s) ^ 2)) := by
    have hform_eval : g.eval r = a * f.eval r + u.eval r := by
      simp [u]
    have hform_der_eval : g.derivative.eval r =
        a * f.derivative.eval r + u.derivative.eval r := by
      simp [u]
    rw [hform_eval, hform_der_eval, hfr_der, mul_zero, zero_add,
      hu_eval, hu_derivative_eval, ha_zero]
    have hsum :
        (∑ s ∈ f.roots.toFinset,
            (g.eval s / f.derivative.eval s) / s * f.eval r) +
          (∑ s ∈ f.roots.toFinset,
            (g.eval s / f.derivative.eval s) * (f.eval r / (r - s))) -
          (∑ s ∈ f.roots.toFinset,
            r * ((g.eval s / f.derivative.eval s) * (-f.eval r / (r - s) ^ 2))) =
          ∑ s ∈ f.roots.toFinset,
            f.eval r * ((g.eval s / f.derivative.eval s) * r ^ 2 /
              (s * (r - s) ^ 2)) := by
      calc
        _ = ∑ s ∈ f.roots.toFinset,
            ((g.eval s / f.derivative.eval s) / s * f.eval r +
              (g.eval s / f.derivative.eval s) * (f.eval r / (r - s)) -
              r * ((g.eval s / f.derivative.eval s) *
                (-f.eval r / (r - s) ^ 2))) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl; intro s hs
          have hs_ne : s ≠ 0 := by linarith [(hroot_data s hs).1]
          have hrs := (hroot_data s hs).2.1
          field_simp; ring
    rw [add_mul, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.mul_sum]
    linear_combination hsum
  have hconstant : 0 < g.eval 0 / f.eval 0 := div_pos hg_zero hf_zero
  have hterms : 0 ≤ ∑ s ∈ f.roots.toFinset,
      (g.eval s / f.derivative.eval s) * r ^ 2 /
        (s * (r - s) ^ 2) := by
    apply Finset.sum_nonneg
    intro s hs
    have hres_neg : g.eval s / f.derivative.eval s < 0 := by
      have hprod := hfg.eval_mul_derivative_neg_of_left_root_of_no_common
        hf_pos hg_pos hno (hroot s hs)
      exact (div_neg_iff.mpr (mul_neg_iff.mp hprod))
    have hden_neg : s * (r - s) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (hroot_data s hs).1
        (sq_pos_of_ne_zero (hroot_data s hs).2.1)
    exact div_nonneg_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hres_neg.le (sq_nonneg r)) hden_neg.le
  have hratio : 0 < g.eval 0 / f.eval 0 +
      ∑ s ∈ f.roots.toFinset,
        (g.eval s / f.derivative.eval s) * r ^ 2 /
          (s * (r - s) ^ 2) := add_pos_of_pos_of_nonneg hconstant hterms
  rw [eval_sub, eval_mul, eval_X, hmain]
  nlinarith [sq_pos_of_ne_zero hfr_ne]

/-- Every PF polynomial precedes its Euler derivative, including zero and constants. -/
theorem IsPFPolynomial.interl_theta {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl p (theta p) := by
  by_cases hp0 : p = 0
  · simp [hp0, interl_zero_zero, theta]
  by_cases hdeg : p.natDegree = 0
  · rw [show theta p = 0 by simp [theta, derivative_eq_zero.mpr hdeg]]
    exact interl_zero_right p
  · exact (strictInterl_self_theta_of_natDegree_ne_zero hp hdeg).toInterl

/-- The derivative of a PF polynomial precedes the polynomial, including constants. -/
theorem IsPFPolynomial.interl_derivative_self {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl p.derivative p := by
  by_cases hdeg : p.natDegree = 0
  · rw [derivative_eq_zero.mpr hdeg]
    exact interl_zero_left p
  · exact (derivative_interlaces_of_natDegree_ne_zero
      (hp.ne_zero_and_splits (fun hp0 ↦ hdeg (by simp [hp0]))).2 hdeg).toStrictInterl.toInterl

/-- The Euler derivative of a PF polynomial precedes its product by `X`. -/
theorem IsPFPolynomial.interl_theta_X_mul {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl (theta p) (X * p) := by
  simpa [theta] using interl_X_mul_both_of_pf hp.derivative hp
    hp.interl_derivative_self

/-- Zero-aware `X`-duality for PF polynomials. -/
theorem interl_iff_interl_X_mul {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) :
    Interl p q ↔ Interl q (X * p) := by
  constructor
  · intro hpq
    exact interl_mul_X_of_interl hpq hp.hasNonnegCoeffs hq.hasNonnegCoeffs
  · intro hqXp
    rcases eq_or_ne p 0 with rfl | hp0
    · exact interl_zero_left q
    rcases eq_or_ne q 0 with rfl | hq0
    · exact interl_zero_right p
    have hstrict : StrictInterl q (X * p) :=
      hqXp.toStrictInterl_of_ne hq0 (mul_ne_zero X_ne_zero hp0)
    exact ((strictInterl_iff_mul_X_of_roots_nonpos hp.roots_nonpos hq.roots_nonpos).mpr
      hstrict).toInterl

/-- The sum of an interlacing PF pair is PF. -/
theorem IsPFPolynomial.add_of_interl {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    IsPFPolynomial (p + q) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hp.hasNonnegCoeffs.add hq.hasNonnegCoeffs
  rcases hpq with rfl | rfl | hpq
  · simpa using hq.eq_zero_or_splits
  · simpa using hp.eq_zero_or_splits
  · right
    simpa using (hpq.isRealRooted_pos_combo
      (hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1)
      (hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1) one_pos one_pos).2

/-- The sum of the derivatives of an interlacing PF pair is PF. -/
theorem isPFPolynomial_derivative_add_derivative_of_interl
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    IsPFPolynomial (p.derivative + q.derivative) := by
  simpa [derivative_add] using (hp.add_of_interl hq hpq).derivative

/-- The mixed right output `q + X * p'` of an interlacing PF pair is PF. -/
theorem isPFPolynomial_add_X_mul_derivative_of_interl
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    IsPFPolynomial (q + X * p.derivative) := by
  have hinterl : Interl p (q + theta p) :=
    interl_add_right_of_common_left_of_nonneg hpq hp.interl_theta hq.hasNonnegCoeffs
      (theta_preserves_pf hp).hasNonnegCoeffs
  have hpf : IsPFPolynomial (q + theta p) := by
    by_cases hp0 : p = 0
    · simpa [hp0, theta] using hq
    apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
      (hq.hasNonnegCoeffs.add (theta_preserves_pf hp).hasNonnegCoeffs)
    by_cases hzero : q + theta p = 0
    · exact Or.inl hzero
    · exact Or.inr (hinterl.toStrictInterl_of_ne hp0 hzero).2.1.2
  simpa [theta] using hpf

/-- Coprime, strictly negative inputs satisfy the directed mixed differential lemma. -/
theorem interl_derivative_add_derivative_add_X_mul_derivative_of_isCoprime
    {p q : ℝ[X]}
    (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : StrictInterl p q) (hcop : IsCoprime p q)
    (hp_zero : 0 < p.eval 0) (hq_zero : 0 < q.eval 0) :
    Interl (p.derivative + q.derivative) (q + X * p.derivative) := by
  let h : ℝ[X] := p + q
  let F : ℝ[X] := q + X * p.derivative
  have hp_pos : HasPosLeadingCoeff p := hp.hasNonnegCoeffs.pos_leadingCoeff hpq.1.1
  have hq_pos : HasPosLeadingCoeff q := hq.hasNonnegCoeffs.pos_leadingCoeff hpq.2.1.1
  have hhq : StrictInterl h q := by
    simpa [h] using hpq.convex_right hp_pos hq_pos one_pos one_pos
  have hh_pf : IsPFPolynomial h := by
    simpa [h] using hp.add_of_interl hq hpq.toInterl
  have hh_pos : HasPosLeadingCoeff h :=
    hh_pf.hasNonnegCoeffs.pos_leadingCoeff hhq.1.1
  have hh_zero : 0 < h.eval 0 := by
    simp only [h, eval_add]; linarith
  have hno : ∀ x, h.IsRoot x → ¬ q.IsRoot x := by
    intro x hhx hqx
    apply hcop.not_isRoot_right
    · simpa [h, Polynomial.IsRoot.def, Polynomial.IsRoot.def.mp hqx] using hhx
    · exact hqx
  have hh_simple : HasSimpleRoots h :=
    (hhq.hasSimpleRoots_of_no_common_root fun x hx ↦ hno x hx.1 hx.2).1
  have hh_deg : h.natDegree = q.natDegree := by
    rcases hpq.natDegree_eq_or_eq_succ with hsame | hsucc
    · exact (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        hsame.symm hp_pos hq_pos).trans hsame.symm
    · exact natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by lia) hq_pos
  have hF_pf : IsPFPolynomial F := by
    simpa [F] using isPFPolynomial_add_X_mul_derivative_of_interl
      hp hq hpq.toInterl
  have hF_coeff : 0 < F.coeff q.natDegree := by
    dsimp [F]
    rw [coeff_add]
    exact add_pos_of_pos_of_nonneg hq_pos
      (hp.hasNonnegCoeffs.derivative.X_mul q.natDegree)
  have hF_deg : F.natDegree = q.natDegree := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · dsimp [F]
      refine (natDegree_add_le _ _).trans (max_le le_rfl ?_)
      simpa [theta] using (natDegree_theta_le p).trans hpq.natDegree_le
    · exact hF_coeff.ne'
  have hF_pos : HasPosLeadingCoeff F :=
    hF_pf.hasNonnegCoeffs.pos_leadingCoeff (by
      intro hzero
      rw [hzero] at hF_coeff
      simp at hF_coeff)
  rcases Nat.eq_zero_or_pos h.natDegree with hdeg0 | hdegpos
  · have hqdeg0 : q.natDegree = 0 := by rw [hh_deg] at hdeg0; exact hdeg0
    have hpdeg0 : p.natDegree = 0 := by
      have := hpq.natDegree_le
      lia
    rw [derivative_eq_zero.mpr hpdeg0, derivative_eq_zero.mpr hqdeg0]
    simp only [zero_add]
    exact interl_zero_left _
  rcases eq_or_lt_of_le (show 1 ≤ h.natDegree by lia) with hdeg1 | hdeg2
  · have hhdeg1 : h.natDegree = 1 := by lia
    have hGdeg0 : h.derivative.natDegree = 0 := by
      rw [h.natDegree_derivative, hhdeg1]
    have hGne : h.derivative ≠ 0 := derivative_ne_zero.mpr (by lia)
    have hGsplits : h.derivative.Splits := Splits.of_natDegree_eq_zero hGdeg0
    have hFdeg1 : F.natDegree = 1 := by rw [hF_deg, ← hh_deg, hhdeg1]
    have hstrict : StrictInterl h.derivative F :=
      StrictInterl.of_degree_zero_right_of_degree_one hGne hGsplits hF_pos.ne_zero
        (hF_pf.ne_zero_and_splits hF_pos.ne_zero).2 hGdeg0 hFdeg1
    simpa [h, F, derivative_add] using hstrict.toInterl
  · have hh_splits : h.Splits := hhq.1.2
    have hh_roots_neg : ∀ x, h.IsRoot x → x < 0 := by
      intro x hx
      have hx_nonpos := hh_pf.roots_nonpos x ((mem_roots hhq.1.1).mpr hx)
      have hx_ne : x ≠ 0 := by
        intro hx0
        subst x
        exact hh_zero.ne' hx
      exact lt_of_le_of_ne hx_nonpos hx_ne
    have hG_ne : h.derivative ≠ 0 := derivative_ne_zero.mpr (by lia)
    have hG_splits : h.derivative.Splits :=
      ((derivative_eq_zero_or_ne_zero_and_splits hh_splits).resolve_left hG_ne).2
    have hG_pos : HasPosLeadingCoeff h.derivative := hh_pos.derivative (by lia)
    have hGdeg : h.derivative.natDegree = h.natDegree - 1 := h.natDegree_derivative
    have hGG : Interlaces h.derivative.derivative h.derivative :=
      interlaces_derivative_of_pos_natDegree hG_ne hG_splits hG_pos (by lia)
    have hGG_pos : HasPosLeadingCoeff h.derivative.derivative :=
      hG_pos.derivative (by lia)
    have hG_h : StrictInterl h.derivative h :=
      (derivative_interlaces_of_natDegree_ne_zero hh_splits (by lia)).toStrictInterl
    have hG_h_no : ∀ x, h.derivative.IsRoot x → ¬ h.IsRoot x :=
      fun _ hGx hx ↦ (hh_simple.eval_derivative_ne_zero hx) hGx
    have hroot_sign : ∀ x, h.derivative.IsRoot x →
        F.eval x * h.derivative.derivative.eval x < 0 := by
      intro x hx
      have hratio := eval_sub_X_mul_derivative_mul_eval_pos
        hhq hh_pos hq_pos hh_deg hdeg2 hh_simple hno hh_roots_neg hh_zero hq_zero hx
      have hF_eval : F.eval x = (q - X * q.derivative).eval x := by
        have hx0 : h.derivative.eval x = 0 := hx
        have hx0' : p.derivative.eval x + q.derivative.eval x = 0 := by
          simpa only [h, derivative_add, eval_add] using hx0
        have hpq_eval : p.derivative.eval x = -q.derivative.eval x := by
          linarith
        dsimp only [F]
        simp only [eval_add, eval_mul, eval_X, eval_sub]
        rw [hpq_eval]
        ring
      have hratioF : 0 < F.eval x * h.eval x := by rw [hF_eval]; exact hratio
      have hopposite := hG_h.eval_mul_derivative_neg_of_left_root_of_no_common
        hG_pos hh_pos hG_h_no hx
      have hh_eval_ne : h.eval x ≠ 0 := by
        simpa [Polynomial.IsRoot.def] using hG_h_no x hx
      nlinarith [mul_neg_of_pos_of_neg hratioF hopposite, sq_pos_of_ne_zero hh_eval_ne]
    have hstrict : StrictInterl h.derivative F :=
      strictInterl_of_interlaces_eval_mul_neg_succ hGG hGG_pos hF_pos
        (by rw [hF_deg, ← hh_deg, hGdeg]; lia) hroot_sign
    simpa [h, F, derivative_add] using hstrict.toInterl

end RealRooted
