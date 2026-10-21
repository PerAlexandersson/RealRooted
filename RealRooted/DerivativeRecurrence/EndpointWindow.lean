import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.Basic.AffineInterlacing
import RealRooted.Interlacing.NegativeRoots

/-!
# Endpoint root windows

The endpoint signs used here are the factorization argument in Ma and Wang,
*q-Eulerian polynomials and polynomials with only real zeros*, Theorem 2
([arXiv:math/0611826](https://arxiv.org/abs/math/0611826)).
-/

open Polynomial

namespace RealRooted

section Endpoint

variable {f F : ℝ[X]} {L U : ℝ}

/-- For an interlacing successor, the upper endpoint sign is equivalent to a strict
root bound when the roots of the preceding polynomial are strictly below that endpoint. -/
theorem roots_lt_iff_eval_pos_of_interlaces (hinter : Interlaces f F)
    (hFpos : 0 < F.leadingCoeff) (hfU : ∀ t ∈ f.roots, t < U) :
    (∀ t ∈ F.roots, t < U) ↔ 0 < F.eval U := by
  constructor
  · intro hFU
    rw [Polynomial.Splits.eval_eq_prod_roots hinter.1.2 U]
    refine mul_pos hFpos (Multiset.prod_pos fun y hy => ?_)
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
    exact sub_pos.mpr (hFU t ht)
  · intro hFU
    have hinter' := interlaces_comp_X_add_C hinter U
    have hFpos' : 0 < (F.comp (X + C U)).leadingCoeff :=
      (HasPosLeadingCoeff.comp_X_add_C hFpos U)
    have hFU' : 0 < (F.comp (X + C U)).eval 0 := by
      simpa [Polynomial.eval_comp] using hFU
    have hfneg' : ∀ r, (f.comp (X + C U)).IsRoot r → r < 0 := by
      intro r hr
      have hr' : f.IsRoot (r + U) := by
        simpa [Polynomial.IsRoot.def, Polynomial.eval_comp, add_comm] using hr
      have hrmem : r + U ∈ f.roots :=
        (mem_roots hinter.2.1.1).mpr hr'
      have := hfU (r + U) hrmem
      linarith
    have hFneg' := roots_neg_of_interlaces_of_eval_zero_pos hinter' hFpos' hFU' hfneg'
    intro t ht
    have htF : F.IsRoot t := (mem_roots hinter.1.1).mp ht
    have ht' : (F.comp (X + C U)).IsRoot (t - U) := by
      simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using htF
    have := hFneg' (t - U) ht'
    linarith

/-- For an interlacing successor, the upper endpoint sign is equivalent to a weak
root bound when the roots of the preceding polynomial are strictly below that endpoint. -/
theorem roots_le_iff_eval_nonneg_of_interlaces (hinter : Interlaces f F)
    (hFpos : 0 < F.leadingCoeff) (hfU : ∀ t ∈ f.roots, t < U) :
    (∀ t ∈ F.roots, t ≤ U) ↔ 0 ≤ F.eval U := by
  constructor
  · intro hFU
    rw [Polynomial.Splits.eval_eq_prod_roots hinter.1.2 U]
    refine mul_nonneg hFpos.le (Multiset.prod_nonneg fun y hy => ?_)
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
    exact sub_nonneg.mpr (hFU t ht)
  · intro hFU
    rcases eq_or_lt_of_le hFU with hzero | hFU
    · have hinter' := interlaces_comp_X_add_C hinter U
      have hfneg' : ∀ r, (f.comp (X + C U)).IsRoot r → r < 0 := by
        intro r hr
        have hr' : f.IsRoot (r + U) := by
          simpa [Polynomial.IsRoot.def, Polynomial.eval_comp, add_comm] using hr
        have hrmem : r + U ∈ f.roots :=
          (mem_roots hinter.2.1.1).mpr hr'
        have := hfU (r + U) hrmem
        linarith
      have hFnonpos' := roots_nonpos_of_interlaces_of_zero_root_of_roots_neg hinter'
        (by simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using hzero.symm) hfneg'
      intro t ht
      have htF : F.IsRoot t := (mem_roots hinter.1.1).mp ht
      have ht' : (F.comp (X + C U)).IsRoot (t - U) := by
        simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using htF
      have := hFnonpos' (t - U) ht'
      linarith
    · intro t ht
      exact ((roots_lt_iff_eval_pos_of_interlaces hinter hFpos hfU).mpr hFU) t ht |>.le

/-- For an interlacing successor, the lower endpoint sign is equivalent to a strict
root bound when the roots of the preceding polynomial are strictly above that endpoint. -/
theorem roots_gt_iff_neg_one_pow_mul_eval_pos_of_interlaces (hinter : Interlaces f F)
    (hFpos : 0 < F.leadingCoeff) (hfL : ∀ t ∈ f.roots, L < t) :
    (∀ t ∈ F.roots, L < t) ↔ 0 < (-1 : ℝ) ^ F.natDegree * F.eval L := by
  constructor
  · intro hFL
    rw [Polynomial.Splits.eval_eq_prod_roots hinter.1.2 L,
      ← Polynomial.splits_iff_card_roots.mp hinter.1.2,
      mul_left_comm, show F.roots.card = (F.roots.map (L - ·)).card by simp,
      ← Multiset.prod_map_neg]
    refine mul_pos hFpos (Multiset.prod_pos fun y hy => ?_)
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hy
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    linarith [hFL t ht]
  · intro hFL
    let qf := f.comp (-X + C L)
    let qF := F.comp (-X + C L)
    have hinter' : Interlaces qf qF := by
      simpa [qf, qF, sub_eq_add_neg] using interlaces_comp_neg_X_sub_C hinter (-L)
    have hqFpos : 0 < (C ((-1 : ℝ) ^ F.natDegree) * qF).leadingCoeff := by
      have hlin : (-X + C L : ℝ[X]).leadingCoeff = -1 := by
        rw [show -X + C L = -(X + C (-L)) by
          simp only [map_neg]
          ring]
        simp only [leadingCoeff_neg, leadingCoeff_X_add_C]
      rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by simp), hlin]
      have hpow : (-1 : ℝ) ^ F.natDegree * (-1) ^ F.natDegree = 1 := by
        rw [← mul_pow]
        norm_num
      have hcalc : (-1 : ℝ) ^ F.natDegree *
          (F.leadingCoeff * (-1 : ℝ) ^ F.natDegree) = F.leadingCoeff := by
        calc
          _ = F.leadingCoeff * ((-1 : ℝ) ^ F.natDegree * (-1 : ℝ) ^ F.natDegree) := by ring
          _ = F.leadingCoeff := by rw [hpow, mul_one]
      rw [hcalc]
      exact hFpos
    have hscaled : Interlaces (C ((-1 : ℝ) ^ f.natDegree) * qf)
        (C ((-1 : ℝ) ^ F.natDegree) * qF) := by
      exact (hinter'.toStrictInterl.C_mul_left
        (pow_ne_zero f.natDegree (by norm_num : (-1 : ℝ) ≠ 0))).C_mul_right
        (pow_ne_zero F.natDegree (by norm_num : (-1 : ℝ) ≠ 0)) |>.toInterlaces
        (by
          rw [natDegree_mul (C_ne_zero.mpr (pow_ne_zero f.natDegree (by norm_num)))
            hinter'.2.1.1,
            natDegree_mul (C_ne_zero.mpr (pow_ne_zero F.natDegree (by norm_num)))
              hinter'.1.1]
          simpa [qf, qF, natDegree_comp] using hinter.2.2.1)
    have hqFzero : 0 < (C ((-1 : ℝ) ^ F.natDegree) * qF).eval 0 := by
      simpa [qF, Polynomial.eval_comp, eval_mul, eval_C, mul_assoc] using hFL
    have hqfneg : ∀ r, (C ((-1 : ℝ) ^ f.natDegree) * qf).IsRoot r → r < 0 := by
      intro r hr
      have hr' : f.IsRoot (L - r) := by
        simpa [qf, Polynomial.IsRoot.def, Polynomial.eval_comp, eval_mul, eval_C,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hr
      have hrmem : L - r ∈ f.roots := (mem_roots hinter.2.1.1).mpr hr'
      have := hfL (L - r) hrmem
      linarith
    have hqFneg := roots_neg_of_interlaces_of_eval_zero_pos hscaled hqFpos hqFzero hqfneg
    intro t ht
    have htF : F.IsRoot t := (mem_roots hinter.1.1).mp ht
    have ht' : qF.IsRoot (L - t) := by
      simpa [qF, Polynomial.IsRoot.def, Polynomial.eval_comp, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using htF
    have := hqFneg (L - t) ((by
      simpa [qF, Polynomial.IsRoot.def, eval_mul, eval_C] using ht') :
        (C ((-1 : ℝ) ^ F.natDegree) * qF).IsRoot (L - t))
    linarith

/-- For an interlacing successor, the lower endpoint sign is equivalent to a weak
root bound when the roots of the preceding polynomial are strictly above that endpoint. -/
theorem roots_ge_iff_neg_one_pow_mul_eval_nonneg_of_interlaces (hinter : Interlaces f F)
    (hFpos : 0 < F.leadingCoeff) (hfL : ∀ t ∈ f.roots, L < t) :
    (∀ t ∈ F.roots, L ≤ t) ↔ 0 ≤ (-1 : ℝ) ^ F.natDegree * F.eval L := by
  constructor
  · intro hFL
    rw [Polynomial.Splits.eval_eq_prod_roots hinter.1.2 L,
      ← Polynomial.splits_iff_card_roots.mp hinter.1.2,
      mul_left_comm, show F.roots.card = (F.roots.map (L - ·)).card by simp,
      ← Multiset.prod_map_neg]
    refine mul_nonneg hFpos.le (Multiset.prod_nonneg fun y hy => ?_)
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hy
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
    linarith [hFL t ht]
  · intro hFL
    rcases eq_or_lt_of_le hFL with hzero | hFL
    · let qf := f.comp (-X + C L)
      let qF := F.comp (-X + C L)
      have hinter' : Interlaces qf qF := by
        simpa [qf, qF, sub_eq_add_neg] using interlaces_comp_neg_X_sub_C hinter (-L)
      have hqFpos : 0 < (C ((-1 : ℝ) ^ F.natDegree) * qF).leadingCoeff := by
        have hlin : (-X + C L : ℝ[X]).leadingCoeff = -1 := by
          rw [show -X + C L = -(X + C (-L)) by
            simp only [map_neg]
            ring]
          simp only [leadingCoeff_neg, leadingCoeff_X_add_C]
        rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by simp), hlin]
        have hpow : (-1 : ℝ) ^ F.natDegree * (-1) ^ F.natDegree = 1 := by
          rw [← mul_pow]
          norm_num
        have hcalc : (-1 : ℝ) ^ F.natDegree *
            (F.leadingCoeff * (-1 : ℝ) ^ F.natDegree) = F.leadingCoeff := by
          calc
            _ = F.leadingCoeff * ((-1 : ℝ) ^ F.natDegree * (-1 : ℝ) ^ F.natDegree) := by ring
            _ = F.leadingCoeff := by rw [hpow, mul_one]
        rw [hcalc]
        exact hFpos
      have hscaled : Interlaces (C ((-1 : ℝ) ^ f.natDegree) * qf)
          (C ((-1 : ℝ) ^ F.natDegree) * qF) := by
        exact (hinter'.toStrictInterl.C_mul_left
          (pow_ne_zero f.natDegree (by norm_num : (-1 : ℝ) ≠ 0))).C_mul_right
          (pow_ne_zero F.natDegree (by norm_num : (-1 : ℝ) ≠ 0)) |>.toInterlaces
          (by
            rw [natDegree_mul (C_ne_zero.mpr (pow_ne_zero f.natDegree (by norm_num)))
              hinter'.2.1.1,
              natDegree_mul (C_ne_zero.mpr (pow_ne_zero F.natDegree (by norm_num)))
                hinter'.1.1]
            simpa [qf, qF, natDegree_comp] using hinter.2.2.1)
      have hqfneg : ∀ r, (C ((-1 : ℝ) ^ f.natDegree) * qf).IsRoot r → r < 0 := by
        intro r hr
        have hr' : f.IsRoot (L - r) := by
          simpa [qf, Polynomial.IsRoot.def, Polynomial.eval_comp, eval_mul, eval_C,
            sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hr
        have hrmem : L - r ∈ f.roots := (mem_roots hinter.2.1.1).mpr hr'
        have := hfL (L - r) hrmem
        linarith
      have hqFzero : (C ((-1 : ℝ) ^ F.natDegree) * qF).IsRoot 0 := by
        simpa [qF, Polynomial.IsRoot.def, eval_mul, eval_C, Polynomial.eval_comp] using hzero.symm
      have hqFnonpos := roots_nonpos_of_interlaces_of_zero_root_of_roots_neg hscaled
        hqFzero hqfneg
      intro t ht
      have htF : F.IsRoot t := (mem_roots hinter.1.1).mp ht
      have ht' : qF.IsRoot (L - t) := by
        simpa [qF, Polynomial.IsRoot.def, Polynomial.eval_comp, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc] using htF
      have := hqFnonpos (L - t) ((by
        simpa [qF, Polynomial.IsRoot.def, eval_mul, eval_C] using ht') :
          (C ((-1 : ℝ) ^ F.natDegree) * qF).IsRoot (L - t))
      linarith
    · intro t ht
      exact ((roots_gt_iff_neg_one_pow_mul_eval_pos_of_interlaces hinter hFpos hfL).mpr hFL)
        t ht |>.le

end Endpoint

section Sequence

variable {P A B : ℕ → ℝ[X]} {D₀ : ℕ}

/-- Interlacing for a derivative recurrence with a window callback that may use the
newly proved interlacing relation before placing the next row in its window. -/
theorem derivativeRecurrence_interlaces_of_endpoint_windows (W : ℕ → ℝ → Prop)
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n) (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hA : ∀ n x, W n x → (A n).eval x ≤ 0)
    (hW : ∀ n, (P n).Splits → (∀ t ∈ (P n).roots, W n t) →
      Interlaces (P n) (P (n + 1)) → ∀ t ∈ (P (n + 1)).roots, W (n + 1) t)
    (h0 : (P 0).Splits) (hW0 : ∀ t ∈ (P 0).roots, W 0 t)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  have hroot : ∀ n, (∀ t ∈ (P n).roots, W n t) → ∀ r, (P n).IsRoot r →
      (A n).eval r ≤ 0 := fun n hw r hr => hA n r (hw r
        ((mem_roots (leadingCoeff_ne_zero.mp (hpos n).ne')).mpr hr))
  have key : ∀ n, (P n).Splits ∧ (∀ t ∈ (P n).roots, W n t) ∧
      Interlaces (P n) (P (n + 1)) := by
    intro n
    induction n with
    | zero =>
        refine ⟨h0, hW0, ?_⟩
        rcases Nat.eq_zero_or_pos D₀ with hD | hD
        · exact h01 hD
        · exact derivativeRecurrence_interlaces_step hrec hdeg hpos 0 (hroot 0 hW0) h0 (by lia)
    | succ n ih =>
        obtain ⟨hs, hw, hi⟩ := ih
        have hw' := hW n hs hw hi
        exact ⟨hi.1.2, hw', derivativeRecurrence_interlaces_step hrec hdeg hpos (n + 1)
          (hroot (n + 1) hw') hi.1.2 (by lia)⟩
  exact fun n => (key n).2.2

end Sequence

end RealRooted

namespace RealRooted
private theorem eval_pos_at_upper_of_roots_lt {p : ℝ[X]} {U : ℝ}
    (hs : p.Splits) (hpos : 0 < p.leadingCoeff)
    (h : ∀ t ∈ p.roots, t < U) : 0 < p.eval U := by
  rw [Polynomial.Splits.eval_eq_prod_roots hs U]
  refine mul_pos hpos (Multiset.prod_pos fun y hy => ?_)
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hy
  linarith [h t ht]

private theorem neg_one_pow_mul_eval_pos_at_lower_of_roots_gt
    {p : ℝ[X]} {L : ℝ} (hs : p.Splits) (hpos : 0 < p.leadingCoeff)
    (h : ∀ t ∈ p.roots, L < t) :
    0 < (-1 : ℝ) ^ p.natDegree * p.eval L := by
  have hcard : p.roots.card = (p.roots.map (L - ·)).card := by simp
  rw [Polynomial.Splits.eval_eq_prod_roots hs L, ← Polynomial.splits_iff_card_roots.mp hs,
    mul_left_comm, hcard, ← Multiset.prod_map_neg]
  refine mul_pos hpos (Multiset.prod_pos fun y hy => ?_)
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hs
  linarith [h t ht]

/-- A degree-zero polynomial has no roots, so every strict root window holds. -/
theorem roots_window_of_natDegree_zero {p : ℝ[X]} {L U : ℝ}
    (hdeg : p.natDegree = 0) : ∀ t ∈ p.roots, L < t ∧ t < U := by
  intro t ht
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, Polynomial.roots_C] at ht
  simp at ht

/-- A moving open interval is invariant under a derivative recurrence when
the derivative coefficient is nonpositive inside it, vanishes at both
endpoints, and the row coefficient has the two outward endpoint signs. -/
theorem derivativeRecurrence_interlaces_of_endpoint_evaluations
    {P A B : ℕ → ℝ[X]} {D₀ : ℕ} (L U : ℕ → ℝ)
    (hrec : ∀ n, P (n + 1) = A n * (P n).derivative + B n * P n)
    (hdeg : ∀ n, (P n).natDegree = D₀ + n)
    (hpos : ∀ n, 0 < (P n).leadingCoeff)
    (hLmono : ∀ n, L (n + 1) ≤ L n)
    (hUmono : ∀ n, U n ≤ U (n + 1))
    (hA : ∀ n x, L n < x → x < U n → (A n).eval x ≤ 0)
    (hAL : ∀ n, (A n).eval (L n) = 0)
    (hAU : ∀ n, (A n).eval (U n) = 0)
    (hBL : ∀ n, (B n).eval (L n) < 0)
    (hBU : ∀ n, 0 < (B n).eval (U n))
    (h0 : (P 0).Splits)
    (hW0 : ∀ t ∈ (P 0).roots, L 0 < t ∧ t < U 0)
    (h01 : D₀ = 0 → Interlaces (P 0) (P 1)) :
    ∀ n, Interlaces (P n) (P (n + 1)) := by
  let W := fun n x => L n < x ∧ x < U n
  apply derivativeRecurrence_interlaces_of_endpoint_windows W hrec hdeg hpos
  · intro n x hx
    exact hA n x hx.1 hx.2
  · intro n hs hw hi t ht
    have holdL : ∀ s ∈ (P n).roots, L n < s := fun s hsroot => (hw s hsroot).1
    have holdU : ∀ s ∈ (P n).roots, s < U n := fun s hsroot => (hw s hsroot).2
    have hsignL : 0 < (-1 : ℝ) ^ (P n).natDegree * (P n).eval (L n) :=
      neg_one_pow_mul_eval_pos_at_lower_of_roots_gt hs (hpos n) holdL
    have hsignU : 0 < (P n).eval (U n) :=
      eval_pos_at_upper_of_roots_lt hs (hpos n) holdU
    have hsignL' : 0 < (-1 : ℝ) ^ (D₀ + n) * (P n).eval (L n) := by
      simpa only [hdeg n] using hsignL
    have hnextL : 0 < (-1 : ℝ) ^ (P (n + 1)).natDegree *
        (P (n + 1)).eval (L n) := by
      have heval : (P (n + 1)).eval (L n) =
          (B n).eval (L n) * (P n).eval (L n) := by
        rw [hrec n, eval_add, eval_mul, eval_mul, hAL n, zero_mul, zero_add]
      have hindex : D₀ + (n + 1) = (D₀ + n) + 1 := by grind
      rw [hdeg (n + 1), hindex, heval]
      have hid :
          (-1 : ℝ) ^ ((D₀ + n) + 1) *
              ((B n).eval (L n) * (P n).eval (L n)) =
            (-(B n).eval (L n)) *
              ((-1 : ℝ) ^ (D₀ + n) * (P n).eval (L n)) := by
        rw [pow_succ]
        ring
      rw [hid]
      exact mul_pos (neg_pos.mpr (hBL n)) hsignL'
    have hnextU : 0 < (P (n + 1)).eval (U n) := by
      rw [hrec n, eval_add, eval_mul, eval_mul, hAU n, zero_mul, zero_add]
      exact mul_pos (hBU n) hsignU
    have hrootL : L n < t :=
      (roots_gt_iff_neg_one_pow_mul_eval_pos_of_interlaces
        hi (hpos (n + 1)) holdL).mpr hnextL t ht
    have hrootU : t < U n :=
      (roots_lt_iff_eval_pos_of_interlaces hi (hpos (n + 1)) holdU).mpr
        hnextU t ht
    exact ⟨lt_of_le_of_lt (hLmono n) hrootL,
      lt_of_lt_of_le hrootU (hUmono n)⟩
  · exact h0
  · exact hW0
  · exact h01

end RealRooted
