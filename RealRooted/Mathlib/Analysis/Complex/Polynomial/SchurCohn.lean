import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# The Schur–Cohn stability criterion

Let `p = a₀ + a₁ X + ⋯ + aₙ Xⁿ` be a complex polynomial of degree `n ≥ 1`, and let
`p* = conj aₙ + conj aₙ₋₁ X + ⋯ + conj a₀ Xⁿ` be its conjugate reciprocal, so that
`p*(z) = zⁿ · conj (p (1 / conj z))` for `z ≠ 0`.  The polynomial
`conj aₙ • p - a₀ • p*` has vanishing constant term; dividing it by `X` gives the
*Schur transform* `T p`, of degree `n - 1` when `‖a₀‖ < ‖aₙ‖`.

The Schur–Cohn criterion (Schur 1917, Cohn 1922) states that all roots of `p` lie in the open
unit disk if and only if `‖a₀‖ < ‖aₙ‖` and all roots of `T p` lie in the open unit disk.

The proof is elementary and avoids Rouché's theorem.  For a polynomial `q` with all roots in the
open unit disk, the Blaschke-factor inequality `‖1 - conj z * r‖ ≤ ‖z - r‖` (for `‖r‖ < 1 ≤ ‖z‖`)
gives `‖q* z‖ ≤ ‖q z‖` on `1 ≤ ‖z‖`.  Both directions then follow from the identities
`z · T(z) = conj aₙ · p(z) - a₀ · p*(z)` and
`(‖aₙ‖² - ‖a₀‖²) · p(z) = aₙ · z · T(z) + a₀ · T*(z)`.

## Main declarations

* `Polynomial.conjReverse`: the conjugate reciprocal `p*`.
* `Polynomial.IsSchurStable`: `p ≠ 0` and every root lies in the open unit disk.
* `Polynomial.schurTransform`: the Schur transform `T p`.
* `Polynomial.isSchurStable_iff`: the Schur–Cohn criterion.
-/

namespace Polynomial

open ComplexConjugate

/-- The conjugate reciprocal `p* = ∑ conj (a_{n-k}) X^k` of a complex polynomial `p` of
natural degree `n`, so that `p*(z) = zⁿ · conj (p (1 / conj z))` for `z ≠ 0`. -/
noncomputable def conjReverse (p : ℂ[X]) : ℂ[X] :=
  (p.map (starRingEnd ℂ)).reverse

/-- A complex polynomial is *Schur stable* if it is nonzero and all of its roots lie in the open
unit disk. -/
def IsSchurStable (p : ℂ[X]) : Prop :=
  p ≠ 0 ∧ ∀ z : ℂ, p.IsRoot z → ‖z‖ < 1

/-- The Schur transform `(conj aₙ • p - a₀ • p*) / X` of a complex polynomial `p`, where `a₀` is
the constant coefficient and `aₙ` the leading coefficient of `p`.  The numerator has vanishing
constant term, so the division by `X` is exact. -/
noncomputable def schurTransform (p : ℂ[X]) : ℂ[X] :=
  (C (conj p.leadingCoeff) * p - C (p.coeff 0) * p.conjReverse).divX

/-- Evaluation of the conjugate reciprocal: `p*(z) = zⁿ · conj (p (conj z)⁻¹)` for `z ≠ 0`. -/
theorem eval_conjReverse {z : ℂ} (hz : z ≠ 0) (p : ℂ[X]) :
    p.conjReverse.eval z = z ^ p.natDegree * conj (p.eval (conj z)⁻¹) := by
  let := invertibleOfNonzero (inv_ne_zero hz)
  have h := eval₂_reverse_mul_pow (RingHom.id ℂ) z⁻¹ (p.map (starRingEnd ℂ))
  have h2 : (p.map (starRingEnd ℂ)).eval z⁻¹ = conj (p.eval (conj z)⁻¹) := by
    rw [eval_map, ← eval₂_at_apply, map_inv₀, Complex.conj_conj]
  rw [invOf_eq_inv, inv_inv, natDegree_map] at h
  change (p.map (starRingEnd ℂ)).reverse.eval z * z⁻¹ ^ p.natDegree =
    (p.map (starRingEnd ℂ)).eval z⁻¹ at h
  rw [conjReverse, ← h2, ← h, mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel₀ hz, one_pow,
    mul_one]

theorem coeff_zero_conjReverse (p : ℂ[X]) : p.conjReverse.coeff 0 = conj p.leadingCoeff := by
  rw [conjReverse, coeff_zero_reverse, leadingCoeff_map]

theorem coeff_natDegree_conjReverse (p : ℂ[X]) :
    p.conjReverse.coeff p.natDegree = conj (p.coeff 0) := by
  rw [conjReverse, coeff_reverse, natDegree_map, revAt_le le_rfl, Nat.sub_self, coeff_map]

theorem natDegree_conjReverse_le (p : ℂ[X]) : p.conjReverse.natDegree ≤ p.natDegree :=
  (reverse_natDegree_le _).trans (natDegree_map _).le

/-- The defining identity of the Schur transform: `T p * X = conj aₙ • p - a₀ • p*`. -/
theorem schurTransform_mul_X (p : ℂ[X]) :
    p.schurTransform * X = C (conj p.leadingCoeff) * p - C (p.coeff 0) * p.conjReverse := by
  have h0 : (C (conj p.leadingCoeff) * p - C (p.coeff 0) * p.conjReverse).coeff 0 = 0 := by
    rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_zero_conjReverse, mul_comm]
    exact sub_self _
  have h := divX_mul_X_add (C (conj p.leadingCoeff) * p - C (p.coeff 0) * p.conjReverse)
  rwa [h0, C_0, add_zero] at h

theorem eval_schurTransform_mul (p : ℂ[X]) (z : ℂ) :
    p.schurTransform.eval z * z =
      conj p.leadingCoeff * p.eval z - p.coeff 0 * p.conjReverse.eval z := by
  have h := congrArg (eval z) (schurTransform_mul_X p)
  rwa [eval_mul, eval_X, eval_sub, eval_mul, eval_mul, eval_C, eval_C] at h

/-- If `‖a₀‖ < ‖aₙ‖`, the Schur transform has natural degree exactly `n - 1`. -/
theorem natDegree_schurTransform {p : ℂ[X]} (h : ‖p.coeff 0‖ < ‖p.leadingCoeff‖) :
    p.schurTransform.natDegree = p.natDegree - 1 := by
  rw [schurTransform, natDegree_divX_eq_natDegree_tsub_one]
  congr 1
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_le _ _)
      ((natDegree_C_mul_le _ _).trans (natDegree_conjReverse_le p)))
  · rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_natDegree_conjReverse, ← leadingCoeff,
      mul_comm, Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_sub, Complex.ofReal_ne_zero,
      sub_ne_zero, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact (pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero).ne'

/-- The Blaschke-factor inequality: if `‖r‖ < 1 ≤ ‖z‖` then `‖1 - conj z * r‖ ≤ ‖z - r‖`. -/
theorem norm_one_sub_conj_mul_le {z r : ℂ} (hr : ‖r‖ < 1) (hz : 1 ≤ ‖z‖) :
    ‖1 - conj z * r‖ ≤ ‖z - r‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm]
  have h1 : Complex.normSq r < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg r]
  have h2 : 1 ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith
  rw [Complex.normSq_apply] at h1 h2
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1.le)]

theorem norm_eval_eq_mul_prod (p : ℂ[X]) (z : ℂ) :
    ‖p.eval z‖ = ‖p.leadingCoeff‖ * (p.roots.map fun r => ‖z - r‖).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p))]
  rw [eval_mul, eval_C, eval_multiset_prod, norm_mul, Multiset.map_map]
  congr 1
  refine (map_multiset_prod (normHom : ℂ →*₀ ℝ) _).trans ?_
  simp [Multiset.map_map]

private theorem prod_map_norm_nonneg (s : Multiset ℂ) (f : ℂ → ℂ) :
    0 ≤ (s.map fun r => ‖f r‖).prod :=
  Multiset.prod_nonneg fun x hx => by
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hx
    exact norm_nonneg _

private theorem pow_card_mul_prod_le {s : Multiset ℂ} (hs : ∀ r ∈ s, ‖r‖ < 1) {z : ℂ}
    (hz : 1 ≤ ‖z‖) :
    ‖z‖ ^ Multiset.card s * (s.map fun r => ‖(conj z)⁻¹ - r‖).prod ≤
      (s.map fun r => ‖z - r‖).prod := by
  have hz0 : conj z ≠ 0 := by
    rw [_root_.map_ne_zero]
    rintro rfl
    norm_num at hz
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hfac : ‖z‖ * ‖(conj z)⁻¹ - a‖ ≤ ‖z - a‖ := by
      rw [← Complex.norm_conj z, ← norm_mul, mul_sub, mul_inv_cancel₀ hz0]
      exact norm_one_sub_conj_mul_le (hs a (Multiset.mem_cons_self a s)) hz
    have ih' := ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, pow_succ]
    calc _ = (‖z‖ * ‖(conj z)⁻¹ - a‖) *
          (‖z‖ ^ Multiset.card s * (s.map fun r => ‖(conj z)⁻¹ - r‖).prod) := by ring
      _ ≤ _ := mul_le_mul hfac ih' (mul_nonneg (by positivity) (prod_map_norm_nonneg _ _))
          (norm_nonneg _)

private theorem prod_map_norm_lt_one {s : Multiset ℂ} (hs : ∀ r ∈ s, ‖r‖ < 1) (hne : s ≠ 0) :
    (s.map fun r => ‖0 - r‖).prod < 1 := by
  have hle : ∀ t : Multiset ℂ, (∀ r ∈ t, ‖r‖ < 1) → (t.map fun r => ‖0 - r‖).prod ≤ 1 := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro ht
      have ha : ‖0 - a‖ < 1 := by
        rw [zero_sub, norm_neg]
        exact ht a (Multiset.mem_cons_self a t)
      have ih' := ih fun r hr => ht r (Multiset.mem_cons_of_mem hr)
      have h0 := prod_map_norm_nonneg t (fun r => 0 - r)
      rw [Multiset.map_cons, Multiset.prod_cons]
      nlinarith [norm_nonneg (0 - a)]
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ha' : ‖0 - a‖ < 1 := by
    rw [zero_sub, norm_neg]
    exact hs a ha
  have ht := hle t fun r hr => hs r (Multiset.mem_cons_of_mem hr)
  have h0 := prod_map_norm_nonneg t (fun r => 0 - r)
  rw [Multiset.map_cons, Multiset.prod_cons]
  nlinarith [norm_nonneg (0 - a)]

/-- For a Schur stable polynomial `q`, `‖q* z‖ ≤ ‖q z‖` whenever `1 ≤ ‖z‖`. -/
theorem IsSchurStable.norm_eval_conjReverse_le {p : ℂ[X]} (hp : p.IsSchurStable) {z : ℂ}
    (hz : 1 ≤ ‖z‖) : ‖p.conjReverse.eval z‖ ≤ ‖p.eval z‖ := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hroots : ∀ r ∈ p.roots, ‖r‖ < 1 := fun r hr => hp.2 r (isRoot_of_mem_roots hr)
  rw [eval_conjReverse hz0, norm_mul, Complex.norm_conj, norm_pow, norm_eval_eq_mul_prod,
    norm_eval_eq_mul_prod, ← IsAlgClosed.card_roots_eq_natDegree (p := p)]
  calc _ = ‖p.leadingCoeff‖ * (‖z‖ ^ Multiset.card p.roots *
        (p.roots.map fun r => ‖(conj z)⁻¹ - r‖).prod) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_card_mul_prod_le hroots hz) (norm_nonneg _)

/-- A Schur stable polynomial of positive degree satisfies `‖a₀‖ < ‖aₙ‖`. -/
theorem IsSchurStable.norm_coeff_zero_lt {p : ℂ[X]} (hp : p.IsSchurStable)
    (hn : p.natDegree ≠ 0) : ‖p.coeff 0‖ < ‖p.leadingCoeff‖ := by
  have hroots : ∀ r ∈ p.roots, ‖r‖ < 1 := fun r hr => hp.2 r (isRoot_of_mem_roots hr)
  have hne : p.roots ≠ 0 := by
    intro h0
    apply hn
    rw [← IsAlgClosed.card_roots_eq_natDegree, h0, Multiset.card_zero]
  have hlc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.2 (leadingCoeff_ne_zero.2 hp.1)
  rw [coeff_zero_eq_eval_zero, norm_eval_eq_mul_prod]
  calc _ < ‖p.leadingCoeff‖ * 1 := mul_lt_mul_of_pos_left (prod_map_norm_lt_one hroots hne) hlc
    _ = _ := mul_one _

/-- Evaluation of the conjugate reciprocal of the Schur transform:
`(T p)*(z) = aₙ · p*(z) - conj a₀ · p(z)` for `z ≠ 0`, provided `‖a₀‖ < ‖aₙ‖`. -/
theorem eval_conjReverse_schurTransform {p : ℂ[X]} (h : ‖p.coeff 0‖ < ‖p.leadingCoeff‖)
    (hn : p.natDegree ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    p.schurTransform.conjReverse.eval z =
      p.leadingCoeff * p.conjReverse.eval z - conj (p.coeff 0) * p.eval z := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hu : (conj z)⁻¹ ≠ 0 := inv_ne_zero ((_root_.map_ne_zero _).2 hz)
  have e1 := eval_schurTransform_mul p (conj z)⁻¹
  have e2 := eval_conjReverse hu p
  have e3 := eval_conjReverse hz p
  rw [map_inv₀, Complex.conj_conj, inv_inv] at e2
  rw [e2] at e1
  have e1' := congrArg conj e1
  simp only [map_mul, map_sub, map_pow, map_inv₀, Complex.conj_conj] at e1'
  rw [eval_conjReverse hz, natDegree_schurTransform h, hm, Nat.add_sub_cancel]
  rw [hm] at e1' e3
  have f1 : z ^ m = z ^ (m + 1) * z⁻¹ := by
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ hz, mul_one]
  have f2 : z ^ (m + 1) * z⁻¹ ^ (m + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  linear_combination conj (p.schurTransform.eval (conj z)⁻¹) * f1 + z ^ (m + 1) * e1' -
    p.leadingCoeff * e3 - conj (p.coeff 0) * p.eval z * f2

/-- **Schur–Cohn criterion** (Schur 1917, Cohn 1922).  A complex polynomial `p` of positive
degree has all its roots in the open unit disk if and only if `‖a₀‖ < ‖aₙ‖` and its Schur
transform `(conj aₙ • p - a₀ • p*) / X` has all its roots in the open unit disk. -/
theorem isSchurStable_iff {p : ℂ[X]} (hn : p.natDegree ≠ 0) :
    p.IsSchurStable ↔ ‖p.coeff 0‖ < ‖p.leadingCoeff‖ ∧ p.schurTransform.IsSchurStable := by
  constructor
  · intro hp
    have hlt := hp.norm_coeff_zero_lt hn
    have key : ∀ w : ℂ, 1 ≤ ‖w‖ → p.schurTransform.eval w * w ≠ 0 := by
      intro w hw h
      rw [eval_schurTransform_mul, sub_eq_zero] at h
      have hpos : 0 < ‖p.eval w‖ := norm_pos_iff.2 fun h' => (not_lt.2 hw) (hp.2 w h')
      have h1 : ‖p.leadingCoeff‖ * ‖p.eval w‖ = ‖p.coeff 0‖ * ‖p.conjReverse.eval w‖ := by
        rw [← Complex.norm_conj p.leadingCoeff, ← norm_mul, ← norm_mul, h]
      have h2 := mul_le_mul_of_nonneg_left (hp.norm_eval_conjReverse_le hw)
        (norm_nonneg (p.coeff 0))
      have h3 := mul_lt_mul_of_pos_right hlt hpos
      linarith
    refine ⟨hlt, fun h0 => key 1 (by simp) (by rw [h0, eval_zero, zero_mul]), fun w hw => ?_⟩
    by_contra hw'
    exact key w (not_lt.1 hw') (by rw [hw.eq_zero, zero_mul])
  · rintro ⟨hlt, hT⟩
    refine ⟨fun h0 => hn (by rw [h0, natDegree_zero]), fun z hz => ?_⟩
    by_contra hz'
    have hz1 : 1 ≤ ‖z‖ := not_lt.1 hz'
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz1
    have hTz : 0 < ‖p.schurTransform.eval z‖ :=
      norm_pos_iff.2 fun h => hz' (hT.2 z h)
    have e1 := eval_schurTransform_mul p z
    have e2 := eval_conjReverse_schurTransform hlt hn hz0
    have hid : p.leadingCoeff * z * p.schurTransform.eval z =
        -(p.coeff 0 * p.schurTransform.conjReverse.eval z) := by
      rw [e2]
      linear_combination p.leadingCoeff * e1 + (p.leadingCoeff * conj p.leadingCoeff -
        p.coeff 0 * conj (p.coeff 0)) * hz.eq_zero
    have h1 := congrArg norm hid
    rw [norm_neg, norm_mul, norm_mul, norm_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left (hT.norm_eval_conjReverse_le hz1)
      (norm_nonneg (p.coeff 0))
    have h3 := mul_lt_mul_of_pos_right hlt hTz
    have h4 := mul_le_mul_of_nonneg_left hz1
      (mul_nonneg (norm_nonneg p.leadingCoeff) hTz.le)
    nlinarith

end Polynomial
