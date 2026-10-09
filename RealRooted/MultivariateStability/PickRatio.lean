import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Fold
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# A Pick-type lemma for real rational functions

If `F` is real-rooted and `Im (G w / F w) ≤ 0` for every `w` in the upper half-plane, then to
the right of all roots of `F`, the function `t ↦ G t / F t` has nonpositive first and
nonnegative second derivative.  The proof is elementary: the hypothesis forces simple poles
with positive residues and a polynomial part of degree at most one with nonpositive slope, so
`G / F = b x + c + Σ c_r / (x - r)` with `b ≤ 0 ≤ c_r`.  This is the elementary core of the
Nevanlinna–Pick representation used for the Marcus–Spielman–Srivastava barrier argument.
Proof found by Aristotle (Harmonic) and adapted to the repository.
-/

open Polynomial

namespace RealRooted

noncomputable section

namespace PickRatio

/-- A continuous function whose imaginary part is nonpositive for `s > 0` has nonpositive
imaginary part at `0`. -/
private lemma im_nonpos_of_continuousAt (φ : ℝ → ℂ) (hc : ContinuousAt φ 0)
    (h : ∀ s : ℝ, 0 < s → (φ s).im ≤ 0) : (φ 0).im ≤ 0 := by
  have h1 : Filter.Tendsto (fun s => (φ s).im) (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0).im) :=
    ((Complex.continuous_im.tendsto _).comp hc).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto h1 (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- If `A * sin (m θ) ≥ 0` for all `θ ∈ (0, π)`, with `A ≠ 0` and `m ≥ 1`, then `m = 1`
and `A > 0`. -/
private lemma sign_lemma (A : ℝ) (m : ℕ) (hm : 1 ≤ m) (hA : A ≠ 0)
    (h : ∀ θ : ℝ, 0 < θ → θ < Real.pi → 0 ≤ A * Real.sin (m * θ)) :
    m = 1 ∧ 0 < A := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := h (Real.pi / (2 * m)) (by positivity) (by
    rw [div_lt_iff₀ (by positivity)]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [Real.pi_pos])
  have e1 : (m : ℝ) * (Real.pi / (2 * m)) = Real.pi / 2 := by
    field_simp
  rw [e1, Real.sin_pi_div_two, mul_one] at h1
  have hApos : 0 < A := lt_of_le_of_ne h1 (Ne.symm hA)
  refine ⟨?_, hApos⟩
  by_contra hne
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by lia : 2 ≤ m)
  have h2 := h (3 * Real.pi / (2 * m)) (by positivity) (by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos])
  have e2 : (m : ℝ) * (3 * Real.pi / (2 * m)) = Real.pi / 2 + Real.pi := by
    field_simp
    ring
  rw [e2, Real.sin_add_pi, Real.sin_pi_div_two] at h2
  linarith

private lemma im_ofReal_mul_exp (A x : ℝ) :
    ((A : ℂ) * Complex.exp (x * Complex.I)).im = A * Real.sin x := by
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- Local analysis at a real root which is not a root of `G`. -/
private lemma local_pole (F G : ℝ[X]) (hF : F ≠ 0) (r : ℝ) (hr : F.IsRoot r)
    (hG : G.eval r ≠ 0)
    (hUHP : ∀ w : ℂ, 0 < w.im →
      (F.map (algebraMap ℝ ℂ)).eval w ≠ 0 ∧
        ((G.map (algebraMap ℝ ℂ)).eval w / (F.map (algebraMap ℝ ℂ)).eval w).im ≤ 0) :
    F.rootMultiplicity r = 1 ∧ 0 < G.eval r / (F /ₘ (X - C r)).eval r := by
  set m := F.rootMultiplicity r with hm
  have hm1 : 1 ≤ m := (rootMultiplicity_pos hF).2 hr
  set F1 := F /ₘ (X - C r) ^ m with hF1
  have hFe : (X - C r) ^ m * F1 = F := pow_mul_divByMonic_rootMultiplicity_eq F r
  have hF1r : F1.eval r ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero r hF
  set A := G.eval r / F1.eval r with hA
  have hA0 : A ≠ 0 := div_ne_zero hG hF1r
  have key : ∀ θ : ℝ, 0 < θ → θ < Real.pi → 0 ≤ A * Real.sin (m * θ) := by
    intro θ hθ0 hθπ
    set ζ : ℂ := Complex.exp (θ * Complex.I) with hζ
    have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
    have hζim : ζ.im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    set φ : ℝ → ℂ := fun s => aeval ((r : ℂ) + s * ζ) G /
      (ζ ^ m * aeval ((r : ℂ) + s * ζ) F1) with hφ
    have hφ0 : φ 0 = (A : ℂ) * Complex.exp ((-(m * θ) : ℝ) * Complex.I) := by
      simp only [hφ, hA, Complex.ofReal_zero, zero_mul, add_zero]
      rw [← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval,
        aeval_algebraMap_apply_eq_algebraMap_eval, hζ, ← Complex.exp_nat_mul]
      simp only [Complex.coe_algebraMap]
      have harg : ((-(m * θ) : ℝ) : ℂ) * Complex.I = -(m * (θ * Complex.I)) := by
        push_cast
        ring
      rw [harg, Complex.exp_neg]
      have h' : ((F1.eval r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF1r
      have h'' := Complex.exp_ne_zero (m * (θ * Complex.I))
      push_cast
      field_simp
    have hcont : ContinuousAt φ 0 := by
      have hc : ∀ Q : ℝ[X], Continuous (fun s : ℝ => aeval ((r : ℂ) + s * ζ) Q) :=
        fun Q => (Polynomial.continuous_aeval Q).comp (by fun_prop)
      have hden : ζ ^ m * aeval ((r : ℂ) + ((0 : ℝ) : ℂ) * ζ) F1 ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ hζ0) ?_
        simp only [Complex.ofReal_zero, zero_mul, add_zero]
        rw [← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval,
          Complex.coe_algebraMap]
        exact Complex.ofReal_ne_zero.2 hF1r
      exact ((hc G).continuousAt).div ((continuous_const.mul (hc F1)).continuousAt) hden
    have hpos : ∀ s : ℝ, 0 < s → (φ s).im ≤ 0 := by
      intro s hs
      simp only [hφ]
      set w : ℂ := (r : ℂ) + s * ζ with hw
      have hwim : 0 < w.im := by
        simp only [hw, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, hζim, zero_add]
        positivity
      obtain ⟨h1, h2⟩ := hUHP w hwim
      simp only [eval_map_algebraMap] at h1 h2
      have hFw : aeval w F = ((s : ℂ) * ζ) ^ m * aeval w F1 := by
        rw [← hFe]
        simp [hw]
      rw [hFw] at h1 h2
      have hF1w : aeval w F1 ≠ 0 := right_ne_zero_of_mul h1
      have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
      have heq : aeval w G / (ζ ^ m * aeval w F1) =
          ((s ^ m : ℝ) : ℂ) * (aeval w G / (((s : ℂ) * ζ) ^ m * aeval w F1)) := by
        push_cast
        field_simp
        ring
      rw [heq, Complex.im_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
    have h0 := im_nonpos_of_continuousAt φ hcont hpos
    rw [hφ0, im_ofReal_mul_exp, Real.sin_neg] at h0
    linarith
  obtain ⟨h1, h2⟩ := sign_lemma A m hm1 hA0 key
  refine ⟨h1, ?_⟩
  have hF1eq : F /ₘ (X - C r) = F1 := by rw [hF1, h1, pow_one]
  rw [hF1eq]
  exact h2

/-- Partial fraction identity for a split polynomial with simple roots. -/
private lemma pf_identity (F G : ℝ[X]) (hF : F ≠ 0) (hs : F.Splits) (hnd : F.roots.Nodup) :
    ∃ Q : ℝ[X], G = Q * F + ∑ r ∈ F.roots.toFinset,
      C (G.eval r / (F /ₘ (X - C r)).eval r) * (F /ₘ (X - C r)) := by
  set S := ∑ r ∈ F.roots.toFinset, C (G.eval r / (F /ₘ (X - C r)).eval r) *
    (F /ₘ (X - C r))
  have hmult : ∀ r ∈ F.roots, F.rootMultiplicity r = 1 := by
    intro r hr
    have h1 := (Multiset.nodup_iff_count_le_one.1 hnd) r
    have h2 := Multiset.count_pos.2 hr
    rw [count_roots] at h1 h2
    lia
  have hDr : ∀ r ∈ F.roots, (F /ₘ (X - C r)).eval r ≠ 0 := by
    intro r hr
    have h := eval_divByMonic_pow_rootMultiplicity_ne_zero r hF
    rwa [hmult r hr, pow_one] at h
  have hDr' : ∀ r ∈ F.roots, ∀ r' ∈ F.roots, r' ≠ r →
      (F /ₘ (X - C r)).eval r' = 0 := by
    intro r hr r' hr' hne
    have hFe : (X - C r) * (F /ₘ (X - C r)) = F :=
      mul_divByMonic_eq_iff_isRoot.2 ((mem_roots hF).1 hr)
    have h0 : F.eval r' = 0 := (mem_roots hF).1 hr'
    rw [← hFe, eval_mul] at h0
    simp only [eval_sub, eval_X, eval_C] at h0
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
  have hroot : ∀ r ∈ F.roots, (G - S).IsRoot r := by
    intro r hr
    simp only [IsRoot, eval_sub, S, eval_finsetSum, eval_mul, eval_C]
    rw [Finset.sum_eq_single r]
    · rw [div_mul_cancel₀ _ (hDr r hr), sub_self]
    · intro r' hr' hne
      rw [hDr' r' (Multiset.mem_toFinset.1 hr') r hr (Ne.symm hne), mul_zero]
    · intro h
      exact absurd (Multiset.mem_toFinset.2 hr) h
  have hdvd : F ∣ G - S := by
    by_cases h0 : G - S = 0
    · rw [h0]
      exact dvd_zero _
    have hle : F.roots ≤ (G - S).roots :=
      (Multiset.le_iff_subset hnd).2 fun r hr => (mem_roots h0).2 (hroot r hr)
    have h1 := (Multiset.prod_X_sub_C_dvd_iff_le_roots h0 F.roots).2 hle
    have hFe := hs.eq_prod_roots
    calc
      F = _ := hFe
      _ ∣ G - S := (C_mul_dvd (leadingCoeff_ne_zero.2 hF)).2 h1
  obtain ⟨Q, hQ⟩ := hdvd
  exact ⟨Q, by rw [mul_comm, ← hQ]; ring⟩

private lemma pf_eval {K : Type*} [Field K] [Algebra ℝ K] (F G Q : ℝ[X]) (S : Finset ℝ)
    (c : ℝ → ℝ) (hS : ∀ r ∈ S, F.IsRoot r)
    (hid : G = Q * F + ∑ r ∈ S, C (c r) * (F /ₘ (X - C r))) (w : K)
    (hw : aeval w F ≠ 0) :
    aeval w G / aeval w F = aeval w Q +
      ∑ r ∈ S, algebraMap ℝ K (c r) / (w - algebraMap ℝ K r) := by
  rw [hid, map_add, map_mul, map_sum, add_div, mul_div_assoc, div_self hw, mul_one,
    Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  have hFe : (X - C r) * (F /ₘ (X - C r)) = F :=
    mul_divByMonic_eq_iff_isRoot.2 (hS r hr)
  have hF' : aeval w F = (w - algebraMap ℝ K r) * aeval w (F /ₘ (X - C r)) := by
    conv_lhs => rw [← hFe]
    simp
  rw [hF'] at hw ⊢
  have h1 : w - algebraMap ℝ K r ≠ 0 := left_ne_zero_of_mul hw
  have h2 := right_ne_zero_of_mul hw
  simp only [map_mul, aeval_C]
  field_simp

/-- Behaviour at infinity: the polynomial part has degree `≤ 1` and nonpositive slope. -/
private lemma poly_part (Q : ℝ[X]) (S : Finset ℝ) (c : ℝ → ℝ)
    (h : ∀ w : ℂ, 0 < w.im →
      (aeval w Q + ∑ r ∈ S, (c r : ℂ) / (w - r)).im ≤ 0) :
    Q.natDegree ≤ 1 ∧ Q.coeff 1 ≤ 0 := by
  set d := Q.natDegree with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · exact ⟨by lia, le_of_eq (coeff_eq_zero_of_natDegree_lt (by lia))⟩
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp [d] at hdpos
  have hq : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hQ0
  have key : ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      0 ≤ (-Q.leadingCoeff) * Real.sin (d * θ) := by
    intro θ hθ0 hθπ
    set ζ : ℂ := Complex.exp (θ * Complex.I) with hζ
    have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
    have hζim' : ζ.im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ
    have hζim : 0 < ζ.im := hζim' ▸ Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    set φ : ℝ → ℂ := fun s =>
      ∑ i ∈ Finset.range (d + 1), (Q.coeff i : ℂ) * ζ ^ i * (s : ℂ) ^ (d - i) +
        ∑ r ∈ S, (c r : ℂ) * (s : ℂ) ^ (d + 1) / (ζ - r * s) with hφ
    have hcont : ContinuousAt φ 0 := by
      apply ContinuousAt.add
      · exact (continuous_finsetSum _ fun i _ => by fun_prop).continuousAt
      · refine tendsto_finsetSum _ fun r _ => ?_
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        simpa using hζ0
    have hφ0 : φ 0 = (Q.leadingCoeff : ℂ) * Complex.exp ((d * θ : ℝ) * Complex.I) := by
      simp only [φ, Complex.ofReal_zero]
      rw [Finset.sum_eq_single d]
      · have hpow : Complex.exp ((d * θ : ℝ) * Complex.I) = ζ ^ d := by
          rw [hζ, ← Complex.exp_nat_mul]
          push_cast
          ring_nf
        rw [hpow, hd]
        simp
      · intro i hi hne
        have hdiff : 0 < d - i := by
          have hi' := Finset.mem_range.1 hi
          lia
        simp [zero_pow hdiff.ne']
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.lt_succ_self d)) h
    have hpos : ∀ s : ℝ, 0 < s → (φ s).im ≤ 0 := by
      intro s hs
      have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
      have heq : φ s = ((s ^ d : ℝ) : ℂ) *
          (aeval (ζ / s) Q + ∑ r ∈ S, (c r : ℂ) / (ζ / s - r)) := by
        simp only [φ]
        rw [aeval_eq_sum_range, ← hd, mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [Complex.real_smul]
          push_cast
          rw [show (s : ℂ) ^ d = (s : ℂ) ^ (d - i) * (s : ℂ) ^ i by
            rw [← pow_add, Nat.sub_add_cancel hi']]
          rw [div_pow]
          field_simp
        · refine Finset.sum_congr rfl fun r _ => ?_
          have hne : ζ - r * s ≠ 0 := by
            intro h0
            have him := congrArg Complex.im h0
            have him' : ζ.im = 0 := by
              simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
                Complex.ofReal_re, zero_mul, mul_zero, add_zero, sub_zero,
                Complex.zero_im] using him
            rw [him'] at hζim
            linarith
          have hne' : ζ / s - r ≠ 0 := by
            rw [div_sub' hs0]
            exact div_ne_zero (by rwa [mul_comm]) hs0
          push_cast
          rw [div_sub' hs0]
          field_simp
          ring
      rw [heq, Complex.im_ofReal_mul]
      refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (h _ ?_)
      rw [Complex.div_ofReal_im]
      exact div_pos hζim hs
    have h0 := im_nonpos_of_continuousAt φ hcont hpos
    rw [hφ0, im_ofReal_mul_exp] at h0
    linarith
  obtain ⟨h1, h2⟩ := sign_lemma (-Q.leadingCoeff) d hdpos (neg_ne_zero.2 hq) key
  refine ⟨h1.le, ?_⟩
  have hcoeff : Q.coeff 1 = Q.leadingCoeff := by
    rw [leadingCoeff, ← hd, h1]
  rw [hcoeff]
  linarith

private lemma deriv_congr_open (f g : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (t : ℝ)
    (ht : t ∈ U) (hfg : ∀ x ∈ U, f x = g x) :
    deriv f t = deriv g t ∧ deriv (deriv f) t = deriv (deriv g) t := by
  have key : ∀ x ∈ U, deriv f x = deriv g x := fun x hx =>
    Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) hfg)
  exact ⟨key t ht, Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds ht) key)⟩

/-- The explicit computation for `Q + Σ c_r/(x - r)`. -/
private lemma explicit_derivs (Q : ℝ[X]) (S : Finset ℝ) (c : ℝ → ℝ)
    (hQ : Q.natDegree ≤ 1) (hb : Q.coeff 1 ≤ 0) (hc : ∀ r ∈ S, 0 < c r) (t : ℝ)
    (ht : ∀ r ∈ S, r < t) :
    deriv (fun s => Q.eval s + ∑ r ∈ S, c r / (s - r)) t ≤ 0 ∧
      deriv (deriv (fun s => Q.eval s + ∑ r ∈ S, c r / (s - r))) t ≥ 0 := by
  set U : Set ℝ := ⋂ r ∈ S, Set.Ioi r
  have hU : IsOpen U := isOpen_biInter_finset fun r _ => isOpen_Ioi
  have htU : t ∈ U := Set.mem_iInter₂.2 ht
  have hQe := eq_X_add_C_of_natDegree_le_one hQ
  have d1 : ∀ x ∈ U, HasDerivAt (fun s => Q.eval s + ∑ r ∈ S, c r / (s - r))
      (Q.coeff 1 + ∑ r ∈ S, c r * (-1 / (x - r) ^ 2)) x := by
    intro x hx
    have hx' : ∀ r ∈ S, x - r ≠ 0 := fun r hr =>
      sub_ne_zero.2 (ne_of_gt (Set.mem_iInter₂.1 hx r hr))
    have hQd : HasDerivAt (fun s => Q.eval s) (Q.coeff 1) x := by
      rw [hQe]
      simpa using ((hasDerivAt_id x).const_mul (Q.coeff 1)).add_const (Q.coeff 0)
    refine hQd.add (HasDerivAt.fun_sum fun r hr => ?_)
    have h := (((hasDerivAt_id x).sub_const r).inv (hx' r hr)).const_mul (c r)
    convert h using 1
    · rfl
    · rfl
  have d2 : HasDerivAt (fun x => Q.coeff 1 + ∑ r ∈ S, c r * (-1 / (x - r) ^ 2))
      (∑ r ∈ S, c r * (2 * (t - r) / ((t - r) ^ 2) ^ 2)) t := by
    have h := (hasDerivAt_const t (Q.coeff 1)).add (HasDerivAt.fun_sum (u := S) fun r hr =>
      ((((hasDerivAt_id t).sub_const r).pow 2).inv
        (pow_ne_zero 2 (sub_ne_zero.2 (ne_of_gt (ht r hr))))).const_mul (-c r))
    convert h using 1
    · ext x
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
      ring
    · simp only [Nat.cast_ofNat, id_eq, Nat.add_one_sub_one, pow_one, mul_one, Pi.pow_apply,
        neg_mul, Finset.sum_neg_distrib, zero_add]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
  have hderiv : ∀ x ∈ U, deriv (fun s => Q.eval s + ∑ r ∈ S, c r / (s - r)) x =
      Q.coeff 1 + ∑ r ∈ S, c r * (-1 / (x - r) ^ 2) := fun x hx => (d1 x hx).deriv
  refine ⟨?_, ?_⟩
  · rw [hderiv t htU]
    have hsum : ∑ r ∈ S, c r * (-1 / (t - r) ^ 2) ≤ 0 :=
      Finset.sum_nonpos fun r hr => by
        have hcr := hc r hr
        have hsq : 0 < (t - r) ^ 2 := pow_pos (sub_pos.2 (ht r hr)) 2
        have hneg : -1 / (t - r) ^ 2 < 0 := div_neg_of_neg_of_pos (by norm_num) hsq
        nlinarith
    linarith
  · rw [Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds htU) hderiv),
      d2.deriv]
    exact Finset.sum_nonneg fun r hr => by
      have hcr := hc r hr
      have hpos : 0 < t - r := sub_pos.2 (ht r hr)
      positivity

/-- The case where `F` and `G` have no common real root. -/
private lemma coprime_case (F G : ℝ[X]) (hF : F ≠ 0) (hs : F.Splits)
    (hcop : ∀ r ∈ F.roots, G.eval r ≠ 0)
    (hUHP : ∀ w : ℂ, 0 < w.im →
      (F.map (algebraMap ℝ ℂ)).eval w ≠ 0 ∧
        ((G.map (algebraMap ℝ ℂ)).eval w / (F.map (algebraMap ℝ ℂ)).eval w).im ≤ 0)
    (t : ℝ) (ht : ∀ r ∈ F.roots, r < t) :
    deriv (fun s => G.eval s / F.eval s) t ≤ 0 ∧
      deriv (deriv (fun s => G.eval s / F.eval s)) t ≥ 0 := by
  have hloc : ∀ r ∈ F.roots, F.rootMultiplicity r = 1 ∧
      0 < G.eval r / (F /ₘ (X - C r)).eval r := fun r hr =>
    local_pole F G hF r ((mem_roots hF).1 hr) (hcop r hr) hUHP
  have hnd : F.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    rw [count_roots]
    by_cases ha : a ∈ F.roots
    · rw [(hloc a ha).1]
    · rw [rootMultiplicity_eq_zero (fun h => ha ((mem_roots hF).2 h))]
      lia
  obtain ⟨Q, hQ⟩ := pf_identity F G hF hs hnd
  set S := F.roots.toFinset with hSdef
  set c : ℝ → ℝ := fun r => G.eval r / (F /ₘ (X - C r)).eval r with hcdef
  have hS : ∀ r ∈ S, F.IsRoot r := fun r hr =>
    (mem_roots hF).1 (Multiset.mem_toFinset.1 hr)
  have hpos : ∀ r ∈ S, 0 < c r := fun r hr =>
    (hloc r (Multiset.mem_toFinset.1 hr)).2
  have hpp := poly_part Q S c (by
    intro w hw
    have h1 := hUHP w hw
    rw [eval_map_algebraMap, eval_map_algebraMap] at h1
    have h2 := pf_eval F G Q S c hS hQ w h1.1
    simp only [Complex.coe_algebraMap] at h2
    rw [← h2]
    exact h1.2)
  have hexp := explicit_derivs Q S c hpp.1 hpp.2 hpos t
    (fun r hr => ht r (Multiset.mem_toFinset.1 hr))
  have hcongr := deriv_congr_open (fun s => G.eval s / F.eval s)
    (fun s => Q.eval s + ∑ r ∈ S, c r / (s - r)) (⋂ r ∈ S, Set.Ioi r)
    (isOpen_biInter_finset fun r _ => isOpen_Ioi) t
    (Set.mem_iInter₂.2 fun r hr => ht r (Multiset.mem_toFinset.1 hr))
    (by
      intro x hx
      have hx' : ∀ r ∈ S, r < x := fun r hr => Set.mem_iInter₂.1 hx r hr
      have hFx : F.eval x ≠ 0 := by
        intro h0
        have hr := hx' x (Multiset.mem_toFinset.2 ((mem_roots hF).2 h0))
        exact lt_irrefl _ hr
      have h2 := pf_eval (K := ℝ) F G Q S c hS hQ x (by simpa using hFx)
      simpa using h2)
  rw [hcongr.1, hcongr.2]
  exact hexp

/-- A Pick-type lemma for rational functions.  This is the elementary core of the
Marcus--Spielman--Srivastava Pick/Nevanlinna representation route (their Lemma 5.7).
If `F` is nonzero and split, and `G/F` has nonpositive imaginary part on the upper
half-plane, then to the right of the roots of `F` its first derivative is nonpositive
and its second derivative is nonnegative. -/
theorem deriv_nonpos_and_second_deriv_nonneg (F G : ℝ[X]) (hF : F ≠ 0) (hs : F.Splits)
    (hUHP : ∀ w : ℂ, 0 < w.im →
      (F.map (algebraMap ℝ ℂ)).eval w ≠ 0 ∧
        ((G.map (algebraMap ℝ ℂ)).eval w / (F.map (algebraMap ℝ ℂ)).eval w).im ≤ 0)
    (t : ℝ) (ht : ∀ r ∈ F.roots, r < t) :
    deriv (fun s => G.eval s / F.eval s) t ≤ 0 ∧
      deriv (deriv (fun s => G.eval s / F.eval s)) t ≥ 0 := by
  induction h : F.natDegree using Nat.strong_induction_on generalizing F G with
  | _ n ih =>
    by_cases hcop : ∀ r ∈ F.roots, G.eval r ≠ 0
    · exact coprime_case F G hF hs hcop hUHP t ht
    · push Not at hcop
      obtain ⟨r, hrF, hrG⟩ := hcop
      have hrF' : F.IsRoot r := (mem_roots hF).1 hrF
      set F' := F /ₘ (X - C r)
      set G' := G /ₘ (X - C r)
      have hFe : (X - C r) * F' = F := mul_divByMonic_eq_iff_isRoot.2 hrF'
      have hGe : (X - C r) * G' = G := mul_divByMonic_eq_iff_isRoot.2 hrG
      have hF' : F' ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at hFe
        exact hF hFe.symm
      have hdeg : F'.natDegree < n := by
        rw [← h, ← hFe, natDegree_mul (X_sub_C_ne_zero r) hF', natDegree_X_sub_C]
        lia
      have hs' : F'.Splits := hs.of_dvd hF ⟨X - C r, by rw [← hFe, mul_comm]⟩
      have hroots : ∀ x ∈ F'.roots, x ∈ F.roots := by
        intro x hx
        rw [← hFe, roots_mul (by rw [hFe]; exact hF)]
        exact Multiset.mem_add.2 (Or.inr hx)
      have hUHP' : ∀ w : ℂ, 0 < w.im →
          (F'.map (algebraMap ℝ ℂ)).eval w ≠ 0 ∧
            ((G'.map (algebraMap ℝ ℂ)).eval w /
              (F'.map (algebraMap ℝ ℂ)).eval w).im ≤ 0 := by
        intro w hw
        obtain ⟨h1, h2⟩ := hUHP w hw
        have hwr : w - (r : ℂ) ≠ 0 := by
          intro h0
          have him : w.im = 0 := by
            have him' := congrArg Complex.im h0
            simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] using him'
          linarith
        rw [← hFe] at h1 h2
        rw [← hGe] at h2
        simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, eval_mul, eval_sub,
          eval_X, eval_C, Complex.coe_algebraMap] at h1 h2
        refine ⟨fun h0 => h1 (by rw [h0, mul_zero]), ?_⟩
        rwa [mul_div_mul_left _ _ hwr] at h2
      obtain ⟨hd1, hd2⟩ := ih _ hdeg F' G' hF' hs' hUHP'
        (fun x hx => ht x (hroots x hx)) rfl
      have hcongr := deriv_congr_open (fun s => G.eval s / F.eval s)
        (fun s => G'.eval s / F'.eval s) {x | x ≠ r} isOpen_ne t (ne_of_gt (ht r hrF))
        (by
          intro x hx
          simp only [Set.mem_ofPred_eq] at hx
          have hxr : x - r ≠ 0 := sub_ne_zero.2 hx
          rw [← hFe, ← hGe]
          simp only [eval_mul, eval_sub, eval_X, eval_C]
          rw [mul_div_mul_left _ _ hxr])
      rw [hcongr.1, hcongr.2]
      exact ⟨hd1, hd2⟩

end PickRatio

end

end RealRooted
