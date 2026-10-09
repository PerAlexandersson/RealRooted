import RealRooted.PFPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Brändén's theorem: the log-concavity transform preserves Pólya frequency

For `p = Σ a_k X^k`, `logConcavityTransform p = Σ (a_k² − a_(k−1) a_(k+1)) X^k`.
`IsPFPolynomial.logConcavityTransform`: if `p` has nonnegative coefficients and only real,
nonpositive zeros, so does its transform (P. Brändén, “Iterated sequences and the geometry of
zeros”, J. reine angew. Math. 658 (2011), 115–131; conjectured by Fisk, McNamara–Sagan and
Stanley).

The proof here differs from Brändén's.  It was found by Aristotle (Harmonic) and adapted.  It
uses linear functionals `X^k ↦ w_k` that do not vanish on polynomials whose zeros lie in a
half-plane: this property holds for evaluation at `0`, survives composition with `1 − c d/dX`
and pointwise limits, and holds for the Catalan-type moment sequence obtained from Laguerre-type
approximations; a factorization of the transform then gives real-rootedness.
-/



/-!
## Linear functionals that do not vanish on polynomials with zeros in a half-plane

For a sequence `w : ℕ → ℂ` we consider the linear functional `Lam w : ℂ[X] → ℂ`
sending `X ^ k` to `w k`. The predicate `Good w` asserts a quantitative non-vanishing property on
polynomials all
of whose zeros lie in a half-plane `{z | m ≤ z.im}`.  It holds for evaluation at `0`, is preserved
by `Lam w ↦ Lam w ∘ (1 - c • d/dX)` for real `c`, and is closed under pointwise limits.
-/


open Polynomial Finset

namespace RealRooted.Branden

/-- The linear functional with moment sequence `w`. -/
private noncomputable def Lam (w : ℕ → ℂ) (P : ℂ[X]) : ℂ := P.sum fun k a => a * w k

/-- Evaluate `Lam` as a finite coefficient sum. -/
private lemma Lam_eq_sum_range (w : ℕ → ℂ) (P : ℂ[X]) {D : ℕ} (hD : P.natDegree < D) :
    Lam w P = ∑ k ∈ range D, P.coeff k * w k :=
  sum_over_range' P (by simp) D hD

private lemma Lam_add (w : ℕ → ℂ) (P Q : ℂ[X]) : Lam w (P + Q) = Lam w P + Lam w Q := by
  unfold Lam
  exact sum_add_index P Q _ (by simp) (by intros; ring)

private lemma Lam_C_mul (w : ℕ → ℂ) (c : ℂ) (P : ℂ[X]) :
    Lam w (C c * P) = c * Lam w P := by
  set D := max (C c * P).natDegree P.natDegree + 1
  have hD₁ : (C c * P).natDegree < D := by
    dsimp [D]
    exact Nat.lt_succ_of_le (le_max_left _ _)
  have hD₂ : P.natDegree < D := by
    dsimp [D]
    exact Nat.lt_succ_of_le (le_max_right _ _)
  rw [Lam_eq_sum_range w _ hD₁, Lam_eq_sum_range w _ hD₂, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp [coeff_C_mul, mul_assoc]

private lemma Lam_sub (w : ℕ → ℂ) (P Q : ℂ[X]) : Lam w (P - Q) = Lam w P - Lam w Q := by
  have := Lam_add w (P - Q) Q
  simp only [sub_add_cancel] at this
  rw [this]; ring

/-- A moment sequence is good when its functional has the required lower bound. -/
private def Good (w : ℕ → ℂ) : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ P : ℂ[X], P ≠ 0 → (∀ z, P.IsRoot z → m ≤ z.im) →
    ‖P.leadingCoeff‖ * m ^ P.natDegree ≤ ‖Lam w P‖

/-- The moments of evaluation at zero. -/
private noncomputable def w0 : ℕ → ℂ := fun k => if k = 0 then 1 else 0

private lemma Lam_w0 (P : ℂ[X]) : Lam w0 P = P.coeff 0 := by
  rw [Lam_eq_sum_range w0 P (Nat.lt_succ_self _), sum_range_succ']
  simp [w0]

/-- Evaluation at zero is a good moment functional. -/
private lemma good_w0 : Good w0 := by
  intro m hm P hP hroots
  have hnp : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map (‖·‖)).prod := fun s => by
    have := map_multiset_prod (normHom (α := ℂ)) s
    simpa using this
  rw [Lam_w0, coeff_zero_eq_eval_zero, (IsAlgClosed.splits P).eval_eq_prod_roots, norm_mul,
    hnp, Multiset.map_map]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [(IsAlgClosed.splits P).natDegree_eq_card_roots]
  have key : ∀ s : Multiset ℂ, (∀ z ∈ s, m ≤ z.im) →
      m ^ Multiset.card s ≤ (s.map ((fun x => ‖x‖) ∘ fun x => 0 - x)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro h
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ, mul_comm]
      have ha : m ≤ ‖0 - a‖ := by
        rw [zero_sub, norm_neg]
        exact (h a (Multiset.mem_cons_self a t)).trans
          ((le_abs_self _).trans (Complex.abs_im_le_norm a))
      exact mul_le_mul ha (ih fun z hz => h z (Multiset.mem_cons_of_mem hz))
        (pow_nonneg hm _) (norm_nonneg _)
  exact key _ fun z hz => hroots z ((mem_roots hP).mp hz)

private lemma im_multiset_sum_pos (s : Multiset ℂ) (hs : s ≠ 0) (h : ∀ x ∈ s, 0 < x.im) :
    0 < s.sum.im := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a t ih =>
    rw [Multiset.sum_cons, Complex.add_im]
    have ha := h a (Multiset.mem_cons_self a t)
    by_cases ht : t = 0
    · simp [ht, ha]
    · have := ih ht (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      linarith

/-- Key lemma: below the half-plane, the logarithmic derivative has positive imaginary part. -/
private lemma im_logDeriv_pos {P : ℂ[X]} (hP : P ≠ 0) {m : ℝ}
    (hroots : ∀ z, P.IsRoot z → m ≤ z.im)
    {z : ℂ} (hz : z.im < m) (hdeg : 0 < P.natDegree) :
    P.eval z ≠ 0 ∧ 0 < (P.derivative.eval z / P.eval z).im := by
  have hne : P.eval z ≠ 0 := fun h => absurd (hroots z h) (not_le.mpr hz)
  refine ⟨hne, ?_⟩
  rw [(IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hne]
  have hcard : P.roots ≠ 0 := (IsAlgClosed.splits P).roots_ne_zero hdeg.ne'
  refine im_multiset_sum_pos _ (by simpa using hcard) ?_
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  have hrm := hroots r ((mem_roots hP).mp hr)
  have hzr : z - r ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; linarith
  rw [one_div, Complex.inv_im, Complex.sub_im]
  apply div_pos
  · linarith
  · exact Complex.normSq_pos.mpr hzr

/-- The moment sequence obtained by applying a real first-order shift. -/
private noncomputable def wstep (w : ℕ → ℂ) (c : ℝ) : ℕ → ℂ :=
  fun k => w k - c * k * w (k - 1)

/-- Applying `wstep` corresponds to subtracting a derivative term. -/
private lemma Lam_wstep (w : ℕ → ℂ) (c : ℝ) (P : ℂ[X]) :
    Lam (wstep w c) P = Lam w (P - C (c : ℂ) * derivative P) := by
  rw [Lam_sub, Lam_C_mul]
  have h1 : P.natDegree < P.natDegree + 2 := by lia
  have h2 : (derivative P).natDegree < P.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_derivative_le P) (by lia)
  rw [Lam_eq_sum_range _ P h1, Lam_eq_sum_range w P h1, Lam_eq_sum_range w _ h2]
  simp only [wstep, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  rw [sum_range_succ']
  simp only [CharP.cast_eq_zero, mul_zero, zero_mul, add_zero, coeff_derivative]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-- Goodness is preserved by the real first-order shift. -/
private lemma good_wstep {w : ℕ → ℂ} (hw : Good w) (c : ℝ) : Good (wstep w c) := by
  intro m hm P hP hroots
  rw [Lam_wstep]
  by_cases hdeg : P.natDegree = 0
  · have hd : derivative P = 0 := by
      obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hdeg
      rw [← ha, derivative_C]
    simpa [hd] using hw m hm P hP hroots
  have hlt : (C (c : ℂ) * derivative P).natDegree < P.natDegree :=
    lt_of_le_of_lt (natDegree_C_mul_le _ _) (natDegree_derivative_lt hdeg)
  have hnd : (P - C (c : ℂ) * derivative P).natDegree = P.natDegree :=
    natDegree_sub_eq_left_of_natDegree_lt hlt
  have hlc : (P - C (c : ℂ) * derivative P).leadingCoeff = P.leadingCoeff :=
    leadingCoeff_sub_of_degree_lt (degree_lt_degree hlt)
  have hQ : P - C (c : ℂ) * derivative P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hnd; exact hdeg hnd.symm
  have hrQ : ∀ z, (P - C (c : ℂ) * derivative P).IsRoot z → m ≤ z.im := by
    intro z hz
    by_contra hlt'
    push Not at hlt'
    obtain ⟨hne, hpos⟩ := im_logDeriv_pos hP hroots hlt' (Nat.pos_of_ne_zero hdeg)
    have hz' : P.eval z = c * (derivative P).eval z := by
      have := hz.eq_zero
      simp only [eval_sub, eval_mul, eval_C] at this
      linear_combination this
    have h1 : (c : ℂ) * ((derivative P).eval z / P.eval z) = 1 := by
      rw [mul_div_assoc', ← hz', div_self hne]
    have h2 := congrArg Complex.im h1
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.one_im] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · rw [h] at hz'
      exact hne (by simpa using hz')
    · linarith
  have := hw m hm _ hQ hrQ
  rwa [hnd, hlc] at this

/-- Goodness is closed under pointwise convergence of moment sequences. -/
private lemma good_of_tendsto {w : ℕ → ℕ → ℂ} {v : ℕ → ℂ} (hw : ∀ N, Good (w N))
    (hlim : ∀ k, Filter.Tendsto (fun N => w N k) Filter.atTop (nhds (v k))) : Good v := by
  intro m hm P hP hroots
  have hT : Filter.Tendsto (fun N => ‖Lam (w N) P‖) Filter.atTop (nhds ‖Lam v P‖) := by
    simp only [Lam_eq_sum_range _ P (Nat.lt_succ_self _)]
    exact (tendsto_finsetSum _ fun k _ => (hlim k).const_mul _).norm
  exact ge_of_tendsto' hT fun N => hw N m hm P hP hroots

end RealRooted.Branden

/-!
## Laguerre reduction for the stability-functional proof

This is part of a different stability-functional/Laguerre proof of Brändén's
result, found by Aristotle. The cited result is P. Brändén, “Iterated
sequences and the geometry of zeros”, J. reine angew. Math. 658 (2011),
115–131.
-/



/-!
## Good functionals from real-rooted polynomials

If `H` is a real polynomial with only negative zeros and `H 0 = 1`, then the functional with
moments `w (2j) = (2j)! (-1)^j H_j`, `w (2j+1) = 0` is `Good`.
-/


open Polynomial Finset

namespace RealRooted.Branden

/-- The moments associated with the polynomial functional `H(-D²)`. -/
private noncomputable def wH (H : ℝ[X]) : ℕ → ℂ := fun k =>
  if Even k then (k.factorial : ℂ) * (-1) ^ (k / 2) * (H.coeff (k / 2) : ℂ) else 0

/-- Two opposite first-order shifts give the second-order moment recurrence. -/
private lemma wstep_wstep (w : ℕ → ℂ) (c : ℝ) (k : ℕ) :
    wstep (wstep w c) (-c) k = w k - (c : ℂ) ^ 2 * k * (k - 1) * w (k - 2) := by
  rcases k with _ | k
  · simp [wstep]
  · simp only [wstep, Nat.add_sub_cancel, (by lia : k + 1 - 2 = k - 1)]
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- The constant polynomial gives the evaluation-at-zero moments. -/
private lemma wH_one : wH 1 = w0 := by
  funext k
  unfold wH w0
  by_cases hk : k = 0
  · subst hk; simp
  · rw [ite_eq_right hk, coeff_one]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; obtain ⟨j, rfl⟩ := h1; lia) | simp

/-- Multiplying `G` by a linear factor transforms its moments explicitly. -/
private lemma wH_mul (G : ℝ[X]) (r : ℝ) (k : ℕ) :
    wH (G - C (1 / r) * X * G) k = wH G k + ((1 / r : ℝ) : ℂ) * k * (k - 1) * wH G (k - 2) := by
  unfold wH
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rcases j with _ | i
    · simp
    · have e1 : (i + 1 + (i + 1)) / 2 = i + 1 := by lia
      have e2 : (i + 1 + (i + 1) - 2) = i + i := by lia
      have e3 : (i + i) / 2 = i := by lia
      have he1 : Even (i + 1 + (i + 1)) := ⟨i + 1, rfl⟩
      have he2 : Even (i + i) := ⟨i, rfl⟩
      rw [e2, ite_eq_left he1, ite_eq_left he2, e1, e3]
      rw [ite_eq_left he1, mul_assoc, coeff_sub,
        (by ring : C (1 / r) * X * G = C (1 / r) * (X * G)), coeff_C_mul,
        coeff_X_mul]
      rw [(by lia : i + 1 + (i + 1) = (i + i + 1) + 1), Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
  · have hodd : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
    rw [ite_eq_right hodd, ite_eq_right hodd]
    rcases j with _ | j
    · simp
    · have : ¬ Even (2 * (j + 1) + 1 - 2) := by
        rw [(by lia : 2 * (j + 1) + 1 - 2 = 2 * j + 1)]
        exact Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
      rw [ite_eq_right this]; simp

/-- A normalized polynomial with strictly negative roots gives a good sequence. -/
private lemma good_wH : ∀ (n : ℕ) (H : ℝ[X]), H.natDegree = n → H.Splits →
    (∀ r ∈ H.roots, r < 0) →
    H.eval 0 = 1 → Good (wH H) := by
  intro n
  induction n with
  | zero =>
    intro H hn _ _ h0
    obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hn
    simp only [eval_C] at h0
    subst h0
    rw [map_one, wH_one]
    exact good_w0
  | succ n ih =>
    intro H hn hs hneg h0
    have hH0 : H ≠ 0 := by rintro rfl; simp at h0
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero (hs.roots_ne_zero (by lia))
    have hr0 : r < 0 := hneg r hr
    have hroot : H.IsRoot r := (mem_roots hH0).mp hr
    set H₁ := H /ₘ (X - C r) with hH₁
    have hfac : (X - C r) * H₁ = H := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hH₁0 : H₁ ≠ 0 := by rintro h; rw [h, mul_zero] at hfac; exact hH0 hfac.symm
    have hdeg₁ : H₁.natDegree = n := by
      have := congrArg natDegree hfac
      rw [natDegree_mul (X_sub_C_ne_zero r) hH₁0, natDegree_X_sub_C] at this
      lia
    have hs₁ : H₁.Splits := splits_X_sub_C_mul_iff.mp (hfac ▸ hs)
    have hroots₁ : ∀ x ∈ H₁.roots, x < 0 := by
      intro x hx
      apply hneg
      rw [← hfac, roots_mul (hfac.symm ▸ hH0)]
      exact Multiset.mem_add.mpr (Or.inr hx)
    have h0₁ : H₁.eval 0 = -1 / r := by
      have := congrArg (eval 0) hfac
      rw [eval_mul, h0] at this
      simp only [eval_sub, eval_X, eval_C, zero_sub] at this
      rw [eq_div_iff hr0.ne]
      linarith
    set G := C (-r) * H₁ with hG
    have hGdeg : G.natDegree = n := by rw [hG, natDegree_C_mul (by linarith)]; exact hdeg₁
    have hGs : G.Splits := hs₁.C_mul _
    have hGroots : ∀ x ∈ G.roots, x < 0 := by
      intro x hx
      rw [hG, roots_C_mul _ (by linarith)] at hx
      exact hroots₁ x hx
    have hG0 : G.eval 0 = 1 := by
      rw [hG, eval_mul, eval_C, h0₁]
      calc -r * (-1 / r) = r / r := by ring
        _ = 1 := div_self hr0.ne
    have hgood := ih G hGdeg hGs hGroots hG0
    have hHG : H = G - C (1 / r) * X * G := by
      rw [← hfac, hG]
      have : r ≠ 0 := by linarith
      have hC : C (1 / r) * C (-r) = (-1 : ℝ[X]) := by
        have hscalar : (1 / r : ℝ) * (-r) = -1 := by
          calc
            (1 / r : ℝ) * (-r) = -(r / r) := by ring
            _ = -1 := by rw [div_self this]
        rw [← C_mul, hscalar]
        simp
      have hnegC : C (-r) = -C r := by rw [map_neg]
      have hC' : C (1 / r) * (-C r) = (-1 : ℝ[X]) := by
        rw [← hnegC]
        exact hC
      rw [hnegC]
      linear_combination (X * H₁) * hC'
    set c := Real.sqrt (-1 / r)
    have hc : c ^ 2 = -1 / r := Real.sq_sqrt (by
      apply div_nonneg_of_nonpos (by norm_num) hr0.le)
    have hw : wH H = wstep (wstep (wH G) c) (-c) := by
      funext k
      rw [wstep_wstep, hHG, wH_mul]
      have : ((c : ℂ)) ^ 2 = ((-1 / r : ℝ) : ℂ) := by rw [← Complex.ofReal_pow, hc]
      rw [this]
      push_cast
      ring
    rw [hw]
    exact good_wstep (good_wstep hgood c) (-c)

end RealRooted.Branden

/-!
## Approximating functionals for the stability-functional proof

This is part of a different stability-functional/Laguerre proof of Brändén's
result, found by Aristotle. The cited result is P. Brändén, “Iterated
sequences and the geometry of zeros”, J. reine angew. Math. 658 (2011),
115–131.
-/



/-!
## The Catalan functional is `Good`

We approximate the functional with moments `w (2j) = (-1)^j Cat_j`, `w (2j+1) = 0` by functionals
`wH H_N` where `H_N` are explicit real-rooted polynomials (obtained from Rolle's theorem applied to
`X^(N+1) (X + a)^N`) converging coefficientwise to `∑ y^j / (j! (j+1)!)`.
-/


open Polynomial Finset Filter

namespace RealRooted.Branden

/-- The scaling parameter. -/
private noncomputable def aN (N : ℕ) : ℝ := ((N : ℝ) + 1) ^ 2

private lemma aN_pos (N : ℕ) : 0 < aN N := by unfold aN; positivity

private noncomputable def FN (N : ℕ) : ℝ[X] := X ^ (N + 1) * (X + C (aN N)) ^ N

private noncomputable def gN (N : ℕ) : ℝ[X] :=
  ∑ k ∈ range (N + 1),
    C (((k + 1 + N).descFactorial N : ℝ) * aN N ^ (N - k) * (N.choose k : ℝ)) * X ^ k

private lemma gN_coeff (N k : ℕ) :
    (gN N).coeff k = ((k + 1 + N).descFactorial N : ℝ) * aN N ^ (N - k) * (N.choose k : ℝ) := by
  unfold gN
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simp at h; lia)]; simp

private lemma iterate_derivative_FN (N : ℕ) : derivative^[N] (FN N) = X * gN N := by
  ext m
  rw [coeff_iterate_derivative, FN, coeff_X_pow_mul']
  rcases m with _ | k
  · simp
  · rw [coeff_X_mul, gN_coeff, ite_eq_left (by lia),
      (by lia : k + 1 + N - (N + 1) = k), coeff_X_add_C_pow, nsmul_eq_mul,
      (by rfl : k + 1 + N = k + 1 + N)]
    ring

private lemma card_roots_iterate_derivative (p : ℝ[X]) (k : ℕ) :
    Multiset.card p.roots ≤ Multiset.card (derivative^[k] p).roots + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := card_roots_le_derivative (derivative^[k] p)
    lia

private lemma gN_coeff_zero_pos (N : ℕ) : 0 < (gN N).coeff 0 := by
  rw [gN_coeff]
  have := aN_pos N
  have h : 0 < (0 + 1 + N).descFactorial N := Nat.descFactorial_pos.mpr (by lia)
  exact mul_pos (mul_pos (by exact_mod_cast h) (pow_pos (aN_pos N) _)) (by simp)

private lemma gN_ne_zero (N : ℕ) : gN N ≠ 0 := by
  intro h
  have := gN_coeff_zero_pos N
  rw [h, coeff_zero] at this
  exact lt_irrefl _ this

private lemma gN_natDegree_le (N : ℕ) : (gN N).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [gN_coeff, Nat.choose_eq_zero_of_lt (by exact_mod_cast hk)]
  simp

private lemma gN_splits (N : ℕ) : (gN N).Splits := by
  have hF : (FN N).Splits := (Splits.X_pow _).mul ((Splits.X_add_C _).pow _)
  have hF0 : FN N ≠ 0 := by
    unfold FN
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_add_C_ne_zero _))
  have hFdeg : (FN N).natDegree = N + 1 + N := by
    unfold FN
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_add_C_ne_zero _)),
      natDegree_pow, natDegree_pow, natDegree_X, natDegree_X_add_C]
    ring
  have hcard := card_roots_iterate_derivative (FN N) N
  rw [← hF.natDegree_eq_card_roots, hFdeg, iterate_derivative_FN,
    roots_mul (mul_ne_zero X_ne_zero (gN_ne_zero N)), roots_X, Multiset.card_add,
    Multiset.card_singleton] at hcard
  rw [splits_iff_card_roots]
  have h1 := card_roots' (gN N)
  have h2 := gN_natDegree_le N
  lia

private lemma gN_eval_pos (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 < (gN N).eval x := by
  unfold gN
  rw [eval_finsetSum]
  apply sum_pos'
  · intro k _
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    have := aN_pos N
    positivity
  · refine ⟨0, by simp, ?_⟩
    simp only [eval_C, pow_zero, mul_one]
    rw [← gN_coeff]
    exact gN_coeff_zero_pos N

/-- The normalized approximants. -/
private noncomputable def HN (N : ℕ) : ℝ[X] := C (1 / (gN N).coeff 0) * gN N

private lemma good_wH_HN (N : ℕ) : Good (wH (HN N)) := by
  have hc : 1 / (gN N).coeff 0 ≠ 0 := one_div_ne_zero (gN_coeff_zero_pos N).ne'
  refine good_wH _ (HN N) rfl ((gN_splits N).C_mul _) ?_ ?_
  · intro r hr
    rw [HN, roots_C_mul _ hc] at hr
    by_contra h
    push Not at h
    have := gN_eval_pos N h
    rw [(mem_roots (gN_ne_zero N)).mp hr] at this
    exact lt_irrefl _ this
  · rw [HN, eval_mul, eval_C, ← coeff_zero_eq_eval_zero]
    field_simp [(gN_coeff_zero_pos N).ne']

private lemma descFactorial_div_tendsto (c j : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).descFactorial j : ℝ) /
      ((N : ℝ) + 1) ^ j) atTop (nhds 1) := by
  set P : ℝ[X] := (descPochhammer ℝ j).comp (X + C (c : ℝ))
  set Q : ℝ[X] := (X + C 1) ^ j
  have hPm : P.Monic := (monic_descPochhammer ℝ j).comp (monic_X_add_C _)
    (by rw [natDegree_X_add_C]; norm_num)
  have hQm : Q.Monic := (monic_X_add_C _).pow j
  have hPd : P.natDegree = j := by
    rw [natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]
  have hQd : Q.natDegree = j := by rw [natDegree_pow, natDegree_X_add_C, mul_one]
  have hdeg : P.degree = Q.degree := by
    rw [degree_eq_natDegree hPm.ne_zero, degree_eq_natDegree hQm.ne_zero, hPd, hQd]
  have := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q hdeg).comp
    tendsto_natCast_atTop_atTop
  rw [hPm.leadingCoeff, hQm.leadingCoeff, div_one] at this
  refine this.congr fun N => ?_
  simp only [Function.comp_apply, P, Q, eval_comp, eval_add, eval_X, eval_C, eval_pow]
  rw [(by push_cast; ring : (N : ℝ) + c = ((N + c : ℕ) : ℝ)),
    descPochhammer_eval_eq_descFactorial]

private lemma HN_coeff (N j : ℕ) (h : j ≤ N) :
    (HN N).coeff j = ((N + (j + 1)).descFactorial j : ℝ) / ((N : ℝ) + 1) ^ j *
      (((N + 0).descFactorial j : ℝ) / ((N : ℝ) + 1) ^ j) /
        (j.factorial * (j + 1).factorial) := by
  rw [HN, coeff_C_mul, gN_coeff, gN_coeff]
  have e1 : ((j + 1 + N).descFactorial N : ℝ) * (j + 1).factorial = (N + j + 1).factorial := by
    have := Nat.factorial_mul_descFactorial (by lia : N ≤ j + 1 + N)
    rw [(by lia : j + 1 + N - N = j + 1),
      (by ring : j + 1 + N = N + j + 1)] at this
    rw [(by ring : j + 1 + N = N + j + 1)]
    exact_mod_cast (by rw [mul_comm]; exact this)
  have e2 : ((N + (j + 1)).descFactorial j : ℝ) * (N + 1).factorial = (N + j + 1).factorial := by
    have := Nat.factorial_mul_descFactorial (by lia : j ≤ N + (j + 1))
    rw [(by lia : N + (j + 1) - j = N + 1),
      (by ring : N + (j + 1) = N + j + 1)] at this
    rw [(by ring : N + (j + 1) = N + j + 1)]
    exact_mod_cast (by rw [mul_comm]; exact this)
  have e3 : ((0 + 1 + N).descFactorial N : ℝ) = (N + 1).factorial := by
    have := Nat.factorial_mul_descFactorial (by lia : N ≤ 0 + 1 + N)
    rw [(by lia : 0 + 1 + N - N = 1), (by ring : 0 + 1 + N = N + 1)] at this
    rw [(by ring : 0 + 1 + N = N + 1)]
    simpa using congrArg (fun x : ℕ => (x : ℝ)) this
  have e4 : ((N + 0).descFactorial j : ℝ) = j.factorial * N.choose j := by
    rw [Nat.add_zero, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have e5 : aN N ^ N = aN N ^ (N - j) * ((N : ℝ) + 1) ^ j * ((N : ℝ) + 1) ^ j := by
    rw [mul_assoc, ← mul_pow, ← sq, (by rfl : ((N : ℝ) + 1) ^ 2 = aN N), ← pow_add,
      Nat.sub_add_cancel h]
  rw [e3, e4, Nat.sub_zero, e5, Nat.choose_zero_right]
  have hA := aN_pos N
  have hf1 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
  have hf2 : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
  have hf3 : (j.factorial : ℝ) ≠ 0 := by positivity
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hD : ((N + (j + 1)).descFactorial j : ℝ) = (N + j + 1).factorial / (N + 1).factorial := by
    rw [eq_div_iff hf2, e2]
  have hD' : ((j + 1 + N).descFactorial N : ℝ) = (N + j + 1).factorial / (j + 1).factorial := by
    rw [eq_div_iff hf1, e1]
  rw [hD, hD']
  field_simp
  push_cast
  ring

/-- The Catalan moment sequence used in the limiting functional. -/
private noncomputable def wcat : ℕ → ℂ := fun k =>
  if Even k then (-1) ^ (k / 2) * (((k.factorial : ℝ) /
    ((k / 2).factorial * (k / 2 + 1).factorial) : ℝ) : ℂ) else 0

private lemma tendsto_wH_HN (k : ℕ) : Tendsto (fun N => wH (HN N) k) atTop (nhds (wcat k)) := by
  unfold wH wcat
  split_ifs with hk
  · set j := k / 2
    have hlim : Tendsto (fun N => (HN N).coeff j) atTop
        (nhds (1 * 1 / (j.factorial * (j + 1).factorial))) := by
      refine Tendsto.congr' ?_ (((descFactorial_div_tendsto (j + 1) j).mul
        (descFactorial_div_tendsto 0 j)).div_const _)
      filter_upwards [eventually_ge_atTop j] with N hN
      rw [HN_coeff N j hN]
    have := ((Complex.continuous_ofReal.tendsto _).comp hlim).const_mul
      ((k.factorial : ℂ) * (-1) ^ j)
    refine this.congr' (Eventually.of_forall fun N => ?_) |>.trans ?_
    · simp
    · rw [one_mul]
      refine le_of_eq ?_
      congr 1
      push_cast
      ring
  · exact tendsto_const_nhds

/-- The Catalan moment sequence is good. -/
private theorem good_wcat : Good wcat :=
  good_of_tendsto (fun N => good_wH_HN N) tendsto_wH_HN

end RealRooted.Branden

/-!
## Coefficient identities for the stability-functional proof

This is part of a different stability-functional/Laguerre proof of Brändén's
result, found by Aristotle. The cited result is P. Brändén, “Iterated
sequences and the geometry of zeros”, J. reine angew. Math. 658 (2011),
115–131.
-/



/-!
## Algebraic identities

* `Lam wcat F` equals a combination of three coefficients of `X^(D+2) F(X - 1/X)`.
* The coefficient identity relating that combination to the log-concavity operator.
-/


open Polynomial Finset

namespace RealRooted.Branden

/-- The polynomial encoding `X^(D+2) F(X - X⁻¹)`. -/
private noncomputable def PhiD (D : ℕ) (F : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ range (D + 1), C (F.coeff k) * (X ^ 2 - 1) ^ k * X ^ (D + 2 - k)

/-- The coefficient functional that extracts the Catalan moment functional. -/
private noncomputable def kappa (D : ℕ) (G : ℂ[X]) : ℂ :=
  G.coeff (D + 2) + (G.coeff (D + 4) + G.coeff D) / 2

private lemma coeff_X_sq_sub_one_pow (k n : ℕ) :
    ((X ^ 2 - 1 : ℂ[X]) ^ k).coeff n =
      if 2 ∣ n then (-1) ^ (k - n / 2) * (k.choose (n / 2) : ℂ) else 0 := by
  have : (X ^ 2 - 1 : ℂ[X]) ^ k = expand ℂ 2 ((X + C (-1)) ^ k) := by
    simp only [map_pow, map_add, expand_X, map_neg, map_one]
    ring
  rw [this, coeff_expand (by norm_num)]
  split_ifs
  · rw [coeff_X_add_C_pow]
  · rfl

private lemma choose_identity (j : ℕ) :
    ((2 * j).choose j : ℝ) - ((2 * j).choose (j + 1) : ℝ) =
      ((2 * j).factorial : ℝ) / (j.factorial * (j + 1).factorial) := by
  have h1 : ((2 * j).choose (j + 1) : ℝ) * (j + 1) = ((2 * j).choose j : ℝ) * j := by
    have := Nat.choose_succ_right_eq (2 * j) j
    rw [(by lia : 2 * j - j = j)] at this
    exact_mod_cast this
  have h2 : ((2 * j).choose j : ℝ) * (j.factorial * j.factorial) = (2 * j).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (by lia : j ≤ 2 * j)
    rw [(by lia : 2 * j - j = j)] at this
    rw [← mul_assoc]; exact_mod_cast this
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ, Nat.cast_mul, eq_div_iff (by positivity), ← h2]
  have : ((2 * j).choose (j + 1) : ℝ) = ((2 * j).choose j : ℝ) * j / (j + 1) := by
    rw [eq_div_iff hj, h1]
  rw [this]
  field_simp
  push_cast
  ring

/-- Express a Catalan moment using coefficients of `(X² - 1)^k`. -/
private lemma wcat_eq (k : ℕ) :
    wcat k = ((X ^ 2 - 1 : ℂ[X]) ^ k).coeff k +
      (((X ^ 2 - 1 : ℂ[X]) ^ k).coeff (k + 2) +
        (if 2 ≤ k then ((X ^ 2 - 1 : ℂ[X]) ^ k).coeff (k - 2) else 0)) / 2 := by
  simp only [coeff_X_sq_sub_one_pow]
  unfold wcat
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [ite_eq_left ⟨j, rfl⟩, ite_eq_left ⟨j, by ring⟩, ite_eq_left ⟨j + 1, by ring⟩,
      (by lia : (j + j) / 2 = j), (by lia : (j + j + 2) / 2 = j + 1),
      (by lia : j + j - j = j)]
    rcases j with _ | i
    · simp
    · rw [ite_eq_left (by lia), ite_eq_left ⟨i, by lia⟩,
        (by lia : (i + 1 + (i + 1) - 2) / 2 = i),
        (by lia : i + 1 + (i + 1) - i = i + 2),
        (by lia : i + 1 + (i + 1) - (i + 1 + 1) = i)]
      have hc := choose_identity (i + 1)
      have hsym : (2 * (i + 1)).choose i = (2 * (i + 1)).choose (i + 1 + 1) := by
        rw [← Nat.choose_symm (by lia : i ≤ 2 * (i + 1))]
        congr 1; lia
      rw [(by ring : i + 1 + (i + 1) = 2 * (i + 1)), hsym]
      rw [← hc]
      push_cast
      ring
  · have h1 : ¬ 2 ∣ 2 * j + 1 := by lia
    have h2 : ¬ 2 ∣ 2 * j + 1 + 2 := by lia
    have h3 : ¬ Even (2 * j + 1) := Nat.not_even_iff_odd.mpr ⟨j, rfl⟩
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
    split_ifs with h4 h5
    · exact absurd h5 (by lia)
    · simp
    · simp

/-- Relate the Catalan moment functional to `kappa` and `PhiD`. -/
private lemma Lam_wcat_eq_kappa (F : ℂ[X]) (D : ℕ) (hF : F.natDegree ≤ D) :
    Lam wcat F = kappa D (PhiD D F) := by
  rw [Lam_eq_sum_range wcat F (Nat.lt_succ_of_le hF), kappa, PhiD]
  simp only [finsetSum_coeff, ← sum_add_distrib]
  rw [sum_div, ← sum_add_distrib]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [wcat_eq]
  simp only [mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  rw [ite_eq_left (by lia : D + 2 - k ≤ D + 2),
    ite_eq_left (by lia : D + 2 - k ≤ D + 4),
    (by lia : D + 2 - (D + 2 - k) = k),
    (by lia : D + 4 - (D + 2 - k) = k + 2)]
  by_cases h2 : 2 ≤ k
  · rw [ite_eq_left h2, ite_eq_left (by lia : D + 2 - k ≤ D),
      (by lia : D - (D + 2 - k) = k - 2)]
    ring
  · rw [ite_eq_right h2, ite_eq_right (by lia)]
    ring

/-- Evaluate the encoded substitution polynomial away from zero. -/
private lemma PhiD_eval (D : ℕ) (F : ℂ[X]) (hF : F.natDegree ≤ D) {z : ℂ} (hz : z ≠ 0) :
    (PhiD D F).eval z = z ^ (D + 2) * F.eval (z - z⁻¹) := by
  rw [PhiD, eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hF), mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hk)
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_one]
  rw [(by lia : D + 2 = (D + 2 - k) + k), pow_add,
    (by lia : D + 2 - k + k - k = D + 2 - k)]
  have hz2 : z ^ 2 - 1 = z * (z - z⁻¹) := by rw [mul_sub, mul_inv_cancel₀ hz]; ring
  rw [hz2, mul_pow]
  ring

/-- The scaled coefficient polynomial used in the factorization identity. -/
private noncomputable def Upol (n : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), C (a k * s ^ k) * X ^ k

/-- The reversed scaled coefficient polynomial used in the factorization identity. -/
private noncomputable def Vpol (n : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ[X] :=
  ∑ k ∈ range (n + 1), C (a k * (-s) ^ k) * X ^ (n - k)

/-- Compute coefficients of `Upol n a s * Vpol n a s * X²`. -/
private lemma coeff_UVX2 (n : ℕ) (a : ℕ → ℂ) (s : ℂ) (m : ℕ) :
    (Upol n a s * Vpol n a s * X ^ 2).coeff m =
      ∑ i ∈ range (n + 1), ∑ l ∈ range (n + 1),
        if m = i + (n - l) + 2 then (a i * s ^ i) * (a l * (-s) ^ l) else 0 := by
  have : Upol n a s * Vpol n a s * X ^ 2 = ∑ i ∈ range (n + 1), ∑ l ∈ range (n + 1),
      C ((a i * s ^ i) * (a l * (-s) ^ l)) * X ^ (i + (n - l) + 2) := by
    rw [Upol, Vpol, sum_mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun l _ => ?_
    simp only [map_mul, map_pow, map_neg, pow_add]
    ring
  rw [this, finsetSum_coeff]
  refine sum_congr rfl fun i _ => ?_
  rw [finsetSum_coeff]
  refine sum_congr rfl fun l _ => ?_
  rw [coeff_C_mul_X_pow]

/-- Evaluate `kappa` on the product of the two coefficient polynomials. -/
private lemma kappa_UV (n : ℕ) (a : ℕ → ℂ) (ha : ∀ k, n < k → a k = 0) (s : ℂ) :
    kappa n (Upol n a s * Vpol n a s * X ^ 2) =
      ∑ k ∈ range (n + 1), (a k ^ 2 - (if k = 0 then 0 else a (k - 1)) * a (k + 1)) *
        (-s ^ 2) ^ k := by
  unfold kappa
  simp only [coeff_UVX2]
  have T0 : (∑ i ∈ range (n + 1), ∑ l ∈ range (n + 1),
      if n + 2 = i + (n - l) + 2 then (a i * s ^ i) * (a l * (-s) ^ l) else 0) =
      ∑ i ∈ range (n + 1), a i ^ 2 * (-s ^ 2) ^ i := by
    refine sum_congr rfl fun i hi => ?_
    rw [sum_congr rfl fun l hl => if_congr (by
      simp at hl hi
      lia : n + 2 = i + (n - l) + 2 ↔ l = i) rfl rfl, sum_ite_eq',
      ite_eq_left hi]
    rw [(by ring : -s ^ 2 = s * (-s)), mul_pow]
    ring
  have T4 : (∑ i ∈ range (n + 1), ∑ l ∈ range (n + 1),
      if n + 4 = i + (n - l) + 2 then (a i * s ^ i) * (a l * (-s) ^ l) else 0) =
      ∑ l ∈ range (n + 1), a l * a (l + 2) * (-s ^ 2) ^ l * s ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [sum_congr rfl fun i hi => if_congr (by
      simp at hl hi
      lia : n + 4 = i + (n - l) + 2 ↔ i = l + 2) rfl rfl, sum_ite_eq']
    split_ifs with h
    · rw [(by ring : -s ^ 2 = s * (-s)), mul_pow, pow_add]
      ring
    · rw [ha (l + 2) (by simp at h; lia)]; ring
  have Tm : (∑ i ∈ range (n + 1), ∑ l ∈ range (n + 1),
      if n = i + (n - l) + 2 then (a i * s ^ i) * (a l * (-s) ^ l) else 0) =
      ∑ i ∈ range (n + 1), a i * a (i + 2) * (-s ^ 2) ^ i * s ^ 2 := by
    refine sum_congr rfl fun i hi => ?_
    rw [sum_congr rfl fun l hl => if_congr (by
      simp at hl hi
      lia : n = i + (n - l) + 2 ↔ l = i + 2) rfl rfl, sum_ite_eq']
    split_ifs with h
    · rw [(by ring : -s ^ 2 = s * (-s)), mul_pow, pow_add]
      ring
    · rw [ha (i + 2) (by simp at h; lia)]; ring
  rw [T0, T4, Tm, add_self_div_two]
  simp only [sub_mul, sum_sub_distrib]
  rw [sub_eq_add_neg]
  congr 1
  conv_lhs => rw [sum_range_succ]
  conv_rhs => rw [sum_range_succ']
  rw [ha (n + 2) (by lia)]
  simp only [zero_mul, add_zero, mul_zero, Nat.add_sub_cancel,
    ite_eq_right (Nat.succ_ne_zero _), ite_true]
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [pow_succ]
  ring

end RealRooted.Branden

/-!
## Factorization lemmas for the stability-functional proof

This is part of a different stability-functional/Laguerre proof of Brändén's
result, found by Aristotle. The cited result is P. Brändén, “Iterated
sequences and the geometry of zeros”, J. reine angew. Math. 658 (2011),
115–131.
-/



/-!
## Non-vanishing of the key combination off the negative real axis
-/


open Polynomial Finset

namespace RealRooted.Branden

/-- The linear factors `r² - s² - r s X` over the roots of `p`. -/
private noncomputable def Fpol (p : ℝ[X]) (s : ℂ) : ℂ[X] :=
  (p.roots.map fun r : ℝ => C ((r : ℂ) ^ 2 - s ^ 2) + C (-(r : ℂ) * s) * X).prod

private lemma Fpol_natDegree_le (p : ℝ[X]) (hs : p.Splits) (s : ℂ) :
    (Fpol p s).natDegree ≤ p.natDegree := by
  unfold Fpol
  refine (natDegree_multiset_prod_le _).trans ?_
  rw [Multiset.map_map, hs.natDegree_eq_card_roots]
  have := Multiset.sum_le_card_nsmul
    (p.roots.map (natDegree ∘ fun r : ℝ =>
      C ((r : ℂ) ^ 2 - s ^ 2) + C (-(r : ℂ) * s) * X)) 1
    (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hx
      simp only [Function.comp_apply]
      rw [add_comm]
      exact natDegree_linear_le)
  simpa using this

private lemma eval_map_eq_prod (p : ℝ[X]) (hs : p.Splits) (w : ℂ) :
    (p.map Complex.ofRealHom).eval w =
      (p.leadingCoeff : ℂ) * (p.roots.map fun r : ℝ => w - (r : ℂ)).prod := by
  rw [(hs.map Complex.ofRealHom).eval_eq_prod_roots, hs.roots_map, Multiset.map_map,
    leadingCoeff_map_of_injective Complex.ofRealHom.injective]
  rfl

private lemma Upol_eval (p : ℝ[X]) (s z : ℂ) :
    (Upol p.natDegree (fun k => (p.coeff k : ℂ)) s).eval z =
      (p.map Complex.ofRealHom).eval (s * z) := by
  rw [Upol, eval_finsetSum, eval_eq_sum_range' (n := p.natDegree + 1)]
  · refine sum_congr rfl fun k _ => ?_
    simp [mul_pow, mul_assoc]
  · rw [natDegree_map_eq_of_injective Complex.ofRealHom.injective]; lia

private lemma Vpol_eval (p : ℝ[X]) (s : ℂ) {z : ℂ} (hz : z ≠ 0) :
    (Vpol p.natDegree (fun k => (p.coeff k : ℂ)) s).eval z =
      z ^ p.natDegree * (p.map Complex.ofRealHom).eval (-s / z) := by
  rw [Vpol, eval_finsetSum, eval_eq_sum_range' (n := p.natDegree + 1), mul_sum]
  · refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ p.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hk)
    simp only [eval_mul, eval_C, eval_pow, eval_X, coeff_map, Complex.ofRealHom_eq_coe]
    rw [div_pow, (by lia : p.natDegree = (p.natDegree - k) + k), pow_add,
      (by lia : p.natDegree - k + k - k = p.natDegree - k)]
    field_simp
  · rw [natDegree_map_eq_of_injective Complex.ofRealHom.injective]; lia

private lemma UV_eq_PhiD (p : ℝ[X]) (hs : p.Splits) (s : ℂ) :
    Upol p.natDegree (fun k => (p.coeff k : ℂ)) s *
      Vpol p.natDegree (fun k => (p.coeff k : ℂ)) s *
      X ^ 2 = C ((p.leadingCoeff : ℂ) ^ 2) * PhiD p.natDegree (Fpol p s) := by
  apply eq_of_infinite_eval_eq
  apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℂ))).mono
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  simp only [Set.mem_ofPred_eq, eval_mul, eval_pow, eval_X, eval_C]
  rw [Upol_eval, Vpol_eval p s hz0, PhiD_eval _ _ (Fpol_natDegree_le p hs s) hz0,
    eval_map_eq_prod p hs, eval_map_eq_prod p hs, Fpol, eval_multiset_prod, Multiset.map_map]
  have key : (p.roots.map fun r : ℝ => s * z - (r : ℂ)).prod *
      (p.roots.map fun r : ℝ => -s / z - (r : ℂ)).prod =
      (p.roots.map (eval (z - z⁻¹) ∘ fun r : ℝ =>
        C ((r : ℂ) ^ 2 - s ^ 2) + C (-(r : ℂ) * s) * X)).prod := by
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, eval_add, eval_C, eval_mul, eval_X]
    field_simp
    ring
  rw [← key]
  ring

private lemma factor_ne_zero (r : ℝ) {s : ℂ} (hs : s ≠ 0) :
    C ((r : ℂ) ^ 2 - s ^ 2) + C (-(r : ℂ) * s) * X ≠ 0 := by
  intro h
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, add_zero,
    coeff_zero, coeff_C, coeff_X_one, mul_one, one_ne_zero, ite_false, zero_add, ite_true] at h0 h1
  have hr : (r : ℂ) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact neg_eq_zero.mp h
    · exact absurd h hs
  rw [hr] at h0
  apply hs
  have : s ^ 2 = 0 := by linear_combination -h0
  exact pow_eq_zero_iff (by norm_num) |>.mp this

private lemma root_im_ge {r : ℝ} (hr : r < 0) {s z : ℂ} (hsim : 0 < s.im)
    (hz : ((r : ℂ) ^ 2 - s ^ 2) + (-(r : ℂ) * s) * z = 0) : s.im / (-r) ≤ z.im := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsim; simp at hsim
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne
  have hzeq : z = s / (-(r : ℂ)) - (-(r : ℂ)) / s := by
    field_simp
    linear_combination -hz
  rw [hzeq, Complex.sub_im]
  have h1 : (s / (-(r : ℂ))).im = s.im / (-r) := by
    rw [(by push_cast; ring : (-(r : ℂ)) = ((-r : ℝ) : ℂ)), Complex.div_ofReal_im]
  have h2 : ((-(r : ℂ)) / s).im ≤ 0 := by
    rw [(by push_cast; ring : (-(r : ℂ)) = ((-r : ℝ) : ℂ)), div_eq_mul_inv,
      Complex.im_ofReal_mul, Complex.inv_im]
    have : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs0
    have : 0 ≤ -r := by linarith
    have : 0 ≤ s.im / Complex.normSq s := div_nonneg hsim.le (by linarith)
    rw [neg_div, mul_neg]
    nlinarith
  linarith

private lemma Lam_wcat_Fpol_ne_zero (p : ℝ[X]) (hr : ∀ r ∈ p.roots, r ≤ 0) {s : ℂ}
    (hsim : 0 < s.im) : Lam wcat (Fpol p s) ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsim; simp at hsim
  set M : ℝ := 1 + (p.roots.map fun r => -r).sum
  have hMr : ∀ r ∈ p.roots, -r ≤ M := by
    intro r hrr
    have : -r ≤ (p.roots.map fun r => -r).sum :=
      Multiset.single_le_sum (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx; linarith [hr y hy])
        _ (Multiset.mem_map_of_mem _ hrr)
    linarith
  have hM : 0 < M := by
    have : 0 ≤ (p.roots.map fun r => -r).sum := Multiset.sum_nonneg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx; linarith [hr y hy])
    linarith
  set m := s.im / M
  have hm : 0 < m := div_pos hsim hM
  have hF0 : Fpol p s ≠ 0 := by
    unfold Fpol
    apply Multiset.prod_ne_zero
    intro h
    obtain ⟨r, _, hr0⟩ := Multiset.mem_map.mp h
    exact factor_ne_zero r hs0 hr0
  have hroots : ∀ z, (Fpol p s).IsRoot z → m ≤ z.im := by
    intro z hz
    have := hz.eq_zero
    rw [Fpol, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at this
    obtain ⟨r, hrr, hrz⟩ := Multiset.mem_map.mp this
    simp only [Function.comp_apply, eval_add, eval_C, eval_mul, eval_X] at hrz
    have hrneg : r < 0 := by
      rcases (hr r hrr).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [h] at hrz
        simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, zero_sub, neg_zero, zero_mul, add_zero, neg_eq_zero] at hrz
        exact hs0 (pow_eq_zero_iff (by norm_num) |>.mp hrz)
    refine le_trans ?_ (root_im_ge hrneg hsim hrz)
    exact div_le_div_of_nonneg_left hsim.le (by linarith) (hMr r hrr)
  have hgood := good_wcat m hm.le _ hF0 hroots
  intro h
  rw [h, norm_zero] at hgood
  have : 0 < ‖(Fpol p s).leadingCoeff‖ * m ^ (Fpol p s).natDegree :=
    mul_pos (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hF0)) (pow_pos hm _)
  linarith

private lemma kappa_C_mul (D : ℕ) (c : ℂ) (G : ℂ[X]) : kappa D (C c * G) = c * kappa D G := by
  unfold kappa
  simp only [coeff_C_mul]
  ring

/-- The key stability functional is nonzero off the negative real axis. -/
private theorem key_sum_ne_zero (p : ℝ[X]) (hp0 : p ≠ 0) (hs : p.Splits)
    (hr : ∀ r ∈ p.roots, r ≤ 0)
    {s : ℂ} (hsim : 0 < s.im) :
    ∑ k ∈ range (p.natDegree + 1), (((p.coeff k : ℂ)) ^ 2 -
      (if k = 0 then 0 else (p.coeff (k - 1) : ℂ)) *
        (p.coeff (k + 1) : ℂ)) * (-s ^ 2) ^ k ≠ 0 := by
  rw [← kappa_UV p.natDegree (fun k => (p.coeff k : ℂ))
    (fun k hk => by simp [coeff_eq_zero_of_natDegree_lt hk]) s, UV_eq_PhiD p hs s, kappa_C_mul,
    ← Lam_wcat_eq_kappa _ _ (Fpol_natDegree_le p hs s)]
  refine mul_ne_zero (pow_ne_zero _ ?_) (Lam_wcat_Fpol_ne_zero p hr hsim)
  exact_mod_cast leadingCoeff_ne_zero.mpr hp0

end RealRooted.Branden

/-!
## Brändén's log-concavity transform

This is a different stability-functional/Laguerre proof of Brändén's theorem,
found by Aristotle. The cited result is P. Brändén, “Iterated sequences and the
geometry of zeros”, J. reine angew. Math. 658 (2011), 115–131.
-/


open Polynomial Finset

namespace RealRooted.Branden

/-- The log-concavity operator on coefficient sequences: `a_k² - a_{k-1} a_{k+1}`.
The convention is `a_{-1} = 0`. -/
noncomputable def logConcavityTransform (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree + 1),
    C (p.coeff k ^ 2 - (if k = 0 then 0 else p.coeff (k - 1)) * p.coeff (k + 1)) * X ^ k

private lemma logConcavityTransform_coeff (p : ℝ[X]) (k : ℕ) :
    (logConcavityTransform p).coeff k = if k ≤ p.natDegree then
      p.coeff k ^ 2 - (if k = 0 then 0 else p.coeff (k - 1)) * p.coeff (k + 1) else 0 := by
  unfold logConcavityTransform
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

private lemma logConcavityTransform_eval_map (p : ℝ[X]) (z : ℂ) :
    ((logConcavityTransform p).map Complex.ofRealHom).eval z =
      ∑ k ∈ range (p.natDegree + 1), (((p.coeff k : ℂ)) ^ 2 -
        (if k = 0 then 0 else (p.coeff (k - 1) : ℂ)) * (p.coeff (k + 1) : ℂ)) * z ^ k := by
  unfold logConcavityTransform
  rw [Polynomial.map_sum, eval_finsetSum]
  refine sum_congr rfl fun k _ => ?_
  simp only [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, eval_mul, eval_C, eval_pow,
    eval_X, Complex.ofRealHom_eq_coe]
  split_ifs <;> push_cast <;> ring

private lemma logConcavityTransform_coeff_natDegree (p : ℝ[X]) :
    (logConcavityTransform p).coeff p.natDegree = p.leadingCoeff ^ 2 := by
  rw [logConcavityTransform_coeff, ite_eq_left le_rfl,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), mul_zero, sub_zero]
  rfl

private lemma logConcavityTransform_natDegree (p : ℝ[X]) (hp0 : p ≠ 0) :
    (logConcavityTransform p).natDegree = p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [logConcavityTransform_coeff, ite_eq_right (by exact_mod_cast not_le.mpr hk)]
  · rw [logConcavityTransform_coeff_natDegree]
    exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hp0)

private lemma logConcavityTransform_ne_zero (p : ℝ[X]) (hp0 : p ≠ 0) :
    logConcavityTransform p ≠ 0 := by
  intro h
  have := logConcavityTransform_coeff_natDegree p
  rw [h, coeff_zero] at this
  exact pow_ne_zero 2 (leadingCoeff_ne_zero.mpr hp0) this.symm

/-- Every complex number off `(-∞, 0]` is `-s²` for some `s` in the open upper half-plane. -/
private lemma exists_upper_sqrt (z : ℂ) (hz : ¬ (z.im = 0 ∧ z.re ≤ 0)) :
    ∃ s : ℂ, 0 < s.im ∧ z = -s ^ 2 := by
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_pow_nat_eq (-z) (n := 2) (by norm_num)
  have hz' : z = -s₀ ^ 2 := by rw [hs₀, neg_neg]
  rcases lt_trichotomy s₀.im 0 with h | h | h
  · exact ⟨-s₀, by simpa using h, by rw [hz', neg_sq]⟩
  · exfalso
    apply hz
    rw [hz']
    simp only [sq, Complex.neg_im, Complex.mul_im, h, mul_zero, zero_mul, add_zero, neg_zero,
      Complex.neg_re, Complex.mul_re, sub_zero, true_and, Left.neg_nonpos_iff]
    exact mul_self_nonneg _
  · exact ⟨s₀, h, hz'⟩

private lemma roots_map_logConcavityTransform (p : ℝ[X]) (hp0 : p ≠ 0)
    (hs : p.Splits) (hr : ∀ r ∈ p.roots, r ≤ 0) (z : ℂ)
    (hz : ((logConcavityTransform p).map Complex.ofRealHom).IsRoot z) :
    z.im = 0 ∧ z.re ≤ 0 := by
  by_contra hcon
  obtain ⟨s, hsim, rfl⟩ := exists_upper_sqrt z hcon
  apply key_sum_ne_zero p hp0 hs hr hsim
  rw [← logConcavityTransform_eval_map]
  exact hz

private lemma product_coeff_nonneg (s : Multiset ℝ) (h : ∀ r ∈ s, r ≤ 0) (k : ℕ) :
    0 ≤ ((s.map fun a => X - C a).prod).coeff k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs <;> norm_num
  | cons a t ih =>
    have ha : a ≤ 0 := h a (Multiset.mem_cons_self a t)
    have ih' := fun k => ih (fun r hr => h r (Multiset.mem_cons_of_mem hr)) k
    rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
    rcases k with _ | k
    · rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      exact mul_nonneg (ih' 0) (by linarith)
    · rw [coeff_mul_X_sub_C]
      have := ih' k
      have := ih' (k + 1)
      nlinarith

/-- Brändén (J. reine angew. Math. 658 (2011), "Iterated sequences and the geometry of zeros",
proving a conjecture of Fisk, McNamara–Sagan and Stanley): if `p` has nonnegative coefficients and
only real nonpositive zeros, then so does `logConcavityTransform p`. -/
private theorem logConcavityTransform_splits_and_nonpos (p : ℝ[X]) (hp0 : p ≠ 0)
    (_hnn : ∀ k, 0 ≤ p.coeff k) (hs : p.Splits) (hr : ∀ r ∈ p.roots, r ≤ 0) :
    (logConcavityTransform p).Splits ∧ ∀ r ∈ (logConcavityTransform p).roots, r ≤ 0 := by
  -- The nonnegativity of the coefficients is not needed: real nonpositive roots suffice.
  have hL0 := logConcavityTransform_ne_zero p hp0
  refine ⟨Splits.of_splits_map Complex.ofRealHom (IsAlgClosed.splits _) ?_, ?_⟩
  · intro a ha
    have h1 := (roots_map_logConcavityTransform p hp0 hs hr a
      ((mem_roots (map_ne_zero hL0)).mp ha)).1
    exact ⟨a.re, Complex.ext (by simp) (by simp [h1])⟩
  · intro r hr'
    have hz := ((mem_roots hL0).mp hr').map (f := Complex.ofRealHom)
    simpa using (roots_map_logConcavityTransform p hp0 hs hr _ hz).2

/-- `logConcavityTransform p` keeps nonnegative coefficients under the same hypotheses. -/
private theorem logConcavityTransform_coeff_nonneg (p : ℝ[X]) (_hnn : ∀ k, 0 ≤ p.coeff k)
    (hs : p.Splits) (hr : ∀ r ∈ p.roots, r ≤ 0) (k : ℕ) :
    0 ≤ (logConcavityTransform p).coeff k := by
  by_cases hp0 : p = 0
  · subst hp0
    simp [logConcavityTransform]
  obtain ⟨hLs, hLr⟩ := logConcavityTransform_splits_and_nonpos p hp0 _hnn hs hr
  rw [hLs.eq_prod_roots, coeff_C_mul]
  refine mul_nonneg ?_ (product_coeff_nonneg _ hLr k)
  rw [leadingCoeff, logConcavityTransform_natDegree p hp0, logConcavityTransform_coeff_natDegree]
  exact sq_nonneg _

end RealRooted.Branden

namespace RealRooted.Branden

/-- The coefficient formula for the log-concavity transform. -/
theorem coeff_logConcavityTransform (p : ℝ[X]) (k : ℕ) :
    (logConcavityTransform p).coeff k = if k ≤ p.natDegree then
      p.coeff k ^ 2 - (if k = 0 then 0 else p.coeff (k - 1)) * p.coeff (k + 1) else 0 := by
  exact logConcavityTransform_coeff p k

/-- Nonnegative coefficients of a product of nonpositive real linear factors. -/
theorem coeff_prod_X_sub_C_nonneg (s : Multiset ℝ) (h : ∀ r ∈ s, r ≤ 0) (k : ℕ) :
    0 ≤ ((s.map fun a => X - C a).prod).coeff k := by
  exact product_coeff_nonneg s h k

/-- Brändén's transform preserves the Pólya-frequency polynomial cone. -/
theorem IsPFPolynomial.logConcavityTransform {p : ℝ[X]}
    (hp : IsPFPolynomial p) :
    IsPFPolynomial (RealRooted.Branden.logConcavityTransform p) := by
  by_cases hp0 : p = 0
  · subst hp0
    simpa [RealRooted.Branden.logConcavityTransform] using
      (IsPFPolynomial.zero : IsPFPolynomial (0 : ℝ[X]))
  have hsplits : p.Splits := hp.eq_zero_or_splits.resolve_left hp0
  have hroot := logConcavityTransform_splits_and_nonpos p hp0 hp.hasNonnegCoeffs hsplits
    hp.roots_nonpos
  apply IsPFPolynomial.of_realRooted_nonneg
  · intro k
    exact logConcavityTransform_coeff_nonneg p hp.hasNonnegCoeffs hsplits hp.roots_nonpos k
  · exact hroot.1

end RealRooted.Branden
