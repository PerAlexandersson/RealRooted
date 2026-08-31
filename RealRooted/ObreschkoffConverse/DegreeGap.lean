import RealRooted.AllCombo
import RealRooted.AffineDerivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Obreschkoff converse degree gaps

Analytic constant-shift obstructions and the degree-closeness reduction for
all-real-rooted polynomial pairs.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- If all roots of `p'` are at most `c`, then `p.eval` is strictly increasing
on `[c, +∞)`. This is the analytic core of the degree-gap argument: once the
last critical point is known, any larger real root would force a contradiction. -/
lemma strictMonoOn_eval_Ici_of_derivative_roots_le
    {p : ℝ[X]} {c : ℝ}
    (hp'_ne : p.derivative ≠ 0) (hp'_splits : p.derivative.Splits)
    (hp'_pos : HasPosLeadingCoeff p.derivative)
    (hroots_le : ∀ s ∈ p.derivative.roots, s ≤ c) :
    StrictMonoOn (fun x => p.eval x) (Set.Ici c) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici c) p.continuous.continuousOn ?_
  intro x hx
  have hx' : c < x := by simp_all
  have hlt : ∀ t ∈ p.derivative.roots, t < x := by grind
  have hpos_eval : 0 < p.derivative.eval x :=
    eval_pos_of_all_roots_lt hp'_ne hp'_splits hp'_pos hlt
  simp_all

/-- A root of `p'` always has a root of `p` weakly to its right. We package the
rightmost-root extraction here because it is reused twice in the degree-gap
reduction: first to show a real-rooted polynomial must be nonpositive at its
last critical point, and then again to contradict real-rootedness after a
constant shift. -/
lemma exists_root_ge_of_derivative_root
    {p : ℝ[X]} (hp_splits : p.Splits) (hdeg : 2 ≤ p.natDegree)
    {c : ℝ} (hc : p.derivative.IsRoot c) :
    ∃ r, p.IsRoot r ∧ c ≤ r := by
  obtain ⟨hp_rr, hp'_rr, _, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp_splits hdeg
  have hrs_len : rs.length = p.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hp_rr.2]
  have hrs_ne : rs ≠ [] := by grind
  have hc_mem : c ∈ ss := by
    apply Multiset.mem_coe.mp
    simp_all
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      simp
    simp_all
  · exact listInterlaces_all_le_getLast hrs_ne hrs_sorted hint c hc_mem

/-- Exact degree bookkeeping for iterated derivatives. We use this in the
degree-gap reduction to show that differentiating the smaller polynomial down to
degree `0` still leaves the larger one with degree at least `2`. -/
lemma natDegree_iterate_derivative_eq_sub
    {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) (hk : k ≤ p.natDegree) :
    (derivative^[k] p).natDegree = p.natDegree - k := by
  apply le_antisymm (natDegree_iterate_derivative p k)
  apply le_natDegree_of_ne_zero
  have hcoeff :
      (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    simp_all
  lia

/-- Iterated derivatives stay nonzero as long as we do not differentiate past
the degree. -/
lemma iterate_derivative_ne_zero_of_le_natDegree
    {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) (hk : k ≤ p.natDegree) :
    (derivative^[k] p) ≠ 0 := by
  intro hk0
  have hcoeff :
      (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    simp_all
  simp [hk0] at hcoeff

/-- A positive-leading real-rooted polynomial of degree at least `2` is
nonpositive at its rightmost critical point. The point is chosen as the
rightmost root of `p'`; to the right of it the derivative is strictly
positive, so a positive value there would prevent the real-rooted polynomial
itself from having any root on its right, contradicting interlacing of `p'`
with `p`. -/
lemma exists_rightmost_derivative_root_with_eval_nonpos
    {p : ℝ[X]} (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ c, p.derivative.IsRoot c ∧
      (∀ s ∈ p.derivative.roots, s ≤ c) ∧
      p.eval c ≤ 0 := by
  have hp' : (p.derivative ≠ 0 ∧
    p.derivative.Splits) := (derivative_interlaces hp_splits hdeg).2.1
  have hp'_pos : HasPosLeadingCoeff p.derivative :=
    hp_pos.derivative (by lia)
  have hp'_deg : p.derivative.natDegree = p.natDegree - 1 :=
    p.natDegree_derivative
  obtain ⟨c, hc_root, hc_top⟩ :=
    exists_rightmost_root_of_isRealRooted hp'.1 hp'.2 (by lia)
  have hnonpos : p.eval c ≤ 0 := by
    by_contra hpc
    have hmono :
        StrictMonoOn (fun x => p.eval x) (Set.Ici c) :=
      strictMonoOn_eval_Ici_of_derivative_roots_le hp'.1 hp'.2 hp'_pos hc_top
    obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hp_splits hdeg hc_root
    by_cases hcr : c = r
    · simp_all
    · have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr
      have hlt_eval : p.eval c < p.eval r := hmono (by simp) (by simp_all) hcr_lt
      have : p.eval r = 0 := by simp_all
      linarith
  grind

/-- A positive constant shift destroys real-rootedness once the polynomial has
positive leading coefficient and degree at least `2`. The proof shifts the
polynomial upward past its value at the rightmost critical point; the derivative
is unchanged, so the shifted polynomial would still need a real root on the
right by interlacing, but it is already strictly increasing there. -/
lemma exists_pos_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
    {p : ℝ[X]} (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ t : ℝ, 0 < t ∧ ¬ ((C t + p) ≠ 0 ∧ (C t + p).Splits) := by
  obtain ⟨c, hc_root, hc_top, hpc_nonpos⟩ :=
    exists_rightmost_derivative_root_with_eval_nonpos hp_splits hp_pos hdeg
  let t : ℝ := 1 - p.eval c
  have ht_pos : 0 < t := by grind
  refine ⟨t, ht_pos, ?_⟩
  intro hq
  have hqdeg : 2 ≤ (C t + p).natDegree := by simp_all
  have hq'_rr : ((C t + p).derivative ≠ 0 ∧ (C t + p).derivative.Splits) :=
    (derivative_interlaces hq.2 hqdeg).2.1
  have hmono :
      StrictMonoOn (fun x => (C t + p).eval x) (Set.Ici c) := by
    have hder_eq : (C t + p).derivative = p.derivative := by simp
    refine strictMonoOn_eval_Ici_of_derivative_roots_le hq'_rr.1 hq'_rr.2 ?_ ?_
    · simpa [hder_eq] using hp_pos.derivative (by lia)
    · simp_all
  have hqc_pos : 0 < (C t + p).eval c := by
    have : (C t + p).eval c = 1 := by simp [t]
    linarith
  obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hq.2 hqdeg (by
    simpa using hc_root)
  by_cases hcr : c = r
  · simp_all
  · have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr
    have hlt_eval :
        (C t + p).eval c < (C t + p).eval r := hmono (by simp) (by simp_all) hcr_lt
    have : (C t + p).eval r = 0 := by simp_all
    linarith

/-- For an odd-degree positive-leading real-rooted polynomial, a sufficiently
large positive downward constant shift is not real-rooted. Reflecting across
the vertical axis and negating preserves the positive leading coefficient in
odd degree and converts the downward shift into a positive upward shift. -/
lemma exists_pos_shift_down_not_isRealRooted_of_isRealRooted_of_odd_natDegree
    {p : ℝ[X]} (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) (hodd : Odd p.natDegree) :
    ∃ t : ℝ, 0 < t ∧ ¬ ((p - C t) ≠ 0 ∧ (p - C t).Splits) := by
  let q : ℝ[X] := -(p.comp (-X))
  have hpow : (-1 : ℝ) ^ p.natDegree = -1 := hodd.neg_one_pow
  have hq_splits : q.Splits := by
    dsimp [q]
    exact hp_splits.comp_neg_X.neg
  have hq_pos : HasPosLeadingCoeff q := by simpa [q, HasPosLeadingCoeff, hpow] using hp_pos
  have hq_natDegree : q.natDegree = p.natDegree := by
    dsimp [q]
    rw [Polynomial.natDegree_neg,
      Polynomial.natDegree_comp_eq_of_mul_ne_zero (by simp [hp_pos.ne_zero])]
    simp
  obtain ⟨t, ht_pos, ht_bad⟩ :=
    exists_pos_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
      hq_splits hq_pos (by rw [hq_natDegree]; exact hdeg)
  refine ⟨t, ht_pos, ?_⟩
  intro hdown
  apply ht_bad
  have hcomp_ne : (p - C t).comp (-X) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp [hdown.1]
  have hshift :
      C t + q = -((p - C t).comp (-X)) := by
    dsimp [q]
    rw [Polynomial.sub_comp, Polynomial.C_comp]
    ring
  rw [hshift]
  exact ⟨neg_ne_zero.mpr hcomp_ne, hdown.2.comp_neg_X.neg⟩

/-- A positive downward constant shift destroys real-rootedness for every
positive-leading real-rooted polynomial of degree at least three. -/
lemma exists_pos_shift_down_not_isRealRooted_of_isRealRooted_of_natDegree_ge_three
    {p : ℝ[X]} (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 3 ≤ p.natDegree) :
    ∃ t : ℝ, 0 < t ∧ ¬ ((p - C t) ≠ 0 ∧ (p - C t).Splits) := by
  classical
  by_cases hthree : p.natDegree = 3
  · exact
      exists_pos_shift_down_not_isRealRooted_of_isRealRooted_of_odd_natDegree
        hp_splits hp_pos (by lia) (by norm_num [hthree])
  have hfour : 4 ≤ p.natDegree := by lia
  let t : ℝ :=
    p.derivative.roots.toFinset.sum (fun c => |p.eval c|) + 1
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  refine ⟨t, ht_pos, ?_⟩
  intro hshift
  have hC_deg : (C t : ℝ[X]).natDegree < p.natDegree := by
    simp only [natDegree_C]
    lia
  have hshift_deg : (p - C t).natDegree = p.natDegree :=
    natDegree_sub_eq_left_of_natDegree_lt hC_deg
  have hshift_pos : HasPosLeadingCoeff (p - C t) := by
    unfold HasPosLeadingCoeff at hp_pos ⊢
    rw [leadingCoeff_sub_of_degree_lt (degree_lt_degree hC_deg)]
    exact hp_pos
  have hshift_four : 4 ≤ (p - C t).natDegree := by
    rw [hshift_deg]
    exact hfour
  obtain ⟨c, hc_derivative, hc_nonneg⟩ :=
    exists_derivative_root_eval_nonneg_of_four_le_natDegree
      hshift.2 hshift_pos hshift_four
  have hc_derivative_p : c ∈ p.derivative.roots := by
    simpa only [derivative_sub, derivative_C, sub_zero] using hc_derivative
  have hc_finset : c ∈ p.derivative.roots.toFinset :=
    Multiset.mem_toFinset.mpr hc_derivative_p
  have hc_bound :
      |p.eval c| ≤
        p.derivative.roots.toFinset.sum (fun x => |p.eval x|) :=
    Finset.single_le_sum
      (f := fun x => |p.eval x|) (fun x _ => abs_nonneg _) hc_finset
  have hc_neg : (p - C t).eval c < 0 := by
    rw [eval_sub, eval_C]
    dsimp [t]
    linarith [le_abs_self (p.eval c)]
  exact (not_lt_of_ge hc_nonneg) hc_neg


lemma exists_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
    {p : ℝ[X]} (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ t : ℝ, ¬ ((C t + p) ≠ 0 ∧ (C t + p).Splits) := by
  obtain ⟨t, _, ht⟩ :=
    exists_pos_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
      hp_splits hp_pos hdeg
  grind

/-- A nonzero constant cannot form an `AllComboRealRooted` pair with a
positive-leading degree-`≥ 2` polynomial: a suitable constant shift of the
second polynomial fails to be real-rooted. -/
private theorem not_allComboRealRooted_const_left_of_natDegree_ge_two_of_pos
    {c : ℝ} {p : ℝ[X]}
    (hc : c ≠ 0)
    (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ¬ AllComboRealRooted (C c) p := by
  intro hall
  obtain ⟨t, ht⟩ :=
    exists_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two hp_splits hp_pos hdeg
  have hcombo_t : (C t + p).Splits := by
    have hrewrite : C (t / c) * C c + p = C t + p := by
      calc
        C (t / c) * C c + p = C ((t / c) * c) + p := by simp
        _ = C t + p := by simp_all
    simpa [hrewrite] using (hall (t / c) 1)
  by_cases hzero : C t + p = 0
  · have : p = -C t := by grind
    simp_all
  · simp_all

/-- Sign-normalized version of the constant-vs-degree-`≥ 2` obstruction.

This is the exact lemma used in the degree-closeness theorem: after enough
ordinary derivatives, one polynomial becomes a nonzero constant while the other
still has degree at least `2`, so `AllComboRealRooted` is impossible. -/
private theorem not_allComboRealRooted_const_left_of_natDegree_ge_two
    {c : ℝ} {p : ℝ[X]}
    (hc : c ≠ 0)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hdeg : 2 ≤ p.natDegree) :
    ¬ AllComboRealRooted (C c) p := by
  by_cases hp_pos : 0 < p.leadingCoeff
  · exact
      not_allComboRealRooted_const_left_of_natDegree_ge_two_of_pos
        hc hp_splits hp_pos hdeg
  · intro hall
    have hneg_rr : ((-p) ≠ 0 ∧ (-p).Splits) := by simp_all
    have hneg_pos : HasPosLeadingCoeff (-p) := by
      have hne0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp_ne
      exact hasPosLeadingCoeff_neg (by grind)
    have hall_neg : AllComboRealRooted (C c) (-p) := by
      simpa using
        (allComboRealRooted_C_mul_right (f := C c) (g := p) (c := (-1 : ℝ)) hall)
    exact
      not_allComboRealRooted_const_left_of_natDegree_ge_two_of_pos
        hc hneg_rr.2 hneg_pos (by simp_all) hall_neg

/-- A degree gap of at least `2` is incompatible with `AllComboRealRooted`.

This is the degree-only part of the Obreschkoff converse. It is intentionally
recorded separately because it is a useful first reduction for future agents:
before arguing about root order or orientation, we can already rule out large
degree gaps by differentiating down to the constant-vs-degree-`≥ 2` case. -/
private theorem not_degree_gap_ge_two_of_allComboRealRooted
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hgap : f.natDegree + 2 ≤ g.natDegree) :
    False := by
  let n : ℕ := f.natDegree
  let fN : ℝ[X] := (derivative^[n]) f
  let gN : ℝ[X] := (derivative^[n]) g
  have hallN : AllComboRealRooted fN gN := by
    simpa [n, fN, gN] using allComboRealRooted_iterate_derivative hall n
  have hfN_deg : fN.natDegree = 0 := by
    dsimp [fN, n]
    simpa using natDegree_iterate_derivative_eq_sub hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_ne : fN ≠ 0 := by
    dsimp [fN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_C : fN = C (fN.coeff 0) := eq_C_of_natDegree_eq_zero hfN_deg
  have hfN_coeff_ne : fN.coeff 0 ≠ 0 := by grind
  set cf : ℝ := fN.coeff 0
  have hfN_C' : fN = C cf := by lia
  have hgN_deg : gN.natDegree = g.natDegree - n := by
    dsimp [gN, n]
    exact natDegree_iterate_derivative_eq_sub hg0 (by lia)
  have hgN_deg_ge2 : 2 ≤ gN.natDegree := by lia
  have hgN_ne : gN ≠ 0 := by
    dsimp [gN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hg0 (by lia)
  have hgN_rr : (gN ≠ 0 ∧ gN.Splits) :=
    ⟨hgN_ne, by simpa using hallN 0 1⟩
  exact
    not_allComboRealRooted_const_left_of_natDegree_ge_two
      (c := cf) (p := gN) (by lia) hgN_rr.1 hgN_rr.2 hgN_deg_ge2
      (by lia)

/-- Degree control for the Obreschkoff converse.

The zero-polynomial caveat is essential: `AllComboRealRooted f 0` holds for any
real-rooted `f`, so no degree bound is possible without `f ≠ 0` and `g ≠ 0`.
With that caveat, every all-real-rooted 2-plane is already forced into the
same-degree / differ-by-1 regime before any root-order arguments begin. -/
theorem natDegree_close_of_allComboRealRooted
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  constructor
  · by_contra hfg
    exact
      not_degree_gap_ge_two_of_allComboRealRooted
        (f := g) (g := f) (allComboRealRooted_comm hall) hg0 hf0 (by lia)
  · by_contra hgf
    exact not_degree_gap_ge_two_of_allComboRealRooted hall hf0 hg0 (by lia)

/-- Equivalent trichotomy form of `natDegree_close_of_allComboRealRooted`. -/
theorem natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f.natDegree = g.natDegree ∨
      f.natDegree + 1 = g.natDegree ∨
      g.natDegree + 1 = f.natDegree := by
  rcases natDegree_close_of_allComboRealRooted hall hf0 hg0 with ⟨hfg, hgf⟩
  lia

end RealRooted
