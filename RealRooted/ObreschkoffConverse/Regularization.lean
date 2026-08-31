import RealRooted.AllCombo
import RealRooted.AffineDerivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.ObreschkoffConverse.DegreeGap

/-!
# Obreschkoff regularization

Wronskian regularization, simple-pencil root control, and the common-root
descent infrastructure for the converse to Obreschkoff's theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

def ObreschkoffConverseInternal.wronskianPoly (f g : ℝ[X]) : ℝ[X] :=
  g * f.derivative - f * g.derivative

open ObreschkoffConverseInternal

private lemma wronskian_eval {f g : ℝ[X]} {x : ℝ} :
    (wronskianPoly f g).eval x =
      g.eval x * f.derivative.eval x - f.eval x * g.derivative.eval x := by
  simp [wronskianPoly, sub_eq_add_neg]

private lemma eval_derivative_iterateTDeriv
    (eps : ℝ) (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    (iterateTDeriv eps n p).derivative.eval x =
      (iterateTDeriv eps n p.derivative).eval x := by
  have hcomm :
      (iterateTDeriv eps n p).derivative =
        iterateTDeriv eps n p.derivative := by
    simpa using iterate_derivative_iterateTDeriv eps n 1 p
  lia

private lemma wronskian_iterateTDeriv_eval
    (eps : ℝ) (n : ℕ) (f g : ℝ[X]) (x : ℝ) :
    (wronskianPoly (iterateTDeriv eps n f) (iterateTDeriv eps n g)).eval x =
      (iterateTDeriv eps n g).eval x * (iterateTDeriv eps n f.derivative).eval x -
        (iterateTDeriv eps n f).eval x * (iterateTDeriv eps n g.derivative).eval x := by
  rw [wronskian_eval]
  rw [eval_derivative_iterateTDeriv, eval_derivative_iterateTDeriv]

private lemma continuous_wronskian_iterateTDeriv_eval_joint
    (n : ℕ) (f g : ℝ[X]) :
    Continuous fun z : ℝ × ℝ =>
      (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 := by
  have hf : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n f).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n f
  have hg : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n g).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n g
  have hf' : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n f.derivative).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n f.derivative
  have hg' : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n g.derivative).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n g.derivative
  have hEq :
      (fun z : ℝ × ℝ =>
        (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2) =
      fun z : ℝ × ℝ =>
        (iterateTDeriv z.1 n g).eval z.2 * (iterateTDeriv z.1 n f.derivative).eval z.2 -
          (iterateTDeriv z.1 n f).eval z.2 * (iterateTDeriv z.1 n g.derivative).eval z.2 := by
    funext z
    exact wronskian_iterateTDeriv_eval z.1 n f g z.2
  rw [hEq]
  exact hg.mul hf' |>.sub (hf.mul hg')

private lemma continuousAt_wronskian_iterateTDeriv_eval_joint_zero
    (n : ℕ) (f g : ℝ[X]) (x : ℝ) :
    ContinuousAt
      (fun z : ℝ × ℝ =>
        (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2)
      (0, x) := by
  have hcont :
      ContinuousAt
        (fun z : ℝ × ℝ =>
          (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2)
        (0, x) :=
    (continuous_wronskian_iterateTDeriv_eval_joint n f g).continuousAt
  lia

private lemma exists_delta_wronskian_iterateTDeriv_eval_mul_pos_joint_at_zero
    (n : ℕ) {f g : ℝ[X]} {x : ℝ}
    (hx_eval : (wronskianPoly f g).eval x ≠ 0) :
    ∃ δ > 0, ∀ {z : ℝ × ℝ}, ‖z - (0, x)‖ < δ →
      0 <
        (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 *
          (wronskianPoly f g).eval x := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      (continuousAt_wronskian_iterateTDeriv_eval_joint_zero n f g x)
      (‖(wronskianPoly f g).eval x‖ / 2) (by simp_all)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hclose' :
      ‖(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
          (wronskianPoly f g).eval x‖ <
        ‖(wronskianPoly f g).eval x‖ / 2 := by
    simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose hz
  rcases lt_or_gt_of_ne hx_eval with hx_neg | hx_pos
  · have hneg_iter :
        (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 < 0 := by
      have hneg_norm :
          ‖-(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskianPoly f g).eval x)‖ =
            ‖(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
                (wronskianPoly f g).eval x‖ := by
        rw [sub_eq_add_neg, neg_neg]
        have hEq :
            -(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 +
                (wronskianPoly f g).eval x =
              -((wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
                (wronskianPoly f g).eval x) := by
          ring
        rw [hEq, norm_neg]
      have hclose_neg0 :
          ‖-(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskianPoly f g).eval x)‖ <
            ‖(wronskianPoly f g).eval x‖ / 2 := by
        lia
      have hclose_neg :
          ‖-(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskianPoly f g).eval x)‖ <
            (-(wronskianPoly f g).eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter :
          0 < -(wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 :=
        pos_of_norm_sub_lt_half_of_pos (by simp_all) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter :
        0 < (wronskianPoly (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 :=
      pos_of_norm_sub_lt_half_of_pos hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    simp_all

lemma ObreschkoffConverseInternal.eval_mul_eval_neg_of_interlaces_consecutive_of_no_common
    {f g : ℝ[X]}
    (hgf : Interlaces g f)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
      f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
      g.eval r₁ * g.eval r₂ < 0 := by
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  intro pre r₁ r₂ rest hEq
  have hrs_sort : rs = f.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs_sorted (Multiset.pairwise_sort ..)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq ..).symm)
  have hEq_rs : rs = pre ++ r₁ :: r₂ :: rest := by lia
  have hnonpos :
      g.eval r₁ * g.eval r₂ ≤ 0 :=
    eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted hss_eq hint hEq_rs
  have hr₁_root : f.IsRoot r₁ := by
    apply (mem_roots hf.1).mp
    simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₁ ∈ rs)
  have hr₂_root : f.IsRoot r₂ := by
    apply (mem_roots hf.1).mp
    simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₂ ∈ rs)
  have hg₁_ne : g.eval r₁ ≠ 0 := by simp_all
  have hg₂_ne : g.eval r₂ ≠ 0 := by simp_all
  grind

/-- The right-family pair `(f + g, f + 2g)` stays in the same Obreschkoff plane.

This is a convenient basis change for later converse work: every linear
combination of these two polynomials is still a linear combination of `(f, g)`,
so `AllComboRealRooted` is inherited for free. -/
private lemma allComboRealRooted_right_family_one_two
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (f + g) (f + C (2 : ℝ) * g) := by
  intro α β
  have hrewrite :
      C α * (f + g) + C β * (f + C (2 : ℝ) * g) =
        C (α + β) * f + C (α + 2 * β) * g := by
    grind
  simpa [hrewrite] using hall (α + β) (α + 2 * β)

/-- Safe degree/leading-coefficient packaging for the right-family reroute.

The heuristic "`(f + g, f + 2g)` regularizes to the top degree" is only
reliably true after sign-normalizing so both original leading coefficients are
positive; otherwise the same-degree case can still cancel at the top. This
helper records the version that is actually stable in Lean. -/
lemma right_family_degree_data_of_posLeadingCoeff
    {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    HasPosLeadingCoeff (f + g) ∧
      HasPosLeadingCoeff (f + C (2 : ℝ) * g) ∧
      (f + g).natDegree = g.natDegree ∧
      (f + C (2 : ℝ) * g).natDegree = g.natDegree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 2) (by simp)
  · simpa using
      PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 2) (by simp)

/-- Under the positive-leading and degree-order hypotheses, the stronger
`AllComboRealRooted` assumption implies the positive-combination hypothesis
used by the same-degree converse infrastructure. -/
private lemma posComboRealRooted_of_allComboRealRooted_of_natDegree_le
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  exact ⟨(hasPosLeadingCoeff_pos_combo_of_natDegree_le_right hdeg hf_pos hg_pos hlam hμ).ne_zero,
    hall lam μ⟩
/-- `AllComboRealRooted` is preserved by any linear change of basis in the
`(f, g)`-plane. No invertibility is needed for the forward direction: every
linear combination of the new pair is visibly a linear combination of the old
pair. -/
private lemma allComboRealRooted_linear_change
    {f g p q : ℝ[X]} {a b c d : ℝ}
    (hp : p = C a * f + C b * g)
    (hq : q = C c * f + C d * g)
    (hall : AllComboRealRooted f g) :
    AllComboRealRooted p q := by
  intro α β
  have hrewrite :
      C α * p + C β * q =
        C (α * a + β * c) * f + C (α * b + β * d) * g := by
    grind
  rw [hrewrite]
  exact hall (α * a + β * c) (α * b + β * d)

/-- No-common-roots is preserved by an invertible linear change of basis in the
`(f, g)`-plane. This is the algebraic bridge needed for the "pick a special
combination and a complementary combination" strategy. -/
private lemma no_common_root_linear_change
    {f g p q : ℝ[X]} {a b c d : ℝ}
    (hp : p = C a * f + C b * g)
    (hq : q = C c * f + C d * g)
    (hdet : a * d - b * c ≠ 0)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, p.IsRoot r → ¬ q.IsRoot r := by
  intro r hpr hqr
  have hp_eval : p.eval r = 0 := by simp_all
  have hq_eval : q.eval r = 0 := by simp_all
  rw [hp, eval_add, eval_mul, eval_mul, eval_C, eval_C] at hp_eval
  rw [hq, eval_add, eval_mul, eval_mul, eval_C, eval_C] at hq_eval
  have hdet_eval :
      (a * d - b * c) * f.eval r = 0 := by
    grind
  simp_all

private lemma wronskian_eval_ne_zero_of_eq_zero_or_simple_combo
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg_pos : 0 < max f.natDegree g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} :
    (wronskianPoly f g).eval x ≠ 0 := by
  let p : ℝ[X] := C (g.eval x) * f + C (-f.eval x) * g
  have hp_root : p.IsRoot x := by
    simp [p, Polynomial.IsRoot.def]
    ring
  intro hw
  have hp_der_eval_eq : p.derivative.eval x = (wronskianPoly f g).eval x := by
    simp [p, wronskian_eval]
    ring
  have hp_der_eval : p.derivative.eval x = 0 := by lia
  have hp_der_root : p.derivative.IsRoot x := by simp_all
  rcases hcombo (g.eval x) (-f.eval x) with hp0 | ⟨hp_rr, hp_simple⟩
  · by_cases hgx0 : g.eval x = 0
    · simp_all
    · have hEq1 : C (g.eval x) * f = C (f.eval x) * g := by grind
      have hscalar : f = C (f.eval x / g.eval x) * g := by
        ext n
        have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq1
        grind
      have hfx0 : f.eval x ≠ 0 := by grind
      have hscale_ne : f.eval x / g.eval x ≠ 0 := div_ne_zero hfx0 hgx0
      have hdeg_eq : f.natDegree = g.natDegree := by rw [hscalar, natDegree_C_mul hscale_ne]
      have hg_deg_pos : 0 < g.natDegree := by grind
      obtain ⟨r, hr⟩ :=
        exists_isRoot_of_isRealRooted_of_not_isUnit hg_ne hg_splits
          (not_isUnit_of_natDegree_pos g hg_deg_pos)
      have hfr : f.IsRoot r := by
        have hgr_eval : g.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hr
        have hfr_eval : f.eval r = 0 := by
          rw [hscalar, eval_mul, eval_C]
          simp [hgr_eval]
        simpa [Polynomial.IsRoot.def] using hfr_eval
      grind
  · have hp_ne : p ≠ 0 := hp_rr.1
    have hmult : 1 < p.rootMultiplicity x :=
      (one_lt_rootMultiplicity_iff_isRoot hp_ne).2 ⟨hp_root, hp_der_root⟩
    have hsimple := hp_simple x hp_root
    lia

private lemma hasSimpleRoots_combo_of_wronskian_eval_ne_zero
    {f g : ℝ[X]} {α β : ℝ}
    (hp_ne : (C α * f + C β * g) ≠ 0)
    (hW_ne : ∀ x : ℝ, (wronskianPoly f g).eval x ≠ 0) :
    HasSimpleRoots (C α * f + C β * g) := by
  let p : ℝ[X] := C α * f + C β * g
  intro r hr
  by_contra hmult_ne
  have hmult_pos : 0 < p.rootMultiplicity r :=
    (rootMultiplicity_pos hp_ne).mpr hr
  have hmult_ge2 : 2 ≤ p.rootMultiplicity r := by lia
  have hder_root : p.derivative.IsRoot r :=
    isRoot_derivative_of_rootMultiplicity_ge_two hmult_ge2
  have hp_eval : p.eval r = 0 := by simp_all
  have hp_der_eval : p.derivative.eval r = 0 := by simp_all
  have hp_eval' : α * f.eval r + β * g.eval r = 0 := by simp_all
  have hp_der_eval' : α * f.derivative.eval r + β * g.derivative.eval r = 0 := by
    simpa [p, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C] using hp_der_eval
  have hαβ_ne : α ≠ 0 ∨ β ≠ 0 := by grind
  have hW_zero : (wronskianPoly f g).eval r = 0 := by
    rcases hαβ_ne with hα | hβ
    · have hmul : α * (wronskianPoly f g).eval r = 0 := by
        calc
          α * (wronskianPoly f g).eval r
              = g.eval r * (α * f.derivative.eval r + β * g.derivative.eval r) -
                  g.derivative.eval r * (α * f.eval r + β * g.eval r) := by
                    rw [wronskian_eval]
                    ring
          _ = 0 := by simp_all
      simp_all
    · have hmul : β * (wronskianPoly f g).eval r = 0 := by
        calc
          β * (wronskianPoly f g).eval r
              = f.derivative.eval r * (α * f.eval r + β * g.eval r) -
                  f.eval r * (α * f.derivative.eval r + β * g.derivative.eval r) := by
                    rw [wronskian_eval]
                    ring
          _ = 0 := by simp_all
      simp_all
  simp_all

lemma ObreschkoffConverseInternal.combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hW_ne : ∀ x : ℝ, (wronskianPoly f g).eval x ≠ 0) :
    ∀ α β : ℝ,
      C α * f + C β * g = 0 ∨
        (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
          HasSimpleRoots (C α * f + C β * g)) := by
  intro α β
  by_cases hcombo0 : C α * f + C β * g = 0
  · simp_all
  · exact Or.inr ⟨⟨hcombo0, hall α β⟩,
      hasSimpleRoots_combo_of_wronskian_eval_ne_zero hcombo0 hW_ne⟩

/-- If the Wronskian vanishes at `x`, then inside the same `AllComboRealRooted`
plane we can choose a special basis `(p, q)` such that:
- `p` has a multiple root at `x`,
- `q` does not vanish at `x`,
- the new pair still has no common roots.

This packages the standard "differentiate the special combination at the
Wronskian-zero point" reduction. It is the clean algebraic entry point for the
remaining converse contradiction. -/
lemma ObreschkoffConverseInternal.exists_special_pair_of_wronskian_zero
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ}
    (hw : (wronskianPoly f g).eval x = 0) :
    ∃ p q : ℝ[X],
      p = C (g.eval x) * f + C (-f.eval x) * g ∧
        ((g.eval x = 0 ∧ q = f) ∨ (g.eval x ≠ 0 ∧ q = g)) ∧
        AllComboRealRooted p q ∧
        (∀ r, p.IsRoot r → ¬ q.IsRoot r) ∧
        p.IsRoot x ∧
        p.derivative.IsRoot x ∧
        q.eval x ≠ 0 := by
  let p : ℝ[X] := C (g.eval x) * f + C (-f.eval x) * g
  have hp_root : p.IsRoot x := by
    simp [p, Polynomial.IsRoot.def]
    ring
  have hp_der_eval_eq : p.derivative.eval x = (wronskianPoly f g).eval x := by
    simp [p, wronskian_eval]
    ring
  have hp_der_root : p.derivative.IsRoot x := by simp_all
  by_cases hgx0 : g.eval x = 0
  · have hfx_ne : f.eval x ≠ 0 := fun hfx0 => by simp_all
    refine ⟨p, f, rfl, Or.inl ⟨hgx0, rfl⟩, ?_, ?_, hp_root, hp_der_root, hfx_ne⟩
    · exact
        allComboRealRooted_linear_change
          (p := p) (q := f)
          (a := g.eval x) (b := -f.eval x) (c := 1) (d := 0)
          (by lia) (by simp)
          hall
    · exact
        no_common_root_linear_change
          (p := p) (q := f)
          (a := g.eval x) (b := -f.eval x) (c := 1) (d := 0)
          (by lia) (by simp)
          (by simp_all)
          hno
  · refine ⟨p, g, rfl, Or.inr ⟨hgx0, rfl⟩, ?_, ?_, hp_root, hp_der_root, hgx0⟩
    · exact
        allComboRealRooted_linear_change
          (p := p) (q := g)
          (a := g.eval x) (b := -f.eval x) (c := 0) (d := 1)
          (by lia) (by simp)
          hall
    · exact
        no_common_root_linear_change
          (p := p) (q := g)
          (a := g.eval x) (b := -f.eval x) (c := 0) (d := 1)
          (by lia) (by simp)
          (by simp_all)
          hno

private lemma eval_derivative_ne_zero_of_hasSimpleRoots
    {p : ℝ[X]} (_hp0 : p ≠ 0) (hsimple : HasSimpleRoots p)
    {r : ℝ} (hr : p.IsRoot r) :
    p.derivative.eval r ≠ 0 :=
  hsimple.eval_derivative_ne_zero hr

/-- Local double-root obstruction in the positive-sign case.

If every linear combination of `p` and `q` is real-rooted, `p` has an exact
double root at `x`, and the second-derivative/product sign at `x` is positive,
then a sufficiently small perturbation `p + β q` violates the standard
non-root second-derivative inequality. This is the clean local contradiction
used in the last step of the Obreschkoff converse. -/
lemma ObreschkoffConverseInternal.false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
    {p q : ℝ[X]} {x : ℝ}
    (hall : AllComboRealRooted p q)
    (hp_mult : p.rootMultiplicity x = 2)
    (hq_eval_ne : q.eval x ≠ 0)
    (hprod_pos : 0 < p.derivative.derivative.eval x * q.eval x) :
    False := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hp_mult
  have hp_root : p.IsRoot x :=
    (rootMultiplicity_pos hp0).mp (by lia)
  have hp_der_root : p.derivative.IsRoot x :=
    isRoot_derivative_of_rootMultiplicity_ge_two (by lia)
  have hp_eval0 : p.eval x = 0 := by simp_all
  have hp_der_eval0 : p.derivative.eval x = 0 := by simp_all
  have hp_rr : p.Splits := (hall.isRealRooted_left hp0).2
  let pp : ℝ := p.derivative.derivative.eval x
  let qx : ℝ := q.eval x
  let qp : ℝ := q.derivative.eval x
  let qq : ℝ := q.derivative.derivative.eval x
  have hpp_ne : pp ≠ 0 := by
    have hprod_ne : p.derivative.derivative.eval x * q.eval x ≠ 0 := ne_of_gt hprod_pos
    grind
  have hqx_ne : qx ≠ 0 := by lia
  let A : ℝ := pp * qx
  let B : ℝ := qp ^ 2 - qq * qx
  let δ₁ : ℝ := A / (2 * (|B| + 1))
  let δ₂ : ℝ := |pp| / (2 * (|qq| + 1))
  let β : ℝ := min δ₁ δ₂
  have hA_pos : 0 < A := by lia
  have hβ_pos : 0 < β := by
    dsimp [β, δ₁, δ₂, A, B]
    positivity
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hβ_le_δ₁ : β ≤ δ₁ := min_le_left _ _
  have hβ_le_δ₂ : β ≤ δ₂ := min_le_right _ _
  have hsecond_small : |β * qq| ≤ |pp| / 2 := by
    calc
      |β * qq| = β * |qq| := by rw [abs_mul, abs_of_nonneg (le_of_lt hβ_pos)]
      _ ≤ β * (|qq| + 1) := by simp_all
      _ ≤ δ₂ * (|qq| + 1) := by gcongr
      _ = |pp| / 2 := by grind
  have hcombo_der2_ne :
      (p.derivative.derivative.eval x + β * q.derivative.derivative.eval x) ≠ 0 := by
    grind
  have hcombo_nonzero :
      C 1 * p + C β * q ≠ 0 := by
    intro hzero
    have heval := congrArg (fun r : ℝ[X] => r.eval x) hzero
    have heval0 : p.eval x + β * q.eval x = 0 := by simpa using heval
    simp_all
  have hcombo_rr : (C 1 * p + C β * q).Splits := hall 1 β
  have hcombo_eval_ne :
      (C 1 * p + C β * q).eval x ≠ 0 := by
    simp_all
  have hcombo_deg_ge2 : 2 ≤ (C 1 * p + C β * q).natDegree := by
    by_contra hlt
    have hdeg_lt2 : (C 1 * p + C β * q).natDegree < 2 := by lia
    have hder2_zero : (derivative^[2]) (C 1 * p + C β * q) = 0 :=
      iterate_derivative_eq_zero hdeg_lt2
    have hder2_eval_zero :
        (C 1 * p + C β * q).derivative.derivative.eval x = 0 := by
      simp_all
    have : p.derivative.derivative.eval x + β * q.derivative.derivative.eval x = 0 := by
      simpa using hder2_eval_zero
    lia
  have hineq_raw :=
    deriv2_mul_lt_deriv_sq_at_non_root hcombo_rr (by lia) hcombo_eval_ne
  have hineq : A < β * B := by
    dsimp [A, B, pp, qx, qp, qq]
    have hineq' := hineq_raw
    simp [hp_eval0, hp_der_eval0] at hineq'
    nlinarith [hβ_pos]
  have hβB_lt : β * |B| < A := by
    calc
      β * |B| ≤ β * (|B| + 1) := by simp_all
      _ ≤ δ₁ * (|B| + 1) := by gcongr
      _ = A / 2 := by grind
      _ < A := by simp_all
  have hineq_le : β * B ≤ β * |B| := by
    have hB_le : B ≤ |B| := le_abs_self B
    simp_all
  grind

/-- Local double-root obstruction without a sign assumption. We flip the
companion polynomial if necessary so the positive-branch lemma applies. -/
lemma ObreschkoffConverseInternal.false_of_allComboRealRooted_of_double_root_and_eval_ne
    {p q : ℝ[X]} {x : ℝ}
    (hall : AllComboRealRooted p q)
    (hp_mult : p.rootMultiplicity x = 2)
    (hq_eval_ne : q.eval x ≠ 0) :
    False := by
  by_cases hprod_pos : 0 < p.derivative.derivative.eval x * q.eval x
  · exact
      false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
        hall hp_mult hq_eval_ne hprod_pos
  · have hpp_ne :
        p.derivative.derivative.eval x ≠ 0 :=
      eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
        (by
          intro hp0
          simp [hp0] at hp_mult)
        hp_mult
    have hprod_ne : p.derivative.derivative.eval x * q.eval x ≠ 0 :=
      mul_ne_zero hpp_ne hq_eval_ne
    have hprod_neg : p.derivative.derivative.eval x * q.eval x < 0 := by grind
    have hneg_pos : 0 < p.derivative.derivative.eval x * (-q).eval x := by simp_all
    have hall_neg : AllComboRealRooted p (-q) := by
      simpa using (allComboRealRooted_C_mul_right (f := p) (g := q) (c := (-1 : ℝ)) hall)
    have hq_neg_eval_ne : (-q).eval x ≠ 0 := by simp_all
    exact
      false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
        hall_neg hp_mult hq_neg_eval_ne hneg_pos

lemma ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_pos : 0 < f.natDegree)
    {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hlin : C α * f + C β * g = 0) :
    False := by
  have hEq : C α * f = C (-β) * g := by grind
  have hscalar : f = C ((-β) / α) * g := by
    ext n
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq
    grind
  have hscale_ne : (-β) / α ≠ 0 := div_ne_zero (neg_ne_zero.mpr hβ) hα
  obtain ⟨r, hr⟩ :=
    exists_isRoot_of_isRealRooted_of_not_isUnit hf_ne hf_splits
      (not_isUnit_of_natDegree_pos f hf_deg_pos)
  simp_all

private lemma no_common_root_iterateTDeriv_of_allComboRealRooted
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    {eps : ℝ} (heps : 0 < eps)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    let n := max f.natDegree g.natDegree
    ∀ r, (iterateTDeriv eps n f).IsRoot r → ¬ (iterateTDeriv eps n g).IsRoot r := by
  dsimp
  intro r hfr hgr
  obtain ⟨_, hf', hg', hf_simple, hg_simple, _⟩ :=
    simple_pair_of_allComboRealRooted_iterateTDeriv hf₀ hg₀ hf hg hall hdeg heps
  have hcombo :=
    allComboRealRooted_eq_zero_or_isRealRooted_and_hasSimpleRoots_iterateTDeriv hall heps
  let α : ℝ := (iterateTDeriv eps (max f.natDegree g.natDegree) g).derivative.eval r
  let β : ℝ := -((iterateTDeriv eps (max f.natDegree g.natDegree) f).derivative.eval r)
  have hα_ne : α ≠ 0 :=
    eval_derivative_ne_zero_of_hasSimpleRoots hg'.1 hg_simple hgr
  have hβ_ne : β ≠ 0 :=
    neg_ne_zero.mpr <|
      eval_derivative_ne_zero_of_hasSimpleRoots hf'.1 hf_simple hfr
  have hp_root :
      (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
        C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).IsRoot r := by
    simp_all
  have hp_der_root :
      (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
        C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).derivative.IsRoot r := by
    simp [Polynomial.IsRoot.def, α, β]
    ring
  by_cases hp0 :
      C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
        C β * iterateTDeriv eps (max f.natDegree g.natDegree) g = 0
  · have hlin :
        C α * f + C β * g = 0 := by
        have hiter_eq :
            iterateTDeriv eps (max f.natDegree g.natDegree) (C α * f + C β * g) =
              iterateTDeriv eps (max f.natDegree g.natDegree) 0 := by
          simpa [iterateTDeriv_linear_combo, iterateTDeriv_zero_poly] using hp0
        exact (iterateTDeriv_injective eps (max f.natDegree g.natDegree)) hiter_eq
    have hdeg_iter_pos : 0 < (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree := by
      have hr_mem :
          r ∈ (iterateTDeriv eps (max f.natDegree g.natDegree) f).roots :=
        (mem_roots hf'.1).2 hfr
      have hcard :
          0 < (iterateTDeriv eps (max f.natDegree g.natDegree) f).roots.card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨r, hr_mem⟩
      rw [card_roots_of_splits hf'.2] at hcard
      lia
    have hf_deg_pos : 0 < f.natDegree := by simp_all
    exact ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
      hf₀ hf hno hf_deg_pos hα_ne hβ_ne hlin
  · have hp_simple :=
      (hcombo α β).2 hp0
    have hmult :
        1 <
          (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
            C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).rootMultiplicity r :=
      (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hp_root, hp_der_root⟩
    rw [hp_simple r hp_root] at hmult
    lia

private lemma derivative_sign_at_consecutive_simple_roots
    {f : ℝ[X]} (hf_ne : f ≠ 0) (hsimple : HasSimpleRoots f)
    {r₁ r₂ : ℝ} (hr₁ : f.IsRoot r₁) (hr₂ : f.IsRoot r₂)
    (hlt : r₁ < r₂)
    (hno_between : ∀ r ∈ f.roots, ¬ (r₁ < r ∧ r < r₂)) :
    f.derivative.eval r₁ * f.derivative.eval r₂ < 0 := by
  have hnonpos :=
    derivative_sign_at_consecutive_roots hr₁ hr₂ hlt hno_between hf_ne
  have hder₁_ne : f.derivative.eval r₁ ≠ 0 :=
    eval_derivative_ne_zero_of_hasSimpleRoots hf_ne hsimple hr₁
  have hder₂_ne : f.derivative.eval r₂ ≠ 0 :=
    eval_derivative_ne_zero_of_hasSimpleRoots hf_ne hsimple hr₂
  exact lt_of_le_of_ne hnonpos (mul_ne_zero hder₁_ne hder₂_ne)

private lemma wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg_pos : 0 < max f.natDegree g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x y : ℝ} (hxy : x ≤ y) :
    0 < (wronskianPoly f g).eval x * (wronskianPoly f g).eval y := by
  by_contra hnonpos
  obtain ⟨z, _, _, hz_root⟩ :=
    exists_isRoot_between_of_eval_mul_nonpos hxy (not_lt.mp hnonpos)
  have hz_eval0 : (wronskianPoly f g).eval z = 0 := by simp_all
  exact
    (wronskian_eval_ne_zero_of_eq_zero_or_simple_combo
      hf_ne hg_ne hg_splits hcombo hdeg_pos hno (x := z)) hz_eval0

private lemma hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_left
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g))) :
    HasSimpleRoots f := by
  rcases hcombo 1 0 with hzero | ⟨_, hsimple⟩ <;> simp_all

private lemma hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_right
    {f g : ℝ[X]}
    (hg_ne : g ≠ 0)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g))) :
    HasSimpleRoots g := by
  rcases hcombo 0 1 with hzero | ⟨_, hsimple⟩ <;> simp_all

private theorem prec_or_revPrec_of_eq_zero_or_simple_combo_sameDegree
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg : g.natDegree = f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hf_simple :
      HasSimpleRoots f :=
    hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_left hf_ne hcombo
  have hg_simple :
      HasSimpleRoots g :=
    hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_right hg_ne hcombo
  by_cases hdeg0 : f.natDegree = 0
  · have hgdeg0 : g.natDegree = 0 := by lia
    have hroots_f : f.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hf_splits, hdeg0]
    have hroots_g : g.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hg_splits, hgdeg0]
    left
    refine
      ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, [], [], by simp, by simp,
        ?_, ?_, ?_⟩
    · simp [hroots_f]
    · simp [hroots_g]
    · exact Or.inr ⟨by lia, by simp [ListAlternates]⟩
  by_cases hdeg1 : f.natDegree = 1
  · exact PosComboRealRooted.prec_or_revPrec_of_same_degree_one hdeg hdeg1
  have hdeg_ge2 : 2 ≤ f.natDegree := by lia
  have hgdeg_ge2 : 2 ≤ g.natDegree := by lia
  have hW_ne x : (wronskianPoly f g).eval x ≠ 0 :=
    wronskian_eval_ne_zero_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by grind) hno (x := x)
  have hW_prod {x y : ℝ} :
      x ≤ y → 0 < (wronskianPoly f g).eval x * (wronskianPoly f g).eval y :=
    wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by grind) hno
  have hf'_pos : HasPosLeadingCoeff f.derivative :=
    hf_pos.derivative (by lia)
  have hg'_pos :
      HasPosLeadingCoeff g.derivative :=
    hg_pos.derivative (by lia)
  by_cases hWneg0 : (wronskianPoly f g).eval 0 < 0
  · have hWneg : ∀ x : ℝ, (wronskianPoly f g).eval x < 0 := by
      intro x
      by_cases hx : x ≤ 0
      · have hprod := hW_prod hx
        nlinarith
      · have hx' : 0 ≤ x := le_of_not_ge hx
        have hprod := hW_prod hx'
        nlinarith
    have hder : Interlaces f.derivative f := derivative_interlaces hf_splits hdeg_ge2
    have hroot_sign :
        ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0 := by
      intro r hr
      have hf_eval : f.eval r = 0 := by simp_all
      simpa [wronskian_eval, hf_eval] using hWneg r
    left
    exact prec_of_interlaces_eval_mul_neg_same hder hf'_pos hg_pos hdeg hroot_sign
  · have hWpos0 : 0 < (wronskianPoly f g).eval 0 := by grind
    have hWpos : ∀ x : ℝ, 0 < (wronskianPoly f g).eval x := by
      intro x
      by_cases hx : x ≤ 0
      · have hprod := hW_prod hx
        nlinarith
      · have hx' : 0 ≤ x := le_of_not_ge hx
        have hprod := hW_prod hx'
        nlinarith
    have hder : Interlaces g.derivative g := derivative_interlaces hg_splits hgdeg_ge2
    have hroot_sign :
        ∀ r, g.IsRoot r → f.eval r * g.derivative.eval r < 0 := by
      intro r hr
      have hg_eval : g.eval r = 0 := by simp_all
      have hw : 0 < -(f.eval r * g.derivative.eval r) := by
        simpa [wronskian_eval, hg_eval] using hWpos r
      nlinarith
    right
    exact prec_of_interlaces_eval_mul_neg_same hder hg'_pos hf_pos hdeg.symm hroot_sign

private lemma wronskian_coeff_top_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskianPoly f g).coeff (2 * f.natDegree) = -(f.leadingCoeff * g.leadingCoeff) := by
  have hf'_deg : f.derivative.natDegree = f.natDegree - 1 :=
    f.natDegree_derivative
  have hg'_deg : g.derivative.natDegree = g.natDegree - 1 :=
    g.natDegree_derivative
  have hf'_lc : f.derivative.leadingCoeff = (f.natDegree : ℝ) * f.leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [hf'_deg, coeff_derivative, Nat.sub_add_cancel hf_deg_pos, coeff_natDegree]
    have hnat : (↑(f.natDegree - 1) : ℝ) + 1 = f.natDegree := by simp_all
    grind
  have hg'_lc : g.derivative.leadingCoeff = (g.natDegree : ℝ) * g.leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [hg'_deg, coeff_derivative, Nat.sub_add_cancel (by lia), coeff_natDegree]
    have hnat : (↑(g.natDegree - 1) : ℝ) + 1 = g.natDegree := by simp_all
    grind
  have hcoeff_gf' :
      (g * f.derivative).coeff (2 * f.natDegree) = g.leadingCoeff * f.derivative.leadingCoeff := by
    have htop : g.natDegree + f.derivative.natDegree = 2 * f.natDegree := by grind
    rw [← htop]
    exact coeff_mul_degree_add_degree g f.derivative
  have hcoeff_fg' :
      (f * g.derivative).coeff (2 * f.natDegree) = f.leadingCoeff * g.derivative.leadingCoeff := by
    have htop : f.natDegree + g.derivative.natDegree = 2 * f.natDegree := by grind
    rw [← htop]
    exact coeff_mul_degree_add_degree f g.derivative
  have hdegR : (g.natDegree : ℝ) = f.natDegree + 1 := by simp_all
  unfold wronskianPoly
  rw [coeff_sub, hcoeff_gf', hcoeff_fg', hf'_lc, hg'_lc, hdegR]
  grind

private lemma wronskian_natDegree_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskianPoly f g).natDegree = 2 * f.natDegree := by
  have hcoeff_top := wronskian_coeff_top_succ (f := f) (g := g) hdeg hf_deg_pos
  have hcoeff_top_ne : (wronskianPoly f g).coeff (2 * f.natDegree) ≠ 0 := by
    rw [hcoeff_top, neg_ne_zero]
    exact mul_ne_zero (ne_of_gt hf_pos) (ne_of_gt hg_pos)
  have hgf'_le : (g * f.derivative).natDegree ≤ 2 * f.natDegree := by
    calc
      (g * f.derivative).natDegree ≤ g.natDegree + f.derivative.natDegree := natDegree_mul_le
      _ = 2 * f.natDegree := by
        rw [f.natDegree_derivative, hdeg]
        lia
  have hfg'_le : (f * g.derivative).natDegree ≤ 2 * f.natDegree := by
    calc
      (f * g.derivative).natDegree ≤ f.natDegree + g.derivative.natDegree := natDegree_mul_le
      _ = 2 * f.natDegree := by
        rw [g.natDegree_derivative, hdeg]
        lia
  have hW_le : (wronskianPoly f g).natDegree ≤ 2 * f.natDegree := by
    unfold wronskianPoly
    calc
      (g * f.derivative - f * g.derivative).natDegree
          ≤ max (g * f.derivative).natDegree (f * g.derivative).natDegree := natDegree_sub_le _ _
      _ ≤ 2 * f.natDegree := max_le hgf'_le hfg'_le
  exact natDegree_eq_of_le_of_coeff_ne_zero hW_le hcoeff_top_ne

private lemma leadingCoeff_wronskian_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskianPoly f g).leadingCoeff = -(f.leadingCoeff * g.leadingCoeff) := by
  unfold Polynomial.leadingCoeff
  rw [wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos,
    wronskian_coeff_top_succ hdeg hf_deg_pos]
  simp

private theorem prec_of_eq_zero_or_simple_combo_succDegree
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g := by
  by_cases hdeg0 : f.natDegree = 0
  · have hgdeg1 : g.natDegree = 1 := by lia
    exact prec_degree_zero_right_of_degree_one hf_ne hf_splits hg_ne hg_splits hdeg0 hgdeg1
  have hf_deg_pos : 1 ≤ f.natDegree := by lia
  have hW_ne x : (wronskianPoly f g).eval x ≠ 0 :=
    wronskian_eval_ne_zero_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by simp_all) hno
  have hW_prod {x y : ℝ} :
      x ≤ y → 0 < (wronskianPoly f g).eval x * (wronskianPoly f g).eval y :=
    wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by simp_all) hno
  have hq_pos : HasPosLeadingCoeff (-wronskianPoly f g) := by
    refine hasPosLeadingCoeff_neg ?_
    rw [leadingCoeff_wronskian_succ hdeg hf_pos hg_pos hf_deg_pos]
    nlinarith [mul_pos hf_pos hg_pos]
  have hq_deg_pos : 0 < (-wronskianPoly f g).degree := by
    have hnat : 0 < (-wronskianPoly f g).natDegree := by
      rw [natDegree_neg, wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos]
      lia
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hq_even : Even (-wronskianPoly f g).natDegree := by
    rw [natDegree_neg, wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos]
    simp
  have ht : Filter.Tendsto (fun x => (-wronskianPoly f g).eval x) Filter.atBot Filter.atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hq_pos hq_deg_pos hq_even
  have hq_event : ∀ᶠ x : ℝ in Filter.atBot, 0 < (-wronskianPoly f g).eval x :=
    ht.eventually (Filter.Ioi_mem_atTop 0)
  obtain ⟨x₀, hx₀⟩ := hq_event.exists
  have hWneg₀ : (wronskianPoly f g).eval x₀ < 0 := by simp_all
  have hWneg : ∀ x : ℝ, (wronskianPoly f g).eval x < 0 := by
    intro x
    by_cases hxx₀ : x ≤ x₀
    · have hprod := hW_prod hxx₀
      nlinarith
    · have hx₀x : x₀ ≤ x := le_of_not_ge hxx₀
      have hprod := hW_prod hx₀x
      nlinarith
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_ne hf_splits hf_pos hf_deg_pos
  have hroot_sign :
      ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by simp_all
    simpa [wronskian_eval, hf_eval] using hWneg r
  exact prec_of_interlaces_eval_mul_neg_succ hder hf'_pos hg_pos hdeg hroot_sign

/-- Handoff helper for the Obreschkoff converse.

Once we know that every nonzero linear combination of `f` and `g` is
real-rooted with simple roots, the remaining proof is only bookkeeping:

1. normalize leading-coefficient signs so that the Wronskian lemmas can use the
   existing positive-leading-coefficient API;
2. dispatch to the same-degree / succ-degree simple-pair theorem above; and
3. scale back to the original pair.

This isolates the still-missing bridge in `prec_of_allComboRealRooted`:
producing the `hcombo` hypothesis for the *original* pair from
`AllComboRealRooted` plus the no-common-roots assumption. -/
theorem ObreschkoffConverseInternal.prec_of_eq_zero_or_simple_combo_of_no_common
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf_ne
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg_ne
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by grind
  have hsg_ne : sg ≠ 0 := by grind
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hpos
    · lia
    · grind
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hpos
    · lia
    · grind
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hf₀ : (f₀ ≠ 0 ∧ f₀.Splits) := isRealRooted_C_mul hf_ne hf_splits hsf_ne
  have hg₀ : (g₀ ≠ 0 ∧ g₀.Splits) := isRealRooted_C_mul hg_ne hg_splits hsg_ne
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
  have hcombo₀ :
      ∀ α β : ℝ,
        C α * f₀ + C β * g₀ = 0 ∨
          (((C α * f₀ + C β * g₀) ≠ 0 ∧ (C α * f₀ + C β * g₀).Splits) ∧
            HasSimpleRoots (C α * f₀ + C β * g₀)) := by
    intro α β
    simpa [f₀, g₀, C_mul, mul_assoc, mul_left_comm, mul_comm] using
      hcombo (α * sf) (β * sg)
  have hdeg₀ :
      f₀.natDegree + 1 = g₀.natDegree ∨ f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hno₀ : ∀ r, f₀.IsRoot r → ¬ g₀.IsRoot r := by
    intro r hrf₀ hrg₀
    have hrf : f.IsRoot r := by
      have hrf₀_eval : (C sf * f).eval r = 0 := by
        simpa [f₀, Polynomial.IsRoot.def] using hrf₀
      simp_all
    have hrg : g.IsRoot r := by
      have hrg₀_eval : (C sg * g).eval r = 0 := by
        simpa [g₀, Polynomial.IsRoot.def] using hrg₀
      simp_all
    simp_all
  have hprec₀ : Prec f₀ g₀ ∨ Prec g₀ f₀ := by
    rcases hdeg₀ with hsucc | hsame
    · left
      exact
        prec_of_eq_zero_or_simple_combo_succDegree
          hf₀.1 hf₀.2 hg₀.1 hg₀.2 hcombo₀ hsucc.symm hf₀_pos hg₀_pos hno₀
    · exact
        prec_or_revPrec_of_eq_zero_or_simple_combo_sameDegree
          hf₀.1 hf₀.2 hg₀.1 hg₀.2 hcombo₀ hsame.symm hf₀_pos hg₀_pos hno₀
  have hsf_inv_ne : sf⁻¹ ≠ 0 := inv_ne_zero hsf_ne
  have hsg_inv_ne : sg⁻¹ ≠ 0 := inv_ne_zero hsg_ne
  have hf_scale : C sf⁻¹ * f₀ = f := by grind
  have hg_scale : C sg⁻¹ * g₀ = g := by grind
  rcases hprec₀ with hfg₀ | hgf₀
  · have hscaled : Prec (C sf⁻¹ * f₀) (C sg⁻¹ * g₀) :=
      prec_C_mul_right (prec_C_mul_left hfg₀ hsf_inv_ne) hsg_inv_ne
    lia
  · have hscaled : Prec (C sg⁻¹ * g₀) (C sf⁻¹ * f₀) :=
      prec_C_mul_right (prec_C_mul_left hgf₀ hsg_inv_ne) hsf_inv_ne
    lia
/-- Regularized no-common-root converse step for the `iterateTDeriv` pair.

This packages the exact simple-pair/Wronskian endgame that the main converse
uses after regularization, leaving the remaining `ε → 0` transport as the only
unfinished step. -/
theorem ObreschkoffConverseInternal.precOrRevPrecRegularized
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    {eps : ℝ} (heps : 0 < eps)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    let n := max f.natDegree g.natDegree
    Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∨
      Prec (iterateTDeriv eps n g) (iterateTDeriv eps n f) := by
  dsimp
  have hsimple_data :
      AllComboRealRooted (iterateTDeriv eps (max f.natDegree g.natDegree) f)
          (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∧
        ((iterateTDeriv eps (max f.natDegree g.natDegree) f) ≠ 0 ∧
          (iterateTDeriv eps (max f.natDegree g.natDegree) f).Splits) ∧
        ((iterateTDeriv eps (max f.natDegree g.natDegree) g) ≠ 0 ∧
          (iterateTDeriv eps (max f.natDegree g.natDegree) g).Splits) ∧
        HasSimpleRoots (iterateTDeriv eps (max f.natDegree g.natDegree) f) ∧
        HasSimpleRoots (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∧
        ((iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree + 1 =
            (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree ∨
          (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree =
            (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree) := by
    simpa using
      simple_pair_of_allComboRealRooted_iterateTDeriv hf_ne hg_ne hf_splits hg_splits hall hdeg heps
  have hcombo_simple :
      ∀ α β : ℝ,
        C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
            C β * iterateTDeriv eps (max f.natDegree g.natDegree) g = 0 ∨
          (((C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
                C β * iterateTDeriv eps (max f.natDegree g.natDegree) g) ≠ 0 ∧
              (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
                  C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).Splits) ∧
            HasSimpleRoots
              (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
                C β * iterateTDeriv eps (max f.natDegree g.natDegree) g)) := by
    intro α β
    have hcombo :=
      allComboRealRooted_eq_zero_or_isRealRooted_and_hasSimpleRoots_iterateTDeriv
        hall heps α β
    grind
  have hno_simple :
      ∀ r,
        (iterateTDeriv eps (max f.natDegree g.natDegree) f).IsRoot r →
          ¬ (iterateTDeriv eps (max f.natDegree g.natDegree) g).IsRoot r := by
    simpa using
      no_common_root_iterateTDeriv_of_allComboRealRooted
        hf_ne hg_ne hf_splits hg_splits hall hdeg heps hno
  rcases hsimple_data with ⟨_, hf_iter, hg_iter, _, _, hdeg_iter⟩
  exact
    prec_of_eq_zero_or_simple_combo_of_no_common
      hf_iter.1 hf_iter.2 hg_iter.1 hg_iter.2 hcombo_simple hdeg_iter hno_simple

/-- In the succ-degree branch, the regularized pair has forced orientation by
degree, so the converse endgame returns the left orientation outright. -/
theorem ObreschkoffConverseInternal.prec_iterateTDeriv_of_allComboRealRooted_succ_of_no_common
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hsucc : f.natDegree + 1 = g.natDegree)
    {eps : ℝ} (heps : 0 < eps)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    let n := max f.natDegree g.natDegree
    Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
  have hprec_iter :
      Prec (iterateTDeriv eps (max f.natDegree g.natDegree) f)
          (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∨
        Prec (iterateTDeriv eps (max f.natDegree g.natDegree) g)
          (iterateTDeriv eps (max f.natDegree g.natDegree) f) :=
    precOrRevPrecRegularized
      hf_ne hf_splits hg_ne hg_splits hall (Or.inl hsucc) heps hno
  have hdeg_iter_succ :
      (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree + 1 =
        (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree := by simp_all
  dsimp
  exact prec_forward_of_orientation_of_succDegree hdeg_iter_succ.symm hprec_iter


end
end RealRooted
