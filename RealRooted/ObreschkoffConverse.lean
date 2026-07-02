import RealRooted.AllCombo
import RealRooted.AffineDerivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Obreschkoff converse: AllComboRealRooted → Prec

Wronskian orientation lemmas, the same-degree and succ-degree cases,
and the main converse `prec_of_allComboRealRooted`.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

private def wronskian (f g : ℝ[X]) : ℝ[X] :=
  g * f.derivative - f * g.derivative

private lemma wronskian_eval {f g : ℝ[X]} {x : ℝ} :
    (wronskian f g).eval x =
      g.eval x * f.derivative.eval x - f.eval x * g.derivative.eval x := by
  simp [wronskian, sub_eq_add_neg]

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
    (wronskian (iterateTDeriv eps n f) (iterateTDeriv eps n g)).eval x =
      (iterateTDeriv eps n g).eval x * (iterateTDeriv eps n f.derivative).eval x -
        (iterateTDeriv eps n f).eval x * (iterateTDeriv eps n g.derivative).eval x := by
  rw [wronskian_eval]
  rw [eval_derivative_iterateTDeriv, eval_derivative_iterateTDeriv]

private lemma continuous_wronskian_iterateTDeriv_eval_joint
    (n : ℕ) (f g : ℝ[X]) :
    Continuous fun z : ℝ × ℝ =>
      (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 := by
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
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2) =
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
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2)
      (0, x) := by
  have hcont :
      ContinuousAt
        (fun z : ℝ × ℝ =>
          (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2)
        (0, x) :=
    (continuous_wronskian_iterateTDeriv_eval_joint n f g).continuousAt
  lia

private lemma exists_delta_wronskian_iterateTDeriv_eval_mul_pos_joint_at_zero
    (n : ℕ) {f g : ℝ[X]} {x : ℝ}
    (hx_eval : (wronskian f g).eval x ≠ 0) :
    ∃ δ > 0, ∀ {z : ℝ × ℝ}, ‖z - (0, x)‖ < δ →
      0 <
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 *
          (wronskian f g).eval x := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      (continuousAt_wronskian_iterateTDeriv_eval_joint_zero n f g x)
      (‖(wronskian f g).eval x‖ / 2) (by simp_all)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hclose' :
      ‖(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
          (wronskian f g).eval x‖ <
        ‖(wronskian f g).eval x‖ / 2 := by
    simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose hz
  rcases lt_or_gt_of_ne hx_eval with hx_neg | hx_pos
  · have hneg_iter :
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 < 0 := by
      have hneg_norm :
          ‖-(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskian f g).eval x)‖ =
            ‖(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
                (wronskian f g).eval x‖ := by
        rw [sub_eq_add_neg, neg_neg]
        have hEq :
            -(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 +
                (wronskian f g).eval x =
              -((wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
                (wronskian f g).eval x) := by
          ring
        rw [hEq, norm_neg]
      have hclose_neg0 :
          ‖-(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskian f g).eval x)‖ <
            ‖(wronskian f g).eval x‖ / 2 := by
        lia
      have hclose_neg :
          ‖-(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskian f g).eval x)‖ <
            (-(wronskian f g).eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter :
          0 < -(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 :=
        pos_of_norm_sub_lt_half_of_pos (by simp_all) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter :
        0 < (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 :=
      pos_of_norm_sub_lt_half_of_pos hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    simp_all

private lemma eval_mul_eval_neg_of_interlaces_consecutive_of_no_common
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
  have hEq_rs : rs = pre ++ r₁ :: r₂ :: rest := by
    lia
  have hnonpos :
      g.eval r₁ * g.eval r₂ ≤ 0 :=
    eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted hss_eq hint hEq_rs
  have hr₁_root : f.IsRoot r₁ := by
    apply (mem_roots hf.1).mp
    simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₁ ∈ rs)
  have hr₂_root : f.IsRoot r₂ := by
    apply (mem_roots hf.1).mp
    simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₂ ∈ rs)
  have hg₁_ne : g.eval r₁ ≠ 0 := by
    simp_all
  have hg₂_ne : g.eval r₂ ≠ 0 := by
    simp_all
  grind

/-- Degree-drop converse to the usual Ma--Wang assembly step: if a nonzero
polynomial `F` has strictly alternating signs on consecutive roots of a
real-rooted polynomial `f`, and `F` has strictly smaller degree than `f`, then
the degree gap is forced to be exactly one and `F` is the left interlacer of
`f`.

This is the shape needed for the same-degree Obreschkoff forward direction when
the top coefficient cancels in `α f + β g`: the canceled combination should not
sit on the right of `f`, but rather become the common interlacer on the left. -/
private theorem interlaces_of_consecutive_signs_of_natDegree_lt
    {f F : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0)
    (hdeg_lt : F.natDegree < f.natDegree)
    (hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) :
    Interlaces F f := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted (by grind)
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort, card_roots_of_splits hf_splits]
  have hus_sub : (↑us : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    simp_all
  have hus_card_le : us.length ≤ F.natDegree := by
    calc
      us.length = (↑us : Multiset ℝ).card := (Multiset.coe_card _).symm
      _ ≤ F.roots.card := Multiset.card_le_card hus_sub
      _ ≤ F.natDegree := card_roots' F
  have hus_len_f : us.length = f.natDegree - 1 := by
    lia
  have hdeg : F.natDegree + 1 = f.natDegree := by
    lia
  have hus_len_deg : us.length = F.natDegree := by
    lia
  have hus_eq : (↑us : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hus_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = us.length := hus_len_deg.symm
        _ = (↑us : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : (F ≠ 0 ∧ F.Splits) := by
    refine ⟨hF_ne, splits_of_card_roots ?_⟩
    rw [← hus_eq, Multiset.coe_card, hus_len_deg]
  exact
    ⟨⟨hf_ne, hf_splits⟩, hF, hdeg, rs, us, hrs_sorted, hus_pw.imp le_of_lt, hrs_eq, hus_eq, hus_int⟩

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
  have hp_eval : p.eval r = 0 := by
    simp_all
  have hq_eval : q.eval r = 0 := by
    simp_all
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
    (wronskian f g).eval x ≠ 0 := by
  let p : ℝ[X] := C (g.eval x) * f + C (-f.eval x) * g
  have hp_root : p.IsRoot x := by
    simp [p, Polynomial.IsRoot.def]
    ring
  intro hw
  have hp_der_eval_eq : p.derivative.eval x = (wronskian f g).eval x := by
    simp [p, wronskian_eval]
    ring
  have hp_der_eval : p.derivative.eval x = 0 := by
    lia
  have hp_der_root : p.derivative.IsRoot x := by
    simp_all
  rcases hcombo (g.eval x) (-f.eval x) with hp0 | ⟨hp_rr, hp_simple⟩
  · by_cases hgx0 : g.eval x = 0
    · simp_all
    · have hEq1 : C (g.eval x) * f = C (f.eval x) * g := by
        grind
      have hscalar : f = C (f.eval x / g.eval x) * g := by
        ext n
        have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq1
        grind
      have hfx0 : f.eval x ≠ 0 := by
        grind
      have hscale_ne : f.eval x / g.eval x ≠ 0 := div_ne_zero hfx0 hgx0
      have hdeg_eq : f.natDegree = g.natDegree := by
        rw [hscalar, natDegree_C_mul hscale_ne]
      have hg_deg_pos : 0 < g.natDegree := by
        grind
      obtain ⟨r, hr⟩ :=
        exists_isRoot_of_isRealRooted_of_not_isUnit hg_ne hg_splits
          (not_isUnit_of_natDegree_pos g hg_deg_pos)
      have hfr : f.IsRoot r := by
        have hgr_eval : g.eval r = 0 := by
          simpa [Polynomial.IsRoot.def] using hr
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
    (hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0) :
    HasSimpleRoots (C α * f + C β * g) := by
  let p : ℝ[X] := C α * f + C β * g
  intro r hr
  by_contra hmult_ne
  have hmult_pos : 0 < p.rootMultiplicity r :=
    (rootMultiplicity_pos hp_ne).mpr hr
  have hmult_ge2 : 2 ≤ p.rootMultiplicity r := by
    lia
  have hder_root : p.derivative.IsRoot r :=
    isRoot_derivative_of_rootMultiplicity_ge_two hmult_ge2
  have hp_eval : p.eval r = 0 := by
    simp_all
  have hp_der_eval : p.derivative.eval r = 0 := by
    simp_all
  have hp_eval' : α * f.eval r + β * g.eval r = 0 := by
    simp_all
  have hp_der_eval' : α * f.derivative.eval r + β * g.derivative.eval r = 0 := by
    simpa [p, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C] using hp_der_eval
  have hαβ_ne : α ≠ 0 ∨ β ≠ 0 := by
    grind
  have hW_zero : (wronskian f g).eval r = 0 := by
    rcases hαβ_ne with hα | hβ
    · have hmul : α * (wronskian f g).eval r = 0 := by
        calc
          α * (wronskian f g).eval r
              = g.eval r * (α * f.derivative.eval r + β * g.derivative.eval r) -
                  g.derivative.eval r * (α * f.eval r + β * g.eval r) := by
                    rw [wronskian_eval]
                    ring
          _ = 0 := by simp_all
      simp_all
    · have hmul : β * (wronskian f g).eval r = 0 := by
        calc
          β * (wronskian f g).eval r
              = f.derivative.eval r * (α * f.eval r + β * g.eval r) -
                  f.eval r * (α * f.derivative.eval r + β * g.derivative.eval r) := by
                    rw [wronskian_eval]
                    ring
          _ = 0 := by simp_all
      simp_all
  simp_all

private lemma combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0) :
    ∀ α β : ℝ,
      C α * f + C β * g = 0 ∨
        (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
          HasSimpleRoots (C α * f + C β * g)) := by
  intro α β
  by_cases hcombo0 : C α * f + C β * g = 0
  · exact Or.inl hcombo0
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
private lemma exists_special_pair_of_wronskian_zero
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ}
    (hw : (wronskian f g).eval x = 0) :
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
  have hp_der_eval_eq : p.derivative.eval x = (wronskian f g).eval x := by
    simp [p, wronskian_eval]
    ring
  have hp_der_root : p.derivative.IsRoot x := by
    simp_all
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
    {p : ℝ[X]} (hp0 : p ≠ 0) (hsimple : HasSimpleRoots p)
    {r : ℝ} (hr : p.IsRoot r) :
    p.derivative.eval r ≠ 0 := by
  intro hder0
  have hder_root : p.derivative.IsRoot r := by
    simp_all
  have hmult : 1 < p.rootMultiplicity r :=
    (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hr, hder_root⟩
  rw [hsimple r hr] at hmult
  lia

/-- Local double-root obstruction in the positive-sign case.

If every linear combination of `p` and `q` is real-rooted, `p` has an exact
double root at `x`, and the second-derivative/product sign at `x` is positive,
then a sufficiently small perturbation `p + β q` violates the standard
non-root second-derivative inequality. This is the clean local contradiction
used in the last step of the Obreschkoff converse. -/
private lemma false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
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
  have hp_eval0 : p.eval x = 0 := by
    simp_all
  have hp_der_eval0 : p.derivative.eval x = 0 := by
    simp_all
  have hp_rr : p.Splits := (hall.isRealRooted_left hp0).2
  let pp : ℝ := p.derivative.derivative.eval x
  let qx : ℝ := q.eval x
  let qp : ℝ := q.derivative.eval x
  let qq : ℝ := q.derivative.derivative.eval x
  have hpp_ne : pp ≠ 0 := by
    have hprod_ne : p.derivative.derivative.eval x * q.eval x ≠ 0 := ne_of_gt hprod_pos
    grind
  have hqx_ne : qx ≠ 0 := by
    lia
  let A : ℝ := pp * qx
  let B : ℝ := qp ^ 2 - qq * qx
  let δ₁ : ℝ := A / (2 * (|B| + 1))
  let δ₂ : ℝ := |pp| / (2 * (|qq| + 1))
  let β : ℝ := min δ₁ δ₂
  have hA_pos : 0 < A := by
    lia
  have hβ_pos : 0 < β := by
    dsimp [β, δ₁, δ₂, A, B]
    positivity
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hβ_le_δ₁ : β ≤ δ₁ := min_le_left _ _
  have hβ_le_δ₂ : β ≤ δ₂ := min_le_right _ _
  have hsecond_small : |β * qq| ≤ |pp| / 2 := by
    calc
      |β * qq| = β * |qq| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hβ_pos)]
      _ ≤ β * (|qq| + 1) := by simp_all
      _ ≤ δ₂ * (|qq| + 1) := by
        gcongr
      _ = |pp| / 2 := by
        grind
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
      β * |B| ≤ β * (|B| + 1) := by
        simp_all
      _ ≤ δ₁ * (|B| + 1) := by
        gcongr
      _ = A / 2 := by
        grind
      _ < A := by simp_all
  have hineq_le : β * B ≤ β * |B| := by
    have hB_le : B ≤ |B| := le_abs_self B
    simp_all
  grind

/-- Local double-root obstruction without a sign assumption. We flip the
companion polynomial if necessary so the positive-branch lemma applies. -/
private lemma false_of_allComboRealRooted_of_double_root_and_eval_ne
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
    have hprod_neg : p.derivative.derivative.eval x * q.eval x < 0 := by
      grind
    have hneg_pos : 0 < p.derivative.derivative.eval x * (-q).eval x := by
      simp_all
    have hall_neg : AllComboRealRooted p (-q) := by
      simpa using (allComboRealRooted_C_mul_right (f := p) (g := q) (c := (-1 : ℝ)) hall)
    have hq_neg_eval_ne : (-q).eval x ≠ 0 := by
      simp_all
    exact
      false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
        hall_neg hp_mult hq_neg_eval_ne hneg_pos

private lemma no_nontrivial_linear_relation_of_no_common_root
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_pos : 0 < f.natDegree)
    {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hlin : C α * f + C β * g = 0) :
    False := by
  have hEq : C α * f = C (-β) * g := by
    grind
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
    have hf_deg_pos : 0 < f.natDegree := by
      simpa [natDegree_iterateTDeriv] using hdeg_iter_pos
    exact no_nontrivial_linear_relation_of_no_common_root
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
    0 < (wronskian f g).eval x * (wronskian f g).eval y := by
  by_contra hnonpos
  obtain ⟨z, _, _, hz_root⟩ :=
    exists_isRoot_between_of_eval_mul_nonpos hxy (not_lt.mp hnonpos)
  have hz_eval0 : (wronskian f g).eval z = 0 := by
    simp_all
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
  rcases hcombo 1 0 with hzero | ⟨_, hsimple⟩
  · simp_all
  · simp_all

private lemma hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_right
    {f g : ℝ[X]}
    (hg_ne : g ≠ 0)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g))) :
    HasSimpleRoots g := by
  rcases hcombo 0 1 with hzero | ⟨_, hsimple⟩
  · simp_all
  · simp_all

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
    refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, [], [], by simp, by simp, ?_, ?_, ?_⟩
    · simp [hroots_f]
    · simp [hroots_g]
    · exact Or.inr ⟨by lia, by simp [ListAlternates]⟩
  by_cases hdeg1 : f.natDegree = 1
  · exact PosComboRealRooted.prec_or_revPrec_of_same_degree_one hdeg hdeg1
  have hdeg_ge2 : 2 ≤ f.natDegree := by lia
  have hgdeg_ge2 : 2 ≤ g.natDegree := by lia
  have hW_ne x : (wronskian f g).eval x ≠ 0 :=
    wronskian_eval_ne_zero_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by grind) hno (x := x)
  have hW_prod {x y : ℝ} : x ≤ y → 0 < (wronskian f g).eval x * (wronskian f g).eval y :=
    wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by grind) hno
  have hf'_pos : HasPosLeadingCoeff f.derivative :=
    hf_pos.derivative (by lia)
  have hg'_pos :
      HasPosLeadingCoeff g.derivative :=
    hg_pos.derivative (by lia)
  by_cases hWneg0 : (wronskian f g).eval 0 < 0
  · have hWneg : ∀ x : ℝ, (wronskian f g).eval x < 0 := by
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
      have hf_eval : f.eval r = 0 := by
        simp_all
      simpa [wronskian_eval, hf_eval] using hWneg r
    left
    exact prec_of_interlaces_eval_mul_neg_same hder hf'_pos hg_pos hdeg hroot_sign
  · have hWpos0 : 0 < (wronskian f g).eval 0 := by
      grind
    have hWpos : ∀ x : ℝ, 0 < (wronskian f g).eval x := by
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
      have hg_eval : g.eval r = 0 := by
        simp_all
      have hw : 0 < -(f.eval r * g.derivative.eval r) := by
        simpa [wronskian_eval, hg_eval] using hWpos r
      nlinarith
    right
    exact prec_of_interlaces_eval_mul_neg_same hder hg'_pos hf_pos hdeg.symm hroot_sign

lemma prec_degree_zero_right_of_degree_one
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_deg0 : f.natDegree = 0) (hg_deg1 : g.natDegree = 1) :
    Prec f g := by
  obtain ⟨r, hr_eq⟩ : ∃ r, g.roots = {r} := by
    apply Multiset.card_eq_one.mp
    simpa [hg_deg1] using card_roots_of_splits hg_splits
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [card_roots_of_splits hf_splits, hf_deg0]
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, [], [r], by simp,
    List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp [hroots_f]
  · simp [hr_eq]
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

private lemma interlaces_derivative_of_degree_pos
    {f : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 1 ≤ f.natDegree) :
    Interlaces f.derivative f := by
  by_cases hdeg1 : f.natDegree = 1
  · have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
    have hf'_ne : f.derivative ≠ 0 := by
      simp_all
    have hf'_deg0 : f.derivative.natDegree = 0 := by
      simp [hdeg1, f.natDegree_derivative]
    have hf'_rr : (f.derivative ≠ 0 ∧ f.derivative.Splits) :=
      isRealRooted_of_deg_zero hf'_ne hf'_deg0
    exact
      (prec_degree_zero_right_of_degree_one hf'_rr.1 hf'_rr.2 hf_ne hf_splits
        hf'_deg0 hdeg1).toInterlaces
        (by lia)
  · have hdeg_ge2 : 2 ≤ f.natDegree := by lia
    exact derivative_interlaces hf_splits hdeg_ge2

private lemma wronskian_coeff_top_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskian f g).coeff (2 * f.natDegree) = -(f.leadingCoeff * g.leadingCoeff) := by
  have hf'_deg : f.derivative.natDegree = f.natDegree - 1 :=
    f.natDegree_derivative
  have hg'_deg : g.derivative.natDegree = g.natDegree - 1 :=
    g.natDegree_derivative
  have hf'_lc : f.derivative.leadingCoeff = (f.natDegree : ℝ) * f.leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [hf'_deg, coeff_derivative, Nat.sub_add_cancel hf_deg_pos, coeff_natDegree]
    have hnat : (↑(f.natDegree - 1) : ℝ) + 1 = f.natDegree := by
      simp_all
    grind
  have hg'_lc : g.derivative.leadingCoeff = (g.natDegree : ℝ) * g.leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [hg'_deg, coeff_derivative, Nat.sub_add_cancel (by lia), coeff_natDegree]
    have hnat : (↑(g.natDegree - 1) : ℝ) + 1 = g.natDegree := by
      simp_all
    grind
  have hcoeff_gf' :
      (g * f.derivative).coeff (2 * f.natDegree) = g.leadingCoeff * f.derivative.leadingCoeff := by
    have htop : g.natDegree + f.derivative.natDegree = 2 * f.natDegree := by
      rw [hf'_deg, hdeg]
      lia
    rw [← htop]
    exact coeff_mul_degree_add_degree g f.derivative
  have hcoeff_fg' :
      (f * g.derivative).coeff (2 * f.natDegree) = f.leadingCoeff * g.derivative.leadingCoeff := by
    have htop : f.natDegree + g.derivative.natDegree = 2 * f.natDegree := by
      rw [hg'_deg, hdeg]
      lia
    rw [← htop]
    exact coeff_mul_degree_add_degree f g.derivative
  have hdegR : (g.natDegree : ℝ) = f.natDegree + 1 := by
    simp_all
  unfold wronskian
  rw [coeff_sub, hcoeff_gf', hcoeff_fg', hf'_lc, hg'_lc, hdegR]
  grind

private lemma wronskian_natDegree_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskian f g).natDegree = 2 * f.natDegree := by
  have hcoeff_top := wronskian_coeff_top_succ (f := f) (g := g) hdeg hf_deg_pos
  have hcoeff_top_ne : (wronskian f g).coeff (2 * f.natDegree) ≠ 0 := by
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
  have hW_le : (wronskian f g).natDegree ≤ 2 * f.natDegree := by
    unfold wronskian
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
    (wronskian f g).leadingCoeff = -(f.leadingCoeff * g.leadingCoeff) := by
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
  have hW_ne x : (wronskian f g).eval x ≠ 0 :=
    wronskian_eval_ne_zero_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by simp_all) hno
  have hW_prod {x y : ℝ} : x ≤ y → 0 < (wronskian f g).eval x * (wronskian f g).eval y :=
    wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo hf_ne hg_ne hg_splits
      hcombo (by simp_all) hno
  have hq_pos : HasPosLeadingCoeff (-wronskian f g) := by
    refine hasPosLeadingCoeff_neg ?_
    rw [leadingCoeff_wronskian_succ hdeg hf_pos hg_pos hf_deg_pos]
    nlinarith [mul_pos hf_pos hg_pos]
  have hq_deg_pos : 0 < (-wronskian f g).degree := by
    have hnat : 0 < (-wronskian f g).natDegree := by
      rw [natDegree_neg, wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos]
      lia
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hq_even : Even (-wronskian f g).natDegree := by
    rw [natDegree_neg, wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos]
    simp
  have ht : Filter.Tendsto (fun x => (-wronskian f g).eval x) Filter.atBot Filter.atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hq_pos hq_deg_pos hq_even
  have hq_event : ∀ᶠ x : ℝ in Filter.atBot, 0 < (-wronskian f g).eval x :=
    ht.eventually (Filter.Ioi_mem_atTop 0)
  obtain ⟨x₀, hx₀⟩ := hq_event.exists
  have hWneg₀ : (wronskian f g).eval x₀ < 0 := by
    simp_all
  have hWneg : ∀ x : ℝ, (wronskian f g).eval x < 0 := by
    intro x
    by_cases hxx₀ : x ≤ x₀
    · have hprod := hW_prod hxx₀
      nlinarith
    · have hx₀x : x₀ ≤ x := le_of_not_ge hxx₀
      have hprod := hW_prod hx₀x
      nlinarith
  have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_degree_pos hf_ne hf_splits hf_pos hf_deg_pos
  have hroot_sign :
      ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by
      simp_all
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
private theorem prec_of_eq_zero_or_simple_combo_of_no_common
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
  have hsf_ne : sf ≠ 0 := by
    grind
  have hsg_ne : sg ≠ 0 := by
    grind
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
  have hf_scale : C sf⁻¹ * f₀ = f := by
    grind
  have hg_scale : C sg⁻¹ * g₀ = g := by
    grind
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
private theorem prec_or_revPrec_iterateTDeriv_of_allComboRealRooted_of_no_common
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
    by_cases hzero :
        C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
          C β * iterateTDeriv eps (max f.natDegree g.natDegree) g = 0
    · exact Or.inl hzero
    · exact Or.inr ⟨⟨hzero, hcombo.1⟩, hcombo.2 hzero⟩
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
private theorem prec_iterateTDeriv_of_allComboRealRooted_succ_of_no_common
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
    prec_or_revPrec_iterateTDeriv_of_allComboRealRooted_of_no_common
      hf_ne hf_splits hg_ne hg_splits hall (Or.inl hsucc) heps hno
  have hdeg_iter_succ :
      (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree + 1 =
        (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree := by
    simpa [natDegree_iterateTDeriv, natDegree_iterateTDeriv] using hsucc
  dsimp
  exact prec_forward_of_orientation_of_succDegree hdeg_iter_succ.symm hprec_iter

/-- Same-degree companion to
`interlaces_of_consecutive_signs_of_natDegree_lt`: if a nonzero polynomial `F`
has strict sign changes on consecutive roots of a real-rooted polynomial `f`,
has the same degree as `f`, and has one extra outer root on either side, then
`F` is real-rooted. This is the exact assembly step needed for the non-cancel
opposite-sign branch in the forward same-degree Obreschkoff theorem. -/
private theorem isRealRooted_of_consecutive_signs_of_natDegree_eq_of_outer_root
    {f F : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0)
    (hdeg : F.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (houter :
      (∃ uL, F.IsRoot uL ∧ ∀ r, f.IsRoot r → uL < r) ∨
      (∃ uR, F.IsRoot uR ∧ ∀ r, f.IsRoot r → r < uR)) : (F ≠ 0 ∧ F.Splits) := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted (by grind)
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort, card_roots_of_splits hf_splits]
  have hrs_ne : rs ≠ [] := by
    grind
  have hus_sub : (↑us : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    simp_all
  have hus_len_deg : us.length = F.natDegree - 1 := by
    lia
  rcases houter with ⟨uL, huL_root, huL_lt⟩ | ⟨uR, huR_root, huR_lt⟩
  · obtain ⟨r₀, rs', hrs_cons⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
      cases h : rs with
      | nil => lia
      | cons r₀ rs' =>
          lia
    have hr₀_root : f.IsRoot r₀ := by
      apply (mem_roots hf_ne).mp
      rw [← hrs_eq, hrs_cons]
      simp
    have hus_int' : ListInterlaces us (r₀ :: rs') := by
      lia
    have huL_lt_all_us : ∀ u ∈ us, uL < u :=
      fun u hu =>
        lt_of_lt_of_le (huL_lt r₀ hr₀_root)
          (listInterlaces_all_ge us rs' r₀ hus_int' u hu)
    have hws_pw : (uL :: us).Pairwise (· < ·) := by
      simp_all
    have hws_sub : (↑(uL :: us) : Multiset ℝ) ≤ F.roots := by
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
      intro x hx
      rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx' <;> simp_all
    have hws_len : (uL :: us).length = F.natDegree := by
      simp_all
    have hws_eq : (↑(uL :: us) : Multiset ℝ) = F.roots :=
      Multiset.eq_of_le_of_card_le hws_sub (by
        calc
          F.roots.card ≤ F.natDegree := card_roots' F
          _ = (uL :: us).length := hws_len.symm
          _ = (↑(uL :: us) : Multiset ℝ).card := (Multiset.coe_card _).symm)
    refine ⟨hF_ne, ?_⟩
    exact splits_of_card_roots (by rw [← hws_eq, Multiset.coe_card, hws_len])
  · have hu_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have hu_root : f.IsRoot (rs.getLast hrs_ne) := by
      apply (mem_roots hf_ne).mp
      rw [← hrs_eq]
      simp
    have hus_lt_all_uR : ∀ u ∈ us, u < uR :=
      fun u hu =>
        lt_of_le_of_lt
          (listInterlaces_all_le_getLast hrs_ne hrs_sorted hus_int u hu)
          (huR_lt _ hu_root)
    have hws_pw : (us ++ [uR]).Pairwise (· < ·) := by
      grind
    have hws_sub : (↑(us ++ [uR]) : Multiset ℝ) ≤ F.roots := by
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
      intro x hx
      rcases List.mem_append.mp (Multiset.mem_coe.mp hx) with hx_us | hx_uR <;> simp_all
    have hws_len : (us ++ [uR]).length = F.natDegree := by
      simp_all
    have hws_eq : (↑(us ++ [uR]) : Multiset ℝ) = F.roots :=
      Multiset.eq_of_le_of_card_le hws_sub (by
        calc
          F.roots.card ≤ F.natDegree := card_roots' F
          _ = (us ++ [uR]).length := hws_len.symm
          _ = (↑(us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
    refine ⟨hF_ne, ?_⟩
    exact splits_of_card_roots (by rw [← hws_eq, Multiset.coe_card, hws_len])

/-- Same-degree `hroot_sign` real-rootedness without assuming the target has
positive leading coefficient.

The positive-leading branch is already Ma--Wang:
`prec_of_interlaces_eval_mul_neg_same`. The genuinely new content here is the
negative-leading branch: strict sign changes still force real-rootedness, but
the extra root now comes from the left endpoint rather than the right. This is
exactly the helper needed for the opposite-sign, non-cancel branch in the
forward same-degree Obreschkoff theorem. -/
private theorem isRealRooted_of_interlaces_eval_mul_neg_same_any_lc
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : F.natDegree = f.natDegree)
    (hdeg_pos : 2 ≤ f.natDegree)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) : (F ≠ 0 ∧ F.Splits) := by
  by_cases hF_pos : HasPosLeadingCoeff F
  · exact (prec_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg hroot_sign).2.1
  obtain ⟨hf, hg, hgdeg, rs0, ss, hrs0_sorted, hss_sorted, hrs0_eq, hss_eq, hint0⟩ := hgf
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs0_eq_rs : rs0 = rs := by
    apply List.Perm.eq_of_pairwise' hrs0_sorted hrs_sorted
    exact Multiset.coe_eq_coe.mp (hrs0_eq.trans hrs_eq.symm)
  subst hrs0_eq_rs
  have hint : ListInterlaces ss rs := by
    lia
  have hgf' : Interlaces g f :=
    ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq,
      hss_eq, hint⟩
  have hF_natdeg_pos : 0 < F.natDegree := by
    lia
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [h0] at hF_natdeg_pos
  have hF_lc_ne : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF_ne
  have hF_lc_neg : F.leadingCoeff < 0 := by
    unfold HasPosLeadingCoeff at hF_pos
    grind
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort, card_roots_of_splits hf.2]
  have hrs_ne : rs ≠ [] := by
    grind
  obtain ⟨r₀, rs', hrs_cons⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases h : rs with
    | nil => lia
    | cons r₀ rs' =>
        lia
  have hint_cons : ListInterlaces ss (r₀ :: rs') := by
    lia
  have hhead_eq : rs.head! = r₀ := by
    simp [hrs_cons]
  have hr₀_root : f.IsRoot r₀ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq, hrs_cons]
    simp
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    simp_all
  have hhead_lt_roots_g : ∀ t ∈ g.roots, r₀ < t := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      lia
    have hr₀_le_t : r₀ ≤ t := listInterlaces_all_ge ss rs' r₀ hint_cons t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hEq_rs : rs = pre ++ r₁ :: r₂ :: rest := by
      lia
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr (by grind : r₁ ∈ rs)
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr (by grind : r₂ ∈ rs)
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg : g.eval r₁ * g.eval r₂ < 0 :=
      eval_mul_eval_neg_of_interlaces_consecutive_of_no_common hgf' hno_g_at_f pre hEq
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg
  have hnegF_pos : HasPosLeadingCoeff (C (-1 : ℝ) * F) := by
    simpa using (hasPosLeadingCoeff_neg hF_lc_neg : HasPosLeadingCoeff (-F))
  have hnegF_deg : (C (-1 : ℝ) * F).natDegree = f.natDegree := by
    simp_all
  have hnegF_natdeg_pos : 0 < (C (-1 : ℝ) * F).natDegree := by
    lia
  have hnegF_deg_pos : 0 < (C (-1 : ℝ) * F).degree :=
    natDegree_pos_iff_degree_pos.mp hnegF_natdeg_pos
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r, f.IsRoot r → uL < r := by
    rcases Nat.even_or_odd f.natDegree with hf_even | hf_odd
    · have hg_odd : Odd g.natDegree := by
        grind
      have hg_left_neg : g.eval r₀ < 0 :=
        eval_neg_of_all_roots_gt_of_odd hg.1 hg_pos hg_odd hhead_lt_roots_g
      have hF_left_pos : 0 < F.eval r₀ := by
        have hprod := hroot_sign r₀ hr₀_root
        nlinarith
      have hnegF_left_neg : (C (-1 : ℝ) * F).eval r₀ < 0 := by
        simp_all
      have hnegF_even : Even (C (-1 : ℝ) * F).natDegree := by
        lia
      have ht :
          Filter.Tendsto (fun x => (C (-1 : ℝ) * F).eval x) Filter.atBot Filter.atTop :=
        tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hnegF_pos hnegF_deg_pos hnegF_even
      obtain ⟨uL, huL_le, huL_root_neg⟩ :=
        exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hnegF_left_neg ht
      have huL_root : F.IsRoot uL := by
        simp_all
      have huL_lt_r₀ : uL < r₀ := by
        refine lt_of_le_of_ne huL_le ?_
        intro hEq
        simp_all
      refine ⟨uL, huL_root, ?_⟩
      intro r hr
      have hr_mem : r ∈ rs := by
        apply Multiset.mem_coe.mp
        simp_all
      have hr₀_le_r : r₀ ≤ r := by
        rw [← hhead_eq]
        exact hrs_sorted.head!_le hr_mem
      grind
    · have hg_even : Even g.natDegree := by
        grind
      have hg_left_pos : 0 < g.eval r₀ :=
        eval_pos_of_all_roots_gt_of_even hg.1 hg_pos hg_even hhead_lt_roots_g
      have hF_left_neg : F.eval r₀ < 0 := by
        have hprod := hroot_sign r₀ hr₀_root
        nlinarith
      have hnegF_left_pos : 0 < (C (-1 : ℝ) * F).eval r₀ := by
        simp_all
      have hnegF_odd : Odd (C (-1 : ℝ) * F).natDegree := by
        lia
      have ht :
          Filter.Tendsto (fun x => (C (-1 : ℝ) * F).eval x) Filter.atBot Filter.atBot :=
        tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hnegF_pos hnegF_deg_pos hnegF_odd
      obtain ⟨uL, huL_le, huL_root_neg⟩ :=
        exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hnegF_left_pos ht
      have huL_root : F.IsRoot uL := by
        simp_all
      have huL_lt_r₀ : uL < r₀ := by
        refine lt_of_le_of_ne huL_le ?_
        intro hEq
        simp_all
      refine ⟨uL, huL_root, ?_⟩
      intro r hr
      have hr_mem : r ∈ rs := by
        apply Multiset.mem_coe.mp
        simp_all
      have hr₀_le_r : r₀ ≤ r := by
        rw [← hhead_eq]
        exact hrs_sorted.head!_le hr_mem
      grind
  exact
    isRealRooted_of_consecutive_signs_of_natDegree_eq_of_outer_root
      hf.1 hf.2 hF_ne hdeg (by lia) hsign (Or.inl hleft)

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
  have hlt : ∀ t ∈ p.derivative.roots, t < x := by
    grind
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
  have hrs_ne : rs ≠ [] := by
    grind
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
      have : p.eval r = 0 := by
        simp_all
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
  have ht_pos : 0 < t := by
    grind
  refine ⟨t, ht_pos, ?_⟩
  intro hq
  have hqdeg : 2 ≤ (C t + p).natDegree := by
    simp_all
  have hq'_rr : ((C t + p).derivative ≠ 0 ∧ (C t + p).derivative.Splits) :=
    (derivative_interlaces hq.2 hqdeg).2.1
  have hmono :
      StrictMonoOn (fun x => (C t + p).eval x) (Set.Ici c) := by
    have hder_eq : (C t + p).derivative = p.derivative := by
      simp
    refine strictMonoOn_eval_Ici_of_derivative_roots_le hq'_rr.1 hq'_rr.2 ?_ ?_
    · simpa [hder_eq] using hp_pos.derivative (by lia)
    · simp_all
  have hqc_pos : 0 < (C t + p).eval c := by
    have : (C t + p).eval c = 1 := by
      simp [t]
    linarith
  obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hq.2 hqdeg (by
    simpa using hc_root)
  by_cases hcr : c = r
  · simp_all
  · have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr
    have hlt_eval :
        (C t + p).eval c < (C t + p).eval r := hmono (by simp) (by simp_all) hcr_lt
    have : (C t + p).eval r = 0 := by
      simp_all
    linarith

/-- Constant shifts eventually destroy real-rootedness once the polynomial has
positive leading coefficient and degree at least `2`. -/
lemma exists_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
    {p : ℝ[X]} (hp_splits : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ t : ℝ, ¬ ((C t + p) ≠ 0 ∧ (C t + p).Splits) := by
  obtain ⟨t, _, ht⟩ :=
    exists_pos_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
      hp_splits hp_pos hdeg
  exact ⟨t, ht⟩

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
        C (t / c) * C c + p = C ((t / c) * c) + p := by
          simp
        _ = C t + p := by
          simp_all
    simpa [hrewrite] using (hall (t / c) 1)
  by_cases hzero : C t + p = 0
  · have : p = -C t := by grind
    simp_all
  · exact ht ⟨hzero, hcombo_t⟩

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
    have hneg_rr : ((-p) ≠ 0 ∧ (-p).Splits) := by
      simp_all
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
  have hfN_coeff_ne : fN.coeff 0 ≠ 0 := by
    grind
  set cf : ℝ := fN.coeff 0
  have hfN_C' : fN = C cf := by
    lia
  have hgN_deg : gN.natDegree = g.natDegree - n := by
    dsimp [gN, n]
    exact natDegree_iterate_derivative_eq_sub hg0 (by lia)
  have hgN_deg_ge2 : 2 ≤ gN.natDegree := by
    lia
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

private theorem prec_of_allComboRealRooted_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        (f ≠ 0 ∧ f.Splits) → (g ≠ 0 ∧ g.Splits) →
        AllComboRealRooted f g →
        (f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          (f ≠ 0 ∧ f.Splits) → (g ≠ 0 ∧ g.Splits) →
          AllComboRealRooted f g →
          (f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) →
          Prec f g ∨ Prec g f)
      f.natDegree ?_ rfl ⟨hf_ne, hf_splits⟩ ⟨hg_ne, hg_splits⟩ hall hdeg
  intro n ih f g hfdeg hf hg hall hdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · simp_all
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
    have hqf_ne : qf ≠ 0 := by
      simp_all
    have hqg_ne : qg ≠ 0 := by
      simp_all
    have hqf_rr : (qf ≠ 0 ∧ qf.Splits) :=
      isRealRooted_of_dvd hf.1 hf.2 hqf_ne ⟨X - C r, by grind⟩
    have hqg_rr : (qg ≠ 0 ∧ qg.Splits) :=
      isRealRooted_of_dvd hg.1 hg.2 hqg_ne ⟨X - C r, by grind⟩
    have hqhall : AllComboRealRooted qf qg :=
      allComboRealRooted_common_root_reduction hqf hqg hall
    have hqdeg : qf.natDegree + 1 = qg.natDegree ∨ qf.natDegree = qg.natDegree := by
      rcases hdeg with hsucc | hsame
      · rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
          hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsucc
        lia
      · rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
          hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsame
        lia
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf qg ∨ Prec qg qf :=
      ih qf.natDegree hqf_deg_lt rfl hqf_rr hqg_rr hqhall hqdeg
    rcases hprec_q with hprec_q | hprec_q
    · have hprec_mul : Prec ((X - C r) * qf) ((X - C r) * qg) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec_q
      lia
    · have hprec_mul : Prec ((X - C r) * qg) ((X - C r) * qf) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec_q
      lia
/-- **Obreschkoff's theorem** (Brändén, Theorem 7.7.3): `f` and `g` interlace
if and only if every polynomial in the real linear span `{αf + βg : α, β ∈ ℝ}`
is real-rooted (or zero).

Forward direction: interlacing → all combinations real-rooted.
This follows from Wagner addition (already proved). -/
theorem prec_of_allComboRealRooted {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f := by
  refine prec_of_allComboRealRooted_of_no_common ?_ hf_ne hf_splits hg_ne hg_splits hall hdeg
  intro f g hf hg hall hdeg hno
  let eps : ℝ := 1
  have heps : 0 < eps := by
    grind
  let n : ℕ := max f.natDegree g.natDegree
  have hsimple_data :
      AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∧
        ((iterateTDeriv eps n f) ≠ 0 ∧ (iterateTDeriv eps n f).Splits) ∧
        ((iterateTDeriv eps n g) ≠ 0 ∧ (iterateTDeriv eps n g).Splits) ∧
        HasSimpleRoots (iterateTDeriv eps n f) ∧
        HasSimpleRoots (iterateTDeriv eps n g) ∧
        ((iterateTDeriv eps n f).natDegree + 1 = (iterateTDeriv eps n g).natDegree ∨
            (iterateTDeriv eps n f).natDegree = (iterateTDeriv eps n g).natDegree) := by
    simpa [n] using
      simple_pair_of_allComboRealRooted_iterateTDeriv hf.1 hg.1 hf.2 hg.2 hall hdeg heps
  rcases hsimple_data with ⟨hall_iter, _, _, hf_simple, hg_simple, _⟩
  have hprec_iter :
      Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∨
        Prec (iterateTDeriv eps n g) (iterateTDeriv eps n f) := by
    simpa [n] using
      prec_or_revPrec_iterateTDeriv_of_allComboRealRooted_of_no_common
        hf.1 hf.2 hg.1 hg.2 hall hdeg heps hno
  have hlead_f_iter :
      (iterateTDeriv eps n f).leadingCoeff = f.leadingCoeff := by
    simp
  have hlead_g_iter :
      (iterateTDeriv eps n g).leadingCoeff = g.leadingCoeff := by
    simp
  have hpos_f_iter :
      HasPosLeadingCoeff (iterateTDeriv eps n f) ↔ HasPosLeadingCoeff f := by
    simp
  have hpos_g_iter :
      HasPosLeadingCoeff (iterateTDeriv eps n g) ↔ HasPosLeadingCoeff g := by
    simp
  have hsucc_iter_forced :
      f.natDegree + 1 = g.natDegree →
        Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
    intro hsucc
    simpa [n] using
      prec_iterateTDeriv_of_allComboRealRooted_succ_of_no_common
        hf.1 hf.2 hg.1 hg.2 hall hsucc heps hno
  -- Handoff note:
  -- With `natDegree_close_of_allComboRealRooted` now available earlier in this
  -- file, the remaining converse has a clean two-case split (for nonzero
  -- inputs): up to swapping, either `f.natDegree + 1 = g.natDegree` or
  -- `f.natDegree = g.natDegree`.
  --
  -- The `+1` case is the right next target because the orientation is forced:
  -- one only has to prove `Prec f g`, not an Obreschkoff alternative. In that
  -- branch, `hprec_iter` should also collapse to the left orientation by degree
  -- alone after rewriting `hdeg_iter` with `natDegree_iterateTDeriv_of_isRealRooted`.
  -- So the remaining `+1`-case gap is strictly narrower than the same-degree
  -- gap: transport
  --   `Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g)`
  -- back to
  --   `Prec f g`.
  --
  -- `hprec_iter` is now the fully regularized Obreschkoff conclusion for the
  -- simple `iterateTDeriv` pair. The remaining gap is *only* a transport step
  -- back to `(f, g)`. Two routes still look viable:
  -- 1. prove directly that `hall + hno` already forces every nonzero original
  --    combination `C α * f + C β * g` to have simple roots, then apply the
  --    helper theorem above to `(f, g)` itself and bypass `iterateTDeriv`;
  --    concretely, the target lemma is
  --    `∀ α β : ℝ,
  --        C α * f + C β * g = 0 ∨
  --          (((C α * f + C β * g) ≠ 0 ∧
  --            (C α * f + C β * g).Splits) ∧
  --            HasSimpleRoots (C α * f + C β * g))`.
  --    Once this is available, the endgame is exactly
  --    `prec_of_eq_zero_or_simple_combo_of_no_common hf hg hcombo_original hdeg hno`.
  -- 2. prove a closure / limit theorem saying that the orientation encoded by
  --    `hprec_iter` survives the `iterateTDeriv` regularization.
  --    In the succ-degree branch, the orientation issue is now resolved:
  --    `hsucc_iter_forced` packages the degree argument showing that the
  --    regularized pair cannot land in the reverse orientation. So the only
  --    missing succ-degree step is the transport
  --      `Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) -> Prec f g`.
  --    The new continuity primitives now live in `IteratedDerivativeShift`:
  --      * `iterateTDeriv_zero_eps`
  --      * `coeff_TDeriv`
  --      * `continuous_coeff_iterateTDeriv`
  --      * `continuousAt_coeff_iterateTDeriv_zero`
  --      * `continuous_eval_iterateTDeriv_joint`
  --      * `continuousAt_eval_iterateTDeriv_joint_zero`
  --      * `exists_delta_for_eval_iterateTDeriv_joint_at_zero`
  --      * `exists_delta_eval_mul_pos_iterateTDeriv_joint_at_zero`
  --      * `exists_delta_not_isRoot_iterateTDeriv_near_point`
  --      * `exists_delta_and_real_root_near_iterateTDeriv`
  --      * `exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted`
  --    So the clean next refactor is to stop fixing `eps := 1` here, keep
  --    `eps` symbolic, and combine those coefficientwise `ε → 0` facts with
  --    `RootContinuity`. The new non-monic nearby-root wrapper means the
  --    closure route can work after a one-time leading-coefficient/sign
  --    normalization, without rebuilding monic scaling inside the converse.
  --    For the slot-based variant of that closure route, the minimal public
  --    `CommonInterleaverSeq` API is now available as:
  --      * `polyOfDescRootsDesc`
  --      * `rootSeqDesc_polyOfDescRootsDesc_eq`
  --      * `mem_rootSlotInterval_of_prec_desc`
  --      * `rootSlot_lower_bound_of_mem`
  --      * `rootSlot_upper_bound_of_mem`
  --      * `prec_of_slots_polyOfDescRootsDesc`
  -- 3. reroute through the formalized right-family pair
  --    `(f + g, f + 2g)`: `allComboRealRooted_right_family_one_two` keeps us
  --    in the same Obreschkoff plane, and
  --    `no_common_root_right_family_one_two_of_no_common` keeps the no-common
  --    root hypothesis available for that basis change. The safe version of
  --    this route should first sign-normalize to positive leading coefficients;
  --    only then does the family reliably keep the top degree via
  --    `right_family_degree_data_of_posLeadingCoeff`. The key strict root-sign
  --    inputs are now also packaged:
  --    `eval_mul_right_family_one_neg_at_root_two_of_no_common` and
  --    `eval_mul_right_family_two_neg_at_root_one_of_no_common`.
  --    Concretely, the next Ma--Wang-style continuation to test is:
  --      a. scale `(f, g)` to positive-leading `(f₀, g₀)`;
  --      b. set `F := f₀ + g₀`, `G := f₀ + C (2 : ℝ) * g₀`;
  --      c. use `right_family_degree_data_of_posLeadingCoeff` to get the
  --         same-degree family bookkeeping;
  --      d. prove `Prec F G ∨ Prec G F`, then combine the two strict root-sign
  --         lemmas above with `prec_same_of_root_sign_data` / Ma--Wang to
  --         transport that orientation back to `Prec f₀ g₀ ∨ Prec g₀ f₀`;
  --      e. scale back to `(f, g)`.
  --    Important caveat: the tempting "pure subtraction" lemmas
  --      `Prec p q ↔ Prec p (q - p)` and `Prec p q ↔ Prec (p - q) q`
  --    are false for the current `Prec` API as stated; `prec_refl` already
  --    gives a counterexample by taking `p = q ≠ 0`, since then `q - p = 0`
  --    and `Prec p 0` does not hold. So this route still needs extra
  --    hypotheses/sign data, not just linear algebra on polynomials.
  --
  -- The new helper facts above also settle one normalization annoyance for the
  -- closure route: `iterateTDeriv` preserves leading coefficients exactly
  -- (`hlead_f_iter`, `hlead_g_iter`), hence preserves `HasPosLeadingCoeff`
  -- exactly (`hpos_f_iter`, `hpos_g_iter`). So if we sign-normalize `(f, g)`
  -- once, the entire regularized family keeps that normalization without any
  -- ε-dependent rescaling.
  --    The first two derived facts to keep in scope for that route are
  --    `have hall_family :
  --        AllComboRealRooted (f + g) (f + C (2 : ℝ) * g) :=
  --          allComboRealRooted_right_family_one_two hall`
  --    and
  --    `have hno_family :
  --        ∀ r, (f + g).IsRoot r → ¬ (f + C (2 : ℝ) * g).IsRoot r :=
  --          by simpa using no_common_root_right_family_one_two_of_no_common hno`.
  --
  -- Either route should finish this theorem without changing the Wronskian
  -- infrastructure above. Keeping `hprec_iter` explicit here should make it
  -- easier for another agent to pick up from the exact reduced goal.
  have hcombo_original :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (((C α * f + C β * g) ≠ 0 ∧ (C α * f + C β * g).Splits) ∧
            HasSimpleRoots (C α * f + C β * g)) := by
    by_cases hmax0 : max f.natDegree g.natDegree = 0
    · have hfdeg0 : f.natDegree = 0 := by simp_all
      have hgdeg0 : g.natDegree = 0 := by simp_all
      have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hfdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      intro α β
      by_cases hcomb : C α * f + C β * g = 0
      · lia
      · rw [hfC, hgC] at hcomb ⊢
        let c : ℝ := α * f.coeff 0 + β * g.coeff 0
        have hsum_eq :
            C α * C (f.coeff 0) + C β * C (g.coeff 0) =
              C c := by
          grind
        have hconst_ne : C c ≠ 0 := by
          lia
        have hcoeff_ne : c ≠ 0 := by
          grind
        have hnat0 :
            (C α * C (f.coeff 0) + C β * C (g.coeff 0)).natDegree = 0 := by
          rw [hsum_eq]
          simp
        right
        refine ⟨?_, ?_⟩
        · exact isRealRooted_of_deg_zero hcomb hnat0
        · rw [hsum_eq]
          intro r hr
          have : c = 0 := by
            simpa [Polynomial.IsRoot.def, c] using hr
          lia
    · have hmax_pos : 0 < max f.natDegree g.natDegree := Nat.pos_of_ne_zero hmax0
      have hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0 := by
        /-
        Reduced live frontier.

        The remaining converse contradiction now starts from the special-pair
        reduction above: if the Wronskian vanished at `x`, we could replace
        `(f, g)` inside the same `AllComboRealRooted` plane by a pair `(p, q)`
        with no common roots such that
        * `p` has a multiple root at `x`,
        * `q.eval x ≠ 0`.

        So the last missing theorem is now the explicit contradiction:
        such a pair cannot exist in the positive-degree/no-common-root regime.
        The keepalive facts above (`hprec_iter`, `hall_iter`, `hf_simple`,
        `hg_simple`, `hlead_*_iter`, `hpos_*_iter`, `hsucc_iter_forced`) are
        the intended ingredients for that final local argument.
        -/
        intro x hw
        obtain ⟨p, q, hp_def, hq_case, hpq_all, hpq_no, hp_root, hp_der_root, hq_eval_ne⟩ :=
          exists_special_pair_of_wronskian_zero hall hno hw
        have hq0 : q ≠ 0 := by
          lia
        have hq_rr : (q ≠ 0 ∧ q.Splits) := by
          lia
        have hp0 : p ≠ 0 := by
          rcases hq_case with ⟨hgx0, hqf⟩ | ⟨hgx_ne, hqg⟩
          · simp_all
          · intro hp0
            have hlin : C (g.eval x) * f + C (-f.eval x) * g = 0 := by
              lia
            by_cases hfx0 : f.eval x = 0
            · simp_all
            · by_cases hf_deg_pos : 0 < f.natDegree
              · exact
                  no_nontrivial_linear_relation_of_no_common_root
                    hf.1 hf.2 hno hf_deg_pos hgx_ne (neg_ne_zero.mpr hfx0) hlin
              · have hfdeg0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos hf_deg_pos
                rcases hdeg with hsucc | hsame
                · have hEq : C (g.eval x) * f = C (f.eval x) * g := by
                    grind
                  have hscalar : f = C (f.eval x / g.eval x) * g := by
                    ext n
                    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq
                    grind
                  have hdeg_eq : f.natDegree = g.natDegree := by
                    rw [hscalar, natDegree_C_mul (div_ne_zero hfx0 hgx_ne)]
                  lia
                · simp_all
        have hp_rr : (p ≠ 0 ∧ p.Splits) :=
          ⟨hp0, by simpa using hpq_all 1 0⟩
        have hq_not_root : ¬ q.IsRoot x := by
          simp_all
        have hp_mult_gt : 1 < p.rootMultiplicity x :=
          (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hp_root, hp_der_root⟩
        have hp_mult_ge2 : 2 ≤ p.rootMultiplicity x := by lia
        /-
        Final local contradiction.

        Instead of regularizing all the way to a simple pair and then passing
        slot data back to the limit, we now only iterate `T_ε` long enough to
        reduce the multiple root of `p` at `x` to an exact double root. For a
        sufficiently small shift parameter `η`, the companion polynomial
        `iterateTDeriv η (m - 2) q` still does not vanish at `x`, while
        `iterateTDeriv η (m - 2) p` has root multiplicity exactly `2` there.

        That exact double-root pair is impossible in an `AllComboRealRooted`
        plane: a small perturbation by the companion violates the standard
        second-derivative inequality for non-roots
        (`deriv2_mul_lt_deriv_sq_at_non_root`). So the original Wronskian-zero
        assumption was impossible.
        -/
        let m : ℕ := p.rootMultiplicity x
        let k : ℕ := m - 2
        obtain ⟨δ, hδ, hqk_not_root⟩ :=
          exists_delta_not_isRoot_iterateTDeriv_at_point k hq_not_root
        let η : ℝ := δ / 2
        have hη_pos : 0 < η := by
          grind
        have hη_small : ‖η‖ < δ := by
          have hη_norm : ‖η‖ = δ / 2 := by
            rw [Real.norm_eq_abs, show η = δ / 2 by lia, abs_of_pos hη_pos]
          simp_all
        have hqk_not_root_x : ¬ (iterateTDeriv η k q).IsRoot x := hqk_not_root hη_small
        have hqk_eval_ne : (iterateTDeriv η k q).eval x ≠ 0 := by
          simp_all
        have hk_le : k ≤ p.rootMultiplicity x := by
          lia
        have hpk_mult :
            (iterateTDeriv η k p).rootMultiplicity x = 2 := by
          calc
            (iterateTDeriv η k p).rootMultiplicity x = p.rootMultiplicity x - k :=
              rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hp_rr.1 hp_rr.2 hk_le
            _ = 2 := by
              lia
        have hpq_all_k :
            AllComboRealRooted (iterateTDeriv η k p) (iterateTDeriv η k q) :=
          allComboRealRooted_iterateTDeriv hpq_all hη_pos k
        exact
          false_of_allComboRealRooted_of_double_root_and_eval_ne
            hpq_all_k hpk_mult hqk_eval_ne
      exact
        combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
          hall hW_ne
  have htransport :
      (f.natDegree + 1 = g.natDegree → Prec f g) ∧
        (f.natDegree = g.natDegree → Prec f g ∨ Prec g f) := by
    constructor
    · intro hsucc
      have hprec_or :
          Prec f g ∨ Prec g f :=
        prec_of_eq_zero_or_simple_combo_of_no_common
          hf.1 hf.2 hg.1 hg.2 hcombo_original (Or.inl hsucc) hno
      exact prec_forward_of_orientation_of_succDegree hsucc.symm hprec_or
    · intro hsame
      exact
        prec_of_eq_zero_or_simple_combo_of_no_common
          hf.1 hf.2 hg.1 hg.2 hcombo_original (Or.inr hsame) hno
  lia

private theorem allComboRealRooted_of_prec_succDegree_pos
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    AllComboRealRooted f g := by
  let hfg_inter : Interlaces f g := hfg.toInterlaces hdeg
  intro α β
  by_cases hβ0 : β = 0
  · by_cases hα0 : α = 0
    · simp [hα0, hβ0]
    · have hrr : ((C α * f) ≠ 0 ∧ (C α * f).Splits) := isRealRooted_C_mul hfg.1.1 hfg.1.2 hα0
      simp_all
  · rcases lt_or_gt_of_ne hβ0 with hβneg | hβpos
    · by_cases hα_nonpos : α ≤ 0
      · have hrr_neg :
            ((C (-α) * f + C (-β) * g) ≠ 0 ∧ (C (-α) * f + C (-β) * g).Splits) :=
          isRealRooted_nonneg_combo_of_prec
            hfg hf_pos hg_pos
            (by simp_all) (by grind) (Or.inr (by simp_all))
        have hrr :
            ((C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        grind
      · have hαpos : 0 < α := lt_of_not_ge hα_nonpos
        have hmix_pos : HasPosLeadingCoeff (C (-β) * g + C (-α) * f) := by
          have hdeg_scaled :
              (C (-α) * f).natDegree < (C (-β) * g).natDegree := by
            rw [natDegree_C_mul (show -α ≠ 0 by grind),
              natDegree_C_mul (show -β ≠ 0 by simp_all)]
            lia
          exact
            hasPosLeadingCoeff_add_of_natDegree_lt_left
              hdeg_scaled
              (hasPosLeadingCoeff_C_mul (by simp_all) hg_pos)
        have hmix_deg :
            (C (-β) * g + C (-α) * f).natDegree = g.natDegree := by
          have hdeg_scaled :
              (C (-α) * f).natDegree < (C (-β) * g).natDegree := by
            rw [natDegree_C_mul (show -α ≠ 0 by grind),
              natDegree_C_mul (show -β ≠ 0 by simp_all)]
            lia
          calc
            (C (-β) * g + C (-α) * f).natDegree = (C (-β) * g).natDegree :=
              natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_scaled
                (hasPosLeadingCoeff_C_mul (by simp_all) hg_pos)
            _ = g.natDegree := by rw [natDegree_C_mul (by simp_all : (-β) ≠ 0)]
        have hrr_neg :
            ((C (-β) * g + C (-α) * f) ≠ 0 ∧ (C (-β) * g + C (-α) * f).Splits) := by
          have hmix_lo : g.natDegree ≤ (C (-β) * g + C (-α) * f).natDegree := by
            lia
          have hmix_hi : (C (-β) * g + C (-α) * f).natDegree ≤ g.natDegree + 1 := by
            lia
          have hprec_mix :
              Prec g (C (-β) * g + C (-α) * f) :=
            prec_of_interlaces_evalCoeff_nonpos
              (f := g) (g := f) (a := C (-β)) (b := C (-α))
              hfg_inter hf_pos hmix_pos
              hmix_lo hmix_hi
              (by
                intro r _
                simp
                grind)
          exact hprec_mix.2.1
        have hrr :
            ((C (-1 : ℝ) * (C (-β) * g + C (-α) * f)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-β) * g + C (-α) * f)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        simp_all
    · by_cases hα_nonneg : 0 ≤ α
      · by_cases hα0 : α = 0
        · have hrr : ((C β * g) ≠ 0 ∧ (C β * g).Splits) :=
            isRealRooted_C_mul hfg.2.1.1 hfg.2.1.2 hβ0
          simp_all
        · exact
            (isRealRooted_nonneg_combo_of_prec
              hfg hf_pos hg_pos hα_nonneg (le_of_lt hβpos)
              (Or.inr hβpos)).2
      · have hαneg : α < 0 := lt_of_not_ge hα_nonneg
        have hmix_pos : HasPosLeadingCoeff (C β * g + C α * f) := by
          have hdeg_scaled :
              (C α * f).natDegree < (C β * g).natDegree := by
            rw [natDegree_C_mul (show α ≠ 0 by grind), natDegree_C_mul hβ0]
            lia
          exact
            hasPosLeadingCoeff_add_of_natDegree_lt_left
              hdeg_scaled
              (hasPosLeadingCoeff_C_mul hβpos hg_pos)
        have hmix_deg :
            (C β * g + C α * f).natDegree = g.natDegree := by
          have hdeg_scaled :
              (C α * f).natDegree < (C β * g).natDegree := by
            rw [natDegree_C_mul (show α ≠ 0 by grind), natDegree_C_mul hβ0]
            lia
          calc
            (C β * g + C α * f).natDegree = (C β * g).natDegree :=
              natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_scaled
                (hasPosLeadingCoeff_C_mul hβpos hg_pos)
            _ = g.natDegree := by rw [natDegree_C_mul hβ0]
        have hmix_lo : g.natDegree ≤ (C β * g + C α * f).natDegree := by
          lia
        have hmix_hi : (C β * g + C α * f).natDegree ≤ g.natDegree + 1 := by
          lia
        have hprec_mix :
            Prec g (C β * g + C α * f) :=
          prec_of_interlaces_evalCoeff_nonpos
            (f := g) (g := f) (a := C β) (b := C α)
            hfg_inter hf_pos hmix_pos
            hmix_lo hmix_hi
            (by
              intro r _
              simp
              grind)
        simpa [add_comm, add_left_comm, add_assoc] using hprec_mix.2.1.2

private theorem allComboRealRooted_of_prec_succDegree
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    AllComboRealRooted f g := by
  have hf : (f ≠ 0 ∧ f.Splits) := hfg.1
  have hg : (g ≠ 0 ∧ g.Splits) := hfg.2.1
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by
    grind
  have hsg_ne : sg ≠ 0 := by
    grind
  have hsf_sq : sf * sf = 1 := by
    grind
  have hsg_sq : sg * sg = 1 := by
    grind
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
  have hfg₀ : Prec f₀ g₀ := prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree + 1 = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
  have hall₀ : AllComboRealRooted f₀ g₀ :=
    allComboRealRooted_of_prec_succDegree_pos hfg₀ hdeg₀ hf₀_pos hg₀_pos
  intro α β
  have hEq_f : C α * C sf * (C sf * f) = C α * f := by
    grind
  have hEq_g : C β * C sg * (C sg * g) = C β * g := by
    grind
  simpa [f₀, g₀, mul_assoc, hEq_f, hEq_g] using hall₀ (α * sf) (β * sg)

/-- To prove the same-degree forward direction of Obreschkoff, it is enough to
handle the no-common-roots case. Shared roots can be factored out recursively,
and `AllComboRealRooted` is rebuilt using
`allComboRealRooted_mul_common_factor`. This mirrors the converse reduction but
keeps the orientation fixed. -/
private theorem allComboRealRooted_of_prec_sameDegree_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        Prec f g →
        f.natDegree = g.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          Prec f g →
          f.natDegree = g.natDegree →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hfg hdeg
  intro n ih f g hfdeg hfg hdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · simp_all
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
    have hqf_ne : qf ≠ 0 :=
      right_ne_zero_of_mul (by simpa [hqf] using hfg.1.1)
    have hqg_ne : qg ≠ 0 :=
      right_ne_zero_of_mul (by simpa [hqg] using hfg.2.1.1)
    have hqdeg : qf.natDegree = qg.natDegree := by
      rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
        hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg
      lia
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf qg := by
      apply prec_of_prec_mul_X_sub_C_both r
      lia
    have hqhall : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl hprec_q hqdeg
    have hmul :
        AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hqhall
    lia

private lemma no_common_with_right_factor_quotient
    {f q : ℝ[X]} {uR : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ ((X - C uR) * q).IsRoot r) :
    ∀ r, f.IsRoot r → ¬ q.IsRoot r := by
  simp_all

private lemma root_lt_rightmost_of_prec_sameDegree_no_common
    {f g : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (huR_root : g.IsRoot uR)
    (huR_max : ∀ r ∈ g.roots, r ≤ uR)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → r < uR := by
  intro r hr
  have hr_le : r ≤ uR :=
    roots_le_of_prec_right hfg huR_max r ((mem_roots hfg.1.1).mpr hr)
  grind

private lemma prec_of_right_factor_combo_of_natDegree_ge
    {f q : ℝ[X]} {uR α β : ℝ}
    (hqf : Interlaces q f)
    (hq_pos : HasPosLeadingCoeff q)
    (hF_pos : HasPosLeadingCoeff (C α * f + C β * ((X - C uR) * q)))
    (hdeg_lo : f.natDegree ≤ (C α * f + C β * ((X - C uR) * q)).natDegree)
    (hq_no : ∀ r, f.IsRoot r → ¬ q.IsRoot r)
    (hroot_lt : ∀ r, f.IsRoot r → r < uR)
    (hβ : 0 < β) :
    Prec f (C α * f + C β * ((X - C uR) * q)) := by
  have hq_ne : q ≠ 0 := hqf.2.1.1
  have hbeta_term_eq :
      C β * ((X - C uR) * q) = (C β * (X - C uR)) * q := by
    grind
  have hdeg_hi :
      (C α * f + C β * ((X - C uR) * q)).natDegree ≤ f.natDegree + 1 := by
    have hsum_le :
        (C α * f + (C β * (X - C uR)) * q).natDegree ≤
          max (C α * f).natDegree (((C β * (X - C uR)) * q).natDegree) :=
      natDegree_add_le _ _
    have hscaled_le : (C α * f).natDegree ≤ f.natDegree := natDegree_C_mul_le α f
    have hbeta_term_deg : ((C β * (X - C uR)) * q).natDegree = f.natDegree := by
      rw [natDegree_mul
          (show C β * (X - C uR) ≠ 0 by
            exact mul_ne_zero (C_ne_zero.mpr hβ.ne') (X_sub_C_ne_zero uR))
          hq_ne]
      rw [natDegree_mul (C_ne_zero.mpr hβ.ne') (X_sub_C_ne_zero uR),
        natDegree_C, natDegree_X_sub_C]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hqf.2.2.1
    grind
  have hb_neg : ∀ r, f.IsRoot r → (C β * (X - C uR)).eval r < 0 := by
    intro r hr
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    have hru : r - uR < 0 := sub_neg.mpr (hroot_lt r hr)
    nlinarith
  have hF_pos' : HasPosLeadingCoeff (C α * f + (C β * (X - C uR)) * q) := by
    lia
  have hdeg_lo' : f.natDegree ≤ (C α * f + (C β * (X - C uR)) * q).natDegree := by
    lia
  have hprec :
      Prec f (C α * f + (C β * (X - C uR)) * q) :=
    prec_of_interlaces_evalCoeff_neg
      (f := f) (g := q) (a := C α) (b := C β * (X - C uR))
      hqf hq_pos hF_pos' hdeg_lo' (by lia) hq_no hb_neg
  lia

/-- A nonzero combination `α f + β (X - uR) q` with `β > 0` is real-rooted in
the same-degree/no-common-roots regime. This is the core right-factor reduction
used in the forward equal-degree Obreschkoff proof: depending on whether the
top coefficient cancels, the combination either becomes the left interlacer of
`f` or stays same-degree and is forced to be real-rooted by strict sign changes
plus one outer root. -/
private theorem isRealRooted_of_right_factor_combo_posβ
    {f q : ℝ[X]} {uR α β : ℝ}
    (hqf : Interlaces q f)
    (hq_pos : HasPosLeadingCoeff q)
    (hq_no : ∀ r, f.IsRoot r → ¬ q.IsRoot r)
    (hroot_lt : ∀ r, f.IsRoot r → r < uR)
    (hβ : 0 < β)
    (hF_ne : C α * f + C β * ((X - C uR) * q) ≠ 0)
    (hdeg_pos : 1 ≤ f.natDegree) :
    ((C α * f + C β * ((X - C uR) * q)) ≠ 0 ∧ (C α * f + C β * ((X - C uR) * q)).Splits) := by
  let F : ℝ[X] := C α * f + C β * ((X - C uR) * q)
  have hf : (f ≠ 0 ∧ f.Splits) := hqf.1
  have hq : (q ≠ 0 ∧ q.Splits) := hqf.2.1
  have hF_ne' : F ≠ 0 := by lia
  have hdeg_le : F.natDegree ≤ f.natDegree := by
    have hsum_le :
        F.natDegree ≤ max (C α * f).natDegree (C β * ((X - C uR) * q)).natDegree := by
      simpa [F] using natDegree_add_le (C α * f) (C β * ((X - C uR) * q))
    have hleft_le : (C α * f).natDegree ≤ f.natDegree := natDegree_C_mul_le α f
    have hright_eq : (C β * ((X - C uR) * q)).natDegree = f.natDegree := by
      rw [natDegree_C_mul hβ.ne', natDegree_mul (X_sub_C_ne_zero uR) hq.1, natDegree_X_sub_C]
      simpa [Nat.add_comm] using hqf.2.2.1
    simp_all
  have hroot_sign :
      ∀ r, f.IsRoot r → F.eval r * q.eval r < 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by
      simp_all
    have hq_eval_ne : q.eval r ≠ 0 := by
      simp_all
    have hru : r - uR < 0 := sub_neg.mpr (hroot_lt r hr)
    have hsq : 0 < (q.eval r) ^ 2 := sq_pos_iff.mpr hq_eval_ne
    have hcalc : F.eval r * q.eval r = β * (r - uR) * (q.eval r) ^ 2 := by
      dsimp [F]
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hf_eval,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hprod_neg : β * (r - uR) * (q.eval r) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ hru) hsq
    lia
  have hsign_core :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hrs_eq : (↑(f.roots.sort (· ≤ ·)) : Multiset ℝ) = f.roots := Multiset.sort_eq ..
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using
        Multiset.mem_coe.mpr (by simp_all : r₁ ∈ f.roots.sort (· ≤ ·))
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using
        Multiset.mem_coe.mpr (by simp_all : r₂ ∈ f.roots.sort (· ≤ ·))
    have hFq₁ : F.eval r₁ * q.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFq₂ : F.eval r₂ * q.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hqq : q.eval r₁ * q.eval r₂ < 0 :=
      eval_mul_eval_neg_of_interlaces_consecutive_of_no_common hqf hq_no pre hEq
    exact mul_neg_of_mul_neg_of_mul_neg hFq₁ hFq₂ hqq
  have hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    grind
  by_cases hdeg_lt : F.natDegree < f.natDegree
  · exact (interlaces_of_consecutive_signs_of_natDegree_lt hf.1 hf.2 hF_ne' hdeg_lt hsign).2.1
  · have hdeg_eq : F.natDegree = f.natDegree := by lia
    by_cases hdeg_one : f.natDegree = 1
    · have hF_deg_one : F.natDegree = 1 := by lia
      exact isRealRooted_of_degree_one hF_deg_one
    · have hdeg_two : 2 ≤ f.natDegree := by lia
      exact
        isRealRooted_of_interlaces_eval_mul_neg_same_any_lc
          hqf hq_pos hdeg_eq hdeg_two hroot_sign

/-- Positive-leading, no-common-roots equal-degree forward Obreschkoff. This is
the honest same-degree core: same-sign combinations are covered by Wagner
addition, while opposite-sign combinations are routed through the rightmost
root factorization `g = (X - C uR) * qg` and the helper
`isRealRooted_of_right_factor_combo_posβ`. -/
private theorem allComboRealRooted_of_prec_sameDegree_pos_of_no_common
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g := by
  have hf : (f ≠ 0 ∧ f.Splits) := hfg.1
  have hg : (g ≠ 0 ∧ g.Splits) := hfg.2.1
  by_cases hdeg0 : f.natDegree = 0
  · intro α β
    by_cases hcomb : C α * f + C β * g = 0
    · simp [hcomb]
    · have hgdeg0 : g.natDegree = 0 := by lia
      have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      rw [hfC, hgC] at hcomb ⊢
      have hsum_eq :
          C α * C (f.coeff 0) + C β * C (g.coeff 0) =
            C (α * f.coeff 0 + β * g.coeff 0) := by
        simp
      have hroots_eq :
          (C α * C (f.coeff 0) + C β * C (g.coeff 0)).roots =
            (C (α * f.coeff 0 + β * g.coeff 0)).roots := by
        lia
      have hnat_eq :
          (C α * C (f.coeff 0) + C β * C (g.coeff 0)).natDegree =
            (C (α * f.coeff 0 + β * g.coeff 0)).natDegree := by
        lia
      apply splits_of_card_roots
      rw [hroots_eq, hnat_eq, roots_C, natDegree_C]
      simp
  have hdeg_pos : 1 ≤ f.natDegree := by lia
  obtain ⟨uR, huR_root, huR_max⟩ :=
    exists_rightmost_root_of_isRealRooted hg.1 hg.2 (by lia)
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr huR_root
  have hqg_inter : Interlaces qg f :=
    interlaces_of_prec_sameDegree_rightmost_factor hfg hdeg huR_max hqg
  have hqg_no : ∀ r, f.IsRoot r → ¬ qg.IsRoot r := by
    simp_all
  have hroot_lt : ∀ r, f.IsRoot r → r < uR :=
    root_lt_rightmost_of_prec_sameDegree_no_common hfg huR_root huR_max hno
  have hqg_pos : HasPosLeadingCoeff qg := by
    apply hasPosLeadingCoeff_of_X_sub_C_mul (r := uR)
    simpa [hqg] using hg_pos
  intro α β
  by_cases hβ0 : β = 0
  · simp_all
  · rcases lt_or_gt_of_ne hβ0 with hβneg | hβpos
    · by_cases hα_nonpos : α ≤ 0
      · have hrr_neg :
          ((C (-α) * f + C (-β) * g) ≠ 0 ∧ (C (-α) * f + C (-β) * g).Splits) :=
        isRealRooted_nonneg_combo_of_prec
          hfg hf_pos hg_pos (by simp_all) (by grind) (Or.inr (by simp_all))
        have hrr :
            ((C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        grind
      · have hαpos : 0 < α := lt_of_not_ge hα_nonpos
        have hcomb_neg : C (-α) * f + C (-β) * g ≠ 0 :=
          fun hlin =>
            no_nontrivial_linear_relation_of_no_common_root
              hf.1 hf.2 hno (by lia) (neg_ne_zero.mpr hαpos.ne') (neg_ne_zero.mpr hβ0) hlin
        have hrr_neg :
            ((C (-α) * f + C (-β) * g) ≠ 0 ∧ (C (-α) * f + C (-β) * g).Splits) := by
          simpa [hqg] using
            isRealRooted_of_right_factor_combo_posβ
              (f := f) (q := qg) (uR := uR) (α := -α) (β := -β)
              hqg_inter hqg_pos hqg_no hroot_lt (by simp_all) (by lia)
              hdeg_pos
        have hrr :
            ((C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        grind
    · by_cases hα_nonneg : 0 ≤ α
      · exact
          (isRealRooted_nonneg_combo_of_prec
            hfg hf_pos hg_pos hα_nonneg (le_of_lt hβpos)
            (Or.inr hβpos)).2
      · have hαneg : α < 0 := lt_of_not_ge hα_nonneg
        have hcomb_pos : C α * f + C β * ((X - C uR) * qg) ≠ 0 := by
          intro hlin_q
          have hlin : C α * f + C β * g = 0 := by
            simpa [hqg] using hlin_q
          exact
            no_nontrivial_linear_relation_of_no_common_root
              hf.1 hf.2 hno (by lia) hαneg.ne hβpos.ne' hlin
        simpa [hqg] using
          (isRealRooted_of_right_factor_combo_posβ
            (f := f) (q := qg) (uR := uR) (α := α) (β := β)
            hqg_inter hqg_pos hqg_no hroot_lt hβpos hcomb_pos hdeg_pos).2

/-- Opposite-sign right-factor combinations are real-rooted even when the top
coefficient does not have the sign needed to orient a `Prec` witness directly.
The proof splits into the genuine degree-drop case, where the combination
becomes a left interlacer of `f`, and the same-degree case, where strict sign
changes plus one outer root are enough to force real-rootedness. -/
private theorem allComboRealRooted_of_prec_sameDegree
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    AllComboRealRooted f g := by
  refine allComboRealRooted_of_prec_sameDegree_of_no_common ?_ hfg hdeg
  intro f g hfg hdeg hno
  have hf : (f ≠ 0 ∧ f.Splits) := hfg.1
  have hg : (g ≠ 0 ∧ g.Splits) := hfg.2.1
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by
    grind
  have hsg_ne : sg ≠ 0 := by
    grind
  have hsf_sq : sf * sf = 1 := by
    grind
  have hsg_sq : sg * sg = 1 := by
    grind
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
  have hfg₀ : Prec f₀ g₀ := prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
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
  have hall₀ : AllComboRealRooted f₀ g₀ :=
    allComboRealRooted_of_prec_sameDegree_pos_of_no_common hfg₀ hdeg₀ hf₀_pos hg₀_pos hno₀
  intro α β
  have hEq_f : C α * C sf * (C sf * f) = C α * f := by
    grind
  have hEq_g : C β * C sg * (C sg * g) = C β * g := by
    grind
  simpa [f₀, g₀, mul_assoc, hEq_f, hEq_g] using hall₀ (α * sf) (β * sg)

/-- Forward direction of Obreschkoff: if `f ≪ g` then all real combinations
`αf + βg` are real-rooted (or zero). Follows from Wagner addition. -/
theorem allComboRealRooted_of_prec {f g : ℝ[X]}
    (hfg : Prec f g) :
    AllComboRealRooted f g := by
  have hdeg_bounds := natDegree_bounds_of_prec hfg
  have hdeg :
      f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by
    lia
  rcases hdeg with hsucc | hsame
  · exact allComboRealRooted_of_prec_succDegree hfg hsucc
  · exact allComboRealRooted_of_prec_sameDegree hfg hsame

/-- Differ-by-one case of the standard fact that differentiation preserves
oriented weak proper position.

The proof uses the forward Obreschkoff direction, differentiates the whole
two-dimensional span, and applies the converse.  In the differ-by-one case the
degree gap rules out the reversed orientation returned by the unoriented
converse. -/
theorem derivative_prec0_of_prec_succDegree {f g : ℝ[X]}
    (hfg : Prec f g) (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec0 f.derivative g.derivative := by
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.1.2 with hfzero | hfrr
  · rw [hfzero]
    exact prec0_zero_left _
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.2.1.2 with hgzero | hgrr
  · rw [hgzero]
    exact prec0_zero_right _
  have hall : AllComboRealRooted f.derivative g.derivative :=
    allComboRealRooted_derivative (allComboRealRooted_of_prec hfg)
  have hfdeg : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hfrr.1
  have hgdeg : g.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hgrr.1
  have hfgdeg' : f.derivative.natDegree + 1 = g.derivative.natDegree := by
    rw [f.natDegree_derivative, g.natDegree_derivative]
    lia
  have hdeg' : f.derivative.natDegree + 1 = g.derivative.natDegree ∨
      f.derivative.natDegree = g.derivative.natDegree := Or.inl hfgdeg'
  exact
    (prec_forward_of_orientation_of_succDegree hfgdeg'.symm
      (prec_of_allComboRealRooted hfrr.1 hfrr.2 hgrr.1 hgrr.2 hall hdeg')).toPrec0

/-- In the same-degree case, existing Obreschkoff machinery gives the
derivative pair in proper position up to orientation.  The remaining standard
input below is exactly the oriented branch selection. -/
theorem derivative_prec0_or_revPrec0_of_prec_sameDegree {f g : ℝ[X]}
    (hfg : Prec f g) (hdeg : f.natDegree = g.natDegree) :
    Prec0 f.derivative g.derivative ∨ Prec0 g.derivative f.derivative := by
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.1.2 with hfzero | hfrr
  · left
    rw [hfzero]
    exact prec0_zero_left _
  rcases derivative_eq_zero_or_ne_zero_and_splits hfg.2.1.2 with hgzero | hgrr
  · left
    rw [hgzero]
    exact prec0_zero_right _
  have hall : AllComboRealRooted f.derivative g.derivative :=
    allComboRealRooted_derivative (allComboRealRooted_of_prec hfg)
  have hfdeg : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hfrr.1
  have hgdeg : g.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hgrr.1
  have hdeg' : f.derivative.natDegree = g.derivative.natDegree := by
    rw [f.natDegree_derivative, g.natDegree_derivative]
    lia
  rcases prec_of_allComboRealRooted hfrr.1 hfrr.2 hgrr.1 hgrr.2 hall
    (Or.inr hdeg') with hprec | hrev
  · exact Or.inl hprec.toPrec0
  · exact Or.inr hrev.toPrec0

/-- For monic same-degree polynomials in proper position, the roots of the
derivatives have the same forward sum order. -/
theorem derivative_roots_sum_le_of_prec_sameDegree_monic {f g : ℝ[X]}
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hfg : Prec f g) (hdeg : f.natDegree = g.natDegree) (htwo : 2 ≤ f.natDegree)
    (hfder_splits : f.derivative.Splits) (hgder_splits : g.derivative.Splits) :
    f.derivative.roots.sum ≤ g.derivative.roots.sum := by
  have hg_two : 2 ≤ g.natDegree := by lia
  have hnext : g.nextCoeff ≤ f.nextCoeff :=
    nextCoeff_le_of_prec_sameDegree_monic hf_monic hg_monic hfg hdeg
  have hf_next_der :
      f.derivative.nextCoeff = (f.natDegree - 1 : ℝ) * f.nextCoeff :=
    Polynomial.nextCoeff_derivative_of_two_le_natDegree f htwo
  have hg_next_der :
      g.derivative.nextCoeff = (f.natDegree - 1 : ℝ) * g.nextCoeff := by
    simpa [hdeg] using Polynomial.nextCoeff_derivative_of_two_le_natDegree g hg_two
  have hfactor_nonneg : 0 ≤ (f.natDegree - 1 : ℝ) := by
    have hcast : (1 : ℝ) ≤ (f.natDegree : ℝ) := by
      simpa using
        (Nat.cast_le.mpr (by lia : 1 ≤ f.natDegree) :
          ((1 : Nat) : ℝ) ≤ (f.natDegree : ℝ))
    linarith
  have hnext_der : g.derivative.nextCoeff ≤ f.derivative.nextCoeff := by
    rw [hf_next_der, hg_next_der]
    exact mul_le_mul_of_nonneg_left hnext hfactor_nonneg
  have hf_lc_der : f.derivative.leadingCoeff = (f.natDegree : ℝ) := by
    simp [hf_monic.leadingCoeff]
  have hg_lc_der : g.derivative.leadingCoeff = (f.natDegree : ℝ) := by
    simp [hg_monic.leadingCoeff, hdeg]
  have hf_next_roots :
      f.derivative.nextCoeff = -(f.natDegree : ℝ) * f.derivative.roots.sum := by
    simpa [hf_lc_der] using hfder_splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hg_next_roots :
      g.derivative.nextCoeff = -(f.natDegree : ℝ) * g.derivative.roots.sum := by
    simpa [hg_lc_der] using hgder_splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hdeg_pos : 0 < (f.natDegree : ℝ) := by positivity
  nlinarith

/-- Same-degree branch of the standard fact that differentiation preserves
oriented weak proper position. -/
def derivativePreservesPrecSameDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → f.natDegree = g.natDegree →
    Prec0 f.derivative g.derivative

/-- Scaling both sides by nonzero constants preserves zero-aware proper
position. -/
private lemma prec0_C_mul_left_right {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {f g : ℝ[X]} (h : Prec0 f g) :
    Prec0 (C a * f) (C b * g) := by
  rcases h with rfl | rfl | hprec
  · simp [prec0_zero_left]
  · simp [prec0_zero_right]
  · exact (prec_C_mul_right (prec_C_mul_left hprec ha) hb).toPrec0

/-- Degree-zero polynomials satisfy `Prec` in both orientations. -/
lemma prec_degree_zero_degree_zero
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_deg0 : f.natDegree = 0) (hg_deg0 : g.natDegree = 0) :
    Prec f g := by
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [card_roots_of_splits hf_splits, hf_deg0]
  have hroots_g : g.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [card_roots_of_splits hg_splits, hg_deg0]
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, [], [], by simp, by simp, ?_, ?_, ?_⟩
  · simp [hroots_f]
  · simp [hroots_g]
  · exact Or.inr ⟨by lia, by simp [ListAlternates]⟩

/-- Degree-at-least-two same-degree branch of the standard fact that
differentiation preserves oriented weak proper position. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec0 f.derivative g.derivative

/-- Positive-leading-coefficient form of the degree-at-least-two same-degree
derivative-preservation branch. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreePosLeadingStatement : Prop :=
  ∀ {f g : ℝ[X]}, HasPosLeadingCoeff f → HasPosLeadingCoeff g →
    Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec0 f.derivative g.derivative

/-- Monic form of the degree-at-least-two same-degree derivative-preservation
branch. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement : Prop :=
  ∀ {f g : ℝ[X]}, f.Monic → g.Monic →
    Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec0 f.derivative g.derivative

/-- Strict-`Prec` monic form of the degree-at-least-two same-degree
derivative-preservation branch. -/
def derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicPrecStatement : Prop :=
  ∀ {f g : ℝ[X]}, f.Monic → g.Monic →
    Prec f g → f.natDegree = g.natDegree → 2 ≤ f.natDegree →
    Prec f.derivative g.derivative

/-- Monic degree-at-least-two same-degree branch of the standard fact that
differentiation preserves oriented weak proper position. -/
theorem derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonic :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement := by
  intro f g hf_monic hg_monic hfg hdeg htwo
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hdeg_der : f.derivative.natDegree = g.derivative.natDegree := by
    rw [f.natDegree_derivative, g.natDegree_derivative]
    lia
  rcases derivative_prec0_or_revPrec0_of_prec_sameDegree hfg hdeg with hprec0 | hrev0
  · exact hprec0
  · have hrev : Prec g.derivative f.derivative :=
      hrev0.toPrec_of_ne hgder_ne hfder_ne
    have hsum_der : f.derivative.roots.sum ≤ g.derivative.roots.sum :=
      derivative_roots_sum_le_of_prec_sameDegree_monic hf_monic hg_monic hfg hdeg htwo
        hrev.2.1.2 hrev.1.2
    exact (prec_of_reverse_prec_of_roots_sum_le hrev hdeg_der hsum_der).toPrec0

/-- The strict-`Prec` monic branch follows from the zero-aware monic branch,
since the degree hypotheses make both derivatives nonzero. -/
theorem derivativePreservesPrecSameDegree_monicPrec_of_monic
    (hmonic : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicPrecStatement := by
  intro f g hf_monic hg_monic hfg hdeg htwo
  have hfder_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hgder_ne : g.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  rcases hmonic hf_monic hg_monic hfg hdeg htwo with hfzero | hgzero | hprec
  · exact False.elim (hfder_ne hfzero)
  · exact False.elim (hgder_ne hgzero)
  · exact hprec

/-- The zero-aware monic branch follows from the strict-`Prec` monic branch. -/
theorem derivativePreservesPrecSameDegree_of_monicPrec
    (hmonic : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicPrecStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement :=
  fun {_ _} hf_monic hg_monic hfg hdeg htwo =>
    (hmonic hf_monic hg_monic hfg hdeg htwo).toPrec0

/-- The positive-leading-coefficient branch follows from the monic branch by
normalizing both polynomials by their leading coefficients. -/
theorem derivativePreservesPrecSameDegree_of_monic
    (hmonic : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeMonicStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreePosLeadingStatement := by
  intro f g hf_pos hg_pos hfg hdeg htwo
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hfg₀ : Prec f₀ g₀ :=
    prec_C_mul_right (prec_C_mul_left hfg (inv_ne_zero hf_lc_ne))
      (inv_ne_zero hg_lc_ne)
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul (inv_ne_zero hf_lc_ne),
      natDegree_C_mul (inv_ne_zero hg_lc_ne)] using hdeg
  have htwo₀ : 2 ≤ f₀.natDegree := by
    simpa [f₀, natDegree_C_mul (inv_ne_zero hf_lc_ne)] using htwo
  have hscaled : Prec0 f₀.derivative g₀.derivative :=
    hmonic hf₀_monic hg₀_monic hfg₀ hdeg₀ htwo₀
  have hscaled' :
      Prec0 (C f.leadingCoeff⁻¹ * f.derivative)
        (C g.leadingCoeff⁻¹ * g.derivative) := by
    simpa [f₀, g₀, derivative_C_mul] using hscaled
  have hback :
      Prec0 (C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f.derivative))
        (C g.leadingCoeff * (C g.leadingCoeff⁻¹ * g.derivative)) :=
    prec0_C_mul_left_right hf_lc_ne hg_lc_ne hscaled'
  have hf_inv :
      C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f.derivative) =
        f.derivative := by
    rw [← mul_assoc, ← C_mul]
    simp [hf_lc_ne]
  have hg_inv :
      C g.leadingCoeff * (C g.leadingCoeff⁻¹ * g.derivative) =
        g.derivative := by
    rw [← mul_assoc, ← C_mul]
    simp [hg_lc_ne]
  simpa [hf_inv, hg_inv] using hback

/-- The degree-at-least-two same-degree branch follows from its
positive-leading-coefficient form by scaling both polynomials by signs. -/
theorem derivativePreservesPrecSameDegree_of_posLeading
    (hpos :
      derivativePreservesPrecSameDegreeOfTwoLeNatDegreePosLeadingStatement) :
    derivativePreservesPrecSameDegreeOfTwoLeNatDegreeStatement := by
  intro f g hfg hdeg htwo
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfg.1.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfg.2.1.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by
    grind
  have hsg_ne : sg ≠ 0 := by
    grind
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hposf
    · lia
    · grind
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hposg
    · lia
    · grind
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
  have hfg₀ : Prec f₀ g₀ :=
    prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have htwo₀ : 2 ≤ f₀.natDegree := by
    simpa [f₀, natDegree_C_mul hsf_ne] using htwo
  have hscaled : Prec0 f₀.derivative g₀.derivative :=
    hpos hf₀_pos hg₀_pos hfg₀ hdeg₀ htwo₀
  have hscaled' : Prec0 (C sf * f.derivative) (C sg * g.derivative) := by
    simpa [f₀, g₀, derivative_C_mul] using hscaled
  have hback :
      Prec0 (C sf⁻¹ * (C sf * f.derivative))
        (C sg⁻¹ * (C sg * g.derivative)) :=
    prec0_C_mul_left_right (inv_ne_zero hsf_ne) (inv_ne_zero hsg_ne) hscaled'
  have hsf_inv : C sf⁻¹ * (C sf * f.derivative) = f.derivative := by
    grind
  have hsg_inv : C sg⁻¹ * (C sg * g.derivative) = g.derivative := by
    grind
  simpa [hsf_inv, hsg_inv] using hback

/-- The same-degree derivative-preservation statement follows from its
degree-at-least-two branch.  Degrees zero and one are elementary because the
derivatives are zero or nonzero constants. -/
theorem derivativePreservesPrecSameDegree_of_two_le_natDegree
    (hlarge : derivativePreservesPrecSameDegreeOfTwoLeNatDegreeStatement) :
    derivativePreservesPrecSameDegreeStatement := by
  intro f g hfg hdeg
  by_cases hlarge_deg : 2 ≤ f.natDegree
  · exact hlarge hfg hdeg hlarge_deg
  · by_cases hfdeg0 : f.natDegree = 0
    · have hfder : f.derivative = 0 :=
        Polynomial.derivative_eq_zero.mpr hfdeg0
      have hgdeg0 : g.natDegree = 0 := by
        lia
      have hgder : g.derivative = 0 :=
        Polynomial.derivative_eq_zero.mpr hgdeg0
      rw [hfder, hgder]
      exact prec0_zero_zero
    · have hfdeg1 : f.natDegree = 1 := by
        lia
      have hgdeg1 : g.natDegree = 1 := by
        lia
      have hfder_ne : f.derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr (by lia)
      have hgder_ne : g.derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr (by lia)
      have hfder_deg0 : f.derivative.natDegree = 0 := by
        rw [f.natDegree_derivative, hfdeg1]
      have hgder_deg0 : g.derivative.natDegree = 0 := by
        rw [g.natDegree_derivative, hgdeg1]
      have hfder_rr : (f.derivative ≠ 0 ∧ f.derivative.Splits) :=
        isRealRooted_of_deg_zero hfder_ne hfder_deg0
      have hgder_rr : (g.derivative ≠ 0 ∧ g.derivative.Splits) :=
        isRealRooted_of_deg_zero hgder_ne hgder_deg0
      exact
        (prec_degree_zero_degree_zero hfder_rr.1 hfder_rr.2 hgder_rr.1 hgder_rr.2
          hfder_deg0 hgder_deg0).toPrec0

/-- The full zero-aware derivative-preservation statement follows from the
same-degree branch.  The differ-by-one branch is
`derivative_prec0_of_prec_succDegree`, proved above from the forward and
converse Obreschkoff theorems. -/
theorem derivativePreservesPrec0_of_sameDegree
    (hsame : derivativePreservesPrecSameDegreeStatement) :
    derivativePreservesPrec0Statement := by
  intro f g hfg
  rcases hfg with hfzero | hgzero | hfg'
  · rw [hfzero, derivative_zero]
    exact prec0_zero_left _
  · rw [hgzero, derivative_zero]
    exact prec0_zero_right _
  · have hbounds := natDegree_bounds_of_prec hfg'
    by_cases hdeg : f.natDegree = g.natDegree
    · exact hsame hfg' hdeg
    · exact derivative_prec0_of_prec_succDegree hfg' (by lia)

end
end RealRooted
