/-
# Shift lemma for interlacing polynomials

If `f` and `h` have nonpositive real roots, positive leading coefficients,
`h ≪ f`, and `h(0) ≤ f(0)`, then

  `f ≪ f + (X - 1) * h`.

This module was promoted from the peak-polynomial project so that other
real-rootedness projects can use the same `(X - 1)` shift step.
-/
import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Wagner
import RealRooted.MaWang
import RealRooted.ConvexCombination

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Evaluation helper -/

/-- At a root `r` of `f`, the shift combination evaluates to `(r - 1) * h(r)`. -/
lemma eval_shift_at_root {f h : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f + (X - C 1) * h).eval r = (r - 1) * h.eval r := by
  simp [eval_add, eval_mul, eval_sub, eval_X, IsRoot.def.mp hr]

/-! ## Differ-by-one case via Ma-Wang -/

/-- The shift lemma when `h` has degree one less than `f`. -/
theorem prec_shift_of_interlaces
    {f h : ℝ[X]}
    (hinterl : Interlaces h f)
    (hh_pos : HasPosLeadingCoeff h)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_pos : HasPosLeadingCoeff (f + (X - C 1) * h))
    (hdeg_lo : f.natDegree ≤ (f + (X - C 1) * h).natDegree)
    (hdeg_hi : (f + (X - C 1) * h).natDegree ≤ f.natDegree + 1) :
    Prec f (f + (X - C 1) * h) := by
  have hrewrite : f + (X - C 1) * h = C 1 * f + (X - C 1) * h := by simp [map_one]
  rw [hrewrite]
  refine prec_of_interlaces_evalCoeff_nonpos hinterl hh_pos (by lia) (by lia) (by lia) ?_
  intro r hr
  simp [eval_sub, eval_X]
  have hf_ne : f ≠ 0 := hinterl.1.1
  linarith [hf_nonpos r ((mem_roots hf_ne).mpr hr)]

/-! ## Degree and leading-coefficient lemmas for the shift combination -/

/-- Multiplication by `X - 1` raises the degree by one. -/
private lemma natDegree_X_sub_one_mul {h : ℝ[X]} (hh_ne : h ≠ 0) :
    ((X - C 1) * h).natDegree = h.natDegree + 1 := by
  rw [natDegree_mul (X_sub_C_ne_zero 1) hh_ne, natDegree_X_sub_C]
  lia

lemma shift_natDegree_of_interlaces {f h : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hh_pos : HasPosLeadingCoeff h)
    (hdeg : h.natDegree + 1 = f.natDegree)
    (hh_ne : h ≠ 0) :
    (f + (X - C 1) * h).natDegree = f.natDegree ∧
    HasPosLeadingCoeff (f + (X - C 1) * h) := by
  have hXh_deg : ((X - C 1) * h).natDegree = f.natDegree := by
    rw [natDegree_X_sub_one_mul hh_ne]
    lia
  have hXh_pos := hasPosLeadingCoeff_X_sub_C_mul (r := (1 : ℝ)) hh_pos
  constructor
  · exact natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
      hXh_deg.symm hf_pos hXh_pos
  · exact hasPosLeadingCoeff_add_of_same_natDegree
      hXh_deg.symm hf_pos hXh_pos

/-- When `deg h = deg f`, the shift combination has degree `deg f + 1`. -/
lemma shift_natDegree_of_same_degree {f h : ℝ[X]}
    (hh_pos : HasPosLeadingCoeff h)
    (hdeg : h.natDegree = f.natDegree)
    (hh_ne : h ≠ 0) :
    (f + (X - C 1) * h).natDegree = f.natDegree + 1 ∧
    HasPosLeadingCoeff (f + (X - C 1) * h) := by
  have hXh_deg : ((X - C 1) * h).natDegree = f.natDegree + 1 := by
    rw [natDegree_X_sub_one_mul hh_ne, hdeg]
  have hXh_pos := hasPosLeadingCoeff_X_sub_C_mul (r := (1 : ℝ)) hh_pos
  have hlt : f.natDegree < ((X - C 1) * h).natDegree := by lia
  constructor
  · exact natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hlt hXh_pos ▸ hXh_deg
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_right hlt hXh_pos

/-! ## Same-degree case -/

/-- The shift lemma when `h` and `f` have the same degree. -/
theorem prec_shift_of_same_degree
    {f h : ℝ[X]}
    (hprec : Prec h f)
    (hdeg : h.natDegree = f.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hh_pos : HasPosLeadingCoeff h)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hh_nonpos : ∀ r ∈ h.roots, r ≤ 0)
    (heval : h.eval 0 ≤ f.eval 0) :
    Prec f (f + (X - C 1) * h) := by
  let t : ℝ[X] := (X - C 1) * h
  have hf_le_one : ∀ r ∈ f.roots, r ≤ (1 : ℝ) := by grind
  have hh_le_one : ∀ r ∈ h.roots, r ≤ (1 : ℝ) := by grind
  have hft : Prec f t := by
    let h' := h.comp (X + C 1)
    let f' := f.comp (X + C 1)
    have hh' : (h' ≠ 0 ∧ h'.Splits) := by
      simpa [h'] using isRealRooted_comp_X_add_C hprec.1.1 hprec.1.2 1
    have hf' : (f' ≠ 0 ∧ f'.Splits) := by
      simpa [f'] using isRealRooted_comp_X_add_C hprec.2.1.1 hprec.2.1.2 1
    have hh'_nonpos : ∀ s ∈ h'.roots, s ≤ 0 := by
      intro s hs
      simp only [h', roots_comp_X_add_C 1] at hs
      rcases Multiset.mem_map.mp hs with ⟨u, hu, rfl⟩
      simp_all
    have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
      intro s hs
      simp only [f', roots_comp_X_add_C 1] at hs
      rcases Multiset.mem_map.mp hs with ⟨u, hu, rfl⟩
      simp_all
    have hdeg' : h'.natDegree = f'.natDegree := by
      have hdeg_mul :=
        congrArg (fun n => n * (X + C (1 : ℝ)).natDegree) hdeg
      simpa [h', f', natDegree_comp] using hdeg_mul
    have hprec' : Prec h' f' := by
      simpa [h', f'] using (prec_comp_X_add_C_iff (f := h) (g := f) 1).2 hprec
    have hfX' : Prec f' (X * h') :=
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos hprec' hdeg' hh'_nonpos hf'_nonpos
    have htranslated : Prec f' (t.comp (X + C 1)) := by
      simpa [t, h', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using hfX'
    exact (prec_comp_X_add_C_iff (f := f) (g := t) 1).1 <| by
      lia
  have ht_pos : HasPosLeadingCoeff t := by
    simpa [t] using hasPosLeadingCoeff_X_sub_C_mul (r := (1 : ℝ)) hh_pos
  have hsum : Prec f ([f, t].sum) := by
    apply prec_sum_left_of_common_left_signed
    · intro p hp
      have hp' : p = f ∨ p = t := by simp_all
      rcases hp' with rfl | rfl
      · exact prec_refl hprec.2.1.1 hprec.2.1.2
      · lia
    · simp_all
    · lia
  grind

/-! ## Main shift lemma -/

/-- **Shift lemma.**

If `f` and `h` are real-rooted with nonpositive roots and positive leading
coefficients, `h ≪ f`, and `h(0) ≤ f(0)`, then
`f ≪ f + (X - 1) * h`.
-/
theorem prec_shift
    {f h : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hh_ne : h ≠ 0) (hh_splits : h.Splits)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hh_nonpos : ∀ r ∈ h.roots, r ≤ 0)
    (hf_pos : HasPosLeadingCoeff f)
    (hh_pos : HasPosLeadingCoeff h)
    (hprec : Prec h f)
    (heval : h.eval 0 ≤ f.eval 0) :
    Prec f (f + (X - C 1) * h) := by
  obtain ⟨_, _, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = h.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hh_splits]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  rcases hshape with ⟨hdiffby1, hint⟩ | ⟨hsamedeg, halt⟩
  · have hdeg : h.natDegree + 1 = f.natDegree := by lia
    have hinterl : Interlaces h f :=
      Prec.toInterlaces ⟨⟨hh_ne, hh_splits⟩, ⟨hf_ne, hf_splits⟩, ss, rs, hss_sorted,
        hrs_sorted, hss_eq, hrs_eq, Or.inl ⟨hdiffby1, hint⟩⟩ hdeg
    obtain ⟨hndeg, hpos⟩ := shift_natDegree_of_interlaces hf_pos hh_pos hdeg hh_ne
    exact prec_shift_of_interlaces hinterl hh_pos hf_nonpos hpos
      (by lia) (by lia)
  · have hdeg : h.natDegree = f.natDegree := by lia
    exact prec_shift_of_same_degree
      ⟨⟨hh_ne, hh_splits⟩, ⟨hf_ne, hf_splits⟩, ss, rs, hss_sorted, hrs_sorted,
        hss_eq, hrs_eq, Or.inr ⟨hsamedeg, halt⟩⟩
      hdeg hf_pos hh_pos hf_nonpos hh_nonpos heval

/-- Shift lemma with variables named for applications. -/
theorem prec_shift' {F H : ℝ[X]}
    (hF_ne : F ≠ 0) (hF_splits : F.Splits) (hH_ne : H ≠ 0) (hH_splits : H.Splits)
    (hF_nonpos : ∀ r ∈ F.roots, r ≤ 0)
    (hH_nonpos : ∀ r ∈ H.roots, r ≤ 0)
    (hF_pos : HasPosLeadingCoeff F)
    (hH_pos : HasPosLeadingCoeff H)
    (hinterl : Prec H F)
    (heval : H.eval 0 ≤ F.eval 0) :
    Prec F (F + (X - C 1) * H) :=
  prec_shift hF_ne hF_splits hH_ne hH_splits hF_nonpos hH_nonpos hF_pos hH_pos hinterl heval

end RealRooted
