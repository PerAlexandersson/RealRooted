import RealRooted.Basic.Coefficients
import RealRooted.Basic.ProperPosition
import RealRooted.Interlacing.OuterDifference
import RealRooted.MaWang.Strong
import RealRooted.SimpleRoots

/-!
# Strict root geometry for factorial compression

This module contains the stronger root-order package used internally by the
factorial-compression proofs.  The public theorems of the package are stated
with RealRooted's native `StrictInterl` interface; this package retains strict
root inequalities and no-common-root data only where the proofs need them.
-/

open Polynomial

noncomputable section

namespace RealRooted.FactorialCompression

/-- Root order (1.2), with the constant/linear base convention. -/
def StrictInterlacesRoots : List ℝ → List ℝ → Prop
  | [], [] => True
  | [], [_] => True
  | r :: rs, s₁ :: s₂ :: ss =>
      s₁ < r ∧ r < s₂ ∧ StrictInterlacesRoots rs (s₂ :: ss)
  | _, _ => False

/-- Root order (1.3). -/
def StrictAlternatesRoots : List ℝ → List ℝ → Prop
  | [], [] => True
  | r :: rs, s :: ss => r < s ∧ StrictInterlacesRoots rs (s :: ss)
  | _, _ => False

/-- A polynomial's complete root multiset consists of simple negative roots.
Splitting and nonzeroness exclude vacuous statements about missing real roots. -/
def SimpleNegativeRoots (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits ∧ p.roots.Nodup ∧ ∀ r ∈ p.roots, r < 0

/-- The strict oriented polynomial root orders in the manuscript.
The leading signs, splitting and strictly ordered full root lists are explicit. -/
def StrictRootInterl (f g : ℝ[X]) : Prop :=
  0 < f.leadingCoeff ∧ 0 < g.leadingCoeff ∧ f.Splits ∧ g.Splits ∧
    ∃ rs ss : List ℝ,
      rs.Pairwise (· < ·) ∧ ss.Pairwise (· < ·) ∧
      (↑rs : Multiset ℝ) = f.roots ∧ (↑ss : Multiset ℝ) = g.roots ∧
      ((rs.length + 1 = ss.length ∧ StrictInterlacesRoots rs ss) ∨
        (rs.length = ss.length ∧ StrictAlternatesRoots rs ss))

theorem strictInterlacesRoots_to_upstream :
    ∀ {rs ss : List ℝ}, StrictInterlacesRoots rs ss →
      RealRooted.ListInterlaces rs ss
  | [], [], _ => True.intro
  | [], [_], _ => True.intro
  | [], _ :: _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, [_], h => False.elim h
  | r :: rs, s₁ :: s₂ :: ss, h =>
      ⟨le_of_lt h.1, le_of_lt h.2.1,
        strictInterlacesRoots_to_upstream h.2.2⟩

theorem strictAlternatesRoots_to_upstream :
    ∀ {rs ss : List ℝ}, StrictAlternatesRoots rs ss →
      RealRooted.ListAlternates rs ss
  | [], [], _ => True.intro
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, _ :: _, h =>
      ⟨le_of_lt h.1, strictInterlacesRoots_to_upstream h.2⟩

private theorem head_le_of_pairwise_lt {a : ℝ} {as : List ℝ}
    (h : (a :: as).Pairwise (· < ·)) {x : ℝ} (hx : x ∈ a :: as) : a ≤ x := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · exact le_of_lt ((List.pairwise_cons.mp h).1 x hx)

private theorem strictInterlacesRoots_disjoint :
    ∀ {rs ss : List ℝ}, rs.Pairwise (· < ·) → ss.Pairwise (· < ·) →
      StrictInterlacesRoots rs ss → ∀ r ∈ rs, ∀ s ∈ ss, r ≠ s
  | [], _, _, _, _, _, hr, _, _ => by simp at hr
  | _ :: _, [], _, _, h, _, _, _, _ => False.elim h
  | _ :: _, [_], _, _, h, _, _, _, _ => False.elim h
  | r :: rs, s₁ :: s₂ :: ss, hrs, hss, h, x, hx, y, hy => by
      obtain ⟨hs₁r, hrs₂, htail⟩ := h
      have hrs_tail := (List.pairwise_cons.mp hrs).2
      have hss_tail := (List.pairwise_cons.mp hss).2
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact ne_of_gt hs₁r
        · exact ne_of_lt (lt_of_lt_of_le hrs₂ (head_le_of_pairwise_lt hss_tail hy))
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact ne_of_gt (lt_trans hs₁r ((List.pairwise_cons.mp hrs).1 x hx))
        · exact strictInterlacesRoots_disjoint hrs_tail hss_tail htail x hx y hy

private theorem strictAlternatesRoots_disjoint {rs ss : List ℝ}
    (hrs : rs.Pairwise (· < ·)) (hss : ss.Pairwise (· < ·))
    (h : StrictAlternatesRoots rs ss) : ∀ r ∈ rs, ∀ s ∈ ss, r ≠ s := by
  cases rs with
  | nil => simp
  | cons r rs =>
      cases ss with
      | nil => exact False.elim h
      | cons s ss =>
          obtain ⟨hrs₀, htail⟩ := h
          intro x hx y hy
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ne_of_lt (lt_of_lt_of_le hrs₀ (head_le_of_pairwise_lt hss hy))
          · exact strictInterlacesRoots_disjoint (List.pairwise_cons.mp hrs).2 hss
              htail x hx y hy

private theorem strictInterlacesRoots_of_upstream :
    ∀ {rs ss : List ℝ}, RealRooted.ListInterlaces rs ss →
      (∀ r ∈ rs, ∀ s ∈ ss, r ≠ s) → StrictInterlacesRoots rs ss
  | [], [], _, _ => True.intro
  | [], [_], _, _ => True.intro
  | [], _ :: _ :: _, h, _ => False.elim h
  | _ :: _, [], h, _ => False.elim h
  | _ :: _, [_], h, _ => False.elim h
  | r :: rs, s₁ :: s₂ :: ss, h, hne => by
      refine ⟨lt_of_le_of_ne h.1 ?_, lt_of_le_of_ne h.2.1 ?_, ?_⟩
      · exact (hne r (by simp) s₁ (by simp)).symm
      · exact hne r (by simp) s₂ (by simp)
      · exact strictInterlacesRoots_of_upstream h.2.2 (by
          intro r hr s hs
          exact hne r (by simp [hr]) s (by simp [hs]))

private theorem strictAlternatesRoots_of_upstream :
    ∀ {rs ss : List ℝ}, RealRooted.ListAlternates rs ss →
      (∀ r ∈ rs, ∀ s ∈ ss, r ≠ s) → StrictAlternatesRoots rs ss
  | [], [], _, _ => True.intro
  | [], _ :: _, h, _ => False.elim h
  | _ :: _, [], h, _ => False.elim h
  | r :: rs, s :: ss, h, hne => by
      refine ⟨lt_of_le_of_ne h.1 (hne r (by simp) s (by simp)), ?_⟩
      exact strictInterlacesRoots_of_upstream h.2 (by
        intro r hr s hs
        exact hne r (by simp [hr]) s hs)

theorem StrictRootInterl.toStrictInterl {f g : ℝ[X]}
    (h : StrictRootInterl f g) : RealRooted.StrictInterl f g := by
  obtain ⟨hfpos, hgpos, hfsplits, hgsplits, rs, ss, hrs, hss, hre, hse, hshape⟩ := h
  refine ⟨⟨RealRooted.HasPosLeadingCoeff.ne_zero hfpos, hfsplits⟩,
    ⟨RealRooted.HasPosLeadingCoeff.ne_zero hgpos, hgsplits⟩,
    rs, ss, hrs.imp le_of_lt, hss.imp le_of_lt, hre, hse, ?_⟩
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, hint⟩
  · exact Or.inl ⟨hlen, strictInterlacesRoots_to_upstream hint⟩
  · exact Or.inr ⟨hlen, strictAlternatesRoots_to_upstream hint⟩

theorem StrictRootInterl.noCommonRoot {f g : ℝ[X]}
    (h : StrictRootInterl f g) : ∀ x, f.IsRoot x → ¬ g.IsRoot x := by
  obtain ⟨hfpos, hgpos, hfsplits, hgsplits, rs, ss, hrs, hss, hre, hse, hshape⟩ := h
  have hfne : f ≠ 0 := RealRooted.HasPosLeadingCoeff.ne_zero hfpos
  have hgne : g ≠ 0 := RealRooted.HasPosLeadingCoeff.ne_zero hgpos
  have hdisj : ∀ r ∈ rs, ∀ s ∈ ss, r ≠ s := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, hint⟩
    · exact strictInterlacesRoots_disjoint hrs hss hint
    · exact strictAlternatesRoots_disjoint hrs hss hint
  intro x hfx hgx
  have hxr : x ∈ rs := by
    apply Multiset.mem_coe.mp
    rw [hre]
    exact (Polynomial.mem_roots hfne).mpr hfx
  have hxs : x ∈ ss := by
    apply Multiset.mem_coe.mp
    rw [hse]
    exact (Polynomial.mem_roots hgne).mpr hgx
  exact hdisj x hxr x hxs rfl

theorem strictRootInterl_of_strictInterl_of_noCommonRoot {f g : ℝ[X]}
    (h : RealRooted.StrictInterl f g) (hfpos : 0 < f.leadingCoeff)
    (hgpos : 0 < g.leadingCoeff) (hno : ∀ x, ¬ (f.IsRoot x ∧ g.IsRoot x)) :
    StrictRootInterl f g := by
  have hsimp := h.hasSimpleRoots_of_no_common_root hno
  obtain ⟨hf, hg, rs, ss, hrs, hss, hre, hse, hshape⟩ := h
  have hrnd : rs.Nodup := Multiset.coe_nodup.mp (by rw [hre]; exact hsimp.1.roots_nodup)
  have hsnd : ss.Nodup := Multiset.coe_nodup.mp (by rw [hse]; exact hsimp.2.roots_nodup)
  have hdisj : ∀ r ∈ rs, ∀ s ∈ ss, r ≠ s := by
    intro r hr s hs heq
    subst s
    have hfr : f.IsRoot r := (Polynomial.mem_roots hf.1).mp (by
      rw [← hre]; exact Multiset.mem_coe.mpr hr)
    have hgr : g.IsRoot r := (Polynomial.mem_roots hg.1).mp (by
      rw [← hse]; exact Multiset.mem_coe.mpr hs)
    exact hno r ⟨hfr, hgr⟩
  refine ⟨hfpos, hgpos, hf.2, hg.2, rs, ss,
    (hrs.sortedLE.sortedLT_of_nodup hrnd).pairwise,
    (hss.sortedLE.sortedLT_of_nodup hsnd).pairwise, hre, hse, ?_⟩
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, hint⟩
  · exact Or.inl ⟨hlen, strictInterlacesRoots_of_upstream hint hdisj⟩
  · exact Or.inr ⟨hlen, strictAlternatesRoots_of_upstream hint hdisj⟩

theorem StrictRootInterl.noCommonRootPair {f g : ℝ[X]}
    (h : StrictRootInterl f g) : ∀ r, ¬ (f.IsRoot r ∧ g.IsRoot r) :=
  fun r hr => h.noCommonRoot r hr.1 hr.2

theorem StrictRootInterl.hasSimpleRoots {f g : ℝ[X]}
    (h : StrictRootInterl f g) :
    RealRooted.HasSimpleRoots f ∧ RealRooted.HasSimpleRoots g :=
  h.toStrictInterl.hasSimpleRoots_of_no_common_root h.noCommonRootPair

theorem SimpleNegativeRoots.hasSimpleRoots {p : ℝ[X]} (h : SimpleNegativeRoots p) :
    RealRooted.HasSimpleRoots p :=
  RealRooted.HasSimpleRoots.of_roots_nodup h.1 h.2.2.1

/-- Manuscript Lemma 2.1, with its full strict oriented conclusion. -/
theorem root_sign_criterion {f g : ℝ[X]}
    (hf : SimpleNegativeRoots f) (hflc : 0 < f.leadingCoeff)
    (hd : 0 < f.natDegree) (hg : RealRooted.HasNonnegCoeffs g)
    (hg0 : 0 < g.coeff 0) (hglc : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1)
    (hsign : ∀ r, f.IsRoot r → g.eval r / f.derivative.eval r < 0) :
    SimpleNegativeRoots g ∧ StrictRootInterl f g := by
  have hfder := RealRooted.interlaces_derivative_of_pos_natDegree hf.1 hf.2.1 hflc
    (by lia)
  have hfderpos : RealRooted.HasPosLeadingCoeff f.derivative :=
    RealRooted.HasPosLeadingCoeff.derivative hflc (by lia)
  have hprod : ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0 := by
    intro r hr
    exact mul_neg_iff.mpr (div_neg_iff.mp (hsign r hr))
  have hweak : RealRooted.StrictInterl f g := by
    rcases hdeg with hsame | hsucc
    · exact RealRooted.strictInterl_of_interlaces_eval_mul_neg_same
        hfder hfderpos hglc hsame hprod
    · exact RealRooted.strictInterl_of_interlaces_eval_mul_neg_succ
        hfder hfderpos hglc hsucc hprod
  have hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hneg := hprod r hr
    rw [Polynomial.IsRoot.def.mp hgr, zero_mul] at hneg
    exact (lt_irrefl 0) hneg
  have hsimple := (hweak.hasSimpleRoots_of_no_common_root
    (fun r hr => hno r hr.1 hr.2)).2
  refine ⟨⟨hweak.2.1.1, hweak.2.1.2, hsimple.roots_nodup, ?_⟩,
    strictRootInterl_of_strictInterl_of_noCommonRoot hweak hflc hglc
      (fun r hr => hno r hr.1 hr.2)⟩
  intro r hr
  have hrle : r ≤ 0 := RealRooted.roots_nonpos_of_hasNonnegCoeffs hg r hr
  refine lt_of_le_of_ne hrle ?_
  intro hrzero
  have hroot : g.IsRoot r := (Polynomial.mem_roots hweak.2.1.1).mp hr
  have hgzero : g.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [hrzero] using Polynomial.IsRoot.def.mp hroot
  linarith

/-- Equation (2.1), at a root of the left polynomial. -/
theorem StrictRootInterl.leftRootRatio_neg {f g : ℝ[X]}
    (h : StrictRootInterl f g) {r : ℝ} (hr : f.IsRoot r) :
    g.eval r / f.derivative.eval r < 0 := by
  have hp := h.toStrictInterl.eval_mul_derivative_neg_of_left_root_of_no_common
    h.1 h.2.1 h.noCommonRoot hr
  exact (div_neg_iff).mpr (mul_neg_iff.mp hp)

/-- Equation (2.1), at a root of the right polynomial. -/
theorem StrictRootInterl.rightRootRatio_pos {f g : ℝ[X]}
    (h : StrictRootInterl f g) {s : ℝ} (hs : g.IsRoot s) :
    0 < f.eval s / g.derivative.eval s := by
  have hp := h.toStrictInterl.eval_mul_derivative_pos_of_right_root_of_no_common
    h.1 h.2.1 h.noCommonRoot hs
  exact (div_pos_iff).mpr (mul_pos_iff.mp hp)

theorem SimpleNegativeRoots.C_mul {p : ℝ[X]} (hp : SimpleNegativeRoots p)
    {a : ℝ} (ha : a ≠ 0) : SimpleNegativeRoots (C a * p) := by
  refine ⟨mul_ne_zero (C_ne_zero.mpr ha) hp.1, hp.2.1.C_mul a, ?_, ?_⟩
  · simpa [roots_C_mul p ha] using hp.2.2.1
  · simpa [roots_C_mul p ha] using hp.2.2.2

theorem StrictRootInterl.C_mul {f g : ℝ[X]}
    (hfg : StrictRootInterl f g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictRootInterl (C a * f) (C b * g) := by
  rcases hfg with ⟨hfpos, hgpos, hfs, hgs, rs, ss, hrs, hss, hrf, hsg, horder⟩
  refine ⟨?_, ?_, hfs.C_mul a, hgs.C_mul b, rs, ss, hrs, hss, ?_, ?_, horder⟩
  · simpa [leadingCoeff_mul] using mul_pos ha hfpos
  · simpa [leadingCoeff_mul] using mul_pos hb hgpos
  · simpa [roots_C_mul f ha.ne'] using hrf
  · simpa [roots_C_mul g hb.ne'] using hsg

end RealRooted.FactorialCompression
