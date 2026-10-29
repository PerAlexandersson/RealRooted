module

import RealRooted.Transforms.BrandenE.IntervalPreserver
public import RealRooted.Transforms.BrandenE.BasisImage
import RealRooted.Transforms.BrandenE.Inverse
import RealRooted.DerivativeRecurrence.RootWindow
import RealRooted.MaWang.Weak.Endpoint
import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.FiniteFreeRootCount

/-!
# Brändén's E transform preserves rootwise order as interlacing

P. Brändén, *On linear transformations preserving the Pólya frequency property*,
Trans. Amer. Math. Soc. 358 (2006), arXiv:math/0403364, Theorem 4.6: if `f` and `g` are monic of
the same positive degree, have all roots in `[-1, 0]`, and their sorted roots satisfy
`f ≤ g` coordinatewise (`RootwiseLE`), then `brandenE f` and `brandenE g` interlace
(`brandenE_strictInterl_of_rootwiseLE`).

The proof follows Brändén: the oriented one-root replacement step
`brandenE_strictInterl_one_root_replacement` (which needs no interval hypothesis on the moved
root), applied along a chain of root multisets from all roots `-1` through `f` and `g` to all
roots `0`, closed by the endpoint relation `brandenBasisImage_endpoint_strictInterl` and
`strictInterl_chain_of_consecutive_of_endpoint`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The `E` transform of a root polynomial is nonzero. -/
lemma brandenE_rootPolynomial_ne_zero (s : Multiset ℝ) :
    brandenE (rootPolynomial s) ≠ 0 := by
  intro hzero
  apply rootPolynomial_ne_zero s
  apply brandenE_injective (R := ℝ)
  simpa using hzero

/-- The `E` transform converts adjoining a root into an Euler step. -/
lemma brandenE_rootPolynomial_cons (r : ℝ) (s : Multiset ℝ) :
    brandenE (rootPolynomial (r ::ₘ s)) =
      brandenEulerStep (-r) (brandenE (rootPolynomial s)) := by
  rw [rootPolynomial, Multiset.map_cons, Multiset.prod_cons]
  rw [show X - C r = X + C (-r) by rw [map_neg]; ring]
  change brandenE ((X + C (-r)) * rootPolynomial s) = _
  rw [brandenE_mul_X_add_C]
  rfl

/-- Oriented difference identity for replacing one linear root factor. -/
lemma brandenE_one_root_difference (h : ℝ[X]) (alpha beta : ℝ) :
    brandenE ((X - C beta) * h) =
      brandenE ((X - C alpha) * h) - C (beta - alpha) * brandenE h := by
  rw [show X - C beta = X + C (-beta) by rw [map_neg]; ring,
    show X - C alpha = X + C (-alpha) by rw [map_neg]; ring,
    brandenE_mul_X_add_C, brandenE_mul_X_add_C]
  rw [show C (-beta) = -C beta by simp,
    show C (-alpha) = -C alpha by simp,
    show C (beta - alpha) = C beta - C alpha by simp]
  ring

/-- The `E` transform preserves the degree and positive leading coefficient
of a monic root polynomial. -/
lemma brandenE_rootPolynomial_degree_pos (s : Multiset ℝ) :
    (brandenE (rootPolynomial s)).natDegree = s.card ∧
      HasPosLeadingCoeff (brandenE (rootPolynomial s)) := by
  induction s using Multiset.induction_on with
  | empty =>
      have he : brandenE (rootPolynomial (0 : Multiset ℝ)) = 1 := by
        rw [show rootPolynomial (0 : Multiset ℝ) = 1 by rfl]
        rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
        rfl
      rw [he]
      constructor
      · simp
      · exact hasPosLeadingCoeff_one
  | @cons a s ih =>
      rw [brandenE_rootPolynomial_cons]
      simpa using brandenEulerStep_degree_pos (r := -a) ih.2 ih.1

/-- If the source roots lie in `[-1, 0]`, the roots of its `E` transform
also lie above `-1`. -/
theorem brandenE_rootPolynomial_roots_ge_neg_one :
    ∀ (s : Multiset ℝ),
      (∀ r ∈ s, (-1 : ℝ) ≤ r ∧ r ≤ 0) →
      ∀ r ∈ (brandenE (rootPolynomial s)).roots, (-1 : ℝ) ≤ r := by
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      intro hs r hr
      have he : brandenE (rootPolynomial (0 : Multiset ℝ)) = 1 := by
        rw [show rootPolynomial (0 : Multiset ℝ) = 1 by rfl]
        rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
        rfl
      rw [he] at hr
      simp at hr
  | @cons a s ih =>
      intro hs
      let p := brandenE (rootPolynomial s)
      have hs_box : ∀ r ∈ s, (-1 : ℝ) ≤ r ∧ r ≤ 0 := by
        intro r hr
        exact hs r (Multiset.mem_cons_of_mem hr)
      have ha_box : (-1 : ℝ) ≤ a ∧ a ≤ 0 :=
        hs a (Multiset.mem_cons_self a s)
      have hp_pf : IsPFPolynomial p :=
        brandenE_isPFPolynomial_of_roots_mem_Icc
          (rootPolynomial_splits s)
          (hasPosLeadingCoeff_of_monic (rootPolynomial_monic s)) (by
            intro r hr
            simpa using hs_box r (by simpa using hr))
      have hp_ne : p ≠ 0 := brandenE_rootPolynomial_ne_zero s
      have hp_splits : p.Splits := (hp_pf.ne_zero_and_splits hp_ne).2
      have hp_pos : HasPosLeadingCoeff p :=
        hp_pf.hasNonnegCoeffs.pos_leadingCoeff hp_ne
      have hp_lo : ∀ r ∈ p.roots, (-1 : ℝ) ≤ r := ih hs_box
      rw [brandenE_rootPolynomial_cons]
      apply derivativeRecurrence_roots_ge_step
        (f := p) (A := X * (1 + X)) (B := X + C (-a))
      · simp [brandenEulerStep]
        ring
      · exact hp_splits
      · exact hp_pos
      · exact hp_lo
      · intro x hx
        simp only [eval_mul, eval_X, eval_add, eval_one]
        nlinarith
      · intro x hx
        simp only [eval_add, eval_X, eval_C]
        linarith

/-- Moving one source root to the right inside `[-1, 0]` moves the two
`E` images into oriented weak interlacing position. -/
theorem brandenE_strictInterl_rootPolynomial_cons_move
    (s : Multiset ℝ) {u v : ℝ}
    (hs : ∀ r ∈ s, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (huv : u ≤ v) :
    StrictInterl (brandenE (rootPolynomial (u ::ₘ s)))
      (brandenE (rootPolynomial (v ::ₘ s))) := by
  by_cases hs0 : s = 0
  · subst s
    simp only [brandenE_rootPolynomial_cons]
    have he : brandenE (rootPolynomial (0 : Multiset ℝ)) = 1 := by
      rw [show rootPolynomial (0 : Multiset ℝ) = 1 by rfl]
      rw [show (1 : ℝ[X]) = X ^ 0 by simp, brandenE_X_pow]
      rfl
    have hstep (r : ℝ) : brandenEulerStep (-r) (brandenE (rootPolynomial 0)) =
        X + C (-r) := by
      rw [he]
      simp [brandenEulerStep]
    rw [hstep, hstep]
    apply StrictInterl.X_add_C_iff.mpr
    linarith
  · let p := brandenE (rootPolynomial s)
    let F := brandenEulerStep (-u) p
    let G := brandenEulerStep (-v) p
    have hp_pf : IsPFPolynomial p :=
      brandenE_isPFPolynomial_of_roots_mem_Icc
        (rootPolynomial_splits s)
        (hasPosLeadingCoeff_of_monic (rootPolynomial_monic s)) (by
          intro r hr
          simpa using hs r (by simpa using hr))
    have hp_ne : p ≠ 0 := brandenE_rootPolynomial_ne_zero s
    have hp_splits : p.Splits := (hp_pf.ne_zero_and_splits hp_ne).2
    have hp_pos : HasPosLeadingCoeff p :=
      hp_pf.hasNonnegCoeffs.pos_leadingCoeff hp_ne
    have hp_deg : p.natDegree = s.card := (brandenE_rootPolynomial_degree_pos s).1
    have hp_deg_pos : 1 ≤ s.card := Multiset.card_pos.mpr hs0
    have hp_lo : ∀ r ∈ p.roots, (-1 : ℝ) ≤ r :=
      brandenE_rootPolynomial_roots_ge_neg_one s hs
    have hp_hi : ∀ r ∈ p.roots, r ≤ 0 := by
      intro r hr
      exact hp_pf.roots_nonpos r hr
    have hpF : StrictInterl p F := by
      exact brandenEulerStep_strictInterl hp_splits hp_pos hp_deg hp_deg_pos hp_lo hp_hi
    have hF_degree_pos := brandenEulerStep_degree_pos (r := -u) hp_pos hp_deg
    have hG_degree_pos := brandenEulerStep_degree_pos (r := -v) hp_pos hp_deg
    have hFG : StrictInterl F G := by
      have hidentity : G = 1 * F + (-C (v - u)) * p := by
        dsimp [F, G]
        simp only [brandenEulerStep, one_mul]
        rw [show C (-u) = -C u by simp,
          show C (-v) = -C v by simp,
          show C (v - u) = C v - C u by simp]
        ring
      have h := strictInterl_of_interlaces_evalCoeff_nonpos
        (f := F) (g := p) (a := 1) (b := -C (v - u))
        (hpF.toInterlaces (by
          dsimp [F]
          rw [hp_deg, hF_degree_pos.1])) hp_pos (by
          rw [← hidentity]
          exact hG_degree_pos.2) (by
            rw [← hidentity, hF_degree_pos.1, hG_degree_pos.1]) (by
              rw [← hidentity, hF_degree_pos.1, hG_degree_pos.1]
              lia) (by
                intro r hr
                simp only [eval_neg, eval_C]
                linarith)
      simpa only [hidentity] using h
    simpa only [brandenE_rootPolynomial_cons, p, F, G] using hFG

/-- Arbitrary monic-factor form of the oriented one-root replacement step. -/
theorem brandenE_strictInterl_one_root_replacement
    {h : ℝ[X]} {u v : ℝ}
    (hmonic : h.Monic) (hsplits : h.Splits)
    (hroots : ∀ r ∈ h.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (huv : u ≤ v) :
    StrictInterl (brandenE ((X - C u) * h))
      (brandenE ((X - C v) * h)) := by
  have hh : rootPolynomial h.roots = h := by
    simpa [rootPolynomial] using (hsplits.eq_prod_roots_of_monic hmonic).symm
  have hu_poly : rootPolynomial (u ::ₘ h.roots) = (X - C u) * h := by
    rw [rootPolynomial, Multiset.map_cons, Multiset.prod_cons]
    change (X - C u) * rootPolynomial h.roots = (X - C u) * h
    rw [hh]
  have hv_poly : rootPolynomial (v ::ₘ h.roots) = (X - C v) * h := by
    rw [rootPolynomial, Multiset.map_cons, Multiset.prod_cons]
    change (X - C v) * rootPolynomial h.roots = (X - C v) * h
    rw [hh]
  rw [← hu_poly, ← hv_poly]
  exact brandenE_strictInterl_rootPolynomial_cons_move h.roots hroots huv

private def rootsInUnitBox (s : Multiset ℝ) : Prop :=
  ∀ r ∈ s, (-1 : ℝ) ≤ r ∧ r ≤ 0

private def IsRootMove (s t : Multiset ℝ) : Prop :=
  ∃ (u v : ℝ) (w : Multiset ℝ),
    rootsInUnitBox w ∧ u ≤ v ∧ s = u ::ₘ w ∧ t = v ::ₘ w

private theorem IsRootMove.strictInterl_brandenE {s t : Multiset ℝ}
    (hst : IsRootMove s t) :
    StrictInterl (brandenE (rootPolynomial s))
      (brandenE (rootPolynomial t)) := by
  obtain ⟨u, v, w, hw, huv, rfl, rfl⟩ := hst
  exact brandenE_strictInterl_rootPolynomial_cons_move w hw huv

private theorem IsRootMove.cons (a : ℝ) {s t : Multiset ℝ}
    (ha : (-1 : ℝ) ≤ a ∧ a ≤ 0) (hst : IsRootMove s t) :
    IsRootMove (a ::ₘ s) (a ::ₘ t) := by
  obtain ⟨u, v, w, hw, huv, rfl, rfl⟩ := hst
  refine ⟨u, v, a ::ₘ w, ?_, huv, ?_, ?_⟩
  · intro r hr
    rcases Multiset.mem_cons.mp hr with rfl | hr
    · exact ha
    · exact hw r hr
  · rw [Multiset.cons_swap]
  · rw [Multiset.cons_swap]

private theorem IsRootMove.refl_of_ne_zero {s : Multiset ℝ}
    (hs0 : s ≠ 0) (hs : rootsInUnitBox s) : IsRootMove s s := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hs0
  refine ⟨a, a, s.erase a, ?_, le_rfl, ?_, ?_⟩
  · intro r hr
    exact hs r (Multiset.mem_of_mem_erase hr)
  · exact (Multiset.cons_erase ha).symm
  · exact (Multiset.cons_erase ha).symm

private theorem exists_rootMove_chain_of_forall₂ :
    ∀ {xs ys : List ℝ}, List.Forall₂ (· ≤ ·) xs ys →
      rootsInUnitBox (xs : Multiset ℝ) →
      rootsInUnitBox (ys : Multiset ℝ) →
      ∃ ms : List (Multiset ℝ),
        ms ≠ [] ∧ ms.head? = some (xs : Multiset ℝ) ∧
          ms.getLast? = some (ys : Multiset ℝ) ∧
          (∀ s ∈ ms, rootsInUnitBox s) ∧ ms.IsChain IsRootMove := by
  intro xs ys hxy
  induction hxy with
  | nil =>
      intro hxs hys
      exact ⟨[0], by simp, by simp, by simp, by simp [rootsInUnitBox], by simp⟩
  | @cons u v xs ys huv htail ih =>
      intro hxs hys
      have hu : (-1 : ℝ) ≤ u ∧ u ≤ 0 := hxs u (by simp)
      have hv : (-1 : ℝ) ≤ v ∧ v ≤ 0 := hys v (by simp)
      have hxs_tail : rootsInUnitBox (xs : Multiset ℝ) := by
        intro r hr
        exact hxs r (Multiset.mem_cons_of_mem hr)
      have hys_tail : rootsInUnitBox (ys : Multiset ℝ) := by
        intro r hr
        exact hys r (Multiset.mem_cons_of_mem hr)
      obtain ⟨ms, hms0, hhead, hlast, hbox, hchain⟩ :=
        ih hxs_tail hys_tail
      let lift : Multiset ℝ → Multiset ℝ := fun s ↦ v ::ₘ s
      refine ⟨(u ::ₘ (xs : Multiset ℝ)) :: ms.map lift, by simp,
        by simp, ?_, ?_, ?_⟩
      · rw [List.getLast?_cons, List.getLast?_map, hlast]
        simp [lift]
      · intro s hs
        simp only [List.mem_cons, List.mem_map] at hs
        rcases hs with rfl | ⟨t, ht, rfl⟩
        · exact hxs
        · intro r hr
          rcases Multiset.mem_cons.mp hr with rfl | hr
          · exact hv
          · exact hbox t ht r hr
      · apply List.IsChain.cons
        · rw [List.isChain_map]
          exact List.IsChain.imp
            (S := fun a b ↦ IsRootMove (lift a) (lift b))
            (fun {_a _b} h ↦ IsRootMove.cons v hv h) hchain
        · intro s hs
          have hs' := Option.mem_def.mp hs
          rw [List.head?_map, hhead] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst s
          exact ⟨u, v, xs, hxs_tail, huv, rfl, rfl⟩

private theorem List.getD_zero_eq_of_head?_eq_some
    {A : Type*} {l : List A} {a d : A} (h : l.head? = some a) :
    l.getD 0 d = a := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp h
  rfl

private theorem List.getD_last_eq_of_getLast?_eq_some
    {A : Type*} {l : List A} {a d : A} (h : l.getLast? = some a) :
    l.getD (l.length - 1) d = a := by
  have hl0 : l ≠ [] := by
    intro hl
    simp [hl] at h
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hl0
  rw [List.getD_eq_getElem l d (by lia), ← List.getLast_eq_getElem hl0]
  have hlast := List.getLast?_eq_some_getLast hl0
  rw [h] at hlast
  exact Option.some.inj hlast.symm

/-- Brändén's Theorem 4.6 in `brandenE` coordinates: coordinatewise
increasing roots in `[-1, 0]` give oriented weak interlacing of the images. -/
theorem brandenE_strictInterl_of_rootwiseLE
    {f g : ℝ[X]} {n : ℕ}
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hf_degree : f.natDegree = n) (hg_degree : g.natDegree = n)
    (hn : n ≠ 0)
    (hf_roots : ∀ r ∈ f.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (hg_roots : ∀ r ∈ g.roots, (-1 : ℝ) ≤ r ∧ r ≤ 0)
    (hfg : RootwiseLE f g) :
    StrictInterl (brandenE f) (brandenE g) := by
  replace hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  let xs := f.roots.sort (· ≤ ·)
  let ys := g.roots.sort (· ≤ ·)
  let lo := List.replicate n (-1 : ℝ)
  let hi := List.replicate n (0 : ℝ)
  have hxs_length : xs.length = n := by
    simp [xs, Polynomial.splits_iff_card_roots.mp hf_splits, hf_degree]
  have hys_length : ys.length = n := by
    simp [ys, Polynomial.splits_iff_card_roots.mp hg_splits, hg_degree]
  have hxs_coe : (xs : Multiset ℝ) = f.roots := by
    exact Multiset.sort_eq f.roots (· ≤ ·)
  have hys_coe : (ys : Multiset ℝ) = g.roots := by
    exact Multiset.sort_eq g.roots (· ≤ ·)
  have hxs_box : rootsInUnitBox (xs : Multiset ℝ) := by
    rw [hxs_coe]
    exact hf_roots
  have hys_box : rootsInUnitBox (ys : Multiset ℝ) := by
    rw [hys_coe]
    exact hg_roots
  have hlo_box : rootsInUnitBox (lo : Multiset ℝ) := by
    intro r hr
    have hr' : r = -1 := (by simpa [lo] using hr : n ≠ 0 ∧ r = -1).2
    subst r
    norm_num
  have hhi_box : rootsInUnitBox (hi : Multiset ℝ) := by
    intro r hr
    have hr' : r = 0 := (by simpa [hi] using hr : n ≠ 0 ∧ r = 0).2
    subst r
    norm_num
  have hlo_xs : List.Forall₂ (· ≤ ·) lo xs := by
    apply List.forall₂_of_length_eq_of_get
    · simp [lo, hxs_length]
    · intro i hlo_i hxs_i
      have hmem : xs[i] ∈ (xs : Multiset ℝ) :=
        Multiset.mem_coe.mpr (List.getElem_mem hxs_i)
      simpa [lo] using (hxs_box xs[i] hmem).1
  have hys_hi : List.Forall₂ (· ≤ ·) ys hi := by
    apply List.forall₂_of_length_eq_of_get
    · simp [hi, hys_length]
    · intro i hys_i hhi_i
      have hmem : ys[i] ∈ (ys : Multiset ℝ) :=
        Multiset.mem_coe.mpr (List.getElem_mem hys_i)
      simpa [hi] using (hys_box ys[i] hmem).2
  have hxs_ys : List.Forall₂ (· ≤ ·) xs ys := by
    exact hfg
  obtain ⟨left, hleft0, hleft_head, hleft_last, hleft_box, hleft_chain⟩ :=
    exists_rootMove_chain_of_forall₂ hlo_xs hlo_box hxs_box
  obtain ⟨middle, hmiddle0, hmiddle_head, hmiddle_last, hmiddle_box,
      hmiddle_chain⟩ :=
    exists_rootMove_chain_of_forall₂ hxs_ys hxs_box hys_box
  obtain ⟨right, hright0, hright_head, hright_last, hright_box, hright_chain⟩ :=
    exists_rootMove_chain_of_forall₂ hys_hi hys_box hhi_box
  have hxs0 : (xs : Multiset ℝ) ≠ 0 := by
    intro hzero
    have : xs.length = 0 := by simpa using congrArg Multiset.card hzero
    lia
  have hys0 : (ys : Multiset ℝ) ≠ 0 := by
    intro hzero
    have : ys.length = 0 := by simpa using congrArg Multiset.card hzero
    lia
  have hleft_middle : (left ++ middle).IsChain IsRootMove := by
    apply List.IsChain.append hleft_chain hmiddle_chain
    intro a ha b hb
    have ha' := Option.mem_def.mp ha
    have hb' := Option.mem_def.mp hb
    rw [hleft_last] at ha'
    rw [hmiddle_head] at hb'
    have ha_eq := Option.some.inj ha'.symm
    have hb_eq := Option.some.inj hb'.symm
    subst a
    subst b
    exact IsRootMove.refl_of_ne_zero hxs0 hxs_box
  let ms := (left ++ middle) ++ right
  have hms_chain : ms.IsChain IsRootMove := by
    apply List.IsChain.append hleft_middle hright_chain
    intro a ha b hb
    have ha' := Option.mem_def.mp ha
    have hb' := Option.mem_def.mp hb
    rw [List.getLast?_append, hmiddle_last] at ha'
    simp only [Option.some_or] at ha'
    rw [hright_head] at hb'
    have ha_eq := Option.some.inj ha'.symm
    have hb_eq := Option.some.inj hb'.symm
    subst a
    subst b
    exact IsRootMove.refl_of_ne_zero hys0 hys_box
  have hms0 : ms ≠ [] := by
    simp [ms, hleft0]
  have hms_head : ms.head? = some (lo : Multiset ℝ) := by
    change ((left ++ middle) ++ right).head? = some (lo : Multiset ℝ)
    rw [List.head?_append, List.head?_append, hleft_head]
    rfl
  have hms_last : ms.getLast? = some (hi : Multiset ℝ) := by
    change ((left ++ middle) ++ right).getLast? = some (hi : Multiset ℝ)
    rw [List.getLast?_append, hright_last]
    rfl
  let P : Multiset ℝ → ℝ[X] := fun s ↦ brandenE (rootPolynomial s)
  let F : ℕ → ℝ[X] := fun k ↦ P (ms.getD k 0)
  have hcons : ∀ k, 0 ≤ k → k < ms.length - 1 →
      StrictInterl (F k) (F (k + 1)) := by
    intro k hk0 hk
    have hk' : k + 1 < ms.length := by lia
    have hmove := List.isChain_iff_getElem.mp hms_chain k hk'
    rw [← List.getD_eq_getElem ms 0 (by lia),
      ← List.getD_eq_getElem ms 0 hk'] at hmove
    exact hmove.strictInterl_brandenE
  have hlo_poly : rootPolynomial (lo : Multiset ℝ) = (X + 1) ^ n := by
    simp [lo, rootPolynomial_coe, sub_eq_add_neg]
  have hhi_poly : rootPolynomial (hi : Multiset ℝ) = X ^ n := by
    simp [hi, rootPolynomial_coe]
  have hext : StrictInterl (F 0) (F (ms.length - 1)) := by
    have hfirst := List.getD_zero_eq_of_head?_eq_some
      (d := (0 : Multiset ℝ)) hms_head
    have hlast := List.getD_last_eq_of_getLast?_eq_some
      (d := (0 : Multiset ℝ)) hms_last
    change StrictInterl (P (ms.getD 0 0)) (P (ms.getD (ms.length - 1) 0))
    rw [hfirst, hlast]
    change StrictInterl (brandenE (rootPolynomial (lo : Multiset ℝ)))
      (brandenE (rootPolynomial (hi : Multiset ℝ)))
    rw [hlo_poly, hhi_poly]
    simpa [brandenBasisImage, brandenBinomialBasis] using
      brandenBasisImage_endpoint_strictInterl n hn
  have hall := strictInterl_chain_of_consecutive_of_endpoint
    F 0 (ms.length - 1) hcons hext
  let i := left.length
  let j := left.length + middle.length - 1
  have hi_le_j : i ≤ j := by
    dsimp [i, j]
    have : 1 ≤ middle.length := by
      exact List.length_pos_of_ne_nil hmiddle0
    lia
  have hj_bound : j ≤ ms.length - 1 := by
    dsimp [i, j, ms]
    have : 1 ≤ right.length := by
      exact List.length_pos_of_ne_nil hright0
    simp only [List.length_append]
    lia
  have hFi : F i = brandenE f := by
    have hi_outer : i < (left ++ middle).length := by
      dsimp [i]
      simp only [List.length_append]
      exact Nat.lt_add_of_pos_right
        (List.length_pos_of_ne_nil hmiddle0)
    have hmid_first := List.getD_zero_eq_of_head?_eq_some
      (d := (0 : Multiset ℝ)) hmiddle_head
    have hsource : ms.getD i 0 = (xs : Multiset ℝ) := by
      change ((left ++ middle) ++ right).getD i 0 = (xs : Multiset ℝ)
      rw [List.getD_append _ _ _ _ hi_outer,
        List.getD_append_right left middle 0 i (by simp [i])]
      simpa [i] using hmid_first
    have hf_poly : rootPolynomial (xs : Multiset ℝ) = f := by
      rw [hxs_coe]
      simpa [rootPolynomial] using (hf_splits.eq_prod_roots_of_monic hf_monic).symm
    simp only [F, P, hsource, hf_poly]
  have hFj : F j = brandenE g := by
    have hj_outer : j < (left ++ middle).length := by
      dsimp [j]
      simp only [List.length_append]
      have : 1 ≤ middle.length := by
        exact List.length_pos_of_ne_nil hmiddle0
      lia
    have hmid_last := List.getD_last_eq_of_getLast?_eq_some
      (d := (0 : Multiset ℝ)) hmiddle_last
    have hindex : j - left.length = middle.length - 1 := by
      dsimp [j]
      have := List.length_pos_of_ne_nil hmiddle0
      lia
    have hsource : ms.getD j 0 = (ys : Multiset ℝ) := by
      change ((left ++ middle) ++ right).getD j 0 = (ys : Multiset ℝ)
      rw [List.getD_append _ _ _ _ hj_outer,
        List.getD_append_right left middle 0 j (by
          dsimp [j]
          have := List.length_pos_of_ne_nil hmiddle0
          lia)]
      rw [hindex]
      exact hmid_last
    have hg_poly : rootPolynomial (ys : Multiset ℝ) = g := by
      rw [hys_coe]
      simpa [rootPolynomial] using (hg_splits.eq_prod_roots_of_monic hg_monic).symm
    simp only [F, P, hsource, hg_poly]
  rw [← hFi, ← hFj]
  exact hall i j (Nat.zero_le i) hi_le_j hj_bound

end RealRooted
