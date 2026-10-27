module

public import RealRooted.Basic.Coefficients
public import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer
public import RealRooted.Mesh.Basic
public import RealRooted.NarayanaTransformation.RootGeometry
import RealRooted.Mesh.DiscreteMultiplier
import RealRooted.Basic.RootLists
import RealRooted.Interlacing.OuterDifference
import RealRooted.Linear
import RealRooted.WagnerRightSum.Sign

/-!
# The falling factorial map and Brenti's lemma

Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in finite difference setting*,
Proc. AMS 144 (2016), Lemma 10 (due to Brenti): the linear map `T` with `T (x ^ i) = [x]_i`
sends every polynomial with only real nonnegative roots to a polynomial with only nonnegative
roots and mesh at least one.

The proof is the paper's induction on the degree: if `p = (x - α) q` and `Q = T q`, then
`T p = x Q(x - 1) - α Q`, and `Q ≪ T p`, `Q(x - 1) ≪ T p` by the signed outer-difference cone
`RealRooted.StrictInterl.sub_of_triple_of_posLeadingCoeff`, which gives mesh at least one.
See RealRooted issue #2070.
-/

@[expose] public section

open Polynomial Module

namespace RealRooted

noncomputable section

/-! ### The falling factorial map -/

/-- The linear map `T : ℝ[X] → ℝ[X]` with `T (X ^ i) = [x]_i`, the falling factorial
`descPochhammer ℝ i`. -/
def fallingFactorialMap : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (Polynomial.basisMonomials ℝ).constr ℝ (descPochhammer ℝ)

theorem fallingFactorialMap_monomial (n : ℕ) (a : ℝ) :
    fallingFactorialMap (monomial n a) = a • descPochhammer ℝ n := by
  have h := (Polynomial.basisMonomials ℝ).constr_basis ℝ (descPochhammer ℝ) n
  rw [Polynomial.coe_basisMonomials] at h
  have h1 : fallingFactorialMap (monomial n 1) = descPochhammer ℝ n := h
  calc fallingFactorialMap (monomial n a) = fallingFactorialMap (a • monomial n 1) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
    _ = a • descPochhammer ℝ n := by rw [map_smul, h1]

@[simp]
theorem fallingFactorialMap_X_pow (n : ℕ) :
    fallingFactorialMap (X ^ n) = descPochhammer ℝ n := by
  simpa [← monomial_one_right_eq_X_pow] using fallingFactorialMap_monomial n 1

@[simp]
theorem fallingFactorialMap_C (a : ℝ) : fallingFactorialMap (C a) = C a := by
  rw [← monomial_zero_left, fallingFactorialMap_monomial, descPochhammer_zero]
  simp [smul_eq_C_mul]

/-- `T (x q) = x * T(q)(x - 1)`, since `[x]_{i + 1} = x [x - 1]_i`. -/
theorem fallingFactorialMap_X_mul (q : ℝ[X]) :
    fallingFactorialMap (X * q) = X * (fallingFactorialMap q).comp (X - C 1) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, add_comp, mul_add]
  | monomial n a =>
    rw [X_mul_monomial, fallingFactorialMap_monomial, fallingFactorialMap_monomial,
      descPochhammer_succ_left]
    simp [smul_eq_C_mul, mul_left_comm]

/-! ### Sorted root lists -/

private theorem list_eq_sort {s : Multiset ℝ} {l : List ℝ} (hl : l.Pairwise (· ≤ ·))
    (h : (↑l : Multiset ℝ) = s) : l = s.sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise' hl (Multiset.pairwise_sort s _)
  apply Multiset.coe_eq_coe.mp
  rw [h, Multiset.sort_eq]

/-- The sorted roots of a polynomial with mesh at least one are pairwise at least one apart. -/
theorem _root_.Polynomial.MeshGE.pairwise_sort_roots {Q : ℝ[X]} (h : Q.MeshGE 1) :
    (Q.roots.sort (· ≤ ·)).Pairwise (fun a b : ℝ => a + 1 ≤ b) := by
  let rs := Q.roots.sort (· ≤ ·)
  have hchain : rs.IsChain (fun a b : ℝ => a + 1 ≤ b) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hgap := h.2.2 i (by simpa [rs] using hi)
    simpa [rs, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by lia : i < rs.length),
      List.getElem?_eq_getElem hi, Option.getD_some] using hgap
  have htrans : Trans (fun a b : ℝ => a + 1 ≤ b)
      (fun a b : ℝ => a + 1 ≤ b) (fun a b : ℝ => a + 1 ≤ b) :=
    ⟨by intro a b c hab hbc; linarith⟩
  exact @List.IsChain.pairwise ℝ _ rs htrans hchain

private theorem meshGE_of_pairwise_sort {W : ℝ[X]} (hs : W.Splits)
    (h : (W.roots.sort (· ≤ ·)).Pairwise (fun a b : ℝ => a + 1 ≤ b)) : W.MeshGE 1 := by
  refine ⟨hs, zero_le_one, fun i hi => ?_⟩
  have hi0 : i < (W.roots.sort (· ≤ ·)).length := by lia
  have := List.pairwise_iff_getElem.mp h i (i + 1) hi0 hi (by lia)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0,
    List.getElem?_eq_getElem hi] using this

private theorem pairwise_of_listInterlaces_map :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ListInterlaces (ss.map (· + 1)) rs →
      rs.Pairwise (fun a b : ℝ => a + 1 ≤ b)
  | [], [], _, _ => by simp
  | [], [_], _, _ => by simp
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _ => by simp [ListInterlaces] at h
  | s :: ss, r₁ :: r₂ :: rs, h, h' => by
      simp only [List.map_cons] at h'
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨h1', h2', h3'⟩ := h'
      have ih := pairwise_of_listInterlaces_map ss (r₂ :: rs) h3 h3'
      rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · linarith
      · have := (List.pairwise_cons.mp ih).1 x hx
        linarith

private theorem listInterlaces_cons_map_add_one :
    ∀ (ss : List ℝ) (c : ℝ), ss.Pairwise (fun a b : ℝ => a + 1 ≤ b) → (∀ x ∈ ss, c ≤ x) →
      ListInterlaces ss (c :: ss.map (· + 1))
  | [], c, _, _ => by simp [ListInterlaces]
  | s :: ss, c, hp, hc => by
      rw [List.pairwise_cons] at hp
      simp only [List.map_cons, ListInterlaces]
      refine ⟨hc s (by simp), by linarith, ?_⟩
      exact listInterlaces_cons_map_add_one ss (s + 1) hp.2 (fun x hx => hp.1 x hx)

private theorem listInterlaces_cons_self :
    ∀ (ss : List ℝ) (c : ℝ), ss.Pairwise (· ≤ ·) → (∀ x ∈ ss, c ≤ x) →
      ListInterlaces ss (c :: ss)
  | [], c, _, _ => by simp [ListInterlaces]
  | s :: ss, c, hp, hc => by
      rw [List.pairwise_cons] at hp
      simp only [ListInterlaces]
      exact ⟨hc s (by simp), le_rfl, listInterlaces_cons_self ss s hp.2 hp.1⟩

/-! ### Interlacing with the shift -/

private theorem roots_comp_X_sub_C_one' (Q : ℝ[X]) :
    (Q.comp (X - C 1)).roots = Q.roots.map (· + 1) := by
  rw [show X - C (1 : ℝ) = X + C (-1) by simp [sub_eq_add_neg], roots_comp_X_add_C]
  simp only [sub_neg_eq_add]

private theorem leadingCoeff_comp_X_sub_C_one' (Q : ℝ[X]) :
    (Q.comp (X - C 1)).leadingCoeff = Q.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_X_sub_C]; exact one_ne_zero), leadingCoeff_X_sub_C,
    one_pow, mul_one]

private theorem natDegree_comp_X_sub_C_one' (Q : ℝ[X]) :
    (Q.comp (X - C 1)).natDegree = Q.natDegree := by
  rw [natDegree_comp, natDegree_X_sub_C, mul_one]

private theorem strictInterl_self_X_mul {R : ℝ[X]} (hR : R ≠ 0) (hs : R.Splits)
    (hnn : ∀ r ∈ R.roots, 0 ≤ r) : StrictInterl R (X * R) := by
  have hXR : X * R ≠ 0 := mul_ne_zero X_ne_zero hR
  have hmem : ∀ x ∈ R.roots.sort (· ≤ ·), 0 ≤ x := fun x hx =>
    hnn x ((Multiset.mem_sort _).mp hx)
  refine ⟨⟨hR, hs⟩, ⟨hXR, Polynomial.Splits.X.mul hs⟩, R.roots.sort (· ≤ ·),
    0 :: R.roots.sort (· ≤ ·), Multiset.pairwise_sort _ _,
    List.pairwise_cons.mpr ⟨hmem, Multiset.pairwise_sort _ _⟩, by simp, ?_,
    Or.inl ⟨by simp, listInterlaces_cons_self _ 0 (Multiset.pairwise_sort _ _) hmem⟩⟩
  rw [roots_mul hXR, roots_X, Multiset.singleton_add, ← Multiset.cons_coe, Multiset.sort_eq]

private theorem strictInterl_self_X_mul_comp {Q : ℝ[X]} (hmesh : Q.MeshGE 1)
    (hnn : ∀ r ∈ Q.roots, 0 ≤ r) (hR : Q.comp (X - C 1) ≠ 0) :
    StrictInterl Q (X * Q.comp (X - C 1)) := by
  have hXR : X * Q.comp (X - C 1) ≠ 0 := mul_ne_zero X_ne_zero hR
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hR
  have hgap := hmesh.pairwise_sort_roots
  have hmem : ∀ x ∈ Q.roots.sort (· ≤ ·), 0 ≤ x := fun x hx =>
    hnn x ((Multiset.mem_sort _).mp hx)
  have hmap : ((Q.roots.sort (· ≤ ·)).map (· + 1)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact (Multiset.pairwise_sort Q.roots (· ≤ ·)).imp (by intro a b hab; linarith)
  have hs : Q.Splits := hmesh.1
  have hRs : (Q.comp (X - C 1)).Splits := by
    rw [splits_iff_card_roots, roots_comp_X_sub_C_one', Multiset.card_map,
      natDegree_comp_X_sub_C_one']
    exact splits_iff_card_roots.mp hs
  refine ⟨⟨hQ0, hs⟩, ⟨hXR, Polynomial.Splits.X.mul hRs⟩, Q.roots.sort (· ≤ ·),
    0 :: (Q.roots.sort (· ≤ ·)).map (· + 1), Multiset.pairwise_sort _ _,
    List.pairwise_cons.mpr ⟨fun x hx => ?_, hmap⟩, by simp, ?_,
    Or.inl ⟨by simp, listInterlaces_cons_map_add_one _ 0 hgap hmem⟩⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    linarith [hmem y hy]
  · rw [roots_mul hXR, roots_X, roots_comp_X_sub_C_one', Multiset.singleton_add,
      ← Multiset.cons_coe, ← Multiset.map_coe, Multiset.sort_eq]

/-- If `Q ≪ W` and `Q(x - 1) ≪ W` with `deg W = deg Q + 1`, then `W` has mesh at least one:
`w_i ≤ θ_i` and `θ_i + 1 ≤ w_{i + 1}`. -/
private theorem meshGE_one_of_strictInterl_comp_succ {Q W : ℝ[X]} (h1 : StrictInterl Q W)
    (h2 : StrictInterl (Q.comp (X - C 1)) W) (hdeg : Q.natDegree + 1 = W.natDegree) :
    W.MeshGE 1 := by
  obtain ⟨⟨hQ0, hQs⟩, ⟨hW0, hWs⟩, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := h1
  obtain ⟨-, -, ss', rs', hss', hrs', hss'_eq, hrs'_eq, hshape'⟩ := h2
  have hlenss : ss.length = Q.natDegree := by
    rw [← Multiset.coe_card, hss_eq, splits_iff_card_roots.mp hQs]
  have hlenrs : rs.length = W.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, splits_iff_card_roots.mp hWs]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨-, h⟩ | ⟨hl, -⟩
    · exact h
    · exfalso
      lia
  have hrs_sort : rs = W.roots.sort (· ≤ ·) := list_eq_sort hrs hrs_eq
  have hrs'_sort : rs' = W.roots.sort (· ≤ ·) := list_eq_sort hrs' hrs'_eq
  have hmapsorted : (ss.map (· + 1)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hss.imp (by intro a b hab; linarith)
  have hss'_map : ss' = ss.map (· + 1) := by
    have e1 := list_eq_sort hss' hss'_eq
    have e2 := list_eq_sort (s := (Q.comp (X - C 1)).roots) hmapsorted
      (by rw [roots_comp_X_sub_C_one', ← hss_eq, Multiset.map_coe])
    rw [e1, e2]
  have hint' : ListInterlaces (ss.map (· + 1)) rs := by
    rw [← hss'_map, hrs_sort, ← hrs'_sort]
    rcases hshape' with ⟨-, h⟩ | ⟨hl, -⟩
    · exact h
    · exfalso
      have : rs'.length = rs.length := by rw [hrs'_sort, hrs_sort]
      rw [hss'_map, List.length_map] at hl
      lia
  apply meshGE_of_pairwise_sort hWs
  rw [← hrs_sort]
  exact pairwise_of_listInterlaces_map ss rs hint hint'

/-! ### The inductive step -/

/-- The step of Brenti's lemma: for `Q` with positive leading coefficient, mesh at least one and
nonnegative roots, and `α ≥ 0`, the polynomial `x Q(x - 1) - α Q` has degree `deg Q + 1`, positive
leading coefficient, mesh at least one and nonnegative roots. -/
private theorem step {Q : ℝ[X]} {α : ℝ} (hα : 0 ≤ α) (hQpos : HasPosLeadingCoeff Q)
    (hmesh : Q.MeshGE 1) (hnn : ∀ r ∈ Q.roots, 0 ≤ r) :
    (X * Q.comp (X - C 1) - C α * Q).natDegree = Q.natDegree + 1 ∧
      HasPosLeadingCoeff (X * Q.comp (X - C 1) - C α * Q) ∧
      (X * Q.comp (X - C 1) - C α * Q).MeshGE 1 ∧
      HasOnlyNonnegRoots (X * Q.comp (X - C 1) - C α * Q) := by
  have hQ0 : Q ≠ 0 := hQpos.ne_zero
  have hRlc := leadingCoeff_comp_X_sub_C_one' Q
  have hRdeg := natDegree_comp_X_sub_C_one' Q
  have hR0 : Q.comp (X - C 1) ≠ 0 := by
    intro h
    have : Q.leadingCoeff = 0 := by rw [← hRlc, h, leadingCoeff_zero]
    exact hQ0 (leadingCoeff_eq_zero.mp this)
  have hRpos : HasPosLeadingCoeff (Q.comp (X - C 1)) := by
    unfold HasPosLeadingCoeff at hQpos ⊢
    rwa [hRlc]
  have hHpos : HasPosLeadingCoeff (X * Q.comp (X - C 1)) := hRpos.X_mul
  have hHdeg : (X * Q.comp (X - C 1)).natDegree = Q.natDegree + 1 := by
    rw [natDegree_X_mul hR0, hRdeg]
  have hH0 : X * Q.comp (X - C 1) ≠ 0 := hHpos.ne_zero
  have hαQdeg : (C α * Q).natDegree < (X * Q.comp (X - C 1)).natDegree := by
    have := natDegree_C_mul_le α Q
    lia
  have hWdeg : (X * Q.comp (X - C 1) - C α * Q).natDegree = Q.natDegree + 1 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt hαQdeg, hHdeg]
  have hWpos : HasPosLeadingCoeff (X * Q.comp (X - C 1) - C α * Q) := by
    unfold HasPosLeadingCoeff at hHpos ⊢
    rwa [leadingCoeff_sub_of_degree_lt (degree_lt_degree hαQdeg)]
  have hQR : StrictInterl Q (Q.comp (X - C 1)) :=
    ((Polynomial.MeshGE.iff_interl_comp_sub one_pos).1 hmesh).toStrictInterl_of_ne hQ0 hR0
  have hHQ : StrictInterl Q (X * Q.comp (X - C 1)) :=
    strictInterl_self_X_mul_comp hmesh hnn hR0
  have hRnn : ∀ r ∈ (Q.comp (X - C 1)).roots, 0 ≤ r := by
    intro r hr
    rw [roots_comp_X_sub_C_one', Multiset.mem_map] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    linarith [hnn y hy]
  have hHR : StrictInterl (Q.comp (X - C 1)) (X * Q.comp (X - C 1)) :=
    strictInterl_self_X_mul hR0 hQR.2.1.2 hRnn
  have hW1 : StrictInterl Q (X * Q.comp (X - C 1) - C α * Q) ∧
      StrictInterl (Q.comp (X - C 1)) (X * Q.comp (X - C 1) - C α * Q) := by
    rcases hα.eq_or_lt with h0 | hαpos
    · subst h0
      simpa using ⟨hHQ, hHR⟩
    · have hfpos : HasPosLeadingCoeff (C α * Q) := hasPosLeadingCoeff_C_mul hαpos hQpos
      have hfh : StrictInterl (C α * Q) (X * Q.comp (X - C 1)) := hHQ.C_mul_left hαpos.ne'
      exact ⟨StrictInterl.sub_of_triple_of_posLeadingCoeff
          ((StrictInterl.refl hQ0 hmesh.1).C_mul_left hαpos.ne') hHQ hfh hfpos hQpos hHpos hWpos,
        StrictInterl.sub_of_triple_of_posLeadingCoeff (hQR.C_mul_left hαpos.ne') hHR hfh hfpos
          hRpos hHpos hWpos⟩
  have hWmesh := meshGE_one_of_strictInterl_comp_succ hW1.1 hW1.2 hWdeg.symm
  refine ⟨hWdeg, hWpos, hWmesh, Or.inr ⟨hWmesh.1, fun r hr => ?_⟩⟩
  by_contra hneg
  have hneg' : r < 0 := lt_of_not_ge hneg
  have hWne : X * Q.comp (X - C 1) - C α * Q ≠ 0 := hWpos.ne_zero
  have hroot : (X * Q.comp (X - C 1) - C α * Q).eval r = 0 :=
    Polynomial.IsRoot.def.mp ((mem_roots hWne).mp hr)
  simp only [eval_sub, eval_mul, eval_X, eval_comp, eval_C] at hroot
  have hgt : ∀ t ∈ Q.roots, r < t := fun t ht => lt_of_lt_of_le hneg' (hnn t ht)
  have hgt' : ∀ t ∈ Q.roots, r - 1 < t := fun t ht => by linarith [hgt t ht]
  rcases Nat.even_or_odd Q.natDegree with he | ho
  · have h1 := eval_pos_of_all_roots_gt_of_even hQ0 hQpos he hgt
    have h2 := eval_pos_of_all_roots_gt_of_even hQ0 hQpos he hgt'
    nlinarith [mul_nonneg hα h1.le]
  · have h1 := eval_neg_of_all_roots_gt_of_odd hQ0 hQpos ho hgt
    have h2 := eval_neg_of_all_roots_gt_of_odd hQ0 hQpos ho hgt'
    nlinarith [mul_nonneg hα (neg_nonneg.mpr h1.le)]

private theorem fallingFactorialMap_C_mul (a : ℝ) (q : ℝ[X]) :
    fallingFactorialMap (C a * q) = C a * fallingFactorialMap q := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

private theorem fallingFactorialMap_pos (n : ℕ) : ∀ p : ℝ[X], p.natDegree = n →
    HasPosLeadingCoeff p → HasOnlyNonnegRoots p →
      (fallingFactorialMap p).natDegree = n ∧ HasPosLeadingCoeff (fallingFactorialMap p) ∧
        (fallingFactorialMap p).MeshGE 1 ∧ HasOnlyNonnegRoots (fallingFactorialMap p) := by
  induction n with
  | zero =>
    intro p hp hpos _
    obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨p.coeff 0, eq_C_of_natDegree_eq_zero hp⟩
    have hc : 0 < c := by simpa [HasPosLeadingCoeff] using hpos
    have hs : (C c).Splits := Polynomial.Splits.of_natDegree_eq_zero (natDegree_C c)
    rw [fallingFactorialMap_C]
    exact ⟨natDegree_C c, by simpa [HasPosLeadingCoeff] using hc,
      Polynomial.MeshGE.of_natDegree_le_one hs (by simp) zero_le_one, Or.inr ⟨hs, by simp⟩⟩
  | succ n ih =>
    intro p hp hpos hnn
    have hp0 := hpos.ne_zero
    have hpnn : p.Splits ∧ ∀ r ∈ p.roots, 0 ≤ r := hnn.resolve_left hp0
    have hcard : p.roots.card = n + 1 := by rw [splits_iff_card_roots.mp hpnn.1, hp]
    obtain ⟨α, hα⟩ : ∃ α, α ∈ p.roots := Multiset.card_pos_iff_exists_mem.mp (by lia)
    have hαroot : p.IsRoot α := (mem_roots hp0).mp hα
    have hpq : (X - C α) * (p /ₘ (X - C α)) = p := mul_divByMonic_eq_iff_isRoot.mpr hαroot
    set q := p /ₘ (X - C α)
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, mul_zero] at hpq
      exact hp0 hpq.symm
    have hqdeg : q.natDegree = n := by
      have := congrArg natDegree hpq
      rw [natDegree_mul (X_sub_C_ne_zero α) hq0, natDegree_X_sub_C] at this
      lia
    have hqlc : q.leadingCoeff = p.leadingCoeff := by
      rw [← hpq, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
    have hqpos : HasPosLeadingCoeff q := by
      unfold HasPosLeadingCoeff at hpos ⊢
      rwa [hqlc]
    have hqnn : HasOnlyNonnegRoots q := by
      refine Or.inr ⟨hpnn.1.of_dvd hp0 (Dvd.intro_left _ hpq), fun r hr => ?_⟩
      · apply hpnn.2
        rw [mem_roots hp0]
        have hqr := (mem_roots hq0).mp hr
        rw [← hpq]
        simp [Polynomial.IsRoot.def.mp hqr]
    obtain ⟨hQdeg, hQpos, hQmesh, hQnn⟩ := ih q hqdeg hqpos hqnn
    have hQroots : ∀ r ∈ (fallingFactorialMap q).roots, 0 ≤ r :=
      (hQnn.resolve_left hQpos.ne_zero).2
    have hTp : fallingFactorialMap p =
        X * (fallingFactorialMap q).comp (X - C 1) - C α * fallingFactorialMap q := by
      conv_lhs => rw [← hpq]
      rw [sub_mul, map_sub, fallingFactorialMap_X_mul, fallingFactorialMap_C_mul]
    rw [hTp]
    have := step (hpnn.2 α hα) hQpos hQmesh hQroots
    rwa [hQdeg] at this

/-- BKS 2016, Lemma 10 (Brenti): the linear map `T (x ^ i) = [x]_i` sends a polynomial with only
real nonnegative roots to a polynomial with mesh at least one and only nonnegative roots. -/
theorem fallingFactorialMap_meshGE_one {p : ℝ[X]} (hp : HasOnlyNonnegRoots p) :
    (fallingFactorialMap p).MeshGE 1 ∧ HasOnlyNonnegRoots (fallingFactorialMap p) := by
  by_cases hp0 : p = 0
  · subst hp0
    rw [map_zero]
    exact ⟨Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) zero_le_one, Or.inl rfl⟩
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp0) with hneg | hpos
  · have hp' : HasOnlyNonnegRoots (C (-1) * p) :=
      (HasOnlyNonnegRoots.C_mul_iff (by norm_num) p).2 hp
    have hpos' : HasPosLeadingCoeff (C (-1) * p) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C]
      linarith
    obtain ⟨-, -, h1, h2⟩ := fallingFactorialMap_pos _ _ rfl hpos' hp'
    rw [fallingFactorialMap_C_mul] at h1 h2
    exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).1 h1,
      (HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).1 h2⟩
  · obtain ⟨-, -, h1, h2⟩ := fallingFactorialMap_pos _ _ rfl hpos hp
    exact ⟨h1, h2⟩

/-! ### The forward difference -/

/-- The forward difference `∇ p = p(x + 1) - p(x)`. -/
def forwardDifference : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := p.comp (X + C 1) - p
  map_add' p q := by
    simp only [add_comp]
    ring
  map_smul' c p := by
    simp only [smul_comp, RingHom.id_apply, smul_sub]

@[simp]
theorem forwardDifference_apply (p : ℝ[X]) :
    forwardDifference p = p.comp (X + C 1) - p := rfl

/-- `∇ [x]_i = i [x]_{i - 1}` (with the convention `∇ [x]_0 = 0`). -/
theorem forwardDifference_descPochhammer (i : ℕ) :
    forwardDifference (descPochhammer ℝ i) = (i : ℝ) • descPochhammer ℝ (i - 1) := by
  cases i with
  | zero => simp
  | succ k =>
    have h1 : (descPochhammer ℝ (k + 1)).comp (X + C 1) = (X + 1) * descPochhammer ℝ k := by
      rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc]
      simp
    rw [forwardDifference_apply, h1, descPochhammer_succ_right]
    simp only [smul_eq_C_mul, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_add,
      map_natCast, map_one]
    ring

/-- The falling-factorial coordinates of `∇ p` are `(j + 1)` times those of `p` shifted by one:
`∇ [x]_{j + 1} = (j + 1) [x]_j`. -/
theorem descPochhammerBasis_repr_forwardDifference (p : ℝ[X]) (j : ℕ) :
    (descPochhammerBasis ℝ).repr (forwardDifference p) j =
      ((j : ℝ) + 1) * (descPochhammerBasis ℝ).repr p (j + 1) := by
  have e : ∀ k, descPochhammerBasis ℝ k = descPochhammer ℝ k := fun k =>
    descPochhammerBasis_apply k
  have h : (descPochhammerBasis ℝ).coord j ∘ₗ forwardDifference =
      ((j : ℝ) + 1) • (descPochhammerBasis ℝ).coord (j + 1) := by
    refine (descPochhammerBasis ℝ).ext fun i => ?_
    have hL : (descPochhammerBasis ℝ).coord j (forwardDifference (descPochhammerBasis ℝ i)) =
        (i : ℝ) * (if i - 1 = j then 1 else 0) := by
      rw [e i, forwardDifference_descPochhammer, ← e (i - 1), map_smul, Basis.coord_apply,
        Basis.repr_self, Finsupp.single_apply]
      simp [smul_eq_mul]
    have hR : (((j : ℝ) + 1) • (descPochhammerBasis ℝ).coord (j + 1))
        (descPochhammerBasis ℝ i) = ((j : ℝ) + 1) * (if i = j + 1 then 1 else 0) := by
      rw [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
      simp [smul_eq_mul]
    rw [LinearMap.comp_apply, hL, hR]
    rcases i with _ | k
    · simp
    · by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
  have := LinearMap.congr_fun h p
  simpa using this

/-! ### Proper position of the difference -/

private theorem listInterlaces_exists_le' :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ∀ s ∈ ss, ∃ r ∈ rs, r ≤ s
  | [], _, _, s, hs => by simp at hs
  | _ :: _, [], h, _, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _, _ => by simp [ListInterlaces] at h
  | _ :: ss, r₁ :: r₂ :: rs, h, s, hs => by
      obtain ⟨hr, _, htail⟩ := h
      rcases List.mem_cons.mp hs with hs0 | hs'
      · exact ⟨r₁, by simp, hs0 ▸ hr⟩
      · obtain ⟨r, hr', hle⟩ := listInterlaces_exists_le' ss (r₂ :: rs) htail s hs'
        exact ⟨r, List.mem_cons_of_mem _ hr', hle⟩

private theorem listInterlaces_left_ge_head :
    ∀ (ss : List ℝ) (r : ℝ) (rs : List ℝ), ListInterlaces ss (r :: rs) → ∀ x ∈ ss, r ≤ x
  | [], _, _, _, x, hx => by simp at hx
  | _ :: _, _, [], h, _, _ => by simp [ListInterlaces] at h
  | s :: ss, r, r₂ :: rs, h, x, hx => by
      obtain ⟨hr, hs, htail⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hr
      · exact hr.trans (hs.trans (listInterlaces_left_ge_head ss r₂ rs htail x hx'))

private theorem pairwise_of_listInterlaces_map' :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ListInterlaces ss (rs.map (· + 1)) →
      ss.Pairwise (fun a b : ℝ => a + 1 ≤ b)
  | [], _, _, _ => by simp
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _, [_], h, _ => by simp [ListInterlaces] at h
  | s :: ss, r₁ :: r₂ :: rs, h, h' => by
      simp only [List.map_cons] at h'
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨h1', h2', h3'⟩ := h'
      have ih := pairwise_of_listInterlaces_map' ss (r₂ :: rs) h3 (by simpa using h3')
      rw [List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih⟩
      have := listInterlaces_left_ge_head ss (r₂ + 1) (rs.map (· + 1)) h3' x hx
      linarith

/-- The difference `W` in proper position with both `p` and `p(x - 1)`, `deg W + 1 = deg p`, has
mesh at least one, and each of its roots is at least `1` more than some root of `p`. -/
private theorem meshGE_one_of_strictInterl_of_comp {W p : ℝ[X]} (h1 : StrictInterl W p)
    (h2 : StrictInterl W (p.comp (X - C 1))) (hdeg : W.natDegree + 1 = p.natDegree) :
    W.MeshGE 1 ∧ ∀ r ∈ W.roots, ∃ q ∈ p.roots, q + 1 ≤ r := by
  obtain ⟨⟨hW0, hWs⟩, ⟨hp0, hps⟩, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩ := h1
  obtain ⟨-, -, ss', rs', hss', hrs', hss'_eq, hrs'_eq, hshape'⟩ := h2
  have hlenss : ss.length = W.natDegree := by
    rw [← Multiset.coe_card, hss_eq, splits_iff_card_roots.mp hWs]
  have hlenrs : rs.length = p.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, splits_iff_card_roots.mp hps]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨-, h⟩ | ⟨hl, -⟩
    · exact h
    · exfalso
      lia
  have hss_eq' : ss' = ss := by
    rw [list_eq_sort hss' hss'_eq, list_eq_sort hss hss_eq]
  have hmapsorted : (rs.map (· + 1)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hrs.imp (by intro a b hab; linarith)
  have hrs'_map : rs' = rs.map (· + 1) := by
    have e1 := list_eq_sort hrs' hrs'_eq
    have e2 := list_eq_sort (s := (p.comp (X - C 1)).roots) hmapsorted
      (by rw [roots_comp_X_sub_C_one', ← hrs_eq, Multiset.map_coe])
    rw [e1, e2]
  have hint' : ListInterlaces ss (rs.map (· + 1)) := by
    rw [← hrs'_map, ← hss_eq']
    rcases hshape' with ⟨-, h⟩ | ⟨hl, -⟩
    · exact h
    · exfalso
      rw [hrs'_map, List.length_map] at hl
      lia
  refine ⟨?_, fun r hr => ?_⟩
  · apply meshGE_of_pairwise_sort hWs
    rw [← list_eq_sort hss hss_eq]
    exact pairwise_of_listInterlaces_map' ss rs hint hint'
  · rw [← hss_eq] at hr
    obtain ⟨y, hy, hyr⟩ := listInterlaces_exists_le' ss _ hint' r (Multiset.mem_coe.mp hr)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    exact ⟨q, by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hq, hyr⟩

/-- The forward difference `∇ p` of a polynomial of degree `m + 1` with positive leading
coefficient, mesh at least one and nonnegative roots has degree `m`, positive leading coefficient,
mesh at least one and nonnegative roots (BKS 2016, proof of Lemma 11). -/
private theorem forwardDifference_of_posLeadingCoeff {p : ℝ[X]} {m : ℕ}
    (hpos : HasPosLeadingCoeff p)
    (hn : p.natDegree = m + 1) (hmesh : p.MeshGE 1) (hnn : HasOnlyNonnegRoots p) :
    (forwardDifference p).natDegree = m ∧ HasPosLeadingCoeff (forwardDifference p) ∧
      (forwardDifference p).MeshGE 1 ∧ HasOnlyNonnegRoots (forwardDifference p) := by
  obtain ⟨hWpos, hWdeg, hWp, hWq⟩ := strictInterl_sub_comp_X_sub_C_one hpos hn hmesh
  have hp0 := hpos.ne_zero
  have hpr : ∀ r ∈ p.roots, 0 ≤ r := (hnn.resolve_left hp0).2
  obtain ⟨hWmesh, hWroots⟩ := meshGE_one_of_strictInterl_of_comp hWp hWq (by lia)
  have hform : forwardDifference p = (p - p.comp (X - C 1)).comp (X + C 1) := by
    rw [forwardDifference_apply, sub_comp, comp_assoc]
    simp
  have hdeg1 : (X + C (1 : ℝ)).natDegree = 1 := natDegree_X_add_C 1
  have hne : (X + C (1 : ℝ)).natDegree ≠ 0 := by rw [hdeg1]; exact one_ne_zero
  have hmesh' : (forwardDifference p).MeshGE 1 := by
    rw [hform]
    exact (Polynomial.MeshGE.comp_X_add_C_iff _ 1 1).2 hWmesh
  refine ⟨?_, ?_, hmesh', Or.inr ⟨hmesh'.1, fun r hr => ?_⟩⟩
  · rw [hform, natDegree_comp, hdeg1, mul_one, hWdeg]
  · unfold HasPosLeadingCoeff at hWpos ⊢
    rw [hform, leadingCoeff_comp hne, leadingCoeff_X_add_C, one_pow, mul_one]
    exact hWpos
  · rw [hform, roots_comp_X_add_C, Multiset.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    obtain ⟨q, hq, hqw⟩ := hWroots w hw
    linarith [hpr q hq]

/-! ### Lemma 11: signs of the falling-factorial coordinates -/

private theorem neg_one_pow_mul_eval_zero_nonneg {p : ℝ[X]} (hpos : HasPosLeadingCoeff p)
    (hnn : HasOnlyNonnegRoots p) : 0 ≤ (-1 : ℝ) ^ p.natDegree * p.eval 0 := by
  have hp0 := hpos.ne_zero
  obtain ⟨hs, hr⟩ := hnn.resolve_left hp0
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hs
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have h0 : p.eval 0 = p.leadingCoeff * (p.roots.map fun r => -r).prod := by
    conv_lhs => rw [← hfac]
    simp [eval_multiset_prod, Multiset.map_map]
  rw [h0, Multiset.prod_map_neg, hcard, ← mul_assoc, mul_comm _ p.leadingCoeff, mul_assoc,
    ← mul_assoc ((-1 : ℝ) ^ p.natDegree), ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  exact mul_nonneg hpos.le (Multiset.prod_nonneg hr)

/-- BKS 2016, Lemma 11: if `p = ∑ a_i [x]_i` has mesh at least one, nonnegative roots and positive
leading coefficient, then its falling-factorial coordinates satisfy `(-1) ^ (n - i) a_i ≥ 0`,
where `n = deg p`. -/
theorem neg_one_pow_mul_descPochhammerBasis_repr_nonneg {p : ℝ[X]} (hpos : HasPosLeadingCoeff p)
    (hmesh : p.MeshGE 1) (hnn : HasOnlyNonnegRoots p) {i : ℕ} (hi : i ≤ p.natDegree) :
    0 ≤ (-1 : ℝ) ^ (p.natDegree - i) * (descPochhammerBasis ℝ).repr p i := by
  have key : ∀ n : ℕ, ∀ p : ℝ[X], p.natDegree = n → HasPosLeadingCoeff p → p.MeshGE 1 →
      HasOnlyNonnegRoots p → ∀ i, i ≤ n →
        0 ≤ (-1 : ℝ) ^ (n - i) * (descPochhammerBasis ℝ).repr p i := by
    intro n
    induction n with
    | zero =>
      intro p hn hpos hmesh hnn i hi
      obtain rfl : i = 0 := by lia
      have h0 := neg_one_pow_mul_eval_zero_nonneg hpos hnn
      rw [hn] at h0
      simpa [descPochhammerBasis_repr_zero] using h0
    | succ m ih =>
      intro p hn hpos hmesh hnn i hi
      rcases i with _ | j
      · have h0 := neg_one_pow_mul_eval_zero_nonneg hpos hnn
        rw [hn] at h0
        simpa [descPochhammerBasis_repr_zero] using h0
      · obtain ⟨hd, hp', hm', hn'⟩ := forwardDifference_of_posLeadingCoeff hpos hn hmesh hnn
        have h := ih _ hd hp' hm' hn' j (by lia)
        rw [descPochhammerBasis_repr_forwardDifference] at h
        have e : m + 1 - (j + 1) = m - j := by lia
        rw [e]
        have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        by_contra hneg
        push Not at hneg
        nlinarith [mul_pos hj (neg_pos.mpr hneg)]
  exact key _ p rfl hpos hmesh hnn i hi

/-- Sign-free version of `forwardDifference_of_posLeadingCoeff`: `∇` maps a nonzero polynomial
of positive degree with mesh at least one and nonnegative roots to a nonzero polynomial of one
degree less with the same properties. -/
private theorem forwardDifference_of_meshGE {q : ℝ[X]} (hmesh : q.MeshGE 1) (hq0 : q ≠ 0)
    (hnn : HasOnlyNonnegRoots q) (hdeg : q.natDegree ≠ 0) :
    forwardDifference q ≠ 0 ∧ (forwardDifference q).natDegree + 1 = q.natDegree ∧
      (forwardDifference q).MeshGE 1 ∧ HasOnlyNonnegRoots (forwardDifference q) := by
  obtain ⟨m, hm⟩ : ∃ m, q.natDegree = m + 1 := ⟨q.natDegree - 1, by lia⟩
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hq0) with hneg | hpos
  · have hq' : HasPosLeadingCoeff (C (-1) * q) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C]
      linarith
    have hm' : (C (-1) * q).natDegree = m + 1 := by
      rw [natDegree_C_mul (by norm_num), hm]
    obtain ⟨h1, h2, h3, h4⟩ := forwardDifference_of_posLeadingCoeff hq' hm'
      ((Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).2 hmesh)
      ((HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).2 hnn)
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul] at h1 h2 h3 h4
    refine ⟨?_, by rw [natDegree_C_mul (by norm_num)] at h1; lia,
      (Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).1 h3,
      (HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).1 h4⟩
    intro h0
    rw [h0, mul_zero] at h2
    exact h2.ne_zero rfl
  · obtain ⟨h1, h2, h3, h4⟩ := forwardDifference_of_posLeadingCoeff hpos hm hmesh hnn
    exact ⟨h2.ne_zero, by lia, h3, h4⟩

/-- Iterating the forward difference on a nonzero polynomial with mesh at least one and
nonnegative roots keeps these properties and lowers the degree by one each time. -/
theorem _root_.Polynomial.MeshGE.iterate_forwardDifference {q : ℝ[X]} (hmesh : q.MeshGE 1)
    (hq0 : q ≠ 0) (hnn : HasOnlyNonnegRoots q) :
    ∀ r, r ≤ q.natDegree → (⇑forwardDifference)^[r] q ≠ 0 ∧
      ((⇑forwardDifference)^[r] q).natDegree = q.natDegree - r ∧
      ((⇑forwardDifference)^[r] q).MeshGE 1 ∧ HasOnlyNonnegRoots ((⇑forwardDifference)^[r] q) := by
  intro r
  induction r with
  | zero => intro _; exact ⟨hq0, rfl, hmesh, hnn⟩
  | succ r ih =>
    intro hr
    obtain ⟨h0, h1, h2, h3⟩ := ih (by lia)
    obtain ⟨g0, g1, g2, g3⟩ := forwardDifference_of_meshGE h2 h0 h3 (by lia)
    rw [Function.iterate_succ_apply']
    exact ⟨g0, by lia, g2, g3⟩

/-- Iterated forward differences scale the falling-factorial coordinates by positive factors. -/
theorem descPochhammerBasis_repr_iterate_forwardDifference (r : ℕ) :
    ∀ (p : ℝ[X]) (k : ℕ), ∃ f : ℝ, 0 < f ∧
    (descPochhammerBasis ℝ).repr ((⇑forwardDifference)^[r] p) k =
      f * (descPochhammerBasis ℝ).repr p (k + r) := by
  induction r with
  | zero => intro p k; exact ⟨1, one_pos, by simp⟩
  | succ r ih =>
    intro p k
    obtain ⟨f, hf, h⟩ := ih p (k + 1)
    refine ⟨((k : ℝ) + 1) * f, by positivity, ?_⟩
    rw [Function.iterate_succ_apply', descPochhammerBasis_repr_forwardDifference, h,
      show k + (r + 1) = k + 1 + r by lia]
    ring

end

end RealRooted
