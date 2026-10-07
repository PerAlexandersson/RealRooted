import RealRooted.RootContinuity
import Mathlib.Topology.Connected.Clopen

/-!
# Real-rootedness along squarefree paths

If a family of real polynomials of constant degree depends continuously on a parameter in a
preconnected set and stays squarefree there, then real-rootedness at one parameter forces
real-rootedness at every parameter.

The set of parameters where the polynomial splits is clopen:

* **Open.** A monic squarefree split polynomial of degree `d` has `d` distinct real roots.
  Sample points strictly between consecutive roots, and beyond both extreme roots, see strict
  sign alternations. Evaluation at a fixed point is continuous in the coefficients, so the
  alternations persist nearby, and the intermediate value theorem gives `d` distinct real
  roots there.
* **Closed.** A coefficientwise limit of monic split polynomials of a fixed degree splits
  (`RealRooted.splits_of_monic_of_coeff_approx`).

The main statements are `RealRooted.splits_of_isPreconnected` and its unit-interval form
`RealRooted.splits_of_path`.
-/

open Polynomial Set

namespace RealRooted

/-- Given reals `r 0 < ⋯ < r (d - 1)`, there are sample points `x 0, …, x d` interleaving
them: `x i` lies strictly above each `r j` with `j < i` and strictly below each `r j` with
`i ≤ j`. -/
private lemma exists_separating_points (d : ℕ) (r : ℕ → ℝ)
    (hmono : ∀ i j : ℕ, i < j → j < d → r i < r j) :
    ∃ x : ℕ → ℝ,
      (∀ i j : ℕ, j < i → i ≤ d → j < d → r j < x i) ∧
      (∀ i j : ℕ, i ≤ j → j < d → x i < r j) := by
  have hle : ∀ i j : ℕ, i ≤ j → j < d → r i ≤ r j := by
    intro i j hij hj
    rcases hij.lt_or_eq with h | rfl
    · exact (hmono i j h hj).le
    · exact le_rfl
  refine ⟨fun i =>
      if i = 0 then r 0 - 1 else if i < d then (r (i - 1) + r i) / 2 else r (d - 1) + 1,
    ?_, ?_⟩
  · intro i j hji hid hjd
    dsimp only
    split_ifs with hi0 hid'
    · lia
    · have h1 : r j ≤ r (i - 1) := hle j (i - 1) (by lia) (by lia)
      have h2 : r (i - 1) < r i := hmono (i - 1) i (by lia) hid'
      linarith
    · have h1 : r j ≤ r (d - 1) := hle j (d - 1) (by lia) (by lia)
      linarith
  · intro i j hij hjd
    dsimp only
    split_ifs with hi0 hid'
    · subst hi0
      linarith [hle 0 j (by lia) hjd]
    · have h1 : r (i - 1) < r i := hmono (i - 1) i (by lia) hid'
      have h2 : r i ≤ r j := hle i j hij hjd
      linarith
    · lia

/-- A monic squarefree split real polynomial of degree `d` is `∏ i < d, (X - r i)` for a
strictly increasing enumeration `r 0 < ⋯ < r (d - 1)` of its roots. -/
private lemma exists_strictMono_roots_enum {p : ℝ[X]} {d : ℕ}
    (hm : p.Monic) (hdeg : p.natDegree = d) (hs : p.Splits) (hsq : Squarefree p) :
    ∃ r : ℕ → ℝ, (∀ i j : ℕ, i < j → j < d → r i < r j) ∧
      ∀ z : ℝ, p.eval z = ∏ i ∈ Finset.range d, (z - r i) := by
  classical
  have hnodup : p.roots.Nodup :=
    nodup_roots (PerfectField.separable_iff_squarefree.mpr hsq)
  have hcard : Multiset.card p.roots = d := by
    rw [← hdeg]
    exact hs.natDegree_eq_card_roots.symm
  set L : List ℝ := p.roots.sort (· ≤ ·) with hL
  have hcoe : (L : Multiset ℝ) = p.roots := Multiset.sort_eq _ _
  have hlen : L.length = d := by rw [hL, Multiset.length_sort, hcard]
  have hLnodup : L.Nodup := by
    rw [← hcoe] at hnodup
    exact Multiset.coe_nodup.mp hnodup
  have hLsorted : L.SortedLT :=
    List.sortedLT_iff_nodup_and_sortedLE.mpr
      ⟨hLnodup, (Multiset.pairwise_sort _ _).sortedLE⟩
  refine ⟨fun i => L.getD i 0, ?_, ?_⟩
  · intro i j hij hjd
    have hi : i < L.length := by lia
    have hj : j < L.length := by lia
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, Option.getD_some]
    exact hLsorted.getElem_lt_getElem_of_lt hij
  · intro z
    have hfac : (p.roots.map fun a => X - C a).prod = p :=
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hcard, hdeg])
    calc p.eval z = ((p.roots.map fun a => X - C a).prod).eval z := by rw [hfac]
      _ = ((L.map fun a => X - C a).prod).eval z := by
            rw [← hcoe, Multiset.map_coe, Multiset.prod_coe]
      _ = (L.map fun a => z - a).prod := by
            rw [eval_list_prod, List.map_map]
            congr 1
            exact List.map_congr_left fun a _ => by simp
      _ = ∏ i : Fin L.length, (z - L[(i : ℕ)]) := by
            rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
      _ = ∏ i ∈ Finset.range d, (z - L.getD i 0) := by
            rw [← hlen, ← Fin.prod_univ_eq_prod_range (fun n => z - L.getD n 0)]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt,
              Option.getD_some]

/-- The monic case of `RealRooted.splits_of_isPreconnected`. -/
private theorem splits_of_isPreconnected_of_monic {T : Type*} [TopologicalSpace T]
    {s : Set T} (hs : IsPreconnected s) {P : T → ℝ[X]} {d : ℕ}
    (hcoeff : ∀ k : ℕ, ContinuousOn (fun t => (P t).coeff k) s)
    (hdeg : ∀ t ∈ s, (P t).natDegree = d) (hmonic : ∀ t ∈ s, (P t).Monic)
    (hsqfree : ∀ t ∈ s, Squarefree (P t)) {a b : T} (ha : a ∈ s) (hb : b ∈ s)
    (hsplits : (P a).Splits) :
    (P b).Splits := by
  classical
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  set S : Set s := {u | (P u).Splits}
  have hcoeffC : ∀ k : ℕ, Continuous fun u : s => (P u).coeff k :=
    fun k => (hcoeff k).domRestrict
  -- Openness: strict sign alternation at interleaving sample points persists.
  have hopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro u₀ hu₀
    obtain ⟨r, hrmono, hreval⟩ := exists_strictMono_roots_enum
      (hmonic _ u₀.2) (hdeg _ u₀.2) hu₀ (hsqfree _ u₀.2)
    obtain ⟨x, hlow, hhigh⟩ := exists_separating_points d r hrmono
    have hxlt : ∀ i < d, x i < x (i + 1) := fun i hi =>
      (hhigh i i le_rfl hi).trans (hlow (i + 1) i (by lia) (by lia) hi)
    -- A continuous surrogate for evaluation at the fixed sample points.
    set g : ℕ → s → ℝ := fun i u =>
      ∑ k ∈ Finset.range (d + 1), (P u).coeff k * x i ^ k with hg
    have hgC : ∀ i, Continuous (g i) := fun i =>
      continuous_finsetSum _ fun k _ => (hcoeffC k).mul continuous_const
    have hgeval : ∀ (i : ℕ) (u : s), g i u = (P u).eval (x i) := fun i u =>
      (eval_eq_sum_range' (by rw [hdeg _ u.2]; lia) _).symm
    refine ⟨⋂ i ∈ Finset.range d, {u | g i u * g (i + 1) u < 0}, ?_, ?_, ?_⟩
    · -- Sign alternation forces `d` distinct real roots, hence splitting.
      intro u hu
      simp only [mem_iInter, mem_ofPred_eq, Finset.mem_range] at hu
      have hy : ∀ i : Fin d, ∃ z ∈ Ioo (x i) (x (i + 1)), (P u).eval z = 0 := by
        intro i
        have halt := hu i i.isLt
        rw [hgeval, hgeval] at halt
        have hcont : ContinuousOn (fun z => (P u).eval z) (Icc (x i) (x (i + 1))) :=
          (P u).continuous.continuousOn
        rcases lt_or_gt_of_ne (show (P u).eval (x i) ≠ 0 by
            rintro h
            rw [h, zero_mul] at halt
            exact halt.false) with hneg | hpos
        · exact intermediate_value_Ioo (hxlt i i.isLt).le hcont
            ⟨hneg, pos_of_mul_neg_right halt hneg.le⟩
        · exact intermediate_value_Ioo' (hxlt i i.isLt).le hcont
            ⟨neg_of_mul_neg_right halt hpos.le, hpos⟩
      choose y hyIoo hy0 using hy
      have hxle : ∀ i j : ℕ, i ≤ j → j ≤ d → x i ≤ x j := by
        intro i j hij hjd
        induction j, hij using Nat.le_induction with
        | base => exact le_rfl
        | succ n hin ih => exact (ih (by lia)).trans (hxlt n (by lia)).le
      have hyinj : Function.Injective y := by
        have hylt : ∀ i j : Fin d, (i : ℕ) < j → y i < y j := fun i j hij =>
          ((hyIoo i).2.trans_le (hxle (i + 1) j (by lia) (by lia))).trans (hyIoo j).1
        intro i j hij
        by_contra hne
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
        · exact (hylt i j h).ne hij
        · exact (hylt j i h).ne hij.symm
      have hPne : P u ≠ 0 := (hmonic _ u.2).ne_zero
      have hsub : Finset.univ.image y ⊆ (P u).roots.toFinset := by
        intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        rw [Multiset.mem_toFinset, mem_roots hPne]
        exact hy0 i
      have hdle : d ≤ Multiset.card (P u).roots := by
        calc d = (Finset.univ.image y).card := by
              rw [Finset.card_image_of_injective _ hyinj, Finset.card_univ, Fintype.card_fin]
          _ ≤ (P u).roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ Multiset.card (P u).roots := Multiset.toFinset_card_le _
      exact splits_iff_card_roots.mpr
        (le_antisymm (card_roots' _) (by rw [hdeg _ u.2]; exact hdle))
    · exact isOpen_biInter_finset fun i _ =>
        isOpen_lt ((hgC i).mul (hgC (i + 1))) continuous_const
    · -- The base point satisfies the sign alternation.
      simp only [mem_iInter, mem_ofPred_eq, Finset.mem_range]
      intro i hi
      rw [hgeval, hgeval, hreval, hreval, ← Finset.prod_mul_distrib,
        ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)]
      have hneg : (x i - r i) * (x (i + 1) - r i) < 0 :=
        mul_neg_of_neg_of_pos (by linarith [hhigh i i le_rfl hi])
          (by linarith [hlow (i + 1) i (by lia) (by lia) hi])
      have hpos : 0 < ∏ j ∈ (Finset.range d).erase i, (x i - r j) * (x (i + 1) - r j) := by
        refine Finset.prod_pos fun j hj => ?_
        obtain ⟨hne, hjr⟩ := Finset.mem_erase.mp hj
        rw [Finset.mem_range] at hjr
        rcases lt_or_gt_of_ne hne with hji | hij
        · exact mul_pos (by linarith [hlow i j hji (by lia) hjr])
            (by linarith [hlow (i + 1) j (by lia) (by lia) hjr])
        · exact mul_pos_of_neg_of_neg (by linarith [hhigh i j hij.le hjr])
            (by linarith [hhigh (i + 1) j (by lia) hjr])
      exact mul_neg_of_neg_of_pos hneg hpos
  -- Closedness: coefficientwise limits of monic split polynomials of degree `d` split.
  have hclosed : IsClosed S := by
    refine isClosed_of_closure_subset fun u₀ hu₀ => ?_
    refine splits_of_monic_of_coeff_approx (hmonic _ u₀.2) fun ε hε => ?_
    set V : Set s := ⋂ k ∈ Finset.range (d + 1),
      {u | |(P u).coeff k - (P u₀).coeff k| < ε} with hV
    have hVopen : IsOpen V :=
      isOpen_biInter_finset fun k _ =>
        isOpen_lt ((hcoeffC k).sub continuous_const).abs continuous_const
    have hu₀V : u₀ ∈ V := by
      simp only [hV, mem_iInter, mem_ofPred_eq, sub_self, abs_zero]
      exact fun _ _ => hε
    obtain ⟨u, huV, huS⟩ := mem_closure_iff.mp hu₀ V hVopen hu₀V
    refine ⟨P u, hmonic _ u.2, by rw [hdeg _ u.2, hdeg _ u₀.2], huS, fun i => ?_⟩
    by_cases hi : i ≤ d
    · rw [Real.norm_eq_abs]
      exact mem_iInter₂.mp huV i (Finset.mem_range.mpr (by lia))
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg _ u.2]; lia),
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg _ u₀.2]; lia), sub_zero, norm_zero]
      exact hε
  have hS : S = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨a, ha⟩, hsplits⟩
  have hbS : (⟨b, hb⟩ : s) ∈ S := hS ▸ mem_univ _
  exact hbS

/-- **Real-rootedness transports along a squarefree family of constant degree.**

Let `P t` be real polynomials whose coefficients are continuous on a preconnected set `s`, of
constant degree on `s`, and squarefree at every point of `s`. If `P a` splits for some `a ∈ s`,
then `P b` splits for every `b ∈ s`. -/
theorem splits_of_isPreconnected {T : Type*} [TopologicalSpace T]
    {s : Set T} (hs : IsPreconnected s) {P : T → ℝ[X]} {d : ℕ}
    (hcoeff : ∀ k : ℕ, ContinuousOn (fun t => (P t).coeff k) s)
    (hdeg : ∀ t ∈ s, (P t).natDegree = d) (hsqfree : ∀ t ∈ s, Squarefree (P t))
    {a b : T} (ha : a ∈ s) (hb : b ∈ s) (hsplits : (P a).Splits) :
    (P b).Splits := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact Splits.of_natDegree_eq_zero (hdeg b hb)
  have hlc : ∀ t ∈ s, (P t).coeff d ≠ 0 := by
    intro t ht
    have hne : P t ≠ 0 := by
      rintro h
      exact hd (by rw [← hdeg t ht, h, natDegree_zero])
    rw [← hdeg t ht, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hne
  -- Normalize by the leading coefficient.
  set Q : T → ℝ[X] := fun t => C ((P t).coeff d)⁻¹ * P t with hQ
  have hPQ : ∀ t ∈ s, P t = C ((P t).coeff d) * Q t := by
    intro t ht
    rw [hQ, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hlc t ht), C_1, one_mul]
  have hQdeg : ∀ t ∈ s, (Q t).natDegree = d := fun t ht => by
    rw [hQ, natDegree_C_mul (inv_ne_zero (hlc t ht)), hdeg t ht]
  have hQmonic : ∀ t ∈ s, (Q t).Monic := fun t ht => by
    rw [Monic, ← coeff_natDegree, hQdeg t ht, hQ, coeff_C_mul, inv_mul_cancel₀ (hlc t ht)]
  have hQcoeff : ∀ k : ℕ, ContinuousOn (fun t => (Q t).coeff k) s := fun k => by
    simp only [hQ, coeff_C_mul]
    exact ((hcoeff d).inv₀ hlc).mul (hcoeff k)
  have hQsq : ∀ t ∈ s, Squarefree (Q t) := fun t ht =>
    (hsqfree t ht).squarefree_of_dvd (Dvd.intro_left _ (hPQ t ht).symm)
  have hQb := splits_of_isPreconnected_of_monic hs hQcoeff hQdeg hQmonic hQsq ha hb
    (hsplits.C_mul _)
  rw [hPQ b hb]
  exact hQb.C_mul _

/-- **Real-rootedness transports along a squarefree path of constant degree.**

If `P t` has coefficients continuous on `[0, 1]`, constant degree there, and is squarefree at
every `t ∈ [0, 1]`, then `P 1` splits whenever `P 0` does. -/
theorem splits_of_path (P : ℝ → ℝ[X]) {d : ℕ}
    (hcoeff : ∀ k : ℕ, ContinuousOn (fun t => (P t).coeff k) (Icc 0 1))
    (hdeg : ∀ t ∈ Icc (0 : ℝ) 1, (P t).natDegree = d)
    (hsqfree : ∀ t ∈ Icc (0 : ℝ) 1, Squarefree (P t)) (h0 : (P 0).Splits) :
    (P 1).Splits :=
  splits_of_isPreconnected isPreconnected_Icc hcoeff hdeg hsqfree
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) h0

/-- The separable form of `RealRooted.splits_of_path`: over `ℝ`, separability of each fibre
is squarefreeness. Combined with `Polynomial.separable_of_discr_ne_zero`, it suffices that the
discriminant of `P t` does not vanish on `[0, 1]`. -/
theorem splits_of_path_of_separable (P : ℝ → ℝ[X]) {d : ℕ}
    (hcoeff : ∀ k : ℕ, ContinuousOn (fun t => (P t).coeff k) (Icc 0 1))
    (hdeg : ∀ t ∈ Icc (0 : ℝ) 1, (P t).natDegree = d)
    (hsep : ∀ t ∈ Icc (0 : ℝ) 1, (P t).Separable) (h0 : (P 0).Splits) :
    (P 1).Splits :=
  splits_of_path P hcoeff hdeg (fun t ht => (hsep t ht).squarefree) h0

end RealRooted
