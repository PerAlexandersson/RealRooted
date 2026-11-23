/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

public import RealRooted.Basic.ProperPosition
import RealRooted.Mathlib.Analysis.Polynomial.SimpleRootMatching
import RealRooted.SimpleRoots
import RealRooted.Bezoutian.RootEvaluation
import RealRooted.Wronskian.Forward
import TauCeti.Topology.MetricSpace.SeparatedBalls
import Mathlib.Tactic.Linarith

/-!
# Stability of strict root interlacing

Coefficient perturbations of a simple adjacent-degree pair preserve its strict
root inequalities. The two perturbations are independent. A common separation
radius for both reference root sets excludes collisions between the two families.
-/

public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted

/-- Adjacent-degree interlacing without a common root gives strict inequalities
between any increasing enumerations of the roots. -/
theorem StrictInterl.interlacing_fin_succ {p q : ℝ[X]} {n : ℕ}
    (h : StrictInterl p q) (hpdeg : p.natDegree = n) (hqdeg : q.natDegree = n + 1)
    (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x)
    (r : Fin n → ℝ) (hr : StrictMono r) (hrroot : ∀ i, p.IsRoot (r i))
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (hsroot : ∀ i, q.IsRoot (s i)) :
    ∀ i : Fin n, s i.castSucc < r i ∧ r i < s i.succ := by
  obtain ⟨_, _, _, ss, rs, hss, hrs, hsseq, hrseq, hinter⟩ :=
    h.toInterlaces (by lia)
  have hsorteq : ss = List.ofFn s := by
    have hperm : List.Perm ss (q.roots.sort (· ≤ ·)) :=
      Multiset.coe_eq_coe.mp (by rw [hsseq, Multiset.sort_eq])
    have hsorted : (q.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    rw [List.Perm.eq_of_sortedLE hss.sortedLE hsorted.sortedLE hperm]
    simpa only [List.ofFn_eq_map] using
      Polynomial.roots_sort_eq_of_isRoot h.2.1.1 hqdeg s hsroot hs
  have hrorteq : rs = List.ofFn r := by
    have hperm : List.Perm rs (p.roots.sort (· ≤ ·)) :=
      Multiset.coe_eq_coe.mp (by rw [hrseq, Multiset.sort_eq])
    have hsorted : (p.roots.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    rw [List.Perm.eq_of_sortedLE hrs.sortedLE hsorted.sortedLE hperm]
    simpa only [List.ofFn_eq_map] using
      Polynomial.roots_sort_eq_of_isRoot h.1.1 hpdeg r hrroot hr
  rw [hsorteq, hrorteq] at hinter
  intro i
  obtain ⟨hleft, hright⟩ := listInterlaces_getElem_le hinter (by simp) i.val (by
    simp)
  have hleft' : s i.castSucc ≤ r i := by
    cases i
    simpa only [List.getElem_ofFn, Fin.castSucc_mk] using hleft
  have hright' : r i ≤ s i.succ := by
    simpa only [List.getElem_ofFn, Fin.eta, Fin.succ] using hright
  refine ⟨lt_of_le_of_ne hleft' ?_, lt_of_le_of_ne hright' ?_⟩
  · intro he
    exact hno _ (hrroot i) (he ▸ hsroot i.castSucc)
  · intro he
    exact hno _ (hrroot i) (he.symm ▸ hsroot i.succ)

/-- Strict inequalities between complete increasing root enumerations give
adjacent-degree interlacing. The degree-zero left endpoint is included. -/
theorem interlaces_of_interlacing_fin_succ {p q : ℝ[X]} {n : ℕ}
    (hp : p ≠ 0) (hps : p.Splits) (hpdeg : p.natDegree = n)
    (hq : q ≠ 0) (hqs : q.Splits) (hqdeg : q.natDegree = n + 1)
    (r : Fin n → ℝ) (hr : StrictMono r) (hrroot : ∀ i, p.IsRoot (r i))
    (s : Fin (n + 1) → ℝ) (hs : StrictMono s) (hsroot : ∀ i, q.IsRoot (s i))
    (hchain : ∀ i : Fin n, s i.castSucc < r i ∧ r i < s i.succ) :
    Interlaces p q := by
  have hrseq : p.roots.sort (· ≤ ·) = List.ofFn r := by
    simpa only [List.ofFn_eq_map] using
      Polynomial.roots_sort_eq_of_isRoot hp hpdeg r hrroot hr
  have hsseq : q.roots.sort (· ≤ ·) = List.ofFn s := by
    simpa only [List.ofFn_eq_map] using
      Polynomial.roots_sort_eq_of_isRoot hq hqdeg s hsroot hs
  refine ⟨⟨hq, hqs⟩, ⟨hp, hps⟩, by lia,
    q.roots.sort (· ≤ ·), p.roots.sort (· ≤ ·),
    Multiset.pairwise_sort .., Multiset.pairwise_sort ..,
    Multiset.sort_eq .., Multiset.sort_eq .., ?_⟩
  rw [hrseq, hsseq]
  apply listInterlaces_of_interleaves_of_length (by simp)
  exact List.interleaves_ofFn_odd.mpr
    ⟨fun i => (hchain i).2.le, fun i => (hchain i).1.le⟩

/-- Perturbing separated real points by less than their common radius preserves order. -/
private theorem lt_of_close_of_separated {T : Finset ℝ} {ε : ℝ}
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * ε < dist a b)
    {a b a' b' : ℝ} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a < b) (ha' : |a' - a| < ε) (hb' : |b' - b| < ε) : a' < b' := by
  have hgap := hsep a ha b hb hab.ne
  rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hab)] at hgap
  obtain ⟨ha₁, ha₂⟩ := abs_lt.mp ha'
  obtain ⟨hb₁, hb₂⟩ := abs_lt.mp hb'
  linarith

/-- Separated reference root sets remain disjoint under two small root matchings. -/
private theorem no_common_root_of_close_matchings {p q P Q : ℝ[X]}
    {e d : ℝ → ℝ} {ε : ℝ} (hPne : P ≠ 0) (hQne : Q ≠ 0)
    (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x)
    (hsep : ∀ a ∈ p.roots, ∀ b ∈ q.roots, a ≠ b → 2 * ε < dist a b)
    (he : Set.SurjOn e p.roots.toFinset P.roots.toFinset)
    (hd : Set.SurjOn d q.roots.toFinset Q.roots.toFinset)
    (heclose : ∀ a ∈ p.roots, |e a - a| < ε)
    (hdclose : ∀ b ∈ q.roots, |d b - b| < ε) :
    ∀ x, P.IsRoot x → ¬ Q.IsRoot x := by
  intro x hxP hxQ
  obtain ⟨a, ha, hax⟩ := he
    (Multiset.mem_toFinset.mpr ((mem_roots hPne).mpr hxP))
  obtain ⟨b, hb, hbx⟩ := hd
    (Multiset.mem_toFinset.mpr ((mem_roots hQne).mpr hxQ))
  have hap : a ∈ p.roots := Multiset.mem_toFinset.mp ha
  have hbq : b ∈ q.roots := Multiset.mem_toFinset.mp hb
  have hab : a ≠ b := by
    intro hab
    exact hno a (isRoot_of_mem_roots hap) (hab.symm ▸ isRoot_of_mem_roots hbq)
  have hgap := hsep a hap b hbq hab
  have haclose := heclose a hap
  have hbclose := hdclose b hbq
  rw [hax] at haclose
  rw [hbx] at hbclose
  rw [Real.dist_eq] at hgap
  have htri := abs_sub_le a x b
  rw [abs_sub_comm a x] at htri
  linarith

/-- A common coefficient neighborhood preserves genuine strict interlacing of a
monic adjacent-degree reference pair. Neither perturbed polynomial is assumed
to split. The no-common-root conclusion records strictness beyond `Interlaces`.
The empty lower root list, hence `n = 0`, is included. -/
theorem exists_coeff_radius_interlaces {p q : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : IsMonicOfDegree q (n + 1))
    (h : StrictInterl p q) (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x) :
    ∃ δ > 0, ∀ P Q : ℝ[X], P.natDegree ≤ n → Q.natDegree ≤ n + 1 →
      (∀ k ≤ n, |P.coeff k - p.coeff k| < δ) →
      (∀ k ≤ n + 1, |Q.coeff k - q.coeff k| < δ) →
      P.natDegree = n ∧ Q.natDegree = n + 1 ∧
        Interlaces P Q ∧ ∀ x, P.IsRoot x → ¬ Q.IsRoot x := by
  classical
  have hsimple := h.hasSimpleRoots_of_no_common_root fun x hx => hno x hx.1 hx.2
  obtain ⟨r, hr, hrroot⟩ := Polynomial.exists_strictMono_roots h.1.2 hp.natDegree_eq
    hsimple.1.roots_nodup
  obtain ⟨s, hs, hsroot⟩ := Polynomial.exists_strictMono_roots h.2.1.2 hq.natDegree_eq
    hsimple.2.roots_nodup
  have hchain := h.interlacing_fin_succ hp.natDegree_eq hq.natDegree_eq hno
    r hr hrroot s hs hsroot
  let T := p.roots.toFinset ∪ q.roots.toFinset
  obtain ⟨ε, hε, _, hsep⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := T) (U := fun _ => Set.univ) (fun _ _ => Filter.univ_mem)
  have hpT {x : ℝ} (hx : x ∈ p.roots) : x ∈ T :=
    Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr hx))
  have hqT {x : ℝ} (hx : x ∈ q.roots) : x ∈ T :=
    Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hx))
  have hrmem (i : Fin n) : r i ∈ p.roots := (mem_roots hp.monic.ne_zero).mpr (hrroot i)
  have hsmem (i : Fin (n + 1)) : s i ∈ q.roots :=
    (mem_roots hq.monic.ne_zero).mpr (hsroot i)
  obtain ⟨δp, hδp, hmatchp⟩ := _root_.Polynomial.exists_coeff_radius_roots_bijection
    hp h.1.2 hsimple.1.roots_nodup hε
  obtain ⟨δq, hδq, hmatchq⟩ := _root_.Polynomial.exists_coeff_radius_roots_bijection
    hq h.2.1.2 hsimple.2.roots_nodup hε
  refine ⟨min δp δq, lt_min hδp hδq, ?_⟩
  intro P Q hP hQ hPc hQc
  obtain ⟨hPdegree, hPs, _, e, he, heclose⟩ := hmatchp P hP
    (fun k hk => (hPc k hk).trans_le (min_le_left _ _))
  obtain ⟨hQdegree, hQs, _, d, hd, hdclose⟩ := hmatchq Q hQ
    (fun k hk => (hQc k hk).trans_le (min_le_right _ _))
  have hPne : P ≠ 0 := degree_ne_bot.mp (by rw [hPdegree]; exact WithBot.coe_ne_bot)
  have hQne : Q ≠ 0 := degree_ne_bot.mp (by rw [hQdegree]; exact WithBot.coe_ne_bot)
  have hPn : P.natDegree = n := natDegree_eq_of_degree_eq_some hPdegree
  have hQn : Q.natDegree = n + 1 := natDegree_eq_of_degree_eq_some hQdegree
  have heroot (i : Fin n) : P.IsRoot (e (r i)) :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp
      (he.mapsTo (Multiset.mem_toFinset.mpr (hrmem i))))
  have hdroot (i : Fin (n + 1)) : Q.IsRoot (d (s i)) :=
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp
      (hd.mapsTo (Multiset.mem_toFinset.mpr (hsmem i))))
  have hemono : StrictMono (fun i => e (r i)) := by
    intro i j hij
    exact lt_of_close_of_separated hsep (hpT (hrmem i)) (hpT (hrmem j)) (hr hij)
      (heclose _ (hrmem i)).1 (heclose _ (hrmem j)).1
  have hdmono : StrictMono (fun i => d (s i)) := by
    intro i j hij
    exact lt_of_close_of_separated hsep (hqT (hsmem i)) (hqT (hsmem j)) (hs hij)
      (hdclose _ (hsmem i)).1 (hdclose _ (hsmem j)).1
  have hchain' (i : Fin n) : d (s i.castSucc) < e (r i) ∧ e (r i) < d (s i.succ) := by
    exact ⟨lt_of_close_of_separated hsep (hqT (hsmem i.castSucc)) (hpT (hrmem i))
        (hchain i).1
        (hdclose _ (hsmem i.castSucc)).1 (heclose _ (hrmem i)).1,
      lt_of_close_of_separated hsep (hpT (hrmem i)) (hqT (hsmem i.succ)) (hchain i).2
        (heclose _ (hrmem i)).1 (hdclose _ (hsmem i.succ)).1⟩
  refine ⟨hPn, hQn, interlaces_of_interlacing_fin_succ hPne hPs hPn hQne hQs hQn
    (fun i => e (r i)) hemono heroot (fun i => d (s i)) hdmono hdroot hchain', ?_⟩
  exact no_common_root_of_close_matchings hPne hQne hno
    (fun a ha b hb hab => hsep a (hpT ha) b (hqT hb) hab)
    he.surjOn hd.surjOn (fun a ha => (heclose a ha).1) (fun b hb => (hdclose b hb).1)

/-- Two independent finite coefficient limits to a strict adjacent-degree pair
eventually interlace without common roots. This applies equally to two different
windows indexed by one filter. -/
theorem eventually_interlaces_of_coeff_tendsto
    {ι : Type*} {l : Filter ι} {P Q : ι → ℝ[X]} {p q : ℝ[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) (hq : IsMonicOfDegree q (n + 1))
    (h : StrictInterl p q) (hno : ∀ x, p.IsRoot x → ¬ q.IsRoot x)
    (hPdeg : ∀ᶠ t in l, (P t).natDegree ≤ n)
    (hQdeg : ∀ᶠ t in l, (Q t).natDegree ≤ n + 1)
    (hPc : ∀ k ≤ n, Tendsto (fun t => (P t).coeff k) l (𝓝 (p.coeff k)))
    (hQc : ∀ k ≤ n + 1, Tendsto (fun t => (Q t).coeff k) l (𝓝 (q.coeff k))) :
    ∀ᶠ t in l, (P t).natDegree = n ∧ (Q t).natDegree = n + 1 ∧
      Interlaces (P t) (Q t) ∧ ∀ x, (P t).IsRoot x → ¬ (Q t).IsRoot x := by
  obtain ⟨δ, hδ, hclose⟩ := exists_coeff_radius_interlaces hp hq h hno
  have hPe : ∀ᶠ t in l, ∀ i : Fin (n + 1),
      |(P t).coeff i.val - p.coeff i.val| < δ := by
    apply eventually_all.mpr
    intro i
    have hi : Tendsto (fun t => |(P t).coeff i.val - p.coeff i.val|) l (𝓝 0) := by
      simpa only [sub_self, abs_zero] using
        ((hPc i.val (Nat.le_of_lt_succ i.is_lt)).sub
          (tendsto_const_nhds (x := p.coeff i.val))).abs
    exact hi.eventually_lt tendsto_const_nhds hδ
  have hQe : ∀ᶠ t in l, ∀ i : Fin (n + 2),
      |(Q t).coeff i.val - q.coeff i.val| < δ := by
    apply eventually_all.mpr
    intro i
    have hi : Tendsto (fun t => |(Q t).coeff i.val - q.coeff i.val|) l (𝓝 0) := by
      simpa only [sub_self, abs_zero] using
        ((hQc i.val (by lia)).sub (tendsto_const_nhds (x := q.coeff i.val))).abs
    exact hi.eventually_lt tendsto_const_nhds hδ
  filter_upwards [hPdeg, hQdeg, hPe, hQe] with t htP htQ hcP hcQ
  exact hclose (P t) (Q t) htP htQ
    (fun k hk => hcP ⟨k, by lia⟩) (fun k hk => hcQ ⟨k, by lia⟩)

end RealRooted
