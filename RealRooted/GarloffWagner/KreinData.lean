import RealRooted.GarloffWagner.Iterated

/-!
# Garloff--Wagner Krein data

Root-multiplicity divisibility, root-deleted summands, and degree control for
the Krein expansion.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem rootMultiplicity_sub_one_le_of_prec_right {f g : ℝ[X]} (h : Prec f g)
    (u : ℝ) :
    g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u := by
  exact (rootMultiplicity_bounds_of_prec h u).2

/-- If `f ≪ g` and `u` is a root of `g`, then `f` is divisible by all but
one copy of the `u`-factor of `g`.  This is the quotient of the left input
used before defining the Krein coefficient at `u`. -/
theorem exists_precLeft_factor_of_right_isRoot {f g : ℝ[X]} (h : Prec f g)
    {u : ℝ} (hu : g.IsRoot u) :
    ∃ s : ℝ[X],
      f = (X - C u) ^ (g.rootMultiplicity u - 1) * s ∧
        s ≠ 0 ∧ s.Splits ∧
        1 ≤ g.rootMultiplicity u := by
  have hf0 : f ≠ 0 := h.1.1
  have hfs : f.Splits := h.1.2
  have hmul : g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u :=
    rootMultiplicity_sub_one_le_of_prec_right h u
  have hdvd : (X - C u) ^ (g.rootMultiplicity u - 1) ∣ f :=
    (le_rootMultiplicity_iff hf0).mp hmul
  obtain ⟨s, hs⟩ := hdvd
  have hs0 : s ≠ 0 := by
    intro hs_zero
    rw [hs_zero, mul_zero] at hs
    exact hf0 hs
  have hs_dvd : s ∣ f := ⟨(X - C u) ^ (g.rootMultiplicity u - 1), by
    rw [hs]
    ring⟩
  exact ⟨s, hs, hs0, (isRealRooted_of_dvd hf0 hfs hs0 hs_dvd).2,
    Nat.succ_le_of_lt ((rootMultiplicity_pos h.2.1.1).2 hu)⟩

/-- For the coefficient construction, every residual `f - c g` is divisible by
the same one-less-than-full `u`-factor measured from the right input `g`. -/
theorem exists_precResidual_factor_of_right_rootMultiplicity {f g : ℝ[X]}
    (h : Prec f g) (u : ℝ) (c : ℝ) :
    ∃ s : ℝ[X],
      f - C c * g = (X - C u) ^ (g.rootMultiplicity u - 1) * s := by
  let d : ℝ[X] := (X - C u) ^ (g.rootMultiplicity u - 1)
  have hdvd_f : d ∣ f := by
    have hf0 : f ≠ 0 := h.1.1
    have hmul : g.rootMultiplicity u - 1 ≤ f.rootMultiplicity u :=
      rootMultiplicity_sub_one_le_of_prec_right h u
    dsimp [d]
    exact (le_rootMultiplicity_iff hf0).mp hmul
  have hg0 : g ≠ 0 := h.2.1.1
  have hmul_g : g.rootMultiplicity u - 1 ≤ g.rootMultiplicity u := Nat.sub_le _ _
  have hdvd_g : d ∣ g := by
    dsimp [d]
    exact (le_rootMultiplicity_iff hg0).mp hmul_g
  obtain ⟨sf, hf⟩ := hdvd_f
  obtain ⟨sg, hg⟩ := hdvd_g
  refine ⟨sf - C c * sg, ?_⟩
  change f - C c * g = d * (sf - C c * sg)
  rw [hf, hg]
  ring

/-- If two polynomials have the same `(m - 1)`-fold root factor at `u`, then
choosing the coefficient by quotient evaluation makes their difference gain
the full `m`-fold root factor. -/
theorem kreinCoefficient_sub_dvd_fullRoot
    {h q r s : ℝ[X]} {u : ℝ} {m : ℕ}
    (hm : 1 ≤ m)
    (hh : h = (X - C u) ^ (m - 1) * s)
    (hq : q = (X - C u) ^ (m - 1) * r)
    (hr : r.eval u ≠ 0) :
    (X - C u) ^ m ∣ h - C (s.eval u / r.eval u) * q := by
  let a : ℝ := s.eval u / r.eval u
  change (X - C u) ^ m ∣ h - C a * q
  have hroot : (s - C a * r).IsRoot u := by
    rw [Polynomial.IsRoot.def, eval_sub, eval_mul, eval_C]
    dsimp [a]
    field_simp [hr]
    ring
  obtain ⟨t, ht⟩ := (dvd_iff_isRoot).2 hroot
  refine ⟨t, ?_⟩
  rw [hh, hq]
  calc
    (X - C u) ^ (m - 1) * s - C a * ((X - C u) ^ (m - 1) * r)
        = (X - C u) ^ (m - 1) * (s - C a * r) := by ring
    _ = (X - C u) ^ (m - 1) * ((X - C u) * t) := by rw [ht]
    _ = (X - C u) ^ m * t := by
      nth_rw 2 [show m = m - 1 + 1 by exact (Nat.sub_add_cancel hm).symm]
      ring

/-- Coefficient-evaluation divisibility step in the local Garloff--Wagner
orientation.  After factoring a residual and a deleted-root summand by the
same one-less-than-full right-root power, subtracting the evaluation coefficient
makes the new residual divisible by the full right-root power. -/
theorem kreinCoefficient_sub_dvd_rightRootMultiplicity
    {f g q r s : ℝ[X]} (hfg : Prec f g) {u c : ℝ} (hu : g.IsRoot u)
    (hres : f - C c * g = (X - C u) ^ (g.rootMultiplicity u - 1) * s)
    (hq : q = (X - C u) ^ (g.rootMultiplicity u - 1) * r)
    (hr : r.eval u ≠ 0) :
    (X - C u) ^ (g.rootMultiplicity u) ∣
      f - C c * g - C (s.eval u / r.eval u) * q :=
  kreinCoefficient_sub_dvd_fullRoot
    (m := g.rootMultiplicity u)
    (Nat.succ_le_of_lt ((rootMultiplicity_pos hfg.2.1.1).2 hu))
    hres hq hr

/-- Deleting the root `u` from `g` leaves the full root multiplicity at every
different root `v`.  This is the preservation input for iterating the
coefficient subtraction over distinct roots. -/
theorem kreinDeletedSummand_dvd_fullRootMultiplicity_of_ne
    {g q : ℝ[X]} {u v : ℝ} (hg0 : g ≠ 0)
    (hfactor : g = (X - C u) * q) (hvu : v ≠ u) :
    (X - C v) ^ (g.rootMultiplicity v) ∣ q := by
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hfactor
    exact hg0 hfactor
  have hmul0 : (X - C u) * q ≠ 0 := by
    rw [← hfactor]
    exact hg0
  have hmul := rootMultiplicity_mul (x := v) hmul0
  have hlin : (X - C u : ℝ[X]).rootMultiplicity v = 0 := by
    rw [rootMultiplicity_X_sub_C]
    simp [hvu]
  have hmult : g.rootMultiplicity v = q.rootMultiplicity v := by rw [hfactor, hmul, hlin, zero_add]
  exact (le_rootMultiplicity_iff hq0).mp hmult.le

/-- Subtracting a multiple of a root-deleted summand preserves full-power
divisibility at every other root. -/
theorem fullRootMultiplicity_dvd_sub_kreinDeletedSummand_of_ne
    {g h q : ℝ[X]} {u v a : ℝ}
    (hdvd : (X - C v) ^ (g.rootMultiplicity v) ∣ h)
    (hg0 : g ≠ 0) (hfactor : g = (X - C u) * q) (hvu : v ≠ u) :
    (X - C v) ^ (g.rootMultiplicity v) ∣ h - C a * q := by
  have hq_dvd : (X - C v) ^ (g.rootMultiplicity v) ∣ q :=
    kreinDeletedSummand_dvd_fullRootMultiplicity_of_ne hg0 hfactor hvu
  exact dvd_sub hdvd (dvd_mul_of_dvd_right hq_dvd (C a))

/-- A finite list of deleted-root summands preserves full divisibility at a
fixed different root. -/
theorem fullRootMultiplicity_dvd_sub_weightedSum_deletedSummands_of_forall_ne
    {g h : ℝ[X]} {v : ℝ} (hg0 : g ≠ 0)
    {l : List (ℝ × ℝ[X])}
    (hdvd : (X - C v) ^ (g.rootMultiplicity v) ∣ h)
    (hfactor : ∀ ap ∈ l, ∃ u : ℝ, g = (X - C u) * ap.2 ∧ v ≠ u) :
    (X - C v) ^ (g.rootMultiplicity v) ∣ h - weightedSum l := by
  induction l generalizing h with
  | nil =>
      simpa using hdvd
  | cons ap l ih =>
      rcases ap with ⟨a, p⟩
      rcases hfactor (a, p) (by simp) with ⟨u, hfactor_u, hvu⟩
      have htail : ∀ bp ∈ l, ∃ w : ℝ, g = (X - C w) * bp.2 ∧ v ≠ w := by
        intro bp hbp
        exact hfactor bp (by simp [hbp])
      have hstep : (X - C v) ^ (g.rootMultiplicity v) ∣ h - C a * p :=
        fullRootMultiplicity_dvd_sub_kreinDeletedSummand_of_ne
          hdvd hg0 hfactor_u hvu
      have htail_dvd :
          (X - C v) ^ (g.rootMultiplicity v) ∣
            (h - C a * p) - weightedSum l :=
        ih hstep htail
      convert htail_dvd using 1
      simp [weightedSum_cons]
      ring_nf

/-- Simultaneously subtracting the coefficient attached to each distinct root
of `g` leaves a residual divisible by the full root power at every processed
root, provided the one-root coefficient step has been proved for each root. -/
theorem fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
    {g h : ℝ[X]} (hg0 : g ≠ 0)
    (roots : List ℝ) (hnodup : roots.Nodup)
    (a : ℝ → ℝ) (q : ℝ → ℝ[X])
    (hfactor : ∀ u ∈ roots, g = (X - C u) * q u)
    (hgain : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ h - C (a u) * q u) :
    ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣
        h - weightedSum (roots.map fun v => (a v, q v)) := by
  induction roots generalizing h with
  | nil =>
      simp
  | cons x xs ih =>
      intro u hu
      have hx_not_mem : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hu with hux | hu_xs
      · subst u
        have hdvd_x :
            (X - C x) ^ (g.rootMultiplicity x) ∣ h - C (a x) * q x :=
          hgain x (by simp)
        have htail_factor :
            ∀ ap ∈ xs.map fun v => (a v, q v),
              ∃ y : ℝ, g = (X - C y) * ap.2 ∧ x ≠ y := by
          intro ap hap
          rcases List.mem_map.mp hap with ⟨y, hy, rfl⟩
          have hxy : x ≠ y := by
            intro hxy
            exact hx_not_mem (by simpa [hxy] using hy)
          exact ⟨y, hfactor y (by simp [hy]), hxy⟩
        have htail_dvd :
            (X - C x) ^ (g.rootMultiplicity x) ∣
              (h - C (a x) * q x) - weightedSum (xs.map fun v => (a v, q v)) :=
          fullRootMultiplicity_dvd_sub_weightedSum_deletedSummands_of_forall_ne
            hg0 hdvd_x htail_factor
        convert htail_dvd using 1
        simp [weightedSum_cons]
        ring_nf
      · have hfactor_tail : ∀ v ∈ xs, g = (X - C v) * q v := by
          intro v hv
          exact hfactor v (by simp [hv])
        have hgain_tail : ∀ v ∈ xs,
            (X - C v) ^ (g.rootMultiplicity v) ∣
              (h - C (a x) * q x) - C (a v) * q v := by
          intro v hv
          have hdvd_v :
              (X - C v) ^ (g.rootMultiplicity v) ∣ h - C (a v) * q v :=
            hgain v (by simp [hv])
          have hvx : v ≠ x := by
            intro hvx
            exact hx_not_mem (by simpa [hvx] using hv)
          have hpres :
              (X - C v) ^ (g.rootMultiplicity v) ∣
                (h - C (a v) * q v) - C (a x) * q x :=
            fullRootMultiplicity_dvd_sub_kreinDeletedSummand_of_ne
              hdvd_v hg0 (hfactor x (by simp)) hvx
          convert hpres using 1
          ring
        have htail_dvd :
            (X - C u) ^ (g.rootMultiplicity u) ∣
              (h - C (a x) * q x) -
                weightedSum (xs.map fun v => (a v, q v)) :=
          ih hxs_nodup hfactor_tail hgain_tail u hu_xs
        convert htail_dvd using 1
        simp [weightedSum_cons]
        ring_nf

/-- If a residual is divisible by every full root power of a splitting
polynomial `g`, then it is divisible by `g`. -/
theorem dvd_of_forall_fullRootMultiplicity_dvd
    {g h : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits)
    (hdiv : ∀ u : ℝ, (X - C u) ^ g.rootMultiplicity u ∣ h) :
    g ∣ h := by
  by_cases hh0 : h = 0
  · simp [hh0]
  apply hgs.dvd_of_roots_le_roots hg0
  rw [Multiset.le_iff_count]
  intro u
  rw [count_roots g, count_roots h]
  exact (le_rootMultiplicity_iff hh0).mpr (hdiv u)

/-- Root-list version of `dvd_of_forall_fullRootMultiplicity_dvd`, matching the
output expected from the finite distinct-root assembly. -/
theorem dvd_of_roots_fullRootMultiplicity_dvd
    {g h : ℝ[X]} (hg0 : g ≠ 0) (hgs : g.Splits)
    (hdiv : ∀ u ∈ g.roots, (X - C u) ^ g.rootMultiplicity u ∣ h) :
    g ∣ h := by
  by_cases hh0 : h = 0
  · simp [hh0]
  apply hgs.dvd_of_roots_le_roots hg0
  rw [Multiset.le_iff_count]
  intro u
  rw [count_roots g, count_roots h]
  by_cases hu : u ∈ g.roots
  · exact (le_rootMultiplicity_iff hh0).mpr (hdiv u hu)
  · have hcount : rootMultiplicity u g = 0 := by
      rw [← count_roots g]
      exact Multiset.count_eq_zero.mpr hu
    simp [hcount]

/-- A summand of the cone in Garloff--Wagner Lemma 7, relative to the right
polynomial `g`: either `g` itself or the quotient obtained by deleting one
linear root factor from `g`. -/
def IsGWKreinSummand (g q : ℝ[X]) : Prop :=
  q = g ∨ ∃ u : ℝ, g = (X - C u) * q

namespace IsGWKreinSummand

theorem ne_zero_and_splits {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    q ≠ 0 ∧ q.Splits := by
  rcases h with hself | ⟨u, hq⟩
  · simpa [hself] using ⟨hg0, hgs⟩
  · have hq0 : q ≠ 0 := by
      intro hq0
      rw [hq0, mul_zero] at hq
      exact hg0 hq
    have hq_dvd : q ∣ g := ⟨X - C u, by rw [hq]; ring⟩
    exact isRealRooted_of_dvd hg0 hgs hq0 hq_dvd

theorem hasPosLeadingCoeff {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hgpos : HasPosLeadingCoeff g) :
    HasPosLeadingCoeff q := by
  rcases h with hself | ⟨u, hq⟩
  · simpa [hself] using hgpos
  · have hmul : HasPosLeadingCoeff ((X - C u) * q) := by simpa [hq] using hgpos
    exact hasPosLeadingCoeff_of_X_sub_C_mul hmul

theorem gwJL_prec {k : ℕ} {g q : ℝ[X]} (h : IsGWKreinSummand g q)
    (hg0 : g ≠ 0) (hgs : g.Splits) :
    Prec (gwJL k q) (gwJL k g) := by
  rcases h with hself | ⟨u, hq⟩
  · rw [hself]
    exact prec_refl ((gwJL_ne_zero_iff k g).2 hg0)
      (gwJL_splits_of_splits hg0 hgs k)
  · obtain ⟨hq0, hqs⟩ := ne_zero_and_splits (g := g) (q := q) (Or.inr ⟨u, hq⟩)
      hg0 hgs
    rw [hq]
    exact gwJL_factor_prec_of_splits (k := k) (u := u) (f := q) hq0 hqs

end IsGWKreinSummand

/-- Factor a root of `g` into the one-root-deleted Krein summand and the
full-multiplicity residual.  The residual is nonzero at the deleted root, which
is the algebraic input used to define the corresponding Krein coefficient. -/
theorem exists_kreinSummand_factor_of_isRoot {g : ℝ[X]} (hg0 : g ≠ 0)
    (hgs : g.Splits) {u : ℝ} (hu : g.IsRoot u) :
    ∃ q r : ℝ[X],
      g = (X - C u) * q ∧
        q = (X - C u) ^ (g.rootMultiplicity u - 1) * r ∧
        ¬ (X - C u) ∣ r ∧
        r.eval u ≠ 0 ∧
        q ≠ 0 ∧ q.Splits ∧
        r ≠ 0 ∧ r.Splits ∧
        IsGWKreinSummand g q := by
  obtain ⟨r, hgr, hr_nodvd⟩ :=
    exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg0 u
  let q : ℝ[X] := (X - C u) ^ (g.rootMultiplicity u - 1) * r
  have hm : 1 ≤ g.rootMultiplicity u :=
    Nat.succ_le_of_lt ((rootMultiplicity_pos hg0).2 hu)
  have hfactor : g = (X - C u) * q := by
    rw [hgr]
    change (X - C u) ^ g.rootMultiplicity u * r =
      (X - C u) * ((X - C u) ^ (g.rootMultiplicity u - 1) * r)
    nth_rw 1 [show g.rootMultiplicity u = g.rootMultiplicity u - 1 + 1 by
      exact (Nat.sub_add_cancel hm).symm]
    ring
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hfactor
    exact hg0 hfactor
  have hq_dvd : q ∣ g := ⟨X - C u, by simpa [mul_comm] using hfactor⟩
  have hq_split : q.Splits := (isRealRooted_of_dvd hg0 hgs hq0 hq_dvd).2
  have hr0 : r ≠ 0 := by
    intro hr0
    rw [hr0, mul_zero] at hgr
    exact hg0 hgr
  have hr_dvd : r ∣ g := ⟨(X - C u) ^ g.rootMultiplicity u, by
    simpa [mul_comm] using hgr⟩
  have hr_split : r.Splits := (isRealRooted_of_dvd hg0 hgs hr0 hr_dvd).2
  exact ⟨q, r, hfactor, rfl, hr_nodvd,
    (fun hroot => hr_nodvd ((dvd_iff_isRoot).2 hroot)),
    hq0, hq_split, hr0, hr_split, Or.inr ⟨u, hfactor⟩⟩

/-- Single-root coefficient package for the Garloff--Wagner Lemma 7
construction.  For a root `u` of the right polynomial, this chooses the
deleted-root summand and the coefficient that gains the full `u`-root power. -/
theorem exists_kreinCoefficientData_of_right_isRoot {f g : ℝ[X]}
    (hfg : Prec f g) (hgs : g.Splits) (c : ℝ) {u : ℝ}
    (hu : g.IsRoot u) :
    ∃ a : ℝ, ∃ q : ℝ[X],
      g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
  rcases exists_kreinSummand_factor_of_isRoot hfg.2.1.1 hgs hu with
    ⟨q, r, hfactor, hq, _, hr_eval, _, _, _, _, hsummand⟩
  rcases exists_precResidual_factor_of_right_rootMultiplicity hfg u c with
    ⟨s, hres⟩
  exact ⟨s.eval u / r.eval u, q, hfactor, hsummand,
    kreinCoefficient_sub_dvd_rightRootMultiplicity hfg hu hres hq hr_eval⟩

/-- Subtracting the coefficient chosen at each distinct root of `g` gives a
residual divisible by `g`.  This is the identity-side part of the
Garloff--Wagner Lemma 7 expansion, before the final degree and sign arguments. -/
theorem exists_kreinRootDeletedSub_dvd_right {f g : ℝ[X]}
    (hfg : Prec f g) (c : ℝ) :
    ∃ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        g ∣ f - C c * g - weightedSum l := by
  classical
  let roots : List ℝ := g.roots.toFinset.toList
  have hroots_nodup : roots.Nodup := Finset.nodup_toList _
  have hroot : ∀ u ∈ roots, g.IsRoot u := by
    intro u hu
    exact (mem_roots hfg.2.1.1).mp
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hu))
  have hdata : ∀ u ∈ roots, ∃ a : ℝ, ∃ q : ℝ[X],
      g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
    intro u hu
    exact exists_kreinCoefficientData_of_right_isRoot hfg hfg.2.1.2 c (hroot u hu)
  choose a q hfactor hsummand hgain using hdata
  let a' : ℝ → ℝ := fun u => if hu : u ∈ roots then a u hu else 0
  let q' : ℝ → ℝ[X] := fun u => if hu : u ∈ roots then q u hu else 0
  let l : List (ℝ × ℝ[X]) := roots.map fun u => (a' u, q' u)
  have hfactor' : ∀ u ∈ roots, g = (X - C u) * q' u := by
    intro u hu
    simp [q', hu, hfactor u hu]
  have hgain' : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - C (a' u) * q' u := by
    intro u hu
    simp [a', q', hu, hgain u hu]
  have hdiv_roots : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    simpa [l] using
      fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
        hfg.2.1.1 roots hroots_nodup a' q' hfactor' hgain'
  have hdiv_all_roots : ∀ u ∈ g.roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    intro u hu
    exact hdiv_roots u (by
      rw [Finset.mem_toList, Multiset.mem_toFinset]
      exact hu)
  refine ⟨l, ?_, dvd_of_roots_fullRootMultiplicity_dvd hfg.2.1.1 hfg.2.1.2 hdiv_all_roots⟩
  intro ap hap
  rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
  simp [q', hu, hsummand u hu]

/-- Degree bound for a finite weighted sum, assuming every summand has degree
at most the same bound. -/
theorem natDegree_weightedSum_le_of_forall {l : List (ℝ × ℝ[X])} {n : ℕ}
    (h : ∀ ap ∈ l, ap.2.natDegree ≤ n) :
    (weightedSum l).natDegree ≤ n := by
  induction l with
  | nil => simp
  | cons ap l ih =>
      rcases ap with ⟨a, p⟩
      have hp : (C a * p).natDegree ≤ n :=
        (natDegree_C_mul_le a p).trans (h (a, p) (by simp))
      have htail : (weightedSum l).natDegree ≤ n := by
        apply ih
        intro bp hbp
        exact h bp (by simp [hbp])
      simpa [weightedSum_cons] using natDegree_add_le_of_le hp htail

/-- Strict version of `natDegree_weightedSum_le_of_forall`, for positive
degree bounds. -/
theorem natDegree_weightedSum_lt_of_forall {l : List (ℝ × ℝ[X])} {n : ℕ}
    (hn : 0 < n) (h : ∀ ap ∈ l, ap.2.natDegree < n) :
    (weightedSum l).natDegree < n := by
  have hle : (weightedSum l).natDegree ≤ n - 1 :=
    natDegree_weightedSum_le_of_forall (l := l) (n := n - 1) (by
      intro ap hap
      exact Nat.le_pred_of_lt (h ap hap))
  lia

/-- Deleting one linear factor from a nonzero polynomial strictly lowers
`natDegree`. -/
theorem natDegree_lt_of_kreinDeleted_factor {g q : ℝ[X]} {u : ℝ}
    (hg0 : g ≠ 0) (hfactor : g = (X - C u) * q) :
    q.natDegree < g.natDegree := by
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hfactor
    exact hg0 hfactor
  have hdeg : g.natDegree = q.natDegree + 1 := by
    rw [hfactor, natDegree_mul (X_sub_C_ne_zero u) hq0, natDegree_X_sub_C]
    exact Nat.add_comm 1 q.natDegree
  rw [hdeg]
  exact Nat.lt_succ_self _

/-- A weighted sum of one-root-deleted factors of `g` has degree strictly
smaller than `g`, provided `g` has positive degree. -/
theorem natDegree_weightedSum_deletedFactors_lt {g : ℝ[X]}
    (hg0 : g ≠ 0) (hgdeg : 0 < g.natDegree)
    (roots : List ℝ) (a : ℝ → ℝ) (q : ℝ → ℝ[X])
    (hfactor : ∀ u ∈ roots, g = (X - C u) * q u) :
    (weightedSum (roots.map fun u => (a u, q u))).natDegree < g.natDegree := by
  apply natDegree_weightedSum_lt_of_forall hgdeg
  intro ap hap
  rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
  exact natDegree_lt_of_kreinDeleted_factor hg0 (hfactor u hu)

/-- If two polynomials have degree strictly below a positive bound, then so does
their difference. -/
theorem natDegree_sub_lt_of_both_lt {p q : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n := by
  have hle : (p - q).natDegree ≤ n - 1 := by
    simpa using
      natDegree_sub_le_of_le (Nat.le_pred_of_lt hp) (Nat.le_pred_of_lt hq)
  lia

/-- If the coefficient at a positive upper degree bound vanishes, the actual
degree is strictly smaller than that bound. -/
theorem natDegree_lt_of_le_of_coeff_eq_zero {p : ℝ[X]} {n : ℕ}
    (hn : 0 < n) (hle : p.natDegree ≤ n) (hcoeff : p.coeff n = 0) :
    p.natDegree < n := by
  by_cases hp0 : p = 0
  · simp [hp0, hn]
  · by_contra hnot
    have hge : n ≤ p.natDegree := le_of_not_gt hnot
    have heq : p.natDegree = n := le_antisymm hle hge
    have hcoeff_ne : p.coeff n ≠ 0 := by
      rw [← heq]
      exact leadingCoeff_ne_zero.mpr hp0
    exact hcoeff_ne hcoeff

/-- Choose the scalar multiple of `g` that cancels the leading term of `f`,
when `f` has degree at most the positive degree of `g`. -/
theorem exists_C_mul_sub_natDegree_lt_of_le {f g : ℝ[X]}
    (hg0 : g ≠ 0) (hgdeg : 0 < g.natDegree) (hdeg : f.natDegree ≤ g.natDegree) :
    ∃ c : ℝ, (f - C c * g).natDegree < g.natDegree := by
  by_cases hlt : f.natDegree < g.natDegree
  · refine ⟨0, ?_⟩
    simpa using hlt
  · have hdeg_eq : f.natDegree = g.natDegree := le_antisymm hdeg (le_of_not_gt hlt)
    let c : ℝ := f.leadingCoeff / g.leadingCoeff
    refine ⟨c, ?_⟩
    have hc_top : (f - C c * g).coeff g.natDegree = 0 := by
      have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
      have hfcoeff : f.coeff g.natDegree = f.leadingCoeff := by
        rw [← hdeg_eq]
        rfl
      rw [coeff_sub, coeff_C_mul, hfcoeff]
      change f.leadingCoeff -
        (f.leadingCoeff / g.leadingCoeff) * g.leadingCoeff = 0
      field_simp [hg_lc_ne]
      ring
    have hle : (f - C c * g).natDegree ≤ g.natDegree := by
      simpa using natDegree_sub_le_of_le hdeg (natDegree_C_mul_le c g)
    exact natDegree_lt_of_le_of_coeff_eq_zero hgdeg hle hc_top

/-- Choose a nonnegative scalar multiple of `g` that cancels the leading term
of `f`, when both polynomials have positive leading coefficient and
`deg f ≤ deg g`. -/
theorem exists_nonneg_C_mul_sub_natDegree_lt_of_le {f g : ℝ[X]}
    (hfpos : HasPosLeadingCoeff f) (hgpos : HasPosLeadingCoeff g)
    (hgdeg : 0 < g.natDegree) (hdeg : f.natDegree ≤ g.natDegree) :
    ∃ c : ℝ, 0 ≤ c ∧ (f - C c * g).natDegree < g.natDegree := by
  by_cases hlt : f.natDegree < g.natDegree
  · refine ⟨0, by norm_num, ?_⟩
    simpa using hlt
  · have hdeg_eq : f.natDegree = g.natDegree := le_antisymm hdeg (le_of_not_gt hlt)
    let c : ℝ := f.leadingCoeff / g.leadingCoeff
    refine ⟨c, ?_, ?_⟩
    · dsimp [c]
      exact div_nonneg hfpos.le hgpos.le
    · have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hgpos
      have hc_top : (f - C c * g).coeff g.natDegree = 0 := by
        have hfcoeff : f.coeff g.natDegree = f.leadingCoeff := by
          rw [← hdeg_eq]
          rfl
        rw [coeff_sub, coeff_C_mul, hfcoeff]
        change f.leadingCoeff -
          (f.leadingCoeff / g.leadingCoeff) * g.leadingCoeff = 0
        field_simp [hg_lc_ne]
        ring
      have hle : (f - C c * g).natDegree ≤ g.natDegree := by
        simpa using natDegree_sub_le_of_le hdeg (natDegree_C_mul_le c g)
      exact natDegree_lt_of_le_of_coeff_eq_zero hgdeg hle hc_top

/-- A nonzero divisor cannot divide a polynomial of strictly smaller degree,
unless the smaller polynomial is zero. -/
theorem eq_zero_of_dvd_of_natDegree_lt {g h : ℝ[X]}
    (hg0 : g ≠ 0) (hdvd : g ∣ h) (hlt : h.natDegree < g.natDegree) :
    h = 0 := by
  rcases hdvd with ⟨r, rfl⟩
  by_cases hr0 : r = 0
  · simp [hr0]
  · exfalso
    rw [natDegree_mul hg0 hr0] at hlt
    lia

end RealRooted
