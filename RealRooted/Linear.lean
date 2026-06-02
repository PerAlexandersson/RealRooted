import RealRooted.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort

/-!
# Real-rootedness of linear polynomials

This file proves that every polynomial of the form `X - C r` is real-rooted,
and more generally that every nonzero polynomial of degree at most one is
real-rooted.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- `X - C r` is real-rooted: it has exactly one root, namely `r`. -/
lemma isRealRooted_X_sub_C (r : ℝ) : IsRealRooted (X - C r) :=
  ⟨X_sub_C_ne_zero r, by rw [roots_X_sub_C, Multiset.card_singleton, natDegree_X_sub_C]⟩

lemma hasPosLeadingCoeff_X_sub_C_mul {r : ℝ} {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff ((X - C r) * p) := by
  unfold HasPosLeadingCoeff at hp ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using hp

lemma roots_le_X_sub_C_mul {r : ℝ} {f : ℝ[X]}
    (hf : IsRealRooted f)
    (hf_le : ∀ s ∈ f.roots, s ≤ r) :
    ∀ s ∈ ((X - C r) * f).roots, s ≤ r := by
  intro s hs
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hf.1), roots_X_sub_C] at hs
  rcases Multiset.mem_add.mp hs with hs | hs
  · have hs' : s = r := by simpa [Multiset.mem_singleton] using hs
    rw [hs']
  · exact hf_le s hs

/-- A nonzero scalar multiple of a real-rooted polynomial is real-rooted. -/
lemma isRealRooted_C_mul {p : ℝ[X]} (hp : IsRealRooted p) {a : ℝ} (ha : a ≠ 0) :
    IsRealRooted (C a * p) :=
  ⟨mul_ne_zero (C_ne_zero.mpr ha) hp.1,
   by rw [roots_C_mul _ ha, natDegree_C_mul ha]; exact hp.2⟩

/-- A nonzero divisor of a real-rooted polynomial is real-rooted. -/
lemma isRealRooted_of_dvd {p q : ℝ[X]} (hp : IsRealRooted p) (hq0 : q ≠ 0) (hqp : q ∣ p) :
    IsRealRooted q := by
  rcases hqp with ⟨r, rfl⟩
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hp.1
  refine ⟨hq0, ?_⟩
  have hsum : q.roots.card + r.roots.card = (q * r).natDegree := by
    rw [← hp.2, roots_mul hp.1, Multiset.card_add]
  rw [natDegree_mul hq0 hr0] at hsum
  have hq_le : q.roots.card ≤ q.natDegree := card_roots' q
  have hr_le : r.roots.card ≤ r.natDegree := card_roots' r
  lia

/-- A root of a divisor is a root of the dividend. -/
lemma IsRoot.of_dvd {p q : ℝ[X]} (hpq : p ∣ q) {x : ℝ} (hx : p.IsRoot x) :
    q.IsRoot x := by
  rcases hpq with ⟨r, rfl⟩
  rw [Polynomial.IsRoot.def, eval_mul, Polynomial.IsRoot.def.mp hx, zero_mul]

/-- A common root of two polynomials is also a root of their sum. -/
lemma IsRoot.add {p q : ℝ[X]} {x : ℝ} (hp : p.IsRoot x) (hq : q.IsRoot x) :
    (p + q).IsRoot x := by
  rw [Polynomial.IsRoot.def, eval_add, Polynomial.IsRoot.def.mp hp, Polynomial.IsRoot.def.mp hq]
  ring

/-- If `(X - C r)^m` divides both summands, then it divides their sum. -/
lemma pow_X_sub_C_dvd_add {p q : ℝ[X]} {r : ℝ} {m : ℕ}
    (hp : (X - C r) ^ m ∣ p) (hq : (X - C r) ^ m ∣ q) :
    (X - C r) ^ m ∣ p + q := by
  exact dvd_add hp hq

/-- The root multiplicity in a sum is at least the minimum multiplicity
of the two summands. -/
lemma min_rootMultiplicity_le_rootMultiplicity_add {p q : ℝ[X]} {r : ℝ}
    (hpq : p + q ≠ 0) :
    min (p.rootMultiplicity r) (q.rootMultiplicity r) ≤ (p + q).rootMultiplicity r := by
  simpa using (Polynomial.rootMultiplicity_add (p := p) (q := q) r hpq)

/-- A nonunit real-rooted polynomial has a real root. -/
lemma exists_isRoot_of_isRealRooted_of_not_isUnit {p : ℝ[X]} (hp : IsRealRooted p)
    (hu : ¬ IsUnit p) : ∃ r : ℝ, p.IsRoot r := by
  have hdeg : 0 < p.natDegree := by
    rw [natDegree_pos_iff_degree_pos]
    exact degree_pos_of_ne_zero_of_nonunit hp.1 hu
  have hcard : 0 < p.roots.card := by
    rwa [hp.2]
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  exact ⟨r, (mem_roots hp.1).mp hr⟩

/-- If two real-rooted polynomials have no common real root, then they are coprime. -/
lemma isCoprime_of_no_common_real_root_of_isRealRooted {f g : ℝ[X]}
    (hf : IsRealRooted f) (_hg : IsRealRooted g)
    (hno : ∀ r : ℝ, f.IsRoot r → ¬ g.IsRoot r) :
    IsCoprime f g := by
  apply EuclideanDomain.isCoprime_of_dvd
  · exact fun hfg => hf.1 (hfg.1)
  · intro z hz_nonunit hz0 hzf hzg
    have hz_notunit : ¬ IsUnit z := by
      simpa [Set.mem_setOf_eq] using hz_nonunit
    have hz_rr : IsRealRooted z := isRealRooted_of_dvd hf hz0 hzf
    obtain ⟨r, hzr⟩ := exists_isRoot_of_isRealRooted_of_not_isUnit hz_rr hz_notunit
    have hfr : f.IsRoot r := IsRoot.of_dvd hzf hzr
    have hgr : g.IsRoot r := IsRoot.of_dvd hzg hzr
    exact hno r hfr hgr

/-- Any nonzero degree-1 polynomial is real-rooted. -/
lemma isRealRooted_of_degree_one {p : ℝ[X]} (hp : p.natDegree = 1) :
    IsRealRooted p := by
  have hne : p ≠ 0 := by intro h; simp [h] at hp
  have hdeg : p.degree = 1 := by rw [degree_eq_natDegree hne]; exact_mod_cast hp
  exact ⟨hne, by rw [roots_degree_eq_one hdeg, Multiset.card_singleton, hp]⟩

lemma interlaces_one_linear {p : ℝ[X]} (hp_deg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  have h1_rr : IsRealRooted (1 : ℝ[X]) := by
    simpa using isRealRooted_of_deg_zero (p := (1 : ℝ[X])) one_ne_zero (by simp)
  have hp_rr : IsRealRooted p := isRealRooted_of_degree_one hp_deg
  have hp_deg' : p.degree = 1 := by
    rw [degree_eq_natDegree hp_rr.1, hp_deg]
    norm_num
  refine ⟨hp_rr, h1_rr, by simp [Polynomial.natDegree_one, hp_deg], ?_⟩
  refine ⟨[-(p.coeff 1)⁻¹ * p.coeff 0], [], by simp, by simp, ?_, by simp,
    by simp [ListInterlaces]⟩
  simpa [hp_deg'] using (Polynomial.roots_degree_eq_one (p := p) hp_deg').symm

/-- If a list is sorted, then its tail interlaces into it. -/
lemma listInterlaces_tail_of_pairwise :
    ∀ rs : List ℝ, rs.Pairwise (· ≤ ·) → ListInterlaces rs.tail rs
  | [], _ => by simp [ListInterlaces]
  | [_], _ => by simp [ListInterlaces]
  | r₁ :: r₂ :: rs, hrs => by
      have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs (.head _)
      have htail : (r₂ :: rs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hrs).2
      simpa [List.tail, ListInterlaces, hr₁r₂] using
        listInterlaces_tail_of_pairwise (r₂ :: rs) htail

/-- Any sorted list alternates with itself. -/
lemma listAlternates_self_of_pairwise :
    ∀ rs : List ℝ, rs.Pairwise (· ≤ ·) → ListAlternates rs rs
  | [], _ => by simp [ListAlternates]
  | r :: rs, hrs => by
      refine ⟨le_rfl, ?_⟩
      simpa [List.tail] using listInterlaces_tail_of_pairwise (r :: rs) hrs

lemma pairwise_map_sub_const :
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) → ∀ r : ℝ, (rs.map (· - r)).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | x :: xs, h, r => by
      rw [List.pairwise_cons] at h
      rw [List.map, List.pairwise_cons]
      constructor
      · intro y hy
        rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
        exact sub_le_sub_right (h.1 z hz) r
      · simpa [List.map] using pairwise_map_sub_const h.2 r

lemma listInterlaces_map_sub_const :
    ∀ {ss rs : List ℝ}, ListInterlaces ss rs →
      ∀ r : ℝ, ListInterlaces (ss.map (· - r)) (rs.map (· - r))
  | [], [], _, _ => by simp [ListInterlaces]
  | [], [_], _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, h, t => by
      rcases h with ⟨hr₁s, hsr₂, htail⟩
      exact ⟨sub_le_sub_right hr₁s _, sub_le_sub_right hsr₂ _,
        listInterlaces_map_sub_const htail t⟩
  | [], _ :: _ :: _, h, _ => by simp [ListInterlaces] at h
  | _ :: _, [], h, _ => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h, _ => by simp [ListInterlaces] at h

lemma listAlternates_map_sub_const :
    ∀ {ss rs : List ℝ}, ListAlternates ss rs →
      ∀ r : ℝ, ListAlternates (ss.map (· - r)) (rs.map (· - r))
  | [], [], _, _ => by simp [ListAlternates]
  | s :: ss, r :: rs, h, t => by
      rcases h with ⟨hsr, htail⟩
      exact ⟨sub_le_sub_right hsr _, listInterlaces_map_sub_const htail t⟩
  | [], _ :: _, h, _ => by simp [ListAlternates] at h
  | _ :: _, [], h, _ => by simp [ListAlternates] at h

lemma rootMultiplicity_comp_X_add_C {p : ℝ[X]} (r x : ℝ) :
    (p.comp (X + C r)).rootMultiplicity x = p.rootMultiplicity (x + r) := by
  calc
    (p.comp (X + C r)).rootMultiplicity x
      = ((p.comp (X + C r)).comp (X + C x)).rootMultiplicity 0 := by
          rw [Polynomial.rootMultiplicity_eq_rootMultiplicity]
    _ = (p.comp (X + C (x + r))).rootMultiplicity 0 := by
          simp [comp_assoc, add_comm, add_left_comm]
    _ = p.rootMultiplicity (x + r) := by
          rw [← Polynomial.rootMultiplicity_eq_rootMultiplicity]

lemma roots_comp_X_add_C {p : ℝ[X]} (r : ℝ) :
    (p.comp (X + C r)).roots = p.roots.map (fun x => x - r) := by
  ext x
  rw [count_roots, rootMultiplicity_comp_X_add_C]
  simpa [count_roots, add_comm, add_left_comm, add_assoc] using
    (Multiset.count_map_eq_count' (fun y : ℝ => y - r) p.roots
      (fun a b hab => by linarith) (x + r)).symm

lemma isRealRooted_comp_X_add_C {p : ℝ[X]} (hp : IsRealRooted p) (r : ℝ) :
    IsRealRooted (p.comp (X + C r)) := by
  refine ⟨(Polynomial.comp_X_add_C_ne_zero_iff).2 hp.1, ?_⟩
  rw [roots_comp_X_add_C r, Multiset.card_map, natDegree_comp, natDegree_X_add_C, hp.2, mul_one]

/-- Translation by `r` preserves `Prec`: roots are shifted left by `r`,
so the relative order is unchanged. -/
lemma prec_comp_X_add_C {f g : ℝ[X]} (h : Prec f g) (r : ℝ) :
    Prec (f.comp (X + C r)) (g.comp (X + C r)) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  refine ⟨isRealRooted_comp_X_add_C hf r, isRealRooted_comp_X_add_C hg r,
    ss.map (· - r), rs.map (· - r), ?_, ?_, ?_, ?_, ?_⟩
  · exact pairwise_map_sub_const hss r
  · exact pairwise_map_sub_const hrs r
  · calc
      (↑(ss.map (· - r)) : Multiset ℝ) = (↑ss : Multiset ℝ).map (fun x => x - r) := rfl
      _ = f.roots.map (fun x => x - r) := by rw [hss_eq]
      _ = (f.comp (X + C r)).roots := (roots_comp_X_add_C r).symm
  · calc
      (↑(rs.map (· - r)) : Multiset ℝ) = (↑rs : Multiset ℝ).map (fun x => x - r) := rfl
      _ = g.roots.map (fun x => x - r) := by rw [hrs_eq]
      _ = (g.comp (X + C r)).roots := (roots_comp_X_add_C r).symm
  · rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · exact Or.inl ⟨by simpa using hlen, listInterlaces_map_sub_const hint r⟩
    · exact Or.inr ⟨by simpa using hlen, listAlternates_map_sub_const halt r⟩

/-- Translation by `r` is an equivalence on `Prec`. -/
lemma prec_comp_X_add_C_iff {f g : ℝ[X]} (r : ℝ) :
    Prec (f.comp (X + C r)) (g.comp (X + C r)) ↔ Prec f g := by
  constructor
  · intro h
    have h' := prec_comp_X_add_C h (-r)
    simpa [comp_assoc, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h'
  · intro h
    exact prec_comp_X_add_C h r

/-- A real-rooted polynomial interlaces with itself in the same-degree sense. -/
lemma prec_refl {f : ℝ[X]} (hf : IsRealRooted f) : Prec f f := by
  set rs := f.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  exact ⟨hf, hf, rs, rs, hrs_sorted, hrs_sorted, hrs_eq, hrs_eq,
    Or.inr ⟨by simp, listAlternates_self_of_pairwise rs hrs_sorted⟩⟩

/-- Multiplying the left polynomial in a `Prec` relation by a nonzero scalar
preserves interlacing, since it does not change the roots. -/
lemma prec_C_mul_left {f g : ℝ[X]} (h : Prec f g) {a : ℝ} (ha : a ≠ 0) :
    Prec (C a * f) g := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  exact ⟨isRealRooted_C_mul hf ha, hg, ss, rs, hss, hrs, by
    rw [roots_C_mul _ ha, hss_eq], hrs_eq, hcase⟩

/-- Multiplying the right polynomial in a `Prec` relation by a nonzero scalar
preserves interlacing, since it does not change the roots. -/
lemma prec_C_mul_right {f g : ℝ[X]} (h : Prec f g) {a : ℝ} (ha : a ≠ 0) :
    Prec f (C a * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  exact ⟨hf, isRealRooted_C_mul hg ha, ss, rs, hss, hrs, hss_eq, by
    rw [roots_C_mul _ ha, hrs_eq], hcase⟩

/-- In particular, a nonzero scalar multiple of a real-rooted polynomial
interlaces the original polynomial. -/
lemma prec_C_mul_self {f : ℝ[X]} (hf : IsRealRooted f) {a : ℝ} (ha : a ≠ 0) :
    Prec (C a * f) f :=
  prec_C_mul_left (prec_refl hf) ha

/-- If two polynomials have the same degree and positive leading coefficients,
their top coefficients cannot cancel. -/
lemma natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree = q.natDegree)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    (p + q).natDegree = p.natDegree := by
  unfold HasPosLeadingCoeff at hp_pos hq_pos
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hp_pos
  have hq0 : q ≠ 0 := by
    intro hq
    simp [hq] at hq_pos
  apply le_antisymm
  · have h := natDegree_add_le p q
    rwa [max_eq_left (by lia)] at h
  · apply le_natDegree_of_ne_zero
    have hqcoeff : q.coeff p.natDegree = q.leadingCoeff := by
      rw [hdeg]
      rfl
    rw [coeff_add]
    rw [show p.coeff p.natDegree = p.leadingCoeff by rfl]
    rw [hqcoeff]
    nlinarith [hp_pos, hq_pos]

/-- If the right summand has strictly larger degree and positive leading coefficient,
then the sum keeps that degree. -/
lemma natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree < q.natDegree) (hq_pos : HasPosLeadingCoeff q) :
    (p + q).natDegree = q.natDegree := by
  apply le_antisymm
  · have h := natDegree_add_le p q
    rwa [max_eq_right hdeg.le] at h
  · apply le_natDegree_of_ne_zero
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hdeg, zero_add]
    exact ne_of_gt hq_pos

/-- If the left summand has strictly larger degree and positive leading coefficient,
then the sum keeps that degree. -/
lemma natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : q.natDegree < p.natDegree) (hp_pos : HasPosLeadingCoeff p) :
    (p + q).natDegree = p.natDegree := by
  apply le_antisymm
  · have h := natDegree_add_le p q
    rwa [max_eq_left hdeg.le] at h
  · apply le_natDegree_of_ne_zero
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hdeg, add_zero]
    exact ne_of_gt hp_pos

/-- In the natural positive-leading-coefficient situation, same-degree sums
also have positive leading coefficient. -/
lemma hasPosLeadingCoeff_add_of_same_natDegree {p q : ℝ[X]}
    (hdeg : p.natDegree = q.natDegree)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p + q) := by
  unfold HasPosLeadingCoeff at hp_pos hq_pos ⊢
  have hqcoeff : q.coeff p.natDegree = q.leadingCoeff := by
    rw [hdeg]
    rfl
  unfold Polynomial.leadingCoeff
  rw [natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg hp_pos hq_pos, coeff_add]
  rw [show p.coeff p.natDegree = p.leadingCoeff by rfl]
  rw [hqcoeff]
  nlinarith [hp_pos, hq_pos]

/-- If the right summand has strictly larger degree and positive leading coefficient,
then the sum also has positive leading coefficient. -/
lemma hasPosLeadingCoeff_add_of_natDegree_lt_right {p q : ℝ[X]}
    (hdeg : p.natDegree < q.natDegree) (hq_pos : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p + q) := by
  unfold HasPosLeadingCoeff at hq_pos ⊢
  unfold Polynomial.leadingCoeff
  rw [natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hdeg hq_pos, coeff_add,
    coeff_eq_zero_of_natDegree_lt hdeg, zero_add]
  exact hq_pos

/-- If the left summand has strictly larger degree and positive leading coefficient,
then the sum also has positive leading coefficient. -/
lemma hasPosLeadingCoeff_add_of_natDegree_lt_left {p q : ℝ[X]}
    (hdeg : q.natDegree < p.natDegree) (hp_pos : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (p + q) := by
  unfold HasPosLeadingCoeff at hp_pos ⊢
  unfold Polynomial.leadingCoeff
  rw [natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg hp_pos, coeff_add,
    coeff_eq_zero_of_natDegree_lt hdeg, add_zero]
  exact hp_pos

/-- In particular, same-degree positive-leading-coefficient sums are nonzero. -/
lemma add_ne_zero_of_same_natDegree_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree = q.natDegree)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    p + q ≠ 0 := by
  intro hpq
  have hsum_pos := hasPosLeadingCoeff_add_of_same_natDegree hdeg hp_pos hq_pos
  unfold HasPosLeadingCoeff at hsum_pos
  simp [hpq] at hsum_pos

end RealRooted
