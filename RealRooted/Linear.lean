module

public import RealRooted.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
public import RealRooted.Mathlib.Data.List.Interleave
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Multiset.Sort

/-!
# Real-rootedness of linear polynomials

This file proves that every polynomial of the form `X - C r` is real-rooted,
and more generally that every nonzero polynomial of degree at most one is
real-rooted.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- `X - C r` is real-rooted: it has exactly one root, namely `r`. -/
lemma isRealRooted_X_sub_C (r : ℝ) : ((X - C r) ≠ 0 ∧ (X - C r).Splits) :=
  ⟨X_sub_C_ne_zero r, Polynomial.Splits.X_sub_C r⟩

lemma hasPosLeadingCoeff_X_sub_C_mul {r : ℝ} {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff ((X - C r) * p) := by
  simpa [HasPosLeadingCoeff] using hp

lemma hasPosLeadingCoeff_X_sub_C (r : ℝ) :
    HasPosLeadingCoeff (X - C r : ℝ[X]) :=
  hasPosLeadingCoeff_of_monic (monic_X_sub_C r)

lemma hasPosLeadingCoeff_X_add_C (r : ℝ) :
    HasPosLeadingCoeff (X + C r : ℝ[X]) := by
  simpa [sub_eq_add_neg, add_comm] using hasPosLeadingCoeff_X_sub_C (-r)

lemma hasPosLeadingCoeff_of_X_sub_C_mul {q : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff ((X - C r) * q)) :
    HasPosLeadingCoeff q := by
  simpa [HasPosLeadingCoeff] using h

/-- Dividing by `X` preserves nonnegative coefficients. -/
protected lemma HasNonnegCoeffs.divX {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.divX := by
  intro n
  simpa [Polynomial.coeff_divX] using hp (n + 1)

/-- If a positive-leading polynomial has zero constant coefficient, then its
quotient by the common factor `X` still has positive leading coefficient. -/
lemma HasPosLeadingCoeff.divX_of_coeff_zero {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (h0 : p.coeff 0 = 0) :
    HasPosLeadingCoeff p.divX := by
  have hX : X * p.divX = p := by simpa [h0] using Polynomial.X_mul_divX_add p
  rw [← hX] at hp
  simpa [HasPosLeadingCoeff] using hp

lemma hasPosLeadingCoeff_of_pow_X_sub_C_mul {q : ℝ[X]} {r : ℝ} {m : ℕ}
    (h : HasPosLeadingCoeff ((X - C r) ^ m * q)) :
    HasPosLeadingCoeff q := by
  have hpow_ne : ((X - C r) ^ m : ℝ[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero r)
  unfold HasPosLeadingCoeff at h ⊢
  simp_all

lemma roots_le_X_sub_C_mul {r : ℝ} {f : ℝ[X]}
    (hf : f.Splits)
    (hf_le : ∀ s ∈ f.roots, s ≤ r) :
    ∀ s ∈ ((X - C r) * f).roots, s ≤ r := by
  obtain rfl | hf₀ := eq_or_ne f 0
  · simp
  intro s hs
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hf₀), roots_X_sub_C] at hs
  rcases Multiset.mem_add.mp hs with hs | hs <;> simp_all

/-- A nonzero scalar multiple of a real-rooted polynomial is real-rooted. -/
lemma isRealRooted_C_mul {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    {a : ℝ} (ha : a ≠ 0) :
    (C a * p ≠ 0 ∧ (C a * p).Splits) := by simp_all

/-- A nonzero scalar multiple preserves a bundled real-rootedness certificate. -/
lemma isRealRooted_C_mul_of_isRealRooted {p : ℝ[X]}
    (hp : p ≠ 0 ∧ p.Splits) {a : ℝ} (ha : a ≠ 0) :
    C a * p ≠ 0 ∧ (C a * p).Splits :=
  isRealRooted_C_mul hp.1 hp.2 ha

lemma isRealRooted_X_mul {f : ℝ[X]} (hf_ne : f ≠ 0) (hf_splits : f.Splits) :
    ((X * f) ≠ 0 ∧ (X * f).Splits) :=
  isRealRooted_mul (by simp) (by simp) hf_ne hf_splits

/-- Multiplication by `X` preserves a bundled real-rootedness certificate. -/
lemma isRealRooted_X_mul_of_isRealRooted {f : ℝ[X]} (hf : f ≠ 0 ∧ f.Splits) :
    X * f ≠ 0 ∧ (X * f).Splits :=
  isRealRooted_X_mul hf.1 hf.2

lemma isRealRooted_X : ((X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits) := by simp

/-- Orientation sanity check for the local `StrictInterl` convention on linear factors.

The root of `X + C a` is `-a`; hence `StrictInterl (X + C b) (X + C a)` means that
the root of the left polynomial is weakly to the left of the root of the right
polynomial, equivalently `a ≤ b`. -/
lemma StrictInterl.X_add_C_iff {a b : ℝ} :
    StrictInterl (X + C b) (X + C a) ↔ a ≤ b := by
  constructor
  · intro h
    have hsum := h.roots_sum_le_of_sameDegree (by simp)
    simpa using hsum
  · intro hab
    refine ⟨?_, ?_, [(-b)], [(-a)], by simp, by simp, by simp, by simp, ?_⟩
    · simpa [sub_eq_add_neg] using X_sub_C_ne_zero (-b : ℝ)
    · simpa [sub_eq_add_neg] using X_sub_C_ne_zero (-a : ℝ)
    · exact Or.inr ⟨by simp, by simpa [ListAlternates, ListInterlaces] using hab⟩

/-- Orientation criterion for zero-aware proper position of linear factors. -/
lemma Interl.X_add_C_iff {a b : ℝ} :
    Interl (X + C b) (X + C a) ↔ a ≤ b := by
  constructor
  · intro h
    exact (StrictInterl.X_add_C_iff.mp
      (h.toStrictInterl_of_ne (X_add_C_ne_zero b) (X_add_C_ne_zero a)))
  · intro hab
    exact (StrictInterl.X_add_C_iff.mpr hab).toInterl

lemma isRealRooted_of_deg_zero {p : ℝ[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree = 0) :
    p ≠ 0 ∧ p.Splits :=
  ⟨hp, Polynomial.Splits.of_natDegree_eq_zero hdeg⟩

/-- A nonzero divisor of a real-rooted polynomial is real-rooted. -/
lemma isRealRooted_of_dvd {p q : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hq0 : q ≠ 0) (hqp : q ∣ p) : (q ≠ 0 ∧ q.Splits) :=
  ⟨hq0, hp_splits.of_dvd hp_ne hqp⟩

lemma isRealRooted_of_X_mul {f : ℝ[X]}
    (hXf_ne : (X * f) ≠ 0) (hXf_splits : (X * f).Splits) :
    f ≠ 0 ∧ f.Splits := by
  simp_all

/-- A common root of two polynomials is also a root of their sum. -/
lemma IsRoot.add {p q : ℝ[X]} {x : ℝ} (hp : p.IsRoot x) (hq : q.IsRoot x) :
    (p + q).IsRoot x := by simp_all

/-- If two real-rooted polynomials have no common real root, then they are coprime. -/
lemma isCoprime_of_no_common_real_root_of_isRealRooted {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hno : ∀ r : ℝ, f.IsRoot r → ¬ g.IsRoot r) :
    IsCoprime f g := by
  apply EuclideanDomain.isCoprime_of_dvd
  · lia
  · intro z hz_nonunit hz0 hzf hzg
    have hz_notunit : ¬ IsUnit z := by simp_all
    have hz_rr : z ≠ 0 ∧ z.Splits :=
      ⟨hz0, hf_splits.of_dvd hf_ne hzf⟩
    obtain ⟨r, hzr⟩ : ∃ r : ℝ, z.IsRoot r := by
      simpa [Polynomial.IsRoot.def] using hz_rr.2.exists_eval_eq_zero
        (degree_pos_of_ne_zero_of_nonunit hz_rr.1 hz_notunit).ne'
    exact hno r (hzr.dvd hzf) (hzr.dvd hzg)

/-- Any nonzero degree-1 polynomial is real-rooted. -/
lemma isRealRooted_of_degree_one {p : ℝ[X]} (hp : p.natDegree = 1) : (p ≠ 0 ∧ p.Splits) := by
  have hne : p ≠ 0 := by intro h; simp [h] at hp
  exact ⟨hne, Polynomial.Splits.of_natDegree_eq_one hp⟩

/-- Any nonzero polynomial of degree at most one is real-rooted. -/
lemma isRealRooted_of_natDegree_le_one {p : ℝ[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ 1) : (p ≠ 0 ∧ p.Splits) :=
  ⟨hp, Polynomial.Splits.of_natDegree_le_one hdeg⟩

lemma interlaces_one_linear {p : ℝ[X]} (hp_deg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  have h1_rr : ((1 : ℝ[X]) ≠ 0 ∧ (1 : ℝ[X]).Splits) := by simp
  have hp_rr : p ≠ 0 ∧ p.Splits := by
    refine ⟨ne_zero_of_natDegree_gt (n := 0) ?_, Splits.of_natDegree_eq_one hp_deg⟩
    lia
  have hp_deg' : p.degree = 1 := by simpa [hp_deg] using degree_eq_natDegree hp_rr.1
  refine ⟨hp_rr, h1_rr, by simp [Polynomial.natDegree_one, hp_deg], ?_⟩
  refine ⟨[-(p.coeff 1)⁻¹ * p.coeff 0], [], by simp, by simp, ?_, by simp,
    by simp [ListInterlaces]⟩
  simpa [hp_deg'] using (Polynomial.roots_degree_eq_one (p := p) hp_deg').symm

lemma pairwise_map_sub_const :
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) →
      ∀ r : ℝ, (rs.map (· - r)).Pairwise (· ≤ ·)
  | rs, h, r => by
      rw [List.pairwise_map]
      exact h.imp fun hxy => sub_le_sub_right hxy r

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
  simpa [add_comm] using
    Polynomial.rootMultiplicity_comp_C_mul_X_add_C p 1 r x isUnit_one

lemma roots_comp_X_add_C {p : ℝ[X]} (r : ℝ) :
    (p.comp (X + C r)).roots = p.roots.map (fun x => x - r) := by
  simpa using Polynomial.roots_comp_C_mul_X_add_C p 1 r isUnit_one

/-- Translating a polynomial by `a` identifies its roots in `(0, b - a)`
with the original roots in `(a, b)`, including multiplicities. -/
lemma card_roots_comp_X_add_C_Ioo (p : ℝ[X]) (a b : ℝ) :
    ((p.comp (X + C a)).roots.filter (fun x => 0 < x ∧ x < b - a)).card =
      (p.roots.filter (fun x => a < x ∧ x < b)).card := by
  rw [roots_comp_X_add_C, Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro y _
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Translation by `r` preserves positive leading coefficient. -/
lemma HasPosLeadingCoeff.comp_X_add_C {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) (r : ℝ) :
    HasPosLeadingCoeff (p.comp (X + C r)) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow, mul_one]
  exact hp

lemma isRealRooted_comp_X_add_C
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) (r : ℝ) :
    (p.comp (X + C r) ≠ 0 ∧ (p.comp (X + C r)).Splits) :=
  ⟨(Polynomial.comp_X_add_C_ne_zero_iff).2 hp_ne, hp_splits.comp_X_add_C r⟩

/-- Rescaling the variable by a nonzero real preserves real-rootedness. -/
lemma isRealRooted_comp_C_mul_X
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    {a : ℝ} (ha : a ≠ 0) :
    p.comp (C a * X) ≠ 0 ∧ (p.comp (C a * X)).Splits :=
  ⟨mt (Polynomial.comp_C_mul_X_eq_zero_iff (by simp [ha])).mp hp_ne,
    hp_splits.comp_of_natDegree_le_one (by simp [ha])⟩

private lemma listAlternates_reverse_map_one_sub {ss rs : List ℝ}
    (hlen : ss.length = rs.length) (halt : ListAlternates ss rs) :
    ListAlternates (rs.reverse.map (1 - ·)) (ss.reverse.map (1 - ·)) := by
  apply listAlternates_of_interleaves_of_length
  · simp [hlen]
  have hold : List.Interleaves (· ≤ ·) rs ss :=
    interleaves_of_listAlternates_of_length hlen halt
  have hreverse :
      List.Interleaves (fun a b : ℝ => b ≤ a) ss.reverse rs.reverse := by
    apply (List.interleaves_reverse_reverse_of_length_eq_length hlen).2
    simpa [Function.swap] using hold
  exact List.Interleaves.map hreverse (fun x : ℝ ↦ 1 - x) (by
    intro a b hab
    linarith)

private lemma roots_comp_one_sub_X (p : ℝ[X]) :
    (p.comp (1 - X)).roots = p.roots.map (1 - ·) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Polynomial.roots_comp_C_mul_X_add_C p (-1) 1 isUnit_neg_one

/-- Reflection about `1 / 2` reverses same-degree proper position. -/
lemma StrictInterl.comp_one_sub_X_of_natDegree_eq {f g : ℝ[X]}
    (h : StrictInterl f g) (hdeg : f.natDegree = g.natDegree) :
    StrictInterl (g.comp (1 - X)) (f.comp (1 - X)) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hlen : ss.length = rs.length := by
    rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hf.2,
      hdeg, ← Polynomial.splits_iff_card_roots.mp hg.2, ← hrs_eq, Multiset.coe_card]
  obtain ⟨_, halt⟩ := hshape.resolve_left (by simp_all)
  have halt' := listAlternates_reverse_map_one_sub hlen halt
  have hinter :
      List.Interleaves (· ≤ ·) (ss.reverse.map (1 - ·))
        (rs.reverse.map (1 - ·)) :=
    interleaves_of_listAlternates_of_length (by simp [hlen]) halt'
  have hcomp : ∀ {p : ℝ[X]}, p ≠ 0 → p.Splits →
      p.comp (1 - X) ≠ 0 ∧ (p.comp (1 - X)).Splits := by
    intro p hp_ne hp_splits
    refine ⟨?_, hp_splits.comp_of_natDegree_le_one
      ((natDegree_sub_le (1 : ℝ[X]) X).trans (by simp))⟩
    rw [Ne, Polynomial.comp_eq_zero_iff]
    simp [hp_ne]
  refine ⟨hcomp hg.1 hg.2, hcomp hf.1 hf.2,
    rs.reverse.map (1 - ·), ss.reverse.map (1 - ·),
    hinter.pairwise_right, hinter.pairwise_left, ?_, ?_, Or.inr ⟨?_, halt'⟩⟩
  · rw [roots_comp_one_sub_X, ← hrs_eq]
    simp
  · rw [roots_comp_one_sub_X, ← hss_eq]
    simp
  · simp [hlen]

/-- Translation by `r` preserves `StrictInterl`: roots are shifted left by `r`,
so the relative order is unchanged. -/
lemma StrictInterl.comp_X_add_C {f g : ℝ[X]} (h : StrictInterl f g) (r : ℝ) :
    StrictInterl (f.comp (X + C r)) (g.comp (X + C r)) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  have hfcomp : f.comp (X + C r) ≠ 0 ∧ (f.comp (X + C r)).Splits :=
    ⟨comp_X_add_C_ne_zero_iff.mpr hf.1, hf.2.comp_X_add_C r⟩
  have hgcomp : g.comp (X + C r) ≠ 0 ∧ (g.comp (X + C r)).Splits :=
    ⟨comp_X_add_C_ne_zero_iff.mpr hg.1, hg.2.comp_X_add_C r⟩
  refine ⟨hfcomp, hgcomp,
    ss.map (· - r), rs.map (· - r), ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · change (↑ss : Multiset ℝ).map (fun x => x - r) = _
    rw [hss_eq, roots_comp_X_add_C]
  · change (↑rs : Multiset ℝ).map (fun x => x - r) = _
    rw [hrs_eq, roots_comp_X_add_C]
  · exact hcase.elim
      (fun h => Or.inl ⟨by simp_all, listInterlaces_map_sub_const h.2 r⟩)
      (fun h => Or.inr ⟨by simp_all, listAlternates_map_sub_const h.2 r⟩)

/-- Positive rescaling of the variable preserves `StrictInterl`: each root is divided
by the same positive scalar, so its relative order is unchanged. -/
lemma StrictInterl.comp_C_mul_X {f g : ℝ[X]} (h : StrictInterl f g)
    {a : ℝ} (ha : 0 < a) :
    StrictInterl (f.comp (C a * X)) (g.comp (C a * X)) := by
  rcases h with ⟨hf, hg, ss, rs, _, _, hss_eq, hrs_eq, hcase⟩
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have ha_unit : IsUnit a := isUnit_iff_ne_zero.mpr ha_ne
  have hfcomp : f.comp (C a * X) ≠ 0 ∧ (f.comp (C a * X)).Splits :=
    ⟨mt (comp_C_mul_X_eq_zero_iff (by simp [ha_ne])).mp hf.1,
      hf.2.comp_of_natDegree_le_one (by simp [ha_ne])⟩
  have hgcomp : g.comp (C a * X) ≠ 0 ∧ (g.comp (C a * X)).Splits :=
    ⟨mt (comp_C_mul_X_eq_zero_iff (by simp [ha_ne])).mp hg.1,
      hg.2.comp_of_natDegree_le_one (by simp [ha_ne])⟩
  have hmono : ∀ {x y : ℝ}, x ≤ y → a⁻¹ * x ≤ a⁻¹ * y := by
    exact fun {_ _} hxy => mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr ha.le)
  have hroots_f :
      (↑(ss.map (a⁻¹ * ·)) : Multiset ℝ) =
        (f.comp (C a * X)).roots := by
    change (↑ss : Multiset ℝ).map (a⁻¹ * ·) = _
    rw [hss_eq]
    simpa using (Polynomial.roots_comp_C_mul_X_add_C f a 0 ha_unit).symm
  have hroots_g :
      (↑(rs.map (a⁻¹ * ·)) : Multiset ℝ) =
        (g.comp (C a * X)).roots := by
    change (↑rs : Multiset ℝ).map (a⁻¹ * ·) = _
    rw [hrs_eq]
    simpa using (Polynomial.roots_comp_C_mul_X_add_C g a 0 ha_unit).symm
  rcases hcase with ⟨hlen, hinterlaces⟩ | ⟨hlen, halternates⟩
  · have hinter :
        List.Interleaves (fun x y : ℝ => x ≤ y)
          (ss.map (a⁻¹ * ·)) (rs.map (a⁻¹ * ·)) :=
      (interleaves_of_listInterlaces_of_length hlen hinterlaces).map
        (a⁻¹ * ·) @hmono
    refine ⟨hfcomp, hgcomp,
      ss.map (a⁻¹ * ·), rs.map (a⁻¹ * ·),
      hinter.pairwise_left, hinter.pairwise_right, hroots_f, hroots_g,
      Or.inl ⟨by simpa using hlen, ?_⟩⟩
    exact listInterlaces_of_interleaves_of_length (by simpa using hlen) hinter
  · have hinter :
        List.Interleaves (fun x y : ℝ => x ≤ y)
          (rs.map (a⁻¹ * ·)) (ss.map (a⁻¹ * ·)) :=
      (interleaves_of_listAlternates_of_length hlen halternates).map
        (a⁻¹ * ·) @hmono
    refine ⟨hfcomp, hgcomp,
      ss.map (a⁻¹ * ·), rs.map (a⁻¹ * ·),
      hinter.pairwise_right, hinter.pairwise_left, hroots_f, hroots_g,
      Or.inr ⟨by simpa using hlen, ?_⟩⟩
    exact listAlternates_of_interleaves_of_length (by simpa using hlen) hinter

/-- Reflection through the origin reverses same-degree proper position. -/
lemma StrictInterl.comp_neg_X_of_natDegree_eq {f g : ℝ[X]}
    (h : StrictInterl f g) (hdeg : f.natDegree = g.natDegree) :
    StrictInterl (g.comp (-X)) (f.comp (-X)) := by
  have hreflected := h.comp_one_sub_X_of_natDegree_eq hdeg
  simpa [Polynomial.comp_assoc] using hreflected.comp_X_add_C 1

/-- Translation by `r` is an equivalence on `StrictInterl`. -/
lemma StrictInterl.comp_X_add_C_iff {f g : ℝ[X]} (r : ℝ) :
    StrictInterl (f.comp (X + C r)) (g.comp (X + C r)) ↔ StrictInterl f g := by
  constructor
  · intro h
    have h' := h.comp_X_add_C (-r)
    simpa [comp_assoc, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h'
  · exact fun h => h.comp_X_add_C r

/-- Translation by `r` preserves zero-aware proper position. -/
lemma Interl.comp_X_add_C {f g : ℝ[X]} (h : Interl f g) (r : ℝ) :
    Interl (f.comp (X + C r)) (g.comp (X + C r)) := by
  rcases h with rfl | rfl | hstrict
  · simpa using interl_zero_left (g.comp (X + C r))
  · simpa using interl_zero_right (f.comp (X + C r))
  · exact (hstrict.comp_X_add_C r).toInterl

/-- Translation by `r` is an equivalence on zero-aware proper position. -/
lemma Interl.comp_X_add_C_iff {f g : ℝ[X]} (r : ℝ) :
    Interl (f.comp (X + C r)) (g.comp (X + C r)) ↔ Interl f g := by
  constructor
  · intro h
    have h' := h.comp_X_add_C (-r)
    simpa [comp_assoc, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h'
  · exact fun h => h.comp_X_add_C r

/-- Positive rescaling of the variable preserves zero-aware proper position. -/
lemma Interl.comp_C_mul_X {f g : ℝ[X]} (h : Interl f g) {a : ℝ} (ha : 0 < a) :
    Interl (f.comp (C a * X)) (g.comp (C a * X)) := by
  rcases h with rfl | rfl | hstrict
  · simpa using interl_zero_left (g.comp (C a * X))
  · simpa using interl_zero_right (f.comp (C a * X))
  · exact (hstrict.comp_C_mul_X ha).toInterl

/-- Reflection about `1 / 2` reverses same-degree zero-aware proper position. -/
lemma Interl.comp_one_sub_X_of_natDegree_eq {f g : ℝ[X]} (h : Interl f g)
    (hdeg : f.natDegree = g.natDegree) :
    Interl (g.comp (1 - X)) (f.comp (1 - X)) := by
  rcases h with rfl | rfl | hstrict
  · simpa using interl_zero_right (g.comp (1 - X))
  · simpa using interl_zero_left (f.comp (1 - X))
  · exact (hstrict.comp_one_sub_X_of_natDegree_eq hdeg).toInterl

/-- Reflection through the origin reverses same-degree zero-aware proper position. -/
lemma Interl.comp_neg_X_of_natDegree_eq {f g : ℝ[X]} (h : Interl f g)
    (hdeg : f.natDegree = g.natDegree) :
    Interl (g.comp (-X)) (f.comp (-X)) := by
  have hreflected := h.comp_one_sub_X_of_natDegree_eq hdeg
  simpa [Polynomial.comp_assoc] using hreflected.comp_X_add_C 1

/- Deprecated compatibility alias for
`StrictInterl.comp_one_sub_X_of_natDegree_eq`. -/

lemma interlaces_C_linear {p : ℝ[X]} {c : ℝ} (hc : c ≠ 0)
    (hp_deg : p.natDegree = 1) :
    Interlaces (C c) p := by
  have hprec : StrictInterl (C c * (1 : ℝ[X])) p :=
    (interlaces_one_linear hp_deg).toStrictInterl.C_mul_left hc
  have hdeg : (C c * (1 : ℝ[X])).natDegree + 1 = p.natDegree := by simp [hp_deg]
  simpa using hprec.toInterlaces hdeg

/-- If two polynomials have the same degree and positive leading coefficients,
their top coefficients cannot cancel. -/
lemma natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree = q.natDegree)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    (p + q).natDegree = p.natDegree := by
  simpa using
    Polynomial.natDegree_add_C_mul_eq_left_of_natDegree_le_of_coeff_add_ne_zero
      (a := (1 : ℝ)) (by rw [hdeg]) <| by
        unfold HasPosLeadingCoeff at hp_pos hq_pos
        rw [show q.coeff p.natDegree = q.leadingCoeff by rw [hdeg]; rfl]
        positivity

/-- If the right summand has strictly larger degree and positive leading coefficient,
then the sum keeps that degree. -/
@[deprecated Polynomial.natDegree_add_eq_right_of_natDegree_lt +typeChanged
  (since := "2026-10-21")]
lemma natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree < q.natDegree) (hq_pos : HasPosLeadingCoeff q) :
    (p + q).natDegree = q.natDegree := by
  have _ := hq_pos.ne_zero
  exact Polynomial.natDegree_add_eq_right_of_natDegree_lt hdeg

/-- If the left summand has strictly larger degree and positive leading coefficient,
then the sum keeps that degree. -/
@[deprecated Polynomial.natDegree_add_eq_left_of_natDegree_lt +typeChanged
  (since := "2026-10-21")]
lemma natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : q.natDegree < p.natDegree) (hp_pos : HasPosLeadingCoeff p) :
    (p + q).natDegree = p.natDegree := by
  have _ := hp_pos.ne_zero
  exact Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeg

/-- A real parameter avoids canceling `a + t * b` exactly when it is not the
unique cancellation value `-a / b`. -/
private theorem add_mul_ne_zero_iff_ne_neg_div {a b t : ℝ} (hb : b ≠ 0) :
    a + t * b ≠ 0 ↔ t ≠ -a / b := by
  constructor <;> contrapose!
  · rintro rfl
    field_simp [hb]
    ring
  · intro hzero
    field_simp [hb]
    linarith

/-- In the natural positive-leading-coefficient situation, same-degree sums
also have positive leading coefficient. -/
lemma hasPosLeadingCoeff_add_of_same_natDegree {p q : ℝ[X]}
    (hdeg : p.natDegree = q.natDegree)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p + q) := by
  unfold HasPosLeadingCoeff at hp_pos hq_pos ⊢
  have hqcoeff : q.coeff p.natDegree = q.leadingCoeff := by simp_all
  unfold Polynomial.leadingCoeff
  rw [natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff hdeg hp_pos hq_pos, coeff_add]
  rw [show p.coeff p.natDegree = p.leadingCoeff by simp]
  grind

/-- If the right summand has strictly larger degree and positive leading coefficient,
then the sum also has positive leading coefficient. -/
lemma hasPosLeadingCoeff_add_of_natDegree_lt_right {p q : ℝ[X]}
    (hdeg : p.natDegree < q.natDegree) (hq_pos : HasPosLeadingCoeff q) :
    HasPosLeadingCoeff (p + q) := by
  unfold HasPosLeadingCoeff at hq_pos ⊢
  rw [Polynomial.leadingCoeff_add_of_degree_lt (degree_lt_degree hdeg)]
  exact hq_pos

/-- If the left summand has strictly larger degree and positive leading coefficient,
then the sum also has positive leading coefficient. -/
lemma hasPosLeadingCoeff_add_of_natDegree_lt_left {p q : ℝ[X]}
    (hdeg : q.natDegree < p.natDegree) (hp_pos : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff (p + q) := by
  simpa [add_comm] using
    hasPosLeadingCoeff_add_of_natDegree_lt_right (p := q) (q := p) hdeg hp_pos

/-- In particular, same-degree positive-leading-coefficient sums are nonzero. -/
lemma add_ne_zero_of_same_natDegree_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree = q.natDegree)
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q) :
    p + q ≠ 0 :=
  (hasPosLeadingCoeff_add_of_same_natDegree hdeg hp_pos hq_pos).ne_zero

end RealRooted
