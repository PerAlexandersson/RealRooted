import RealRooted.Basic
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
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
lemma isRealRooted_X_sub_C (r : ℝ) : ((X - C r) ≠ 0 ∧ (X - C r).Splits) :=
  ⟨X_sub_C_ne_zero r, splits_of_card_roots <| by
    simp⟩

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
  have hX_pos : HasPosLeadingCoeff (X * p.divX) := by simp_all
  have hXC_pos : HasPosLeadingCoeff ((X - C 0) * p.divX) := by grind
  exact hasPosLeadingCoeff_of_X_sub_C_mul hXC_pos

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

/-- If `p` has zero constant coefficient, splitting of `p.divX` gives splitting
of `p` by restoring the common factor `X`. -/
lemma splits_of_divX_splits_of_coeff_zero {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (h0 : p.coeff 0 = 0)
    (hdiv : p.divX.Splits) :
    p.Splits := by
  have hX : X * p.divX = p := by simpa [h0] using Polynomial.X_mul_divX_add p
  have hdiv_pos : HasPosLeadingCoeff p.divX := hp_pos.divX_of_coeff_zero h0
  have hX_rr := isRealRooted_X_mul hdiv_pos.ne_zero hdiv
  simp_all

lemma isRealRooted_X : ((X : ℝ[X]) ≠ 0 ∧ (X : ℝ[X]).Splits) := by simp

/-- Orientation sanity check for the local `Prec` convention on linear factors.

The root of `X + C a` is `-a`; hence `Prec (X + C b) (X + C a)` means that
the root of the left polynomial is weakly to the left of the root of the right
polynomial, equivalently `a ≤ b`. -/
lemma prec_X_add_C_iff {a b : ℝ} :
    Prec (X + C b) (X + C a) ↔ a ≤ b := by
  constructor
  · intro h
    have hsum := roots_sum_le_of_prec_sameDegree h (by simp)
    simpa using hsum
  · intro hab
    refine ⟨?_, ?_, [(-b)], [(-a)], by simp, by simp, by simp, by simp, ?_⟩
    · simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-b)
    · simpa [sub_eq_add_neg] using isRealRooted_X_sub_C (-a)
    · exact Or.inr ⟨by simp, by simpa [ListAlternates, ListInterlaces] using hab⟩

lemma isRealRooted_of_deg_zero {p : ℝ[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree = 0) :
    p ≠ 0 ∧ p.Splits :=
  ⟨hp, Polynomial.Splits.of_natDegree_eq_zero hdeg⟩

/-- A nonzero divisor of a real-rooted polynomial is real-rooted. -/
lemma isRealRooted_of_dvd {p q : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hq0 : q ≠ 0) (hqp : q ∣ p) : (q ≠ 0 ∧ q.Splits) := by
  rcases hqp with ⟨r, rfl⟩
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hp_ne
  refine ⟨hq0, ?_⟩
  have hsum : q.roots.card + r.roots.card = (q * r).natDegree := by
    rw [← card_roots_of_splits hp_splits, roots_mul hp_ne, Multiset.card_add]
  rw [natDegree_mul hq0 hr0] at hsum
  have hq_le : q.roots.card ≤ q.natDegree := card_roots' q
  have hr_le : r.roots.card ≤ r.natDegree := card_roots' r
  apply splits_of_card_roots
  lia

lemma isRealRooted_of_X_mul {f : ℝ[X]}
    (hXf_ne : (X * f) ≠ 0) (hXf_splits : (X * f).Splits) :
    f ≠ 0 ∧ f.Splits := by
  simp_all

/-- A root of a divisor is a root of the dividend. -/
lemma IsRoot.of_dvd {p q : ℝ[X]} (hpq : p ∣ q) {x : ℝ} (hx : p.IsRoot x) :
    q.IsRoot x := by
  rcases hpq with ⟨r, rfl⟩
  simp_all

/-- A common root of two polynomials is also a root of their sum. -/
lemma IsRoot.add {p q : ℝ[X]} {x : ℝ} (hp : p.IsRoot x) (hq : q.IsRoot x) :
    (p + q).IsRoot x := by simp_all

/-- If `(X - C r)^m` divides both summands, then it divides their sum. -/
lemma pow_X_sub_C_dvd_add {p q : ℝ[X]} {r : ℝ} {m : ℕ}
    (hp : (X - C r) ^ m ∣ p) (hq : (X - C r) ^ m ∣ q) :
    (X - C r) ^ m ∣ p + q :=
  dvd_add hp hq

/-- The root multiplicity in a sum is at least the minimum multiplicity
of the two summands. -/
lemma min_rootMultiplicity_le_rootMultiplicity_add {p q : ℝ[X]} {r : ℝ}
    (hpq : p + q ≠ 0) :
    min (p.rootMultiplicity r) (q.rootMultiplicity r) ≤ (p + q).rootMultiplicity r :=
  Polynomial.rootMultiplicity_add (p := p) (q := q) r hpq

/-- A nonunit real-rooted polynomial has a real root. -/
lemma exists_isRoot_of_isRealRooted_of_not_isUnit {p : ℝ[X]} (hp_ne : p ≠ 0)
    (hp_splits : p.Splits) (hu : ¬ IsUnit p) : ∃ r : ℝ, p.IsRoot r := by
  have hdeg : 0 < p.natDegree := by
    rw [natDegree_pos_iff_degree_pos]
    exact degree_pos_of_ne_zero_of_nonunit hp_ne hu
  have hcard : 0 < p.roots.card := by rwa [card_roots_of_splits hp_splits]
  obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  exact ⟨r, (mem_roots hp_ne).mp hr⟩

/-- If two real-rooted polynomials have no common real root, then they are coprime. -/
lemma isCoprime_of_no_common_real_root_of_isRealRooted {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hno : ∀ r : ℝ, f.IsRoot r → ¬ g.IsRoot r) :
    IsCoprime f g := by
  apply EuclideanDomain.isCoprime_of_dvd
  · lia
  · intro z hz_nonunit hz0 hzf hzg
    have hz_notunit : ¬ IsUnit z := by simp_all
    have hz_rr : (z ≠ 0 ∧ z.Splits) := isRealRooted_of_dvd hf_ne hf_splits hz0 hzf
    obtain ⟨r, hzr⟩ := exists_isRoot_of_isRealRooted_of_not_isUnit hz_rr.1 hz_rr.2 hz_notunit
    have hfr : f.IsRoot r := IsRoot.of_dvd hzf hzr
    have hgr : g.IsRoot r := IsRoot.of_dvd hzg hzr
    simp_all

/-- Any nonzero degree-1 polynomial is real-rooted. -/
lemma isRealRooted_of_degree_one {p : ℝ[X]} (hp : p.natDegree = 1) : (p ≠ 0 ∧ p.Splits) := by
  have hne : p ≠ 0 := by intro h; simp [h] at hp
  have hdeg : p.degree = 1 := by simpa [hp] using degree_eq_natDegree hne
  refine ⟨hne, splits_of_card_roots ?_⟩
  rw [roots_degree_eq_one hdeg, Multiset.card_singleton, hp]

/-- Any nonzero polynomial of degree at most one is real-rooted. -/
lemma isRealRooted_of_natDegree_le_one {p : ℝ[X]}
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ 1) : (p ≠ 0 ∧ p.Splits) := by
  by_cases h0 : p.natDegree = 0
  · exact isRealRooted_of_deg_zero hp h0
  · have h1 : p.natDegree = 1 := by lia
    exact isRealRooted_of_degree_one h1

lemma interlaces_one_linear {p : ℝ[X]} (hp_deg : p.natDegree = 1) :
    Interlaces (1 : ℝ[X]) p := by
  have h1_rr : ((1 : ℝ[X]) ≠ 0 ∧ (1 : ℝ[X]).Splits) := by simp
  have hp_rr : (p ≠ 0 ∧ p.Splits) := isRealRooted_of_degree_one hp_deg
  have hp_deg' : p.degree = 1 := by simpa [hp_deg] using degree_eq_natDegree hp_rr.1
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
    ∀ {rs : List ℝ}, rs.Pairwise (· ≤ ·) →
      ∀ r : ℝ, (rs.map (· - r)).Pairwise (· ≤ ·)
  | [], _, _ => by simp
  | x :: xs, h, r => by
      grind

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
    _ = (p.comp (X + C (x + r))).rootMultiplicity 0 := by simp [comp_assoc, add_comm, add_left_comm]
    _ = p.rootMultiplicity (x + r) := by rw [← Polynomial.rootMultiplicity_eq_rootMultiplicity]

lemma roots_comp_X_add_C {p : ℝ[X]} (r : ℝ) :
    (p.comp (X + C r)).roots = p.roots.map (fun x => x - r) := by
  ext x
  rw [count_roots, rootMultiplicity_comp_X_add_C]
  simpa [count_roots, add_comm, add_left_comm, add_assoc] using
    (Multiset.count_map_eq_count' (fun y : ℝ => y - r) p.roots
      (fun a b hab => by simp_all) (x + r)).symm

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
    (p.comp (X + C r) ≠ 0 ∧ (p.comp (X + C r)).Splits) := by
  refine ⟨(Polynomial.comp_X_add_C_ne_zero_iff).2 hp_ne, ?_⟩
  apply splits_of_card_roots
  rw [roots_comp_X_add_C r, Multiset.card_map, natDegree_comp, natDegree_X_add_C,
    card_roots_of_splits hp_splits, mul_one]

private lemma interleaves_map_of
    {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    {φ : α → β} (hφ : ∀ {a b}, r a b → s (φ a) (φ b)) :
    ∀ {l₁ l₂ : List α}, List.Interleaves r l₁ l₂ →
      List.Interleaves s (l₁.map φ) (l₂.map φ)
  | _, _, .nil_nil => .nil_nil
  | _, _, .nil_singleton a => .nil_singleton (φ a)
  | _, _, .cons_symm h hab => by
      simpa using List.Interleaves.cons_symm
        (interleaves_map_of (φ := φ) hφ h) (hφ hab)

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
  exact interleaves_map_of (fun hab => by linarith) hreverse

lemma roots_comp_one_sub_X (p : ℝ[X]) :
    (p.comp (1 - X)).roots = p.roots.map (1 - ·) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Polynomial.roots_comp_C_mul_X_add_C p (-1) 1 isUnit_neg_one

lemma isRealRooted_comp_one_sub_X
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) :
    (p.comp (1 - X) ≠ 0 ∧ (p.comp (1 - X)).Splits) := by
  have hpneg_ne : p.comp (-X) ≠ 0 := by
    simpa using (Polynomial.comp_neg_X_eq_zero_iff.not.mpr hp_ne)
  have hpneg_splits : (p.comp (-X)).Splits := hp_splits.comp_neg_X
  have htranslated :=
    isRealRooted_comp_X_add_C hpneg_ne hpneg_splits (-1)
  have heq : (p.comp (-X)).comp (X + C (-1)) = p.comp (1 - X) := by
    rw [comp_assoc]
    congr 1
    simp [sub_eq_add_neg]
  rwa [heq] at htranslated

/-- Reflection about `1 / 2` reverses same-degree proper position. -/
lemma prec_comp_one_sub_X_of_sameDegree {f g : ℝ[X]}
    (h : Prec f g) (hdeg : f.natDegree = g.natDegree) :
    Prec (g.comp (1 - X)) (f.comp (1 - X)) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  obtain ⟨_, halt⟩ := hshape.resolve_left (by intro hbad; lia)
  have hlen : ss.length = rs.length := by lia
  have halt' := listAlternates_reverse_map_one_sub hlen halt
  have hinter :
      List.Interleaves (· ≤ ·) (ss.reverse.map (1 - ·))
        (rs.reverse.map (1 - ·)) :=
    interleaves_of_listAlternates_of_length (by simp [hlen]) halt'
  refine ⟨isRealRooted_comp_one_sub_X hg.1 hg.2,
    isRealRooted_comp_one_sub_X hf.1 hf.2,
    rs.reverse.map (1 - ·), ss.reverse.map (1 - ·),
    hinter.pairwise_right, hinter.pairwise_left, ?_, ?_, Or.inr ⟨?_, halt'⟩⟩
  · rw [roots_comp_one_sub_X, ← hrs_eq]
    simp
  · rw [roots_comp_one_sub_X, ← hss_eq]
    simp
  · simp [hlen]

/-- Translation by `r` preserves `Prec`: roots are shifted left by `r`,
so the relative order is unchanged. -/
lemma prec_comp_X_add_C {f g : ℝ[X]} (h : Prec f g) (r : ℝ) :
    Prec (f.comp (X + C r)) (g.comp (X + C r)) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  refine ⟨isRealRooted_comp_X_add_C hf.1 hf.2 r, isRealRooted_comp_X_add_C hg.1 hg.2 r,
    ss.map (· - r), rs.map (· - r), ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · calc
      (↑(ss.map (· - r)) : Multiset ℝ) = (↑ss : Multiset ℝ).map (fun x => x - r) := rfl
      _ = f.roots.map (fun x => x - r) := by lia
      _ = (f.comp (X + C r)).roots := (roots_comp_X_add_C r).symm
  · calc
      (↑(rs.map (· - r)) : Multiset ℝ) = (↑rs : Multiset ℝ).map (fun x => x - r) := rfl
      _ = g.roots.map (fun x => x - r) := by lia
      _ = (g.comp (X + C r)).roots := (roots_comp_X_add_C r).symm
  · exact hcase.elim
      (fun h => Or.inl ⟨by simp_all, listInterlaces_map_sub_const h.2 r⟩)
      (fun h => Or.inr ⟨by simp_all, listAlternates_map_sub_const h.2 r⟩)

/-- Translation by `r` is an equivalence on `Prec`. -/
lemma prec_comp_X_add_C_iff {f g : ℝ[X]} (r : ℝ) :
    Prec (f.comp (X + C r)) (g.comp (X + C r)) ↔ Prec f g := by
  constructor
  · intro h
    have h' := prec_comp_X_add_C h (-r)
    simpa [comp_assoc, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h'
  · exact fun h => prec_comp_X_add_C h r

/-- A real-rooted polynomial interlaces with itself in the same-degree sense. -/
lemma prec_refl {f : ℝ[X]} (hf₀ : f ≠ 0) (hf : f.Splits) : Prec f f := by
  set rs := f.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  exact ⟨⟨hf₀, hf⟩, ⟨hf₀, hf⟩, rs, rs, hrs_sorted, hrs_sorted, hrs_eq, hrs_eq,
    Or.inr ⟨by lia, listAlternates_self_of_pairwise rs hrs_sorted⟩⟩

/-- Multiplying the left polynomial in a `Prec` relation by a nonzero scalar
preserves interlacing, since it does not change the roots. -/
lemma prec_C_mul_left {f g : ℝ[X]} (h : Prec f g) {a : ℝ} (ha : a ≠ 0) :
    Prec (C a * f) g := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  exact ⟨by simp_all, hg, ss, rs, hss, hrs, by simp_all, hrs_eq, hcase⟩

/-- Multiplying the right polynomial in a `Prec` relation by a nonzero scalar
preserves interlacing, since it does not change the roots. -/
lemma prec_C_mul_right {f g : ℝ[X]} (h : Prec f g) {a : ℝ} (ha : a ≠ 0) :
    Prec f (C a * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  exact ⟨hf, by simp_all, ss, rs, hss, hrs, hss_eq, by simp_all, hcase⟩

lemma interlaces_C_linear {p : ℝ[X]} {c : ℝ} (hc : c ≠ 0)
    (hp_deg : p.natDegree = 1) :
    Interlaces (C c) p := by
  have hprec : Prec (C c * (1 : ℝ[X])) p :=
    prec_C_mul_left (interlaces_one_linear hp_deg).toPrec hc
  have hdeg : (C c * (1 : ℝ[X])).natDegree + 1 = p.natDegree := by simp [hp_deg]
  simpa using hprec.toInterlaces hdeg

/-- Multiplying the right polynomial in a zero-aware `Prec0` relation by a
nonnegative scalar preserves the relation; the zero scalar is handled by the
zero-aware cases. -/
lemma prec0_C_mul_right_of_nonneg {f g : ℝ[X]}
    (h : Prec0 f g) {a : ℝ} (ha : 0 ≤ a) :
    Prec0 f (C a * g) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp [prec0_zero_right]
  rcases h with hf0 | hg0 | hprec
  · simpa [hf0] using prec0_zero_left (C a * g)
  · simp [hg0, prec0_zero_right]
  · exact (prec_C_mul_right hprec ha_pos.ne').toPrec0

/-- In particular, a nonzero scalar multiple of a real-rooted polynomial
interlaces the original polynomial. -/
lemma prec_C_mul_self {f : ℝ[X]} (hf₀ : f ≠ 0) (hf : f.Splits) {a : ℝ} (ha : a ≠ 0) :
    Prec (C a * f) f :=
  prec_C_mul_left (prec_refl hf₀ hf) ha

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
lemma natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff {p q : ℝ[X]}
    (hdeg : p.natDegree < q.natDegree) (hq_pos : HasPosLeadingCoeff q) :
    (p + q).natDegree = q.natDegree := by
  apply le_antisymm
  · have h := natDegree_add_le p q
    grind
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
    grind
  · apply le_natDegree_of_ne_zero
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hdeg, add_zero]
    exact ne_of_gt hp_pos

/-- If `q` has degree at most that of a nonzero polynomial `p`, then all
sufficiently small nonnegative right-family perturbations of `p` keep the
degree of `p`. -/
lemma exists_pos_forall_natDegree_add_C_mul_eq_left_of_natDegree_le
    {p q : ℝ[X]} (hp : p ≠ 0) (hdeg : q.natDegree ≤ p.natDegree) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 ≤ μ → μ < ε →
      (p + C μ * q).natDegree = p.natDegree := by
  let ε : ℝ := |p.leadingCoeff| / (|q.coeff p.natDegree| + 1)
  have hp_lc_ne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hε_pos : 0 < ε := by
    unfold ε
    positivity
  refine ⟨ε, hε_pos, ?_⟩
  intro μ hμ_nonneg hμε
  apply Polynomial.natDegree_add_C_mul_eq_left_of_natDegree_le_of_coeff_add_ne_zero hdeg
  intro hsum_zero
  have hμq_abs_lt : |μ * q.coeff p.natDegree| < |p.leadingCoeff| := by
    calc
      |μ * q.coeff p.natDegree| = μ * |q.coeff p.natDegree| := by
        rw [abs_mul, abs_of_nonneg hμ_nonneg]
      _ ≤ μ * (|q.coeff p.natDegree| + 1) := by
        exact
          mul_le_mul_of_nonneg_left
            (by linarith [abs_nonneg (q.coeff p.natDegree)]) hμ_nonneg
      _ < ε * (|q.coeff p.natDegree| + 1) := by exact mul_lt_mul_of_pos_right hμε (by positivity)
      _ = |p.leadingCoeff| := by
        have hden_ne : |q.coeff p.natDegree| + 1 ≠ 0 := by positivity
        exact div_mul_cancel₀ |p.leadingCoeff| hden_ne
  have hp_abs_eq : |p.leadingCoeff| = |μ * q.coeff p.natDegree| := by
    have hp_eq : p.leadingCoeff = -(μ * q.coeff p.natDegree) := by linarith
    rw [hp_eq, abs_neg]
  exact (not_lt_of_ge (le_of_eq hp_abs_eq)) hμq_abs_lt

/-- If `q` has degree at most that of a nonzero polynomial `p`, then on a
sufficiently small nonnegative parameter interval the right-family perturbation
has the same degree as the zero-parameter member. -/
lemma exists_pos_forall_natDegree_add_C_mul_eq_at_zero_on_Icc_of_natDegree_le
    {p q : ℝ[X]} (hp : p ≠ 0) (hdeg : q.natDegree ≤ p.natDegree) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : ℝ, ν < ε →
      ∀ η ∈ Set.Icc (0 : ℝ) ν,
        (p + C η * q).natDegree = (p + C (0 : ℝ) * q).natDegree := by
  rcases exists_pos_forall_natDegree_add_C_mul_eq_left_of_natDegree_le hp hdeg with
    ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro ν hνε η hη
  have hηε : η < ε := lt_of_le_of_lt hη.2 hνε
  have hηdeg : (p + C η * q).natDegree = p.natDegree :=
    hε η hη.1 hηε
  have hzero : (p + C (0 : ℝ) * q).natDegree = p.natDegree := by simp
  exact hηdeg.trans hzero.symm

/-- If the left summand has strictly larger degree, then every member of a
right-family perturbation set has the same degree as any chosen parameter
member. -/
lemma forall_mem_natDegree_add_C_mul_eq_left_of_natDegree_lt
    {p q : ℝ[X]} {s : Set ℝ} {κ : ℝ} (hdeg : q.natDegree < p.natDegree) :
    ∀ τ ∈ s,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree := by
  intro τ _
  rw [Polynomial.natDegree_add_C_mul_eq_left_of_natDegree_lt hdeg,
    Polynomial.natDegree_add_C_mul_eq_left_of_natDegree_lt hdeg]

/-- If the right summand has strictly larger degree, then every nonzero member
of a right-family perturbation set has the same degree as any chosen
nonzero parameter member. -/
lemma forall_mem_natDegree_add_C_mul_eq_right_of_natDegree_lt_of_ne_zero
    {p q : ℝ[X]} {s : Set ℝ} {κ : ℝ}
    (hdeg : p.natDegree < q.natDegree)
    (hκ : κ ≠ 0) (hτ : ∀ τ ∈ s, τ ≠ 0) :
    ∀ τ ∈ s,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree := by
  intro τ hτmem
  rw [Polynomial.natDegree_add_C_mul_of_natDegree_lt (hτ τ hτmem) hdeg,
    Polynomial.natDegree_add_C_mul_of_natDegree_lt hκ hdeg]

/-- If the endpoint degrees are unequal, then every nonzero member of a
right-family perturbation set has the same degree as any chosen nonzero
parameter member. -/
lemma forall_mem_natDegree_add_C_mul_eq_of_natDegree_ne_of_ne_zero
    {p q : ℝ[X]} {s : Set ℝ} {κ : ℝ}
    (hdeg : p.natDegree ≠ q.natDegree)
    (hκ : κ ≠ 0) (hτ : ∀ τ ∈ s, τ ≠ 0) :
    ∀ τ ∈ s,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree := by
  rcases lt_or_gt_of_ne hdeg with hlt | hgt
  · exact forall_mem_natDegree_add_C_mul_eq_right_of_natDegree_lt_of_ne_zero
      hlt hκ hτ
  · exact forall_mem_natDegree_add_C_mul_eq_left_of_natDegree_lt hgt

/-- If the endpoint degrees are unequal, then the right-family perturbation has
constant degree on any positive parameter interval. -/
lemma forall_mem_Icc_natDegree_add_C_mul_eq_of_natDegree_ne
    {p q : ℝ[X]} (hdeg : p.natDegree ≠ q.natDegree)
    {μ ν : ℝ} (hμ_pos : 0 < μ) :
    ∀ τ ∈ Set.Icc μ ν,
      (p + C τ * q).natDegree = (p + C μ * q).natDegree :=
  forall_mem_natDegree_add_C_mul_eq_of_natDegree_ne_of_ne_zero hdeg
    (ne_of_gt hμ_pos)
    (fun _ hτ => ne_of_gt (lt_of_lt_of_le hμ_pos hτ.1))

/-- A real parameter avoids canceling `a + t * b` exactly when it is not the
unique cancellation value `-a / b`. -/
private theorem add_mul_ne_zero_iff_ne_neg_div {a b t : ℝ} (hb : b ≠ 0) :
    a + t * b ≠ 0 ↔ t ≠ -a / b := by
  constructor
  · intro hne ht
    apply hne
    rw [ht]
    field_simp [hb]
    ring
  · intro ht hzero
    apply ht
    have ht_eq : t = -a / b := by
      field_simp [hb]
      linarith
    exact ht_eq

/-- If two summands have the same degree and the leading term never cancels on
a parameter set, then every member of that set has the same degree as any
chosen non-canceling parameter member. -/
lemma forall_mem_natDegree_add_C_mul_eq_of_natDegree_eq_of_forall_add_ne_zero
    {p q : ℝ[X]} {s : Set ℝ} {κ : ℝ}
    (hdeg : p.natDegree = q.natDegree)
    (hκ : p.leadingCoeff + κ * q.leadingCoeff ≠ 0)
    (hτ : ∀ τ ∈ s, p.leadingCoeff + τ * q.leadingCoeff ≠ 0) :
    ∀ τ ∈ s,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree := by
  intro τ hτmem
  have hle : q.natDegree ≤ p.natDegree := by rw [← hdeg]
  have hqcoeff : q.coeff p.natDegree = q.leadingCoeff := by
    rw [hdeg]
    rfl
  rw [Polynomial.natDegree_add_C_mul_eq_left_of_natDegree_le_of_coeff_add_ne_zero hle,
    Polynomial.natDegree_add_C_mul_eq_left_of_natDegree_le_of_coeff_add_ne_zero hle]
  · simpa [hqcoeff] using hκ
  · simpa [hqcoeff] using hτ τ hτmem

/-- In the same-degree case, the only leading-term cancellation parameter is
`-p.leadingCoeff / q.leadingCoeff`.  Away from that value, all right-family
members have the same degree.  If `p = 0`, this says exactly that the
nonzero polynomial `q` is scaled by nonzero parameters. -/
lemma forall_mem_natDegree_add_C_mul_eq_of_natDegree_eq_of_forall_ne_cancel
    {p q : ℝ[X]} {s : Set ℝ} {κ : ℝ}
    (hdeg : p.natDegree = q.natDegree) (hq : q ≠ 0)
    (hκ : κ ≠ -p.leadingCoeff / q.leadingCoeff)
    (hτ : ∀ τ ∈ s, τ ≠ -p.leadingCoeff / q.leadingCoeff) :
    ∀ τ ∈ s,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree := by
  have hq_lc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  apply
    forall_mem_natDegree_add_C_mul_eq_of_natDegree_eq_of_forall_add_ne_zero hdeg
  · exact (add_mul_ne_zero_iff_ne_neg_div hq_lc).mpr hκ
  · intro τ hτmem
    exact (add_mul_ne_zero_iff_ne_neg_div hq_lc).mpr (hτ τ hτmem)

/-- Same-degree right-family degree constancy on an interval strictly below
the unique leading-term cancellation parameter. -/
lemma forall_mem_Icc_natDegree_add_C_mul_eq_of_natDegree_eq_of_upper_lt_cancel
    {p q : ℝ[X]} {a b κ : ℝ}
    (hdeg : p.natDegree = q.natDegree) (hq : q ≠ 0)
    (hκ : κ < -p.leadingCoeff / q.leadingCoeff)
    (hb : b < -p.leadingCoeff / q.leadingCoeff) :
    ∀ τ ∈ Set.Icc a b,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree :=
  forall_mem_natDegree_add_C_mul_eq_of_natDegree_eq_of_forall_ne_cancel
    hdeg hq (ne_of_lt hκ)
    (fun _ hτ => ne_of_lt (lt_of_le_of_lt hτ.2 hb))

/-- Same-degree right-family degree constancy on an interval strictly above
the unique leading-term cancellation parameter. -/
lemma forall_mem_Icc_natDegree_add_C_mul_eq_of_natDegree_eq_of_cancel_lt_lower
    {p q : ℝ[X]} {a b κ : ℝ}
    (hdeg : p.natDegree = q.natDegree) (hq : q ≠ 0)
    (ha : -p.leadingCoeff / q.leadingCoeff < a)
    (hκ : -p.leadingCoeff / q.leadingCoeff < κ) :
    ∀ τ ∈ Set.Icc a b,
      (p + C τ * q).natDegree = (p + C κ * q).natDegree :=
  forall_mem_natDegree_add_C_mul_eq_of_natDegree_eq_of_forall_ne_cancel
    hdeg hq (ne_of_gt hκ)
    (fun _ hτ => ne_of_gt (lt_of_lt_of_le ha hτ.1))

/-- In the same-degree case, the unique leading-term cancellation parameter
strictly lowers the natural degree, provided the common degree is positive. -/
lemma natDegree_add_C_mul_cancel_lt_of_natDegree_eq
    {p q : ℝ[X]} (hdeg : p.natDegree = q.natDegree) (hq : q ≠ 0)
    (hpdeg : 0 < p.natDegree) :
    (p + C (-p.leadingCoeff / q.leadingCoeff) * q).natDegree < p.natDegree := by
  have hqcoeff : q.coeff p.natDegree = q.leadingCoeff := by
    rw [hdeg]
    exact coeff_natDegree
  have hq_lc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hle_scaled :
      (C (-p.leadingCoeff / q.leadingCoeff) * q).natDegree ≤ p.natDegree := by
    exact (Polynomial.natDegree_C_mul_le (-p.leadingCoeff / q.leadingCoeff) q).trans
      (le_of_eq hdeg.symm)
  have hle :
      (p + C (-p.leadingCoeff / q.leadingCoeff) * q).natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_add_le_of_degree_le (le_rfl : p.natDegree ≤ p.natDegree)
      hle_scaled)
  have hcoeff :
      (p + C (-p.leadingCoeff / q.leadingCoeff) * q).coeff p.natDegree = 0 := by
    rw [coeff_add, coeff_C_mul, coeff_natDegree, hqcoeff]
    rw [neg_div, neg_mul, div_mul_cancel₀ _ hq_lc]
    ring
  have hle_pred :
      (p + C (-p.leadingCoeff / q.leadingCoeff) * q).natDegree ≤ p.natDegree - 1 :=
    Polynomial.natDegree_le_pred hle hcoeff
  exact lt_of_le_of_lt hle_pred (by lia)

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
    p + q ≠ 0 :=
  (hasPosLeadingCoeff_add_of_same_natDegree hdeg hp_pos hq_pos).ne_zero

end RealRooted
