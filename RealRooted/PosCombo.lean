import RealRooted.WeightedSum
import RealRooted.MaWang
import RealRooted.ObreschkoffContinuity
import RealRooted.PosCombo.Degree
import RealRooted.AissenSchoenbergWhitney
import RealRooted.DegreeDropReversal

/-!
# Positive-combination real-rootedness

This file develops `PosComboRealRooted`, family and coprimeness lemmas, the
common-left interleaver forward direction, and convex-combination wrapper
theorems.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma exists_common_root_upper_bound (h : ℝ[X]) (l : List (ℝ × ℝ[X])) :
    ∃ c, (∀ r ∈ h.roots, r ≤ c) ∧ ∀ ap ∈ l, ∀ r ∈ ap.2.roots, r ≤ c := by
  induction l with
  | nil =>
      rcases exists_root_upper_bound h with ⟨c, hc⟩
      exact ⟨c, hc, by simp⟩
  | cons ap l ih =>
      rcases ih with ⟨c₁, hc₁, hl₁⟩
      rcases exists_root_upper_bound ap.2 with ⟨c₂, hc₂⟩
      refine ⟨max c₁ c₂, ?_, ?_⟩
      · simp_all
      · intro ap' hap' r hr
        grind

/-- Borcea--Brändén left-cone lemma, weighted form:
if every polynomial in the family is interlaced on the left by the same `h`,
all family members have positive leading coefficient, and the weights are
nonnegative with at least one positive weight, then the weighted sum is also
interlaced on the left by `h`. -/
theorem StrictInterl.weightedSum_left_of_common_left
    (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hstrictInterl : ∀ ap ∈ l, StrictInterl h ap.2)
    (hpos : HasPosLeadingCoeff h)
    (hpoly_pos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    StrictInterl h (weightedSum l) := by
  rcases hex with ⟨ap0, hap0, ha0_pos⟩
  have hex0 : ∃ ap ∈ l, 0 < ap.1 := ⟨ap0, hap0, ha0_pos⟩
  have hh : (h ≠ 0 ∧ h.Splits) := (hstrictInterl ap0 hap0).1
  rcases exists_common_root_upper_bound h l with ⟨r, hh_le, hl_le⟩
  let H := (X - C r) * h
  have hH_pos : HasPosLeadingCoeff H := hasPosLeadingCoeff_X_sub_C_mul hpos
  have hstrictInterl_right : ∀ ap ∈ l, StrictInterl ap.2 H := by
    intro ap hap
    have hp := hstrictInterl ap hap
    have hp_pos := hpoly_pos ap hap
    have hp_le : ∀ s ∈ ap.2.roots, s ≤ r := hl_le ap hap
    rcases hp.natDegree_eq_or_eq_succ with hdeg | hdeg
    · exact hp.mul_X_sub_C_of_sameDegree_of_roots_le
        r hdeg.symm hpos hp_pos hh_le hp_le
    · exact (strictInterl_iff_strictInterl_mul_X_sub_C_of_roots_le r
          hp.1.2 hp.2.1.2 hpos hp_pos hh_le hp_le hdeg.symm).mp hp
  have hweighted_right : StrictInterl (weightedSum l) H :=
    StrictInterl.weightedSum_right_of_nonneg
      l H hnonneg hstrictInterl_right hpoly_pos hex0
  have hweighted_pos : HasPosLeadingCoeff (weightedSum l) :=
    hasPosLeadingCoeff_weightedSum l hnonneg hpoly_pos hex0
  have hH_deg : H.natDegree = h.natDegree + 1 := by
    rw [show H = (X - C r) * h by lia, natDegree_mul (X_sub_C_ne_zero r) hh.1, natDegree_X_sub_C]
    lia
  have hH_le : ∀ s ∈ H.roots, s ≤ r := roots_le_X_sub_C_mul (hstrictInterl ap0 hap0).1.2 hh_le
  have hweighted_le : ∀ s ∈ (weightedSum l).roots, s ≤ r :=
    hweighted_right.roots_le_of_right hH_le
  rcases hweighted_right.natDegree_eq_or_eq_succ with hcase | hcase
  · have hdeg : h.natDegree + 1 = (weightedSum l).natDegree := by lia
    exact
      (strictInterl_iff_strictInterl_mul_X_sub_C_of_roots_le
        r (hstrictInterl ap0 hap0).1.2 hweighted_right.1.2 hpos hweighted_pos
        hh_le hweighted_le hdeg).mpr hweighted_right
  · have hdeg : h.natDegree = (weightedSum l).natDegree := by lia
    exact
      hweighted_right.of_mul_X_sub_C_of_sameDegree_of_roots_le hdeg
        hpos hweighted_pos hh_le hweighted_le

/-- Sign-normalized weighted left cone: the common left polynomial need only
be nonzero; its leading-coefficient sign is normalized internally. -/
theorem StrictInterl.weightedSum_left_of_common_left_signed
    (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hstrictInterl : ∀ ap ∈ l, StrictInterl h ap.2)
    (hpoly_pos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    StrictInterl h (weightedSum l) := by
  rcases hex with ⟨ap0, hap0, ha0_pos⟩
  have hh : h ≠ 0 ∧ h.Splits := (hstrictInterl ap0 hap0).1
  have hlc_ne : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hh.1
  rcases lt_or_gt_of_ne hlc_ne with hneg | hpos
  · let h' : ℝ[X] := C (-1 : ℝ) * h
    have hstrictInterl' : ∀ ap ∈ l, StrictInterl h' ap.2 :=
      fun ap hap => StrictInterl.C_mul_left (hstrictInterl ap hap) (by simp)
    have h'_pos : HasPosLeadingCoeff h' := by
      unfold h' HasPosLeadingCoeff
      simp_all
    have hsum' : StrictInterl h' (weightedSum l) :=
      StrictInterl.weightedSum_left_of_common_left
        l h' hnonneg hstrictInterl' h'_pos hpoly_pos ⟨ap0, hap0, ha0_pos⟩
    have hback : StrictInterl (C (-1 : ℝ) * h') (weightedSum l) :=
      StrictInterl.C_mul_left hsum' (by simp)
    grind
  · exact StrictInterl.weightedSum_left_of_common_left
      l h hnonneg hstrictInterl hpos hpoly_pos ⟨ap0, hap0, ha0_pos⟩

/-- Unweighted left-cone corollary. -/
theorem StrictInterl.sum_left_of_common_left
    (l : List ℝ[X]) (h : ℝ[X])
    (hstrictInterl : ∀ p ∈ l, StrictInterl h p)
    (hpos : HasPosLeadingCoeff h)
    (hpoly_pos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    StrictInterl h l.sum := by
  rw [← weightedSum_map_one l]
  apply StrictInterl.weightedSum_left_of_common_left (l.map (fun p => ((1 : ℝ), p))) h
  · simp
  · simp_all
  · lia
  · simp_all
  · cases l with
    | nil =>
        lia
    | cons p ps =>
        simp

/-- Sign-normalized left-cone theorem: if all summands are interlaced on the
left by the same nonzero real-rooted polynomial `h`, and the summands have
positive leading coefficient, then their sum is interlaced on the left by `h`
without needing to assume the sign of `h.leadingCoeff` in advance. -/
theorem StrictInterl.sum_left_of_common_left_signed
    (l : List ℝ[X]) (h : ℝ[X])
    (hstrictInterl : ∀ p ∈ l, StrictInterl h p)
    (hpoly_pos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    StrictInterl h l.sum := by
  rw [← weightedSum_map_one l]
  apply StrictInterl.weightedSum_left_of_common_left_signed
  · simp
  · simp_all
  · simp_all
  · rcases List.exists_mem_of_ne_nil l hne with ⟨p, hp⟩
    exact ⟨(1, p), by simp [hp]⟩

@[simp] lemma sum_filter_ne_zero (l : List ℝ[X]) :
    (l.filter (· ≠ 0)).sum = l.sum := by
  induction l with
  | nil =>
      simp
  | cons p l ih =>
      grind

/-- Borcea--Brändén left-cone lemma in the nonnegative-coefficients
specialization, zero-aware form on lists: if `h ≪₀ f_i` for every summand and
each `f_i` has nonnegative coefficients, then `h ≪₀ ∑ f_i`. -/
theorem Interl.sum_left_of_common_left_of_nonneg
    (l : List ℝ[X]) (h : ℝ[X])
    (hinterl : ∀ p ∈ l, Interl h p)
    (hnn : ∀ p ∈ l, HasNonnegCoeffs p) :
    Interl h l.sum := by
  by_cases hh0 : h = 0
  · simpa [hh0] using interl_zero_left l.sum
  let l' := l.filter (· ≠ 0)
  have hsum : l'.sum = l.sum := by simpa [l'] using sum_filter_ne_zero l
  by_cases hl' : l' = []
  · have hsum0 : l.sum = 0 := by simp_all
    simpa [hsum0] using interl_zero_right h
  · have hstrictInterl' : ∀ p ∈ l', StrictInterl h p := by
      intro p hp
      have hp_mem : p ∈ l := (List.mem_of_mem_filter hp)
      have hp_ne : p ≠ 0 := by grind
      rcases hinterl p hp_mem with hh | hp0 | hpf <;> lia
    have hpos' : ∀ p ∈ l', HasPosLeadingCoeff p := by
      intro p hp
      have hp_mem : p ∈ l := List.mem_of_mem_filter hp
      have hp_ne : p ≠ 0 := by grind
      have hp_rr : (p ≠ 0 ∧ p.Splits) := (hstrictInterl' p hp).2.1
      exact (hnn p hp_mem).pos_leadingCoeff hp_ne
    have hstrict : StrictInterl h l'.sum :=
      StrictInterl.sum_left_of_common_left_signed l' h hstrictInterl' hpos' hl'
    exact Or.inr <| Or.inr <| by lia

/-- Right cone for `Interl` over finite sums of nonnegative-coefficient polynomials. -/
lemma Interl.finsetSum_right_of_nonneg {ι : Type}
    (s : Finset ι) (f : ι → ℝ[X]) (h : ℝ[X])
    (hinterl : ∀ i ∈ s, Interl (f i) h)
    (hnn : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    Interl (s.sum f) h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using interl_zero_left h
  | @insert a s ha ih =>
      have hinterl_a : Interl (f a) h := hinterl a (by simp)
      have hinterl_s : ∀ i ∈ s, Interl (f i) h := by simp_all
      have hnn_a : HasNonnegCoeffs (f a) := hnn a (by simp)
      have hnn_s : ∀ i ∈ s, HasNonnegCoeffs (f i) := by simp_all
      have ih' : Interl (s.sum f) h := ih hinterl_s hnn_s
      by_cases hfa0 : f a = 0
      · simp_all
      by_cases hs0 : s.sum f = 0
      · simp_all
      by_cases hh0 : h = 0
      · simpa [Finset.sum_insert, ha, hh0] using interl_zero_right ((insert a s).sum f)
      rcases hinterl_a with _ | hh0' | hstrictInterl_a
      · lia
      · lia
      rcases ih' with _ | hh0' | hstrictInterl_s
      · lia
      · lia
      have hs_pos : HasPosLeadingCoeff (s.sum f) :=
        (hasNonnegCoeffs_finsetSum s f hnn_s).pos_leadingCoeff hs0
      have hfa_pos : HasPosLeadingCoeff (f a) := hnn_a.pos_leadingCoeff hfa0
      have hsum_strict : StrictInterl (f a + s.sum f) h :=
        StrictInterl.add_of_right_of_posLeadingCoeff
          hstrictInterl_a hstrictInterl_s hfa_pos hs_pos
      simpa [Finset.sum_insert, ha] using hsum_strict.toInterl

/-- Left cone for `Interl` over finite sums of nonnegative-coefficient polynomials. -/
lemma Interl.finsetSum_left_of_nonneg {ι : Type}
    (h : ℝ[X]) (s : Finset ι) (f : ι → ℝ[X])
    (hinterl : ∀ i ∈ s, Interl h (f i))
    (hnn : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    Interl h (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using interl_zero_right h
  | @insert a s ha ih =>
      have hinterl_s : ∀ i ∈ s, Interl h (f i) := by simp_all
      have hnn_s : ∀ i ∈ s, HasNonnegCoeffs (f i) := by simp_all
      have ih' : Interl h (s.sum f) := ih hinterl_s hnn_s
      have hpair : Interl h ([f a, s.sum f].sum) := by
        apply Interl.sum_left_of_common_left_of_nonneg
        · simp_all
        · intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · simp_all
          · exact hasNonnegCoeffs_finsetSum s f hnn_s
      simp_all

/-- Pairwise finite row-sum wrapper for `Interl`: if every selected left
summand precedes every selected right summand, and all selected summands have
nonnegative coefficients, then the two finite sums are in `Interl` proper
position. -/
lemma Interl.finsetSum_pairwise_of_nonneg {ι κ : Type}
    (s : Finset ι) (t : Finset κ) (f : ι → ℝ[X]) (g : κ → ℝ[X])
    (hinterl : ∀ i ∈ s, ∀ j ∈ t, Interl (f i) (g j))
    (hfnn : ∀ i ∈ s, HasNonnegCoeffs (f i))
    (hgnn : ∀ j ∈ t, HasNonnegCoeffs (g j)) :
    Interl (s.sum f) (t.sum g) := by
  classical
  have hleft : ∀ i ∈ s, Interl (f i) (t.sum g) :=
    fun i hi => Interl.finsetSum_left_of_nonneg (f i) t g (hinterl i hi) hgnn
  exact Interl.finsetSum_right_of_nonneg s f (t.sum g) hleft hfnn

/-! ## Deprecated zero-aware cone-sum names -/

/-- Same-degree shift on the left: if `f ≪ g`, both have positive leading
coefficient, and all roots lie at most `r`, then `g ≪ g + (X - C r) * f`. -/
theorem StrictInterl.add_of_sameDegree_shift_left_of_roots_le
    {f g : ℝ[X]} (hfg : StrictInterl f g) (r : ℝ)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    StrictInterl g (g + (X - C r) * f) := by
  let t : ℝ[X] := (X - C r) * f
  have hgt : StrictInterl g t := by
    simpa [t] using
      hfg.mul_X_sub_C_of_sameDegree_of_roots_le
        r hdeg hf_pos hg_pos hf_le hg_le
  have ht_pos : HasPosLeadingCoeff t := hasPosLeadingCoeff_X_sub_C_mul hf_pos
  have hsum : StrictInterl g ([g, t].sum) := by
    apply StrictInterl.sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact StrictInterl.refl hfg.2.1.1 hfg.2.1.2
      · lia
    · simp_all
    · lia
  grind

/-- If `f ⊳ g` with positive leading coefficients and non-negative `λ, μ`,
    not both zero, then `λf + μg` interlaces `g` from the left:
    `StrictInterl (λf + μg) g`. -/
theorem StrictInterl.nonneg_combo_right {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    StrictInterl (C a * f + C b * g) g := by
  have hweighted : StrictInterl (weightedSum [(a, f), (b, g)]) g := by
    apply StrictInterl.weightedSum_right_of_nonneg [(a, f), (b, g)] g
    · simp_all
    · intro ap hap
      rcases List.mem_cons.mp hap with h | h
      · lia
      · rcases List.mem_cons.mp h with h | h
        · cases h
          exact StrictInterl.refl hfg.2.1.1 hfg.2.1.2
        · simp at h
    · simp_all
    · simp_all
  simp_all

/-- Forward Obreschkoff direction: if `f ⊳ g` with positive leading coefficients,
    then every nontrivial nonnegative linear combination `a f + b g` is real-rooted. -/
theorem StrictInterl.isRealRooted_nonneg_combo {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) : ((C a * f + C b * g) ≠ 0 ∧ (C a * f + C b * g).Splits) :=
  (hfg.nonneg_combo_right hf_pos hg_pos ha hb hab).1

/-- Forward Obreschkoff direction, positive-coefficient special case:
    if `f ⊳ g`, then `a f + b g` is real-rooted for all `a, b > 0`. -/
theorem StrictInterl.isRealRooted_pos_combo {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((C a * f + C b * g) ≠ 0 ∧ (C a * f + C b * g).Splits) :=
  hfg.isRealRooted_nonneg_combo hf_pos hg_pos ha.le hb.le (Or.inl ha)

namespace PosComboRealRooted

/-- Reflecting both members at a common degree bound preserves
positive-combination real-rootedness. -/
lemma reflect_of_natDegree_le {f g : ℝ[X]} (hfg : PosComboRealRooted f g) {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) :
    PosComboRealRooted (reflect N f) (reflect N g) := by
  intro lam μ hlam hμ
  have hbase := hfg (lam := lam) (μ := μ) hlam hμ
  have hdeg_combo : (C lam * f + C μ * g).natDegree ≤ N :=
    (Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_C_mul_le lam f).trans hfN)
        ((Polynomial.natDegree_C_mul_le μ g).trans hgN)
  have hsplit_ref : (reflect N (C lam * f + C μ * g)).Splits :=
    DegreeDropReversal.splits_reflect_of_splits hbase.2 hdeg_combo
  have hne_ref : reflect N (C lam * f + C μ * g) ≠ 0 := by
    intro hzero
    exact hbase.1 (Polynomial.reflect_eq_zero_iff.mp hzero)
  simp_all

/-- Reflecting both members at a common degree bound preserves and reflects
positive-combination real-rootedness. -/
lemma reflect_iff_natDegree_le {f g : ℝ[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) :
    PosComboRealRooted (reflect N f) (reflect N g) ↔ PosComboRealRooted f g := by
  refine ⟨?_, fun hfg ↦ hfg.reflect_of_natDegree_le hfN hgN⟩
  intro hfg
  have hf_ref_N : (reflect N f).natDegree ≤ N :=
    Polynomial.natDegree_reflect_le.trans <| by simp_all
  have hg_ref_N : (reflect N g).natDegree ≤ N :=
    Polynomial.natDegree_reflect_le.trans <| by simp_all
  have hback :
      PosComboRealRooted (reflect N (reflect N f)) (reflect N (reflect N g)) :=
    PosComboRealRooted.reflect_of_natDegree_le
      (f := reflect N f) (g := reflect N g) (N := N) hfg hf_ref_N hg_ref_N
  simp_all

lemma isRealRooted_add {f g : ℝ[X]} (h : PosComboRealRooted f g) :
    ((f + g) ≠ 0 ∧ (f + g).Splits) := by
  simpa using h zero_lt_one zero_lt_one

/-- If both endpoints have zero constant coefficient, we may divide the whole
positive-combination family by the common factor `X`. -/
lemma divX_of_coeff_zero {f g : ℝ[X]} (h : PosComboRealRooted f g)
    (hf0 : f.coeff 0 = 0) (hg0 : g.coeff 0 = 0) :
    PosComboRealRooted f.divX g.divX := by
  intro lam μ hlam hμ
  have hbase := h (lam := lam) (μ := μ) hlam hμ
  have hf_eq : X * f.divX = f := by simpa [hf0] using Polynomial.X_mul_divX_add f
  have hg_eq : X * g.divX = g := by simpa [hg0] using Polynomial.X_mul_divX_add g
  have hfactor :
      X * (C lam * f.divX + C μ * g.divX) = C lam * f + C μ * g := by grind
  have hX :
      (X * (C lam * f.divX + C μ * g.divX) ≠ 0 ∧
        (X * (C lam * f.divX + C μ * g.divX)).Splits) := by simp_all
  exact isRealRooted_of_X_mul hX.1 hX.2

/-- Nonnegative right-family parameters split once the left endpoint is known to
split.  The zero endpoint is supplied by `hf`; positive parameters are supplied
by `PosComboRealRooted`. -/
lemma splits_add_right_of_nonneg {f g : ℝ[X]} (h : PosComboRealRooted f g)
    (hf : f.Splits) {μ : ℝ} (hμ : 0 ≤ μ) :
    (f + C μ * g).Splits := by
  rcases lt_or_eq_of_le hμ with hμ_pos | hμ_zero
  · exact (h.isRealRooted_add_right hμ_pos).2
  · simpa [← hμ_zero] using hf

lemma of_strictInterl {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g :=
  fun {_ _} hlam hμ =>
    hfg.isRealRooted_pos_combo hf_pos hg_pos hlam hμ

lemma iff_add_right {f g : ℝ[X]} :
    PosComboRealRooted f g ↔
      ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
  constructor
  · intro h μ hμ
    simpa [one_mul, add_comm] using h (lam := 1) (μ := μ) zero_lt_one hμ
  · intro h lam μ hlam hμ
    have hbase : ((f + C (μ / lam) * g) ≠ 0 ∧
      (f + C (μ / lam) * g).Splits) := h (μ := μ / lam) (by simp_all)
    have hscaled :
        ((C lam * (f + C (μ / lam) * g)) ≠ 0 ∧
          (C lam * (f + C (μ / lam) * g)).Splits) :=
      isRealRooted_C_mul hbase.1 hbase.2 hlam.ne'
    have hEq : C lam * (f + C (μ / lam) * g) = C lam * f + C μ * g := by
      rw [mul_add]
      congr 1
      calc
        C lam * (C (μ / lam) * g) = (C lam * C (μ / lam)) * g := by grind
        _ = C (lam * (μ / lam)) * g := by simp
        _ = C μ * g := by grind
    lia

lemma iff_add_left {f g : ℝ[X]} :
    PosComboRealRooted f g ↔ ∀ {lam : ℝ}, 0 < lam → ((C lam * f + g) ≠ 0 ∧
      (C lam * f + g).Splits) := by
  constructor
  · intro h lam hlam
    simpa [one_mul] using h (lam := lam) (μ := 1) hlam zero_lt_one
  · intro h lam μ hlam hμ
    have hbase : ((C (lam / μ) * f + g) ≠ 0 ∧
      (C (lam / μ) * f + g).Splits) := h (lam := lam / μ) (by simp_all)
    have hscaled :
        ((C μ * (C (lam / μ) * f + g)) ≠ 0 ∧
          (C μ * (C (lam / μ) * f + g)).Splits) := by
      simp_all [hμ.ne', splits_mul_iff_right]
    have hEq : C μ * (C (lam / μ) * f + g) = C lam * f + C μ * g := by
      rw [mul_add]
      have hleft : C μ * (C (lam / μ) * f) = C lam * f := by
        calc
          C μ * (C (lam / μ) * f) = (C μ * C (lam / μ)) * f := by grind
          _ = C (μ * (lam / μ)) * f := by simp
          _ = C lam * f := by grind
      lia
    lia

lemma of_add_right {f g : ℝ[X]}
    (h : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits)) :
    PosComboRealRooted f g :=
  (iff_add_right (f := f) (g := g)).2 h

lemma of_add_left {f g : ℝ[X]}
    (h : ∀ {lam : ℝ}, 0 < lam → ((C lam * f + g) ≠ 0 ∧ (C lam * f + g).Splits)) :
    PosComboRealRooted f g :=
  (iff_add_left (f := f) (g := g)).2 h

/-- A common left interleaver for `f` and `g` forces every strictly positive
linear combination of `f` and `g` to be real-rooted. This is the forward
Wagner-2 direction behind the common-interleaver formulation of the
restricted Obreschkoff theorem. -/
lemma of_commonLeftInterleaver {f g h : ℝ[X]}
    (hhf : StrictInterl h f) (hhg : StrictInterl h g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  have hhf' : StrictInterl h (C lam * f) := StrictInterl.C_mul_right hhf hlam.ne'
  have hhg' : StrictInterl h (C μ * g) := StrictInterl.C_mul_right hhg hμ.ne'
  have hlam_pos : HasPosLeadingCoeff (C lam * f) := hasPosLeadingCoeff_C_mul hlam hf_pos
  have hμ_pos : HasPosLeadingCoeff (C μ * g) := hasPosLeadingCoeff_C_mul hμ hg_pos
  have hstrictInterl :
      StrictInterl h ([C lam * f, C μ * g].sum) := by
    apply StrictInterl.sum_left_of_common_left_signed
    · simp_all
    · simp_all
    · lia
  simpa using hstrictInterl.2.1

/-- A common right interleaver for `f` and `g` forces every strictly positive
linear combination of `f` and `g` to be real-rooted. -/
lemma of_commonInterleaver {f g h : ℝ[X]}
    (hfh : StrictInterl f h) (hgh : StrictInterl g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  have hstrictInterl : StrictInterl (weightedSum [(lam, f), (μ, g)]) h := by
    apply StrictInterl.weightedSum_right_of_nonneg [(lam, f), (μ, g)] h
    · simp [hlam.le, hμ.le]
    · simp [hfh, hgh]
    · simp [hf_pos, hg_pos]
    · exact ⟨(lam, f), by simp [hlam]⟩
  simpa [weightedSum, weightedSum_cons] using hstrictInterl.1

/-- Positive-combination real-rootedness gives real-rootedness on the closed
line segment once the two endpoints are known to be real-rooted. -/
lemma isRealRooted_closed_segment {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits) := by
  rcases lt_or_eq_of_le hβ0 with hβ_pos | hβ_zero
  · rcases lt_or_eq_of_le hβ1 with hβ_lt | hβ_one
    · exact hfg (sub_pos.mpr hβ_lt) hβ_pos
    · simp_all
  · grind

/-- Equal-degree positive-combination pairs have real-rooted closed segments.
This packages endpoint real-rootedness from the restricted Obreschkoff converse
already available for equal degrees. -/
lemma isRealRooted_closed_segment_of_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ((C (1 - β) * f + C β * g) ≠ 0 ∧ (C (1 - β) * f + C β * g).Splits) :=
  hfg.isRealRooted_closed_segment
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).1
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).1
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
    hβ0 hβ1

/--
ASW/PF bridge for the positive-combination endpoint target.

If every right pencil `f + z g` is nonzero and has a Polya-frequency coefficient sequence,
then ASW gives real-rootedness of
`f + z g`; rescaling by a positive constant gives real-rootedness of every
positive combination `a f + b g`.
-/
theorem of_aissenSchoenbergWhitney_right_pencil
    {f g : ℝ[X]}
    (hne : ∀ {z : ℝ}, 0 ≤ z → f + C z * g ≠ 0)
    (hpf : ∀ {z : ℝ}, 0 ≤ z → IsPolyaFreqSeq (f + C z * g).coeff) :
    PosComboRealRooted f g := by
  intro a b ha hb
  let z : ℝ := b / a
  have hz : 0 ≤ z := div_nonneg hb.le ha.le
  have haz : a * z = b := by grind
  have hterm : C a * (C z * g) = C (a * z) * g := by grind
  have hscale :
      C a * (f + C z * g) = C a * f + C b * g := by
    grind
  rw [← hscale]
  exact ⟨mul_ne_zero (by grind) (hne hz),
    .mul (.C _) <| (aissenSchoenbergWhitneyForward (hpf hz)).1⟩

/--
TNN-named version of `of_aissenSchoenbergWhitney_right_pencil`.

This is convenient for LGV proofs, whose output is usually Toeplitz total
nonnegativity rather than the PF alias.
-/
theorem of_aissenSchoenbergWhitney_right_pencil_tnn
    {f g : ℝ[X]}
    (hne : ∀ {z : ℝ}, 0 ≤ z → f + C z * g ≠ 0)
    (htnn : ∀ {z : ℝ}, 0 ≤ z → IsPolyaFreqSeq (f + C z * g).coeff) :
    PosComboRealRooted f g :=
  PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil hne
    (fun {z} hz => htnn (z := z) hz)

/-- Any two positive combinations from the same one-parameter family again form
an Obreschkoff-compatible pair. -/
lemma family_pair_right {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) :
    PosComboRealRooted (f + C μ₁ * g) (f + C μ₂ * g) := by
  intro lam μ hlam hμ
  have hsum_pos : 0 < lam + μ := add_pos hlam hμ
  have hcomb_pos : 0 < lam * μ₁ + μ * μ₂ := by positivity
  have hbase : ((C (lam + μ) * f + C (lam * μ₁ + μ * μ₂) * g) ≠ 0 ∧
    (C (lam + μ) * f + C (lam * μ₁ + μ * μ₂) * g).Splits) :=
    h hsum_pos hcomb_pos
  grind

/-- Symmetric version of `family_pair_right`, normalized along the left
coefficient. -/
lemma family_pair_left {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {lam₁ lam₂ : ℝ} (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) :
    PosComboRealRooted (C lam₁ * f + g) (C lam₂ * f + g) := by
  intro lam μ hlam hμ
  have hcomb_pos : 0 < lam * lam₁ + μ * lam₂ := by positivity
  have hsum_pos : 0 < lam + μ := add_pos hlam hμ
  have hbase : ((C (lam * lam₁ + μ * lam₂) * f + C (lam + μ) * g) ≠ 0 ∧
    (C (lam * lam₁ + μ * lam₂) * f + C (lam + μ) * g).Splits) :=
    h hcomb_pos hsum_pos
  grind

lemma family_no_common_right {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ₁ μ₂ : ℝ} (hμ : μ₁ ≠ μ₂) :
    ∀ r, (f + C μ₁ * g).IsRoot r → ¬ (f + C μ₂ * g).IsRoot r := by
  intro r hr₁ hr₂
  have h₁ : f.eval r + μ₁ * g.eval r = 0 := by simp_all
  have h₂ : f.eval r + μ₂ * g.eval r = 0 := by simp_all
  have hmul : (μ₁ - μ₂) * g.eval r = 0 := by grind
  have hg0 : g.eval r = 0 := by grind
  simp_all

lemma family_no_common_left {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam₁ lam₂ : ℝ} (hlam : lam₁ ≠ lam₂) :
    ∀ r, (C lam₁ * f + g).IsRoot r → ¬ (C lam₂ * f + g).IsRoot r := by
  intro r hr₁ hr₂
  have h₁ : lam₁ * f.eval r + g.eval r = 0 := by simp_all
  have h₂ : lam₂ * f.eval r + g.eval r = 0 := by simp_all
  have hmul : (lam₁ - lam₂) * f.eval r = 0 := by grind
  have hf0 : f.eval r = 0 := by grind
  simp_all

lemma family_isCoprime_right {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ : μ₁ ≠ μ₂) :
    IsCoprime (f + C μ₁ * g) (f + C μ₂ * g) :=
  isCoprime_of_no_common_real_root_of_isRealRooted
    (hfg.isRealRooted_add_right hμ₁).1
    (hfg.isRealRooted_add_right hμ₁).2
    (family_no_common_right hno hμ)

lemma family_isCoprime_left {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam₁ lam₂ : ℝ} (hlam₁ : 0 < lam₁) (hlam : lam₁ ≠ lam₂) :
    IsCoprime (C lam₁ * f + g) (C lam₂ * f + g) :=
  isCoprime_of_no_common_real_root_of_isRealRooted
    (hfg.isRealRooted_add_left hlam₁).1
    (hfg.isRealRooted_add_left hlam₁).2
    (family_no_common_left hno hlam)

/-- No two distinct closed-segment members `C (1 - βᵢ) * f + C βᵢ * g` share a
real root, provided `f` and `g` have no common real root. -/
lemma family_no_common_segment {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β₁ β₂ : ℝ} (hβ : β₁ ≠ β₂) :
    ∀ r, (C (1 - β₁) * f + C β₁ * g).IsRoot r →
      ¬ (C (1 - β₂) * f + C β₂ * g).IsRoot r := by
  intro r hr₁ hr₂
  have h₁ : (1 - β₁) * f.eval r + β₁ * g.eval r = 0 := by simp_all
  have h₂ : (1 - β₂) * f.eval r + β₂ * g.eval r = 0 := by simp_all
  have hfg : f.eval r = g.eval r := by grind
  have : f.eval r = 0 := by grind
  have hg0 : g.eval r = 0 := by simp_all
  simp_all

/-- Two interior closed-segment members again form a positive-combination
pair.  The scalar coefficients of any strictly positive combination stay
strictly positive because both weights lie in `(0, 1)`. -/
lemma family_pair_segment {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {β₁ β₂ : ℝ} (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1)
    (hβ₂0 : 0 < β₂) (hβ₂1 : β₂ < 1) :
    PosComboRealRooted (C (1 - β₁) * f + C β₁ * g)
      (C (1 - β₂) * f + C β₂ * g) := by
  intro lam μ hlam hμ
  have h1β₁ : 0 < 1 - β₁ := by linarith
  have h1β₂ : 0 < 1 - β₂ := by linarith
  have hA : 0 < lam * (1 - β₁) + μ * (1 - β₂) := by positivity
  have hB : 0 < lam * β₁ + μ * β₂ := by positivity
  have hbase := h hA hB
  grind

/-- Any two distinct closed-segment members of a positive-combination,
common-root-free pair are coprime when the first one is interior. -/
lemma family_isCoprime_segment {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {β₁ β₂ : ℝ} (hβ₁0 : 0 < β₁) (hβ₁1 : β₁ < 1) (hβ : β₁ ≠ β₂) :
    IsCoprime (C (1 - β₁) * f + C β₁ * g) (C (1 - β₂) * f + C β₂ * g) :=
  isCoprime_of_no_common_real_root_of_isRealRooted
    (hfg (by linarith) hβ₁0).1
    (hfg (by linarith) hβ₁0).2
    (family_no_common_segment hno hβ)

/-- Positive-combination real-rootedness descends through a shared real-rooted
factor. This is the common-factor reduction step needed for converse
arguments. -/
lemma of_mul_common_factor {d f g : ℝ[X]}
    (h : PosComboRealRooted (d * f) (d * g)) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  have hEq :
      C lam * (d * f) + C μ * (d * g) = d * (C lam * f + C μ * g) := by
    ring
  have hrr : ((d * (C lam * f + C μ * g)) ≠ 0 ∧ (d * (C lam * f + C μ * g)).Splits) := by
    simpa [hEq] using h hlam hμ
  have hcombo_ne : C lam * f + C μ * g ≠ 0 := right_ne_zero_of_mul hrr.1
  exact isRealRooted_of_dvd hrr.1 hrr.2 hcombo_ne ⟨d, by grind⟩

/-- Positive-combination real-rootedness descends through a shared linear
factor. -/
lemma of_mul_X_sub_C {f g : ℝ[X]} {r : ℝ}
    (h : PosComboRealRooted ((X - C r) * f) ((X - C r) * g)) :
    PosComboRealRooted f g :=
  of_mul_common_factor h

/-- Common-root quotient data for a positive-leading close-degree
`PosComboRealRooted` pair.  This is the reusable one-step data behind
common-root reductions for Obreschkoff-style converse arguments. -/
lemma common_root_reduction_data
    {f g : ℝ[X]} {r : ℝ}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      PosComboRealRooted qf qg ∧
      HasPosLeadingCoeff qf ∧
      HasPosLeadingCoeff qg ∧
      qf.natDegree ≤ qg.natDegree ∧
      qg.natDegree ≤ qf.natDegree + 1 := by
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  have hf_ne : f ≠ 0 := hf_pos.ne_zero
  have hg_ne : g ≠ 0 := hg_pos.ne_zero
  refine ⟨qf, qg, hqf, hqg, ?_, ?_, ?_, ?_, ?_⟩
  · exact (of_mul_X_sub_C (f := qf) (g := qg) (r := r) (by
        lia))
  · exact hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqf] using hf_pos)
  · exact hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqg] using hg_pos)
  · have hqf_ne : qf ≠ 0 := by simp_all
    have hqg_ne : qg ≠ 0 := by simp_all
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg_lo
    lia
  · have hqf_ne : qf ≠ 0 := by simp_all
    have hqg_ne : qg ≠ 0 := by simp_all
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg_hi
    lia

/-- To prove the restricted Obreschkoff converse, it is enough to handle the
no-common-roots case. Shared roots can be factored out recursively.

In the same-degree case the correct conclusion is the Obreschkoff alternative
`StrictInterl f g ∨ StrictInterl g f`; the degree-`+1` case remains oriented. -/
theorem strictInterl_or_reverse_of_posComboRealRooted_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        PosComboRealRooted f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        StrictInterl f g ∨ StrictInterl g f)
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    StrictInterl f g ∨ StrictInterl g f := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          PosComboRealRooted f g →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          StrictInterl f g ∨ StrictInterl g f)
      f.natDegree ?_ rfl hfg hf_pos hg_pos hdeg_lo hdeg_hi
  intro n ih f g hfdeg hfg hf_pos hg_pos hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · simp_all
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data hfg hf_pos hg_pos hdeg_lo hdeg_hi hrf hrg
    have hf_ne : f ≠ 0 := hf_pos.ne_zero
    have hqf_ne : qf ≠ 0 := by simp_all
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hstrictInterl_q : StrictInterl qf qg ∨ StrictInterl qg qf :=
      ih qf.natDegree hqf_deg_lt rfl hqfg hqf_pos hqg_pos hqdeg_lo hqdeg_hi
    rcases hstrictInterl_q with hstrictInterl_q | hstrictInterl_q
    · have hstrictInterl_mul : StrictInterl ((X - C r) * qf) ((X - C r) * qg) :=
        hstrictInterl_q.mul_common_factor
          (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2
      lia
    · have hstrictInterl_mul : StrictInterl ((X - C r) * qg) ((X - C r) * qf) :=
        hstrictInterl_q.mul_common_factor
          (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2
      lia
end PosComboRealRooted

namespace PosComboRealRooted

/-- Same-degree `StrictInterl` can be recovered once one has strict sign changes of `g`
on consecutive roots of `f` and one root of `g` strictly to the right of all
roots of `f`. This repackages the final Ma--Wang assembly step in the form
needed by the same-degree Obreschkoff converse. -/
theorem strictInterl_same_of_root_sign_data
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ f.natDegree)
    (hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        g.eval r₁ * g.eval r₂ < 0)
    (hright :
      let rs := f.roots.sort (· ≤ ·)
      ∃ uR, g.IsRoot uR ∧ ∀ r ∈ rs, r < uR) :
    StrictInterl f g := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hlen : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
      card_roots_of_splits hf_splits]
  have hn : 1 ≤ rs.length := by lia
  have hg_ne : g ≠ 0 := hg_pos.ne_zero
  exact
    strictInterl_same_of_strict_signs_of_right_root
      hf_ne hf_splits hg_ne hrs_sorted hrs_eq hdeg hn
      (by grind)
      (by grind)

/-- An equal-degree Obreschkoff alternative can be oriented once we know that
`f` has a root strictly to the right of an upper bound for all roots of `g`. -/
theorem strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
    {f g : ℝ[X]} {c r : ℝ}
    (h : StrictInterl f g ∨ StrictInterl g f)
    (hg_le : ∀ s ∈ g.roots, s ≤ c)
    (hfr : f.IsRoot r)
    (hc_lt : c < r) :
    StrictInterl g f := by
  rcases h with hfg | hgf
  · exfalso
    have hfle : r ≤ c := hfg.roots_le_of_right hg_le r ((mem_roots hfg.1.1).mpr hfr)
    grind
  · lia

/-- Symmetric orientation selector for the equal-degree Obreschkoff
alternative. -/
theorem reverseStrictInterl_of_strictInterl_or_reverse_of_root_asymmetry
    {f g : ℝ[X]} {c r : ℝ}
    (h : StrictInterl f g ∨ StrictInterl g f)
    (hf_le : ∀ s ∈ f.roots, s ≤ c)
    (hgr : g.IsRoot r)
    (hc_lt : c < r) :
    StrictInterl f g :=
  strictInterl_of_strictInterl_or_reverse_of_root_asymmetry
    (f := g) (g := f) (c := c) (r := r) (by lia)
    hf_le hgr hc_lt

/-- Linear equal-degree case of the same-degree Obreschkoff alternative. -/
theorem strictInterl_or_reverse_of_same_degree_one
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg1 : f.natDegree = 1) :
    StrictInterl f g ∨ StrictInterl g f := by
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_degree_one hf_deg1
  have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one (by lia)
  obtain ⟨rf, hrf_eq⟩ : ∃ rf, f.roots = {rf} :=
    Multiset.card_eq_one.mp (by simpa [hf_deg1] using card_roots_of_splits hf_rr.2)
  obtain ⟨rg, hrg_eq⟩ : ∃ rg, g.roots = {rg} :=
    Multiset.card_eq_one.mp (by
    have : g.natDegree = 1 := by lia
    simpa [this] using card_roots_of_splits hg_rr.2)
  by_cases hle : rf ≤ rg
  · left
    refine
      ⟨hf_rr, hg_rr, [rf], [rg], List.pairwise_singleton _ _,
        List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · simp [hrf_eq]
    · simp [hrg_eq]
    · exact Or.inr ⟨by simp, by simp [ListAlternates, ListInterlaces, hle]⟩
  · right
    have hge : rg ≤ rf := le_of_not_ge hle
    refine
      ⟨hg_rr, hf_rr, [rg], [rf], List.pairwise_singleton _ _,
        List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · simp [hrg_eq]
    · simp [hrf_eq]
    · exact Or.inr ⟨by simp, by simp [ListAlternates, ListInterlaces, hge]⟩

end PosComboRealRooted

/-! ### Note on PosComboRealRooted and interlacing

`PosComboRealRooted f g` (all positive scalar combinations real-rooted) is
equivalent to `f` and `g` having a **common interlacer** (Ryder/Obreschkoff,
Theorem 6.3). This is strictly weaker than `StrictInterl f g` (strong interlacing).

Counterexample: `f = (x+1)(x+3)`, `g = x(x+4)` satisfies `PosComboRealRooted`
but roots `{-4, -3, -1, 0}` don't interlace (pattern g, f, f, g).

For strong interlacing `StrictInterl f g`, one needs the **affine family** hypothesis
`(λx + μ)f + g` real-rooted for all `λ, μ > 0`, with nonneg coefficients.
This is Brändén's Lemma 7.8.4, stated as `strictInterl_of_affine_family_nonneg`
in `InterlacingSequence.lean`.

The correct Obreschkoff converse is: `PosComboRealRooted f g` implies
`∃ h, StrictInterl h f ∧ StrictInterl h g` (existence of a common interlacer). -/

/-- If `f ⊳ g` with positive leading coefficients and positive `λ, μ`,
    then `λf + μg` interlaces `g` from the left: `StrictInterl (λf + μg) g`.
    This is the positive-coefficient special case of `StrictInterl.nonneg_combo_right`. -/
theorem StrictInterl.convex_right {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictInterl (C a * f + C b * g) g :=
  hfg.nonneg_combo_right hf_pos hg_pos ha.le hb.le (Or.inl ha)

/-- If `f ⊳ g` with positive leading coefficients and nonnegative `a, b`,
not both zero, then `f` interlaces `a·f + b·g`: `StrictInterl f (a·f + b·g)`.
This is the common-left cone theorem applied to `f ≪ f` and `f ≪ g`. -/
theorem StrictInterl.nonneg_combo_left {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    StrictInterl f (C a * f + C b * g) := by
  have hweighted : StrictInterl f (weightedSum [(a, f), (b, g)]) := by
    apply StrictInterl.weightedSum_left_of_common_left_signed [(a, f), (b, g)] f
    · simp_all
    · intro ap hap
      rcases List.mem_cons.mp hap with h | h
      · subst h
        exact StrictInterl.refl hfg.1.1 hfg.1.2
      · rcases List.mem_cons.mp h with h | h
        · subst h
          exact hfg
        · simp at h
    · simp_all
    · simp_all
  simp_all

/-- If `f ⊳ g` with positive leading coefficients and positive `a, b`,
then `f` interlaces `a·f + b·g` from the right: `StrictInterl f (a·f + b·g)`. -/
theorem StrictInterl.convex_left {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictInterl f (C a * f + C b * g) :=
  hfg.nonneg_combo_left hf_pos hg_pos ha.le hb.le (Or.inl ha)

/-- A common-factor version of `StrictInterl.convex_left`. If `f` and `g` share a
real-rooted factor `d`, it is enough to know the interlacing and leading
coefficients after factoring out `d`. -/
theorem StrictInterl.convex_left_of_common_factor {d f g : ℝ[X]}
    (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    {f' g' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g')
    (hfg : StrictInterl f' g')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictInterl f (C a * f + C b * g) := by
  subst hf_def hg_def
  have hbase : StrictInterl f' (C a * f' + C b * g') :=
    hfg.convex_left hf'_pos hg'_pos ha hb
  have hmul : StrictInterl (d * f') (d * (C a * f' + C b * g')) :=
    hbase.mul_common_factor hd_ne hd_splits
  grind

end RealRooted
