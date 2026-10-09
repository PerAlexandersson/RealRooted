import RealRooted.OperatorPreservesInterlacing
import RealRooted.Interlacing.NegativeRoots
import RealRooted.LiuOppositeSigns.RootDeletion
import RealRooted.SimpleRoots

/-!
# Linear maps preserving interlacing of negative-rooted pairs

`IsNegativeSimple p`: `p` has positive leading coefficient and simple, strictly negative roots.
A linear map `T : ℝ[X] →ₗ[ℝ] ℝ[X]` that
* maps negative-simple polynomials to negative-simple polynomials of one higher degree
  (`MapsNegativeSimpleBySucc`), and
* maps every `(X − ρ) q` with `q` negative-simple to a polynomial with simple real roots
  (`MapsAffineNegativeSimple`)
preserves strict interlacing without common roots of negative-simple pairs `f ≪ g`
(`strictInterl_map_of_negative_simple_pencil`).  The proof runs through the Obreschkoff pencil:
every member `α f + β g` is a multiple of a negative-simple `q` or of `(X − ρ) q`
(`hasNegativeSimplePencilShapes_of_strictInterl`), so `T` keeps the whole pencil real-rooted.
The no-common-root hypothesis is needed: the repository's `StrictInterl` allows common roots, and
then pencil members can have double roots.  `strictInterl_iterate_of_negative_simple` iterates
the statement along `P (n+1) = T (P n)`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A positive-leading polynomial with pairwise simple, strictly negative roots. -/
def IsNegativeSimple (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits ∧ HasSimpleRoots p ∧ HasPosLeadingCoeff p ∧
    ∀ r ∈ p.roots, r < 0

/-- The simple real-rootedness certificate used for affine pencil members. -/
def IsSimpleRealRooted (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits ∧ HasSimpleRoots p

/-- H1: `T` raises every negative-simple input by one degree. -/
def MapsNegativeSimpleBySucc (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃q : ℝ[X]⦄, IsNegativeSimple q →
    IsNegativeSimple (T q) ∧ (T q).natDegree = q.natDegree + 1

/-- H2: `T` sends every affine negative-simple input to a simple split polynomial. -/
def MapsAffineNegativeSimple (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ ⦃q : ℝ[X]⦄ (ρ : ℝ), IsNegativeSimple q →
    IsSimpleRealRooted (T ((X - C ρ) * q))

/-- The root-shape assertion needed to apply H1 or H2 to a pencil member.

The assertion is independent of `T`: each nonzero split member is either a
nonzero scalar multiple of a negative-simple polynomial or has one affine
factor followed by a negative-simple polynomial. -/
def HasNegativeSimplePencilShapes (f g : ℝ[X]) : Prop :=
  ∀ α β : ℝ,
    (C α * f + C β * g ≠ 0 ∧ (C α * f + C β * g).Splits) →
      ∃ (c : ℝ) (q : ℝ[X]), c ≠ 0 ∧ IsNegativeSimple q ∧
        (C α * f + C β * g = C c * q ∨
          ∃ ρ : ℝ, C α * f + C β * g = C c * ((X - C ρ) * q))

private lemma map_C_mul {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {c : ℝ} {p : ℝ[X]} :
    T (C c * p) = C c * T p := by
  simpa only [Polynomial.smul_eq_C_mul] using T.map_smul c p

private lemma negativeSimple_of_C_mul_of_negativeSimple {p : ℝ[X]} {c : ℝ}
    (hp : IsNegativeSimple p) (hc : c ≠ 0) (hc_pos : 0 < c) :
    IsNegativeSimple (C c * p) := by
  have hrr := isRealRooted_C_mul hp.1 hp.2.1 hc
  have hsimple : HasSimpleRoots (C c * p) := by
    apply HasSimpleRoots.of_roots_nodup hrr.1
    rw [Polynomial.roots_C_mul _ hc]
    exact hp.2.2.1.roots_nodup
  refine ⟨hrr.1, hrr.2, hsimple, ?_, ?_⟩
  · simpa [HasPosLeadingCoeff] using mul_pos hc_pos hp.2.2.2.1
  · intro r hr
    apply hp.2.2.2.2 r
    rw [Polynomial.roots_C_mul _ hc] at hr
    simpa using hr

private lemma negativeSimple_shape_of_strictInterl
    {f p : ℝ[X]} (hf : IsNegativeSimple f)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits)
    (hp_simple : HasSimpleRoots p) (hp_pos : HasPosLeadingCoeff p)
    (hfp : StrictInterl f p)
    (hdeg : p.natDegree = f.natDegree + 1) :
    ∃ (c : ℝ) (q : ℝ[X]), c ≠ 0 ∧ IsNegativeSimple q ∧
      (p = C c * q ∨ ∃ ρ : ℝ, p = C c * ((X - C ρ) * q)) := by
  have hinter : Interlaces f p := hfp.toInterlaces hdeg.symm
  obtain ⟨hp_rr, hf_rr, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ := hinter
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    have : p.natDegree = 0 := by
      rw [← card_roots_of_splits hp_rr.2, ← hrs_eq, hrs_nil]
      simp
    have : f.natDegree + 1 = 0 := by lia
    simp at this
  have hss_neg : ∀ s ∈ ss, s < 0 := by
    intro s hs
    apply hf.2.2.2.2 s
    rw [← hss_eq]
    exact Multiset.mem_coe.mpr hs
  have hrs_drop_neg : ∀ r ∈ rs.dropLast, r < 0 :=
    listInterlaces_dropLast_lt_zero_of_forall_lt_zero hint hss_neg
  let ρ : ℝ := rs.getLast hrs_ne
  have hρ_mem : ρ ∈ rs := by
    exact List.getLast_mem hrs_ne
  have hρ_root : p.IsRoot ρ := by
    apply (mem_roots hp_ne).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr hρ_mem
  have hρ_neg_or_nonneg : ρ < 0 ∨ 0 ≤ ρ := lt_or_ge ρ 0
  let c : ℝ := p.leadingCoeff
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hp_ne
  rcases hρ_neg_or_nonneg with hρ_neg | hρ_nonneg
  · refine ⟨c, C c⁻¹ * p, hc, ?_, ?_⟩
    · have hqrr := isRealRooted_C_mul hp_ne hp_splits (inv_ne_zero hc)
      have hqsimple : HasSimpleRoots (C c⁻¹ * p) := by
        apply HasSimpleRoots.of_roots_nodup hqrr.1
        rw [Polynomial.roots_C_mul _ (inv_ne_zero hc)]
        exact hp_simple.roots_nodup
      have hqpos : HasPosLeadingCoeff (C c⁻¹ * p) := by
        exact hasPosLeadingCoeff_C_mul
          (by simpa [c] using one_div_pos.mpr hp_pos) hp_pos
      refine ⟨hqrr.1, hqrr.2, hqsimple, hqpos, ?_⟩
      intro r hr
      have hrp : r ∈ p.roots := by
        rw [Polynomial.roots_C_mul _ (inv_ne_zero hc)] at hr
        exact hr
      have hr_mem : r ∈ rs := by
        rw [← hrs_eq] at hrp
        exact Multiset.mem_coe.mp hrp
      by_cases hr_last : r = ρ
      · simpa [hr_last] using hρ_neg
      · exact hrs_drop_neg r
          (List.mem_dropLast_of_mem_of_ne_getLast hr_mem hr_last)
    · left
      calc
        p = C 1 * p := by simp
        _ = C (c * c⁻¹) * p := by rw [mul_inv_cancel₀ hc]
        _ = C c * (C c⁻¹ * p) := by rw [C_mul]; ring
  · let q := LiuOppositeSigns.deleteRootFactor p ρ
    have hq := LiuOppositeSigns.deleteRootFactor_ne_zero_and_splits_of_isRoot
      hp_ne hp_splits hρ_root
    have hfactor : (X - C ρ) * q = p :=
      LiuOppositeSigns.factor_deleteRootFactor_of_isRoot hρ_root
    have hq_pos : HasPosLeadingCoeff q := by
      dsimp [q]
      rw [HasPosLeadingCoeff]
      rw [LiuOppositeSigns.leadingCoeff_deleteRootFactor_of_isRoot hp_ne hρ_root]
      simpa only [HasPosLeadingCoeff] using hp_pos
    have hq_not_root : ¬ q.IsRoot ρ := by
      intro hqρ
      rw [Polynomial.IsRoot.def] at hqρ
      have hder : p.derivative.eval ρ = 0 := by
        rw [← hfactor]
        simp [Polynomial.derivative_mul, hqρ]
      exact hp_simple.eval_derivative_ne_zero hρ_root hder
    have hq_simple : HasSimpleRoots q := by
      intro s hs
      have hs_p : p.IsRoot s := by
        rw [Polynomial.IsRoot.def] at hs ⊢
        rw [← hfactor, eval_mul]
        rw [hs, mul_zero]
      have hs_ne : s ≠ ρ := by
        intro hEq
        exact hq_not_root (by simpa [hEq] using hs)
      have hmult := hp_simple s hs_p
      rw [← hfactor, Polynomial.rootMultiplicity_mul
        (by simpa [hfactor] using hp_ne), Polynomial.rootMultiplicity_X_sub_C] at hmult
      simpa [hs_ne] using hmult
    have hq_neg : ∀ s ∈ q.roots, s < 0 := by
      intro s hs
      have hs_q : q.IsRoot s := (mem_roots hq.1).mp hs
      have hs_p : p.IsRoot s := by
        rw [Polynomial.IsRoot.def] at hs_q ⊢
        rw [← hfactor, eval_mul]
        simp [hs_q]
      have hs_ne : s ≠ ρ := by
        intro hEq
        exact hq_not_root (by simpa [hEq] using hs_q)
      have hs_mem : s ∈ rs := by
        have hs_mem' : s ∈ p.roots := (mem_roots hp_ne).mpr hs_p
        rw [← hrs_eq] at hs_mem'
        exact Multiset.mem_coe.mp hs_mem'
      exact hrs_drop_neg s (List.mem_dropLast_of_mem_of_ne_getLast hs_mem hs_ne)
    have hqneg : IsNegativeSimple q :=
      ⟨hq.1, hq.2, hq_simple, hq_pos, hq_neg⟩
    refine ⟨c, C c⁻¹ * q, hc, ?_, ?_⟩
    · exact negativeSimple_of_C_mul_of_negativeSimple hqneg (inv_ne_zero hc)
        (by simpa [c] using (one_div_pos.mpr hp_pos))
    · right
      use ρ
      calc
        p = (X - C ρ) * q := hfactor.symm
        _ = C 1 * ((X - C ρ) * q) := by simp
        _ = C (c * c⁻¹) * ((X - C ρ) * q) := by rw [mul_inv_cancel₀ hc]
        _ = C c * ((X - C ρ) * (C c⁻¹ * q)) := by rw [C_mul]; ring

/-- Every nonzero split member of a strictly-root-disjoint negative pencil has
the required negative-simple root shape. -/
theorem hasNegativeSimplePencilShapes_of_strictInterl
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcop : ∀ r, ¬ (f.IsRoot r ∧ g.IsRoot r))
    (hf : IsNegativeSimple f) (hg : IsNegativeSimple g) :
    HasNegativeSimplePencilShapes f g := by
  have hall : AllComboRealRooted f g := allComboRealRooted_of_strictInterl hfg
  intro α β hp
  by_cases hβ : β = 0
  · have hα : α ≠ 0 := by
      intro hα
      simp [hα, hβ] at hp
    refine ⟨α, f, hα, hf, Or.inl ?_⟩
    simp [hβ]
  · let P : ℝ[X] := C α * f + C β * g
    let P₀ : ℝ[X] := C β⁻¹ * P
    have hP : P ≠ 0 ∧ P.Splits := by simpa [P] using hp
    have hP₀ : P₀ ≠ 0 ∧ P₀.Splits := by
      dsimp [P₀]
      exact isRealRooted_C_mul hP.1 hP.2 (inv_ne_zero hβ)
    have hP₀_eq : P₀ = C (β⁻¹ * α) * f + C 1 * g := by
      dsimp [P₀, P]
      calc
        C β⁻¹ * (C α * f + C β * g) =
            (C β⁻¹ * C α) * f + (C β⁻¹ * C β) * g := by ring
        _ = C (β⁻¹ * α) * f + C 1 * g := by
          rw [← C_mul, ← C_mul, inv_mul_cancel₀ hβ]
    have hall₀ : AllComboRealRooted f P₀ := by
      apply allComboRealRooted_linear_recombination (f := f) (g := g)
        (p := f) (q := P₀)
        (a := 1) (b := 0) (c := β⁻¹ * α) (d := 1)
      · simp
      · exact hP₀_eq
      · exact hall
    have hno₀ : ∀ r, ¬ (f.IsRoot r ∧ P₀.IsRoot r) := by
      intro r hr
      have hfr : f.IsRoot r := hr.1
      have hP₀r : P₀.IsRoot r := hr.2
      have hPr : P.IsRoot r := by
        rw [Polynomial.IsRoot.def] at hP₀r ⊢
        dsimp [P₀] at hP₀r
        rw [eval_mul] at hP₀r
        exact (mul_eq_zero.mp hP₀r).resolve_left (by simp [hβ])
      have hgr : g.IsRoot r := by
        rw [Polynomial.IsRoot.def] at hfr hPr ⊢
        dsimp [P] at hPr
        rw [eval_add, eval_mul, eval_mul] at hPr
        have hPr' : β = 0 ∨ g.eval r = 0 := by
          simpa [hfr] using hPr
        rcases hPr' with hβ0 | hgr
        · exact (hβ hβ0).elim
        · exact hgr
      exact hcop r ⟨hfr, hgr⟩
    have hdeg_lt : (C α * f).natDegree < g.natDegree := by
      exact (natDegree_C_mul_le α f).trans_lt (by lia)
    have hPdeg : P.natDegree = g.natDegree := by
      dsimp [P]
      have hβdeg : (C β * g).natDegree = g.natDegree :=
        Polynomial.natDegree_C_mul hβ
      have hlt : (C α * f).natDegree < (C β * g).natDegree := by
        rw [hβdeg]
        exact hdeg_lt
      have h := Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
      rw [hβdeg] at h
      exact h
    have hdegP₀ : P₀.natDegree = f.natDegree + 1 := by
      dsimp [P₀]
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hβ), hPdeg, hdeg]
    have hP₀_strict_or : StrictInterl f P₀ ∨ StrictInterl P₀ f :=
      strictInterl_of_allComboRealRooted hf.1 hf.2.1 hP₀.1 hP₀.2 hall₀
        (Or.inl hdegP₀.symm)
    have hP₀_strict : StrictInterl f P₀ :=
      StrictInterl.forward_of_orientation_of_succDegree hdegP₀ hP₀_strict_or
    have hP₀_simple : HasSimpleRoots P₀ :=
      (hP₀_strict.hasSimpleRoots_of_no_common_root hno₀).2
    have hP₀_pos : HasPosLeadingCoeff P₀ := by
      have hlead : P.leadingCoeff = β * g.leadingCoeff := by
        dsimp [P]
        rw [Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt (by simp [hβ]) hdeg_lt]
      dsimp [P₀]
      rw [HasPosLeadingCoeff,
        Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero hβ)),
        hlead]
      rw [← mul_assoc, inv_mul_cancel₀ hβ, one_mul]
      exact hg.2.2.2.1
    obtain ⟨c, q, hc, hq, hform⟩ :=
      negativeSimple_shape_of_strictInterl hf hP₀.1 hP₀.2 hP₀_simple hP₀_pos
        hP₀_strict hdegP₀
    have hP_eq : P = C β * P₀ := by
      dsimp [P₀]
      calc
        P = C 1 * P := by simp
        _ = C (β * β⁻¹) * P := by rw [mul_inv_cancel₀ hβ]
        _ = C β * (C β⁻¹ * P) := by rw [C_mul]; ring
    rcases hform with hform | ⟨ρ, hform⟩
    · refine ⟨β * c, q, mul_ne_zero hβ hc, hq, Or.inl ?_⟩
      have hshapeP : P = C (β * c) * q := by
        calc
          P = C β * P₀ := hP_eq
          _ = C β * (C c * q) := by rw [hform]
          _ = C (β * c) * q := by rw [← mul_assoc, C_mul]
      simpa [P] using hshapeP
    · refine ⟨β * c, q, mul_ne_zero hβ hc, hq, Or.inr ⟨ρ, ?_⟩⟩
      have hshapeP : P = C (β * c) * ((X - C ρ) * q) := by
        calc
          P = C β * P₀ := hP_eq
          _ = C β * (C c * ((X - C ρ) * q)) := by rw [hform]
          _ = C (β * c) * ((X - C ρ) * q) := by rw [← mul_assoc, C_mul]
      simpa [P] using hshapeP
  

/-- A linear map satisfying H1--H2 preserves the oriented successor-degree
interlacing relation and root-disjointness of a negative-simple pencil. -/
theorem strictInterl_map_of_negative_simple_pencil
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {f g : ℝ[X]}
    (hfg : StrictInterl f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hcop : ∀ r, ¬ (f.IsRoot r ∧ g.IsRoot r))
    (hf : IsNegativeSimple f) (hg : IsNegativeSimple g)
    (hT₁ : MapsNegativeSimpleBySucc T)
    (hT₂ : MapsAffineNegativeSimple T)
    : StrictInterl (T f) (T g) ∧
      ∀ r, ¬ ((T f).IsRoot r ∧ (T g).IsRoot r) := by
  have hshape := hasNegativeSimplePencilShapes_of_strictInterl hfg hdeg hcop hf hg
  have hall : AllComboRealRooted f g := allComboRealRooted_of_strictInterl hfg
  have hmapSimple : ∀ α β : ℝ,
      (C α * f + C β * g ≠ 0 ∧ (C α * f + C β * g).Splits) →
        IsSimpleRealRooted (T (C α * f + C β * g)) := by
    intro α β hp
    obtain ⟨c, q, hc, hq, hqform⟩ := hshape α β hp
    rcases hqform with hqform | ⟨ρ, hqform⟩
    · have hTq := hT₁ hq
      rw [hqform, map_C_mul]
      have hrr := isRealRooted_C_mul hTq.1.1 hTq.1.2.1 hc
      have hs : HasSimpleRoots (C c * T q) := by
        apply HasSimpleRoots.of_roots_nodup hrr.1
        rw [Polynomial.roots_C_mul _ hc]
        exact hTq.1.2.2.1.roots_nodup
      exact ⟨hrr.1, hrr.2, hs⟩
    · have hTq := hT₂ ρ hq
      rw [hqform, map_C_mul]
      have hrr := isRealRooted_C_mul hTq.1 hTq.2.1 hc
      have hs : HasSimpleRoots (C c * T ((X - C ρ) * q)) := by
        apply HasSimpleRoots.of_roots_nodup hrr.1
        rw [Polynomial.roots_C_mul _ hc]
        exact hTq.2.2.roots_nodup
      exact ⟨hrr.1, hrr.2, hs⟩
  have hmap : ∀ α β : ℝ,
      (C α * f + C β * g ≠ 0 ∧ (C α * f + C β * g).Splits) →
        T (C α * f + C β * g) = 0 ∨
          (T (C α * f + C β * g)).Splits := by
    intro α β hp
    exact Or.inr (hmapSimple α β hp).2.1
  have hallT : AllComboRealRooted (T f) (T g) :=
    allComboRealRooted_map_of_pencil hall hmap
  have hTf := hT₁ hf
  have hTg := hT₁ hg
  have hdegT : (T f).natDegree + 1 = (T g).natDegree := by
    rw [hTf.2, hTg.2, hdeg]
  have hor : StrictInterl (T f) (T g) ∨ StrictInterl (T g) (T f) :=
    strictInterl_of_allComboRealRooted hTf.1.1 hTf.1.2.1 hTg.1.1 hTg.1.2.1
      hallT (Or.inl hdegT)
  have hstrictT : StrictInterl (T f) (T g) :=
    StrictInterl.forward_of_orientation_of_succDegree hdegT.symm hor
  have hnoT : ∀ r, ¬ ((T f).IsRoot r ∧ (T g).IsRoot r) := by
    intro s hs
    have hTf_der : (T f).derivative.eval s ≠ 0 :=
      hTf.1.2.2.1.eval_derivative_ne_zero hs.1
    let t : ℝ := -(T g).derivative.eval s / (T f).derivative.eval s
    have hdouble : (T g + C t * T f).derivative.eval s = 0 := by
      simp only [Polynomial.derivative_add, Polynomial.eval_add,
        Polynomial.derivative_C_mul, eval_mul, eval_C]
      dsimp [t]
      field_simp [hTf_der]
      ring
    have hsource_ne : C t * f + g ≠ 0 := by
      intro hzero
      have hlt : (C t * f).natDegree < g.natDegree := by
        exact (natDegree_C_mul_le t f).trans_lt (by lia)
      have hdegsource := Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
      rw [hzero] at hdegsource
      have hgdeg : 0 < g.natDegree := by lia
      have hdegsource' : (0 : ℕ) = g.natDegree := by
        simpa using hdegsource
      lia
    have hsource_splits : (C t * f + g).Splits := by
      simpa using hall t 1
    have hsimple_source := hmapSimple t 1
      ⟨by simpa using hsource_ne, by simpa using hsource_splits⟩
    have himage : T (C t * f + g) = C t * T f + T g := by
      rw [T.map_add, map_C_mul]
    have hsimple_image : HasSimpleRoots (C t * T f + T g) := by
      rw [← himage]
      simpa using hsimple_source.2.2
    have hroot : (T g + C t * T f).IsRoot s := by
      have hTf_root : (T f).eval s = 0 := hs.1
      have hTg_root : (T g).eval s = 0 := by
        simpa [Polynomial.IsRoot.def] using hs.2
      rw [Polynomial.IsRoot.def]
      simp [hTf_root, hTg_root]
    have hsimple_image' : HasSimpleRoots (T g + C t * T f) := by
      simpa [add_comm] using hsimple_image
    exact hsimple_image'.eval_derivative_ne_zero hroot hdouble
  exact ⟨hstrictT, hnoT⟩

/-- The strict-interlacing and root-disjointness conclusions iterate along an
operator recurrence, starting from two negative-simple consecutive terms. -/
theorem strictInterl_iterate_of_negative_simple
    {T : ℝ[X] →ₗ[ℝ] ℝ[X]} {P : ℕ → ℝ[X]}
    (hrec : ∀ n, P (n + 1) = T (P n))
    (hP0 : IsNegativeSimple (P 0))
    (hP1 : IsNegativeSimple (P 1))
    (hbase : StrictInterl (P 0) (P 1))
    (hbase_cop : ∀ r, ¬ ((P 0).IsRoot r ∧ (P 1).IsRoot r))
    (hT₁ : MapsNegativeSimpleBySucc T)
    (hT₂ : MapsAffineNegativeSimple T) :
    ∀ n, StrictInterl (P n) (P (n + 1)) ∧
      ∀ r, ¬ ((P n).IsRoot r ∧ (P (n + 1)).IsRoot r) := by
  have hmain : ∀ n,
      IsNegativeSimple (P n) ∧ IsNegativeSimple (P (n + 1)) ∧
        StrictInterl (P n) (P (n + 1)) ∧
          ∀ r, ¬ ((P n).IsRoot r ∧ (P (n + 1)).IsRoot r) := by
    intro n
    induction n with
    | zero =>
        exact ⟨hP0, hP1, hbase, hbase_cop⟩
    | succ n ih =>
        have hnext := hT₁ ih.1
        have hPn1 : IsNegativeSimple (P (n + 1)) := by
          simpa [hrec n] using hnext.1
        have hdeg : (P (n + 1)).natDegree = (P n).natDegree + 1 := by
          simpa [hrec n] using hnext.2
        have hstep := strictInterl_map_of_negative_simple_pencil
          ih.2.2.1 hdeg ih.2.2.2 ih.1 hPn1 hT₁ hT₂
        have hstep' :
            StrictInterl (P (n + 1)) (P (n + 1 + 1)) ∧
              ∀ r, ¬ ((P (n + 1)).IsRoot r ∧ (P (n + 1 + 1)).IsRoot r) := by
          simpa [hrec n, hrec (n + 1)] using hstep
        have hPn2 : IsNegativeSimple (P (n + 1 + 1)) := by
          simpa [hrec (n + 1)] using (hT₁ hPn1).1
        exact ⟨hPn1, hPn2, hstep'.1, hstep'.2⟩
  intro n
  exact (hmain n).2.2

/-- Multiplication by `X + 1` does not satisfy H1: it creates a double root. -/
example :
    ¬ MapsNegativeSimpleBySucc (LinearMap.mulLeft ℝ (X + C (1 : ℝ))) := by
  intro hT
  have hq : IsNegativeSimple (X + C (1 : ℝ)) := by
    refine ⟨X_add_C_ne_zero 1, ?_, ?_, hasPosLeadingCoeff_X_add_C 1, ?_⟩
    · simpa [sub_eq_add_neg] using (isRealRooted_X_sub_C (-1 : ℝ)).2
    · exact hasSimpleRoots_of_natDegree_le_one (X_add_C_ne_zero 1) (by simp)
    · intro r hr
      rw [roots_X_add_C] at hr
      have hroot : r = -1 := by simpa using hr
      rw [hroot]
      norm_num
  have hsimple := (hT hq).1.2.2.1
  change HasSimpleRoots ((X + C 1) * (X + C 1)) at hsimple
  have hroot : ((X + C 1) * (X + C 1) : ℝ[X]).IsRoot (-1) := by
    simp [Polynomial.IsRoot.def]
  have hder : ((X + C 1) * (X + C 1) : ℝ[X]).derivative.eval (-1) = 0 := by
    simp [Polynomial.derivative_mul]
  exact hsimple.eval_derivative_ne_zero hroot hder

end RealRooted
