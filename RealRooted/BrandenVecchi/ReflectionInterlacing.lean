import RealRooted.InterlacingSequenceBasic
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.PFPolynomial

/-!
# Reflection-interlacing sequences

This file formalizes the sequence notion from Bränden--Vecchi, Definition 4.9,
in a zero-aware form. It also supplies the elementary scaling, deletion, and
adjacent-sum closure operations from Lemma 4.10.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- `g` is a nonnegative scalar multiple of `f`. -/
def IsNonnegScalarMultiple (f g : ℝ[X]) : Prop :=
  ∃ a : ℝ, 0 ≤ a ∧ g = C a * f

namespace IsNonnegScalarMultiple

theorem C_mul (f : ℝ[X]) {a : ℝ} (ha : 0 ≤ a) :
    IsNonnegScalarMultiple f (C a * f) :=
  ⟨a, ha, rfl⟩

theorem reflect {f g : ℝ[X]} (h : IsNonnegScalarMultiple f g) (n : ℕ) :
    IsNonnegScalarMultiple (f.reflect n) (g.reflect n) := by
  rcases h with ⟨a, ha, rfl⟩
  exact ⟨a, ha, reflect_C_mul f a n⟩

end IsNonnegScalarMultiple

private theorem prec0_C_mul_left_of_nonneg_local {f g : ℝ[X]}
    (h : Prec0 f g) {a : ℝ} (ha : 0 ≤ a) :
    Prec0 (C a * f) g := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp [prec0_zero_left]
  rcases h with hf | hg | hfg
  · simp [hf, prec0_zero_left]
  · simpa [hg] using prec0_zero_right (C a * f)
  · exact (prec_C_mul_left hfg ha_pos.ne').toPrec0

/-- Pointwise replacement by arbitrary nonnegative scalar multiples preserves
a zero-aware nonnegative real-rooted interlacing sequence. -/
theorem IsInterlacingSeq0NonnegRealRooted.nonnegScalarMultiples
    {fs gs : List ℝ[X]} (hfs : IsInterlacingSeq0NonnegRealRooted fs)
    (hscale : List.Forall₂ IsNonnegScalarMultiple fs gs) :
    IsInterlacingSeq0NonnegRealRooted gs := by
  have hlen : fs.length = gs.length := hscale.length_eq
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_iff_get]
    intro i j hij
    have hi : i.val < fs.length := by simp [hlen]
    have hj : j.val < fs.length := by simp [hlen]
    rcases hscale.get hi i.isLt with ⟨a, ha, hia⟩
    rcases hscale.get hj j.isLt with ⟨b, hb, hjb⟩
    have hbase := hfs.interlacingSeq0.prec0
      (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij
    rw [hia, hjb]
    exact prec0_C_mul_right_of_nonneg
      (prec0_C_mul_left_of_nonneg_local hbase ha) hb
  · intro g hg
    rcases List.get_of_mem hg with ⟨i, rfl⟩
    have hi : i.val < fs.length := by simp [hlen]
    rcases hscale.get hi i.isLt with ⟨a, ha, hia⟩
    rw [hia]
    exact nonnegCoeffs_C_mul ha
      (hfs.nonnegCoeffs (fs.get ⟨i, hi⟩) (List.get_mem _ _))
  · intro g hg hg_ne
    rcases List.get_of_mem hg with ⟨i, rfl⟩
    have hi : i.val < fs.length := by simp [hlen]
    rcases hscale.get hi i.isLt with ⟨a, _, hia⟩
    rw [hia] at hg_ne ⊢
    have hnonzero : a ≠ 0 ∧ fs.get ⟨i, hi⟩ ≠ 0 := by simpa using hg_ne
    exact ⟨hg_ne, (hfs.splits (List.get_mem _ _) hnonzero.2).C_mul a⟩

private theorem prec0_self_of_realRootedOrZero {f : ℝ[X]}
    (hf : f ≠ 0 → f.Splits) : Prec0 f f := by
  by_cases hf_zero : f = 0
  · exact Or.inl hf_zero
  · exact (prec_refl hf_zero (hf hf_zero)).toPrec0

private theorem splits_add_of_prec0_of_nonneg {f g : ℝ[X]}
    (hfg : Prec0 f g) (hf : HasNonnegCoeffs f)
    (hg : HasNonnegCoeffs g) (hfr : f ≠ 0 → f.Splits)
    (hgr : g ≠ 0 → g.Splits) (hsum : f + g ≠ 0) :
    (f + g).Splits := by
  rcases hfg with hf_zero | hg_zero | hprec
  · simpa [hf_zero] using
      (show g.Splits from by
        have hg_ne : g ≠ 0 := by simpa [hf_zero] using hsum
        exact hgr hg_ne)
  · simpa [hg_zero] using
      (show f.Splits from by
        have hf_ne : f ≠ 0 := by simpa [hg_zero] using hsum
        exact hfr hf_ne)
  · exact (PosComboRealRooted.isRealRooted_add
      (PosComboRealRooted.of_prec hprec
        (hf.pos_leadingCoeff hprec.1.1)
        (hg.pos_leadingCoeff hprec.2.1.1))).2

private theorem pairwise_insertAdjacentAdd_of_nonneg
    {f g : ℝ[X]} {right : List ℝ[X]} :
    ∀ left : List ℝ[X],
      (left ++ f :: g :: right).Pairwise Prec0 →
      (∀ p ∈ left ++ f :: g :: right, HasNonnegCoeffs p) →
      (∀ p ∈ left ++ f :: g :: right, p ≠ 0 → p.Splits) →
      (left ++ f :: (f + g) :: g :: right).Pairwise Prec0
  | [], hpair, hnonneg, hreal => by
      have hfnn : HasNonnegCoeffs f := hnonneg f (by simp)
      have hgnn : HasNonnegCoeffs g := hnonneg g (by simp)
      have hff : Prec0 f f :=
        prec0_self_of_realRootedOrZero fun hf => hreal f (by simp) hf
      have hgg : Prec0 g g :=
        prec0_self_of_realRootedOrZero fun hg => hreal g (by simp) hg
      rw [List.nil_append, List.pairwise_cons] at hpair ⊢
      rcases hpair with ⟨hf_tail, hg_pair⟩
      rw [List.pairwise_cons] at hg_pair
      rcases hg_pair with ⟨hg_right, hright⟩
      have hfg : Prec0 f g := hf_tail g (by simp)
      refine ⟨?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact prec0_add_right_of_common_left_of_nonneg hff hfg hfnn hgnn
        · exact hf_tail p (by simpa using hp)
      · rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_cons.mpr ⟨hg_right, hright⟩⟩
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact prec0_add_left_of_common_right_of_nonneg hfg hgg hfnn hgnn
        · exact prec0_add_left_of_common_right_of_nonneg
            (hf_tail p (by simp [hp])) (hg_right p hp) hfnn hgnn
  | a :: left, hpair, hnonneg, hreal => by
      rw [List.cons_append, List.pairwise_cons] at hpair ⊢
      refine ⟨?_, pairwise_insertAdjacentAdd_of_nonneg left hpair.2
        (fun p hp => hnonneg p (by simp [hp]))
        (fun p hp => hreal p (by simp [hp]))⟩
      intro p hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp_left | hp_f | hp_sum | hp_g | hp_right
      · exact hpair.1 p (by simp [hp_left])
      · subst p
        exact hpair.1 f (by simp)
      · subst p
        exact prec0_add_right_of_common_left_of_nonneg
          (hpair.1 f (by simp)) (hpair.1 g (by simp))
          (hnonneg f (by simp)) (hnonneg g (by simp))
      · subst p
        exact hpair.1 g (by simp)
      · exact hpair.1 p (by simp [hp_right])

/-- Inserting the sum of two adjacent members preserves a zero-aware
nonnegative real-rooted interlacing sequence. -/
theorem IsInterlacingSeq0NonnegRealRooted.insertAdjacentAdd
    {left right : List ℝ[X]} {f g : ℝ[X]}
    (h : IsInterlacingSeq0NonnegRealRooted (left ++ f :: g :: right)) :
    IsInterlacingSeq0NonnegRealRooted
      (left ++ f :: (f + g) :: g :: right) := by
  have hpair : (left ++ f :: g :: right).Pairwise Prec0 :=
    isInterlacingSeq0_iff_pairwise.mp h.interlacingSeq0
  have hfg : Prec0 f g :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hpair).2.1).1 g (by simp)
  have hfnn : HasNonnegCoeffs f := h.nonnegCoeffs f (by simp)
  have hgnn : HasNonnegCoeffs g := h.nonnegCoeffs g (by simp)
  refine ⟨⟨isInterlacingSeq0_iff_pairwise.mpr
    (pairwise_insertAdjacentAdd_of_nonneg left hpair h.nonnegCoeffs
      fun p hp hp_ne => (h.realRooted p hp hp_ne).2),
      ?_⟩, ?_⟩
  · intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp_left | hp_f | hp_sum | hp_g | hp_right
    · exact h.nonnegCoeffs p (by simp [hp_left])
    · subst p
      exact hfnn
    · subst p
      exact hfnn.add hgnn
    · subst p
      exact hgnn
    · exact h.nonnegCoeffs p (by simp [hp_right])
  · intro p hp hp_ne
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp_left | hp_f | hp_sum | hp_g | hp_right
    · exact h.realRooted p (by simp [hp_left]) hp_ne
    · subst p
      exact h.realRooted f (by simp) hp_ne
    · subst p
      exact ⟨hp_ne, splits_add_of_prec0_of_nonneg hfg hfnn hgnn
        (fun hf_ne => h.splits (by simp) hf_ne)
        (fun hg_ne => h.splits (by simp) hg_ne) hp_ne⟩
    · subst p
      exact h.realRooted g (by simp) hp_ne
    · exact h.realRooted p (by simp [hp_right]) hp_ne

namespace BrandenVecchi

/-- The list obtained by adjoining the reflected members in reverse order. -/
def reflectionClosure (n : ℕ) (fs : List ℝ[X]) : List ℝ[X] :=
  fs ++ (fs.map fun f => f.reflect n).reverse

/-- A zero-aware `Iₙ`-interlacing sequence in the sense of
Bränden--Vecchi, Definition 4.9. Every original member has degree at most `n`,
and adjoining the reversed reflected family gives a nonnegative real-rooted
interlacing sequence. -/
def IsReflectionInterlacingSeq (n : ℕ) (fs : List ℝ[X]) : Prop :=
  (∀ f ∈ fs, f.natDegree ≤ n) ∧
    IsInterlacingSeq0NonnegRealRooted (reflectionClosure n fs)

namespace IsReflectionInterlacingSeq

theorem natDegree_le {n : ℕ} {fs : List ℝ[X]}
    (hfs : IsReflectionInterlacingSeq n fs) {f : ℝ[X]} (hf : f ∈ fs) :
    f.natDegree ≤ n :=
  hfs.1 f hf

theorem closedSequence {n : ℕ} {fs : List ℝ[X]}
    (hfs : IsReflectionInterlacingSeq n fs) :
    IsInterlacingSeq0NonnegRealRooted (reflectionClosure n fs) :=
  hfs.2

theorem nonnegScalarMultiples {n : ℕ} {fs gs : List ℝ[X]}
    (hfs : IsReflectionInterlacingSeq n fs)
    (hscale : List.Forall₂ IsNonnegScalarMultiple fs gs) :
    IsReflectionInterlacingSeq n gs := by
  have hlen : fs.length = gs.length := hscale.length_eq
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases List.get_of_mem hg with ⟨i, rfl⟩
    have hi : i.val < fs.length := by simp [hlen]
    rcases hscale.get hi i.isLt with ⟨a, _, hia⟩
    rw [hia]
    exact (natDegree_C_mul_le a _).trans
      (hfs.1 _ (List.get_mem _ _))
  · apply hfs.2.nonnegScalarMultiples
    apply List.rel_append hscale
    apply List.rel_reverse
    exact List.rel_map (fun _ _ h => h.reflect n) hscale

theorem sublist {n : ℕ} {fs gs : List ℝ[X]}
    (hfs : IsReflectionInterlacingSeq n fs) (hgs : gs.Sublist fs) :
    IsReflectionInterlacingSeq n gs := by
  refine ⟨fun g hg => hfs.1 g (hgs.subset hg), ?_⟩
  apply hfs.2.sublist
  exact hgs.append (hgs.map fun f => f.reflect n).reverse

/-- Inserting the sum of two adjacent members preserves reflection
interlacing. The reflected half receives the corresponding adjacent sum in
the reversed position. -/
theorem insertAdjacentAdd {n : ℕ} {left right : List ℝ[X]} {f g : ℝ[X]}
    (h : IsReflectionInterlacingSeq n (left ++ f :: g :: right)) :
    IsReflectionInterlacingSeq n
      (left ++ f :: (f + g) :: g :: right) := by
  let old : List ℝ[X] := left ++ f :: g :: right
  let new : List ℝ[X] := left ++ f :: (f + g) :: g :: right
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp_left | hp_f | hp_sum | hp_g | hp_right
    · exact h.1 p (by simp [hp_left])
    · subst p
      exact h.1 f (by simp)
    · subst p
      exact (natDegree_add_le f g).trans
        (max_le (h.1 f (by simp)) (h.1 g (by simp)))
    · subst p
      exact h.1 g (by simp)
    · exact h.1 p (by simp [hp_right])
  · have hfirst :
        IsInterlacingSeq0NonnegRealRooted
          (new ++ (right.map fun p => p.reflect n).reverse ++
            g.reflect n :: f.reflect n ::
              (left.map fun p => p.reflect n).reverse) := by
      have hold :
          IsInterlacingSeq0NonnegRealRooted
            (left ++ f :: g ::
              (right ++ (old.map fun p => p.reflect n).reverse)) := by
        simpa [old, reflectionClosure, List.append_assoc] using h.2
      have hadd := hold.insertAdjacentAdd
        (left := left) (f := f) (g := g)
        (right := right ++ (old.map fun p => p.reflect n).reverse)
      simpa [old, new, reflectionClosure, List.reverse_append,
        List.append_assoc] using hadd
    have hsecond := hfirst.insertAdjacentAdd
      (left := new ++ (right.map fun p => p.reflect n).reverse)
      (f := g.reflect n) (g := f.reflect n)
      (right := (left.map fun p => p.reflect n).reverse)
    simpa [new, reflectionClosure, List.reverse_append, reflect_add,
      List.append_assoc, add_comm] using hsecond

end IsReflectionInterlacingSeq

end BrandenVecchi

end

end RealRooted
