module

public import RealRooted.MultiplierSequence.Laguerre
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.OperatorPreservesInterlacing

/-!
# Directed proper position for diagonal multiplier operators

A multiplier sequence preserves real-rootedness of every real pencil `a f + b g`, so it preserves
interlacing up to orientation (finite Pólya--Schur).  Comparing the sums of the roots (Vieta)
fixes the orientation: positive multiplier sequences preserve directed proper position.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem natDegree_diagonalOperator_eq_of_natDegree_eq
    {gamma : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hpdeg : p.natDegree = d) (hp0 : p ≠ 0) (hgamma : gamma d ≠ 0) :
    (diagonalOperator gamma p).natDegree = d := by
  have hdeg : (diagonalOperator gamma p).natDegree = p.natDegree := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_diagonalOperator_le gamma p)
    rw [coeff_diagonalOperator]
    exact mul_ne_zero (by simpa [hpdeg] using hgamma)
      (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  exact hdeg.trans hpdeg

private theorem diagonalOperator_roots_sum_scale
    {gamma : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hd : 0 < d) (hpdeg : p.natDegree = d) (hp0 : p ≠ 0)
    (hps : p.Splits) (hgamma_top : gamma d ≠ 0)
    (hout : (diagonalOperator gamma p).Splits) :
    (diagonalOperator gamma p).roots.sum =
      (gamma (d - 1) / gamma d) * p.roots.sum := by
  have houtdeg : (diagonalOperator gamma p).natDegree = d :=
    natDegree_diagonalOperator_eq_of_natDegree_eq hpdeg hp0 hgamma_top
  have hnext : (diagonalOperator gamma p).nextCoeff =
      gamma (d - 1) * p.nextCoeff := by
    rw [Polynomial.nextCoeff, houtdeg, coeff_diagonalOperator,
      Polynomial.nextCoeff, hpdeg]
    simp [hd.ne']
  have hleading : (diagonalOperator gamma p).leadingCoeff =
      gamma d * p.leadingCoeff := by
    rw [Polynomial.leadingCoeff, houtdeg, coeff_diagonalOperator,
      ← hpdeg, Polynomial.leadingCoeff]
  have hout_vieta := hout.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (by rw [hleading]
        exact mul_ne_zero hgamma_top (Polynomial.leadingCoeff_ne_zero.mpr hp0))
  have hp_vieta := hps.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  rw [hout_vieta, hnext, hleading, hp_vieta]
  field_simp [hgamma_top, Polynomial.leadingCoeff_ne_zero.mpr hp0]

/-- A finite multiplier sequence preserves the directed `StrictInterl` relation.

The top multipliers preserve the two exact degrees.  In the equal-degree case,
the displayed adjacent-sign hypothesis preserves the root-sum order; in the
successor-degree case exact degree preservation determines the orientation.
-/
theorem IsFiniteMultiplierSequence.strictInterl_diagonalOperator
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence N gamma)
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N)
    (hgamma_f : gamma f.natDegree ≠ 0)
    (hgamma_g : gamma g.natDegree ≠ 0)
    (hsign : f.natDegree = g.natDegree → 0 < f.natDegree →
      0 ≤ gamma (f.natDegree - 1) * gamma f.natDegree) :
    StrictInterl (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  have hf0 : f ≠ 0 := hfg.1.1
  have hg0 : g ≠ 0 := hfg.2.1.1
  have hfs : f.Splits := hfg.1.2
  have hgs : g.Splits := hfg.2.1.2
  have hfd : (diagonalOperator gamma f).natDegree = f.natDegree :=
    natDegree_diagonalOperator_eq_of_natDegree_eq rfl hf0 hgamma_f
  have hgd : (diagonalOperator gamma g).natDegree = g.natDegree :=
    natDegree_diagonalOperator_eq_of_natDegree_eq rfl hg0 hgamma_g
  have hTf0 : diagonalOperator gamma f ≠ 0 := by
    intro hzero
    have hcoeff : gamma f.natDegree * f.coeff f.natDegree = 0 := by
      simpa [coeff_diagonalOperator] using
        congrArg (fun p : ℝ[X] => p.coeff f.natDegree) hzero
    have hgamma_zero : gamma f.natDegree = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_right (by
        rw [coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hf0)
    exact hgamma_f hgamma_zero
  have hTg0 : diagonalOperator gamma g ≠ 0 := by
    intro hzero
    have hcoeff : gamma g.natDegree * g.coeff g.natDegree = 0 := by
      simpa [coeff_diagonalOperator] using
        congrArg (fun p : ℝ[X] => p.coeff g.natDegree) hzero
    have hgamma_zero : gamma g.natDegree = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_right (by
        rw [coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hg0)
    exact hgamma_g hgamma_zero
  have hTf_splits : (diagonalOperator gamma f).Splits := by
    rcases hgamma hfdeg hfs with hzero | hsplit
    · exact (hTf0 hzero).elim
    · exact hsplit
  have hTg_splits : (diagonalOperator gamma g).Splits := by
    rcases hgamma hgdeg hgs with hzero | hsplit
    · exact (hTg0 hzero).elim
    · exact hsplit
  have hall : AllComboRealRooted (diagonalOperator gamma f)
      (diagonalOperator gamma g) := by
    intro a b
    have hdegree : (C a * f + C b * g).natDegree ≤ N := by
      exact (Polynomial.natDegree_add_le _ _).trans <|
        max_le ((Polynomial.natDegree_C_mul_le a f).trans hfdeg)
          ((Polynomial.natDegree_C_mul_le b g).trans hgdeg)
    have hcomb := allComboRealRooted_of_strictInterl hfg a b
    have hmap : diagonalOperator gamma (C a * f + C b * g) =
        C a * diagonalOperator gamma f + C b * diagonalOperator gamma g := by
      rw [diagonalOperator_add, diagonalOperator_C_mul,
        diagonalOperator_C_mul]
    rcases hgamma hdegree hcomb with hzero | hsplit_out
    · have houtzero : C a * diagonalOperator gamma f +
          C b * diagonalOperator gamma g = 0 := by
        rw [← hmap, hzero]
      simp [houtzero]
    · rw [← hmap]
      exact hsplit_out
  rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
  · have hdeg_out : (diagonalOperator gamma f).natDegree =
        (diagonalOperator gamma g).natDegree := by rw [hfd, hgd, hsame]
    have hor := strictInterl_of_allComboRealRooted hTf0 hTf_splits hTg0
      hTg_splits hall (Or.inr hdeg_out)
    rcases hor with hforward | hreverse
    · exact hforward
    · by_cases hd : f.natDegree = 0
      · have hroots_f : (diagonalOperator gamma f).roots = 0 := by
          apply Multiset.card_eq_zero.mp
          rw [Polynomial.splits_iff_card_roots.mp hTf_splits, hfd, hd]
        have hroots_g : (diagonalOperator gamma g).roots = 0 := by
          apply Multiset.card_eq_zero.mp
          rw [Polynomial.splits_iff_card_roots.mp hTg_splits, hgd, hsame, hd]
        apply hreverse.of_reverse_of_roots_sum_le hdeg_out
        rw [hroots_f, hroots_g]
      · have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hd
        have hsign' := hsign hsame.symm hpos
        have hratio : 0 ≤ gamma (f.natDegree - 1) / gamma f.natDegree := by
          rcases lt_or_gt_of_ne hgamma_f with hneg | hpos_gamma
          · rw [div_nonneg_iff]
            exact Or.inr ⟨by nlinarith [hsign'], le_of_lt hneg⟩
          · exact div_nonneg (by nlinarith [hsign']) (le_of_lt hpos_gamma)
        have hsum_input : f.roots.sum ≤ g.roots.sum :=
          hfg.roots_sum_le_of_sameDegree hsame.symm
        have hsum_f := diagonalOperator_roots_sum_scale hpos rfl hf0 hfs
          hgamma_f hTf_splits
        have hsum_g := diagonalOperator_roots_sum_scale (d := g.natDegree)
          (by simpa [hsame] using hpos) rfl hg0 hgs
          hgamma_g hTg_splits
        have hsum_g' : (diagonalOperator gamma g).roots.sum =
            (gamma (f.natDegree - 1) / gamma f.natDegree) * g.roots.sum := by
          simpa [hsame] using hsum_g
        apply hreverse.of_reverse_of_roots_sum_le hdeg_out
        rw [hsum_f, hsum_g']
        exact mul_le_mul_of_nonneg_left hsum_input hratio
  · have hdeg_out : (diagonalOperator gamma f).natDegree + 1 =
        (diagonalOperator gamma g).natDegree := by rw [hfd, hgd, hsucc]
    have hor := strictInterl_of_allComboRealRooted hTf0 hTf_splits hTg0
      hTg_splits hall (Or.inl hdeg_out)
    exact StrictInterl.forward_of_orientation_of_succDegree hdeg_out.symm hor

/-- A strictly positive infinite multiplier sequence preserves directed proper
position without a degree bound in the statement. -/
theorem IsMultiplierSequence.strictInterl_diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {f g : ℝ[X]} (hfg : StrictInterl f g) :
    StrictInterl (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  let N := max f.natDegree g.natDegree
  apply IsFiniteMultiplierSequence.strictInterl_diagonalOperator
    (hgamma.finite N) hfg (by exact le_max_left _ _) (by exact le_max_right _ _)
    (hpos _).ne' (hpos _).ne'
  intro hsame hd
  exact mul_nonneg (le_of_lt (hpos (f.natDegree - 1)))
    (le_of_lt (hpos f.natDegree))

/-- A common right interleaver is transported by a strictly positive multiplier
sequence. -/
theorem HasCommonInterleaver.diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs) :
    HasCommonInterleaver (fs.map (diagonalOperator gamma)) := by
  rcases hcommon with ⟨h, hh⟩
  refine ⟨diagonalOperator gamma h, ?_⟩
  intro f hf
  rcases List.mem_map.mp hf with ⟨p, hp, rfl⟩
  exact hgamma.strictInterl_diagonalOperator_of_pos hpos (hh p hp)

/-- A common left interleaver is transported by a strictly positive multiplier
sequence. -/
theorem HasCommonLeftInterleaver.diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaver (fs.map (diagonalOperator gamma)) := by
  rcases hcommon with ⟨h, hh⟩
  refine ⟨diagonalOperator gamma h, ?_⟩
  intro f hf
  rcases List.mem_map.mp hf with ⟨p, hp, rfl⟩
  exact hgamma.strictInterl_diagonalOperator_of_pos hpos (hh p hp)

/-- The shifted Euler operator preserves directed proper position when its
shift is strictly positive. -/
theorem eulerShift_strictInterl_of_pos
    {r : ℝ} (hr : 0 < r) {f g : ℝ[X]} (hfg : StrictInterl f g) :
    StrictInterl (eulerShift r f) (eulerShift r g) := by
  have hpf := isPFMultiplierSequence_natCast_add hr.le
  have hmult : IsMultiplierSequence (fun k => (k : ℝ) + r) :=
    (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
  have h := hmult.strictInterl_diagonalOperator_of_pos
    (fun k => by positivity) hfg
  simpa only [diagonalOperator_natCast_add_eq_eulerShift] using h

/-- The unshifted Euler operator preserves directed proper position when both
outputs are nonzero. -/
theorem eulerShift_zero_strictInterl_of_nonzero
    {f g : ℝ[X]} (hf : eulerShift 0 f ≠ 0) (hg : eulerShift 0 g ≠ 0)
    (hfg : StrictInterl f g) : StrictInterl (eulerShift 0 f) (eulerShift 0 g) := by
  have hmap_f : diagonalOperator (fun k => (k : ℝ)) f = eulerShift 0 f := by
    have heq : (fun k : ℕ => (k : ℝ) + 0) = (fun k : ℕ => (k : ℝ)) := by
      funext k
      simp
    rw [← heq]
    exact diagonalOperator_natCast_add_eq_eulerShift 0 f
  have hmap_g : diagonalOperator (fun k => (k : ℝ)) g = eulerShift 0 g := by
    have heq : (fun k : ℕ => (k : ℝ) + 0) = (fun k : ℕ => (k : ℝ)) := by
      funext k
      simp
    rw [← heq]
    exact diagonalOperator_natCast_add_eq_eulerShift 0 g
  have hfdeg : 0 < f.natDegree := by
    by_contra hnot
    have hdeg : f.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
    apply hf
    rw [← hmap_f]
    rw [← eulerOperator_eq_diagonalOperator_natCast,
      Polynomial.derivative_eq_zero.mpr hdeg]
    simp
  have hgdeg : 0 < g.natDegree := by
    by_contra hnot
    have hdeg : g.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
    apply hg
    rw [← hmap_g]
    rw [← eulerOperator_eq_diagonalOperator_natCast,
      Polynomial.derivative_eq_zero.mpr hdeg]
    simp
  let N := max f.natDegree g.natDegree
  have h := IsFiniteMultiplierSequence.strictInterl_diagonalOperator
    (isMultiplierSequence_natCast.finite N) hfg (le_max_left _ _) (le_max_right _ _)
    (by exact_mod_cast hfdeg.ne') (by exact_mod_cast hgdeg.ne')
    (fun hsame _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [hmap_f, hmap_g] at h
  exact h

/-- The shifted Euler operator preserves the zero-aware directed interlacing
relation for every nonnegative shift. -/
theorem eulerShift_interl_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) {f g : ℝ[X]} (hfg : StrictInterl f g) :
    Interl (eulerShift r f) (eulerShift r g) := by
  by_cases hrpos : 0 < r
  · exact (eulerShift_strictInterl_of_pos hrpos hfg).toInterl
  · have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    subst r
    by_cases hf : eulerShift 0 f = 0
    · rw [hf]
      exact interl_zero_left _
    by_cases hg : eulerShift 0 g = 0
    · rw [hg]
      exact interl_zero_right _
    · exact (eulerShift_zero_strictInterl_of_nonzero hf hg hfg).toInterl

/-- The alternating multiplier sequence reverses the directed order on the
linear pair `X + 2`, `X + 1`. -/
theorem alternating_sign_linear_not_strictInterl :
    ¬ StrictInterl
      (diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C 2))
      (diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C 1)) := by
  have hleft : diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C 2) =
      -X + C 2 := by
    calc
      _ = ((X + C 2 : ℝ[X]).comp (-X)) := by
        simpa only [mul_one, diagonalOperator_one_sequence] using
          diagonalOperator_alternating (fun _ => (1 : ℝ)) (X + C 2)
      _ = -X + C 2 := by
        rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hright : diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C 1) =
      -X + C 1 := by
    calc
      _ = ((X + C 1 : ℝ[X]).comp (-X)) := by
        simpa only [mul_one, diagonalOperator_one_sequence] using
          diagonalOperator_alternating (fun _ => (1 : ℝ)) (X + C 1)
      _ = -X + C 1 := by
        rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  rw [hleft, hright]
  intro h
  have hsum := h.roots_sum_le_of_sameDegree (by simp)
  have hleft := h.1.2.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr h.1.1)
  have hright := h.2.1.2.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr h.2.1.1)
  have hleft_sum : (-X + C 2 : ℝ[X]).roots.sum = 2 := by
    calc
      _ = -(-X + C 2 : ℝ[X]).nextCoeff /
          (-X + C 2 : ℝ[X]).leadingCoeff := hleft
      _ = 2 := by norm_num [Polynomial.nextCoeff, Polynomial.leadingCoeff]
  have hright_sum : (-X + C 1 : ℝ[X]).roots.sum = 1 := by
    calc
      _ = -(-X + C 1 : ℝ[X]).nextCoeff /
          (-X + C 1 : ℝ[X]).leadingCoeff := hright
      _ = 1 := by
        norm_num [Polynomial.nextCoeff, Polynomial.leadingCoeff, coeff_add,
          coeff_neg, coeff_X, coeff_C, coeff_one]
  rw [hleft_sum, hright_sum] at hsum
  norm_num at hsum

end RealRooted
