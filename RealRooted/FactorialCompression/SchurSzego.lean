import RealRooted.FactorialCompression.RootGeometry
import RealRooted.Hadamard.Grace
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.WagnerRightSum.Sign
import RealRooted.CoefficientShape
import RealRooted.CriticalValueContinuation
import RealRooted.IteratedDerivativeShift
import RealRooted.ObreschkoffConverse
import RealRooted.Wronskian.WeakForward

/-!
# Schur--Szegő lemmas used by factorial compression

Reusable consequences of the canonical `schurSzegoComp` operator for a
positive-leading multiplier polynomial with strictly negative roots.  No
second finite-multiplier definition is introduced here.
-/

open Polynomial RealRooted Filter

noncomputable section

namespace RealRooted.FactorialCompression

theorem isPFPolynomial_of_roots_neg {p : ℝ[X]}
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0) :
    IsPFPolynomial p := by
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hpsplit).mpr
      ⟨hppos, fun r hr => (hproots r hr).le⟩).1
  · exact hpsplit

/-- Only the real-rootedness component of Lemma 2.2, allowing zero output.
Repeated roots of the multiplier polynomial p are allowed. -/
theorem schurSzegoComp_eq_zero_or_splits_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree ≤ N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hfsplit : f.Splits) :
    schurSzegoComp N p f = 0 ∨ (schurSzegoComp N p f).Splits := by
  exact schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
    (isPFPolynomial_of_roots_neg hpsplit hppos hproots)
    hpdegree hfdegree hfsplit

theorem schurSzegoComp_splits_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree ≤ N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hfsplit : f.Splits) :
    (schurSzegoComp N p f).Splits := by
  rcases schurSzegoComp_eq_zero_or_splits_of_roots_neg hpdegree hpsplit hppos hproots
      hfdegree hfsplit with hz | hs
  · rw [hz]
    simp
  · exact hs

theorem coeff_zero_pos_of_roots_neg {p : ℝ[X]}
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0) :
    0 < p.coeff 0 := by
  rw [coeff_zero_eq_eval_zero]
  exact eval_pos_of_all_roots_lt hppos.ne_zero hpsplit hppos hproots

/-- Nonzeroness for the negative-root kernels used below.
This is not a claim of simple roots or strict interlacing. -/
theorem schurSzegoComp_coeff_zero_pos {N : ℕ} {p f : ℝ[X]}
    (hpzero : 0 < p.coeff 0) (hfzero : 0 < f.coeff 0) :
    0 < (schurSzegoComp N p f).coeff 0 := by
  rw [coeff_schurSzegoComp]
  simpa using mul_pos hpzero hfzero

theorem coeff_pos_of_roots_neg {p : ℝ[X]}
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0) {k : ℕ} (hk : k ≤ p.natDegree) :
    0 < p.coeff k := by
  have hppf := isPFPolynomial_of_roots_neg hpsplit hppos hproots
  have hpzero := coeff_zero_pos_of_roots_neg hpsplit hppos hproots
  by_cases hkzero : k = 0
  · simpa [hkzero] using hpzero
  by_cases hkdegree : k = p.natDegree
  · simpa only [hkdegree, coeff_natDegree, HasPosLeadingCoeff] using hppos
  have hpdegree : p.coeff p.natDegree ≠ 0 := by
    simpa [coeff_natDegree] using hppos.ne'
  have hkinternal : p.coeff k ≠ 0 :=
    (hasNoInternalCoeffZeros_of_hasNonnegCoeffs_of_eq_zero_or_splits
      hppf.hasNonnegCoeffs (Or.inr hpsplit))
      0 k p.natDegree (Nat.pos_of_ne_zero hkzero)
      (lt_of_le_of_ne hk hkdegree) le_rfl hpzero.ne' hpdegree
  exact lt_of_le_of_ne (hppf.hasNonnegCoeffs k) (Ne.symm hkinternal)

theorem schurSzegoComp_ne_zero_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree = N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hfzero : f ≠ 0) :
    schurSzegoComp N p f ≠ 0 := by
  have hpc : p.coeff f.natDegree ≠ 0 :=
    (coeff_pos_of_roots_neg hpsplit hppos hproots
      (by simpa [hpdegree] using hfdegree)).ne'
  have hfc : f.coeff f.natDegree ≠ 0 := by
    simpa [coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hfzero
  have hchoose : (Nat.choose N f.natDegree : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hfdegree).ne'
  intro hzero
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff f.natDegree) hzero
  rw [coeff_schurSzegoComp, if_pos hfdegree, coeff_zero] at hcoeff
  exact (div_ne_zero (mul_ne_zero hpc hfc) hchoose) hcoeff

theorem schurSzegoComp_add_C (N : ℕ) (p f : ℝ[X]) (u : ℝ) :
    schurSzegoComp N p (f + C u) =
      schurSzegoComp N p f + C (p.coeff 0 * u) := by
  ext k
  rcases k with _ | k
  · simp [coeff_schurSzegoComp]
    ring
  · simp [coeff_schurSzegoComp, coeff_add, coeff_C]

/-- A general simple split polynomial of positive degree admits two-sided
constant perturbations. This openness step is established
using the upstream local root-branch theorem. -/
theorem exists_pos_add_C_splits {f : ℝ[X]}
    (hfdegree : f.natDegree ≠ 0) (hfsplit : f.Splits)
    (hfsimple : HasSimpleRoots f) :
    ∃ ε : ℝ, 0 < ε ∧ (f + C ε).Splits ∧ (f + C (-ε)).Splits := by
  let q : ℝ → ℝ[X] := fun u => f + C u
  obtain ⟨ξ, _hbase, hlocal⟩ :=
    exists_eventually_polynomial_root_branches q (t := 0)
      (D := f.natDegree) hfdegree
      (Filter.Eventually.of_forall fun u : ℝ => by simp [q])
      (by simpa [q] using hfsplit) (by simpa [q] using hfsimple)
      (by
        intro x _
        have heval : (fun z : ℝ × ℝ => (q z.1).eval z.2) =
            fun z => f.eval z.2 + z.1 := by
          funext z
          simp [q]
        rw [heval]
        exact (((Polynomial.contDiff_aeval f 1).comp contDiff_snd).add
          contDiff_fst).contDiffAt)
  have hsplits : ∀ᶠ u in nhds (0 : ℝ), (q u).Splits :=
    hlocal.mono fun u hu => hu.1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hsplits
  refine ⟨δ / 2, half_pos hδ, ?_, ?_⟩
  · apply hball
    simpa [Real.dist_eq, abs_of_pos hδ] using half_lt_self hδ
  · apply hball
    simpa [Real.dist_eq, abs_of_pos hδ] using half_lt_self hδ

/-- The simple-real-root component of Lemma 2.2. The multiplier p may have
repeated negative roots, and f may have roots anywhere on the real line. -/
theorem schurSzegoComp_hasSimpleRoots_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree = N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hfsplit : f.Splits)
    (hfsimple : HasSimpleRoots f) :
    HasSimpleRoots (schurSzegoComp N p f) := by
  let h := schurSzegoComp N p f
  have hhne : h ≠ 0 :=
    schurSzegoComp_ne_zero_of_roots_neg hpdegree hpsplit hppos hproots hfdegree hfsimple.ne_zero
  by_cases hhdegree : h.natDegree ≤ 1
  · exact hasSimpleRoots_of_natDegree_le_one hhne hhdegree
  have hfdegree0 : f.natDegree ≠ 0 := by
    intro hfzero
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hfzero
    have hhC : h = C (p.coeff 0 * f.coeff 0) := by
      dsimp [h]
      rw [hfC]
      ext k
      rcases k with _ | k <;> simp [coeff_schurSzegoComp]
    have hhzero : h.natDegree = 0 := by rw [hhC]; exact natDegree_C _
    lia
  obtain ⟨ε, hε, hfplus, hfminus⟩ :=
    exists_pos_add_C_splits hfdegree0 hfsplit hfsimple
  have hp0 := coeff_zero_pos_of_roots_neg hpsplit hppos hproots
  let c := p.coeff 0 * ε
  have hc : 0 < c := mul_pos hp0 hε
  have hplus : (h + C c).Splits := by
    have hdeg : (f + C ε).natDegree ≤ N := by rw [natDegree_add_C]; exact hfdegree
    have hne : f + C ε ≠ 0 := by
      intro hz
      have := congrArg Polynomial.natDegree hz
      rw [natDegree_add_C, natDegree_zero] at this
      exact hfdegree0 this
    have hout := schurSzegoComp_eq_zero_or_splits_of_roots_neg
      (by lia : p.natDegree ≤ N) hpsplit hppos hproots hdeg hfplus
    have hnonzero := schurSzegoComp_ne_zero_of_roots_neg hpdegree hpsplit hppos hproots hdeg hne
    have hs := hout.resolve_left hnonzero
    rw [schurSzegoComp_add_C] at hs
    exact hs
  have hminus : (h + C (-c)).Splits := by
    have hdeg : (f + C (-ε)).natDegree ≤ N := by rw [natDegree_add_C]; exact hfdegree
    have hne : f + C (-ε) ≠ 0 := by
      intro hz
      have := congrArg Polynomial.natDegree hz
      rw [natDegree_add_C, natDegree_zero] at this
      exact hfdegree0 this
    have hout := schurSzegoComp_eq_zero_or_splits_of_roots_neg
      (by lia : p.natDegree ≤ N) hpsplit hppos hproots hdeg hfminus
    have hnonzero := schurSzegoComp_ne_zero_of_roots_neg hpdegree hpsplit hppos hproots hdeg hne
    have hs := hout.resolve_left hnonzero
    rw [schurSzegoComp_add_C] at hs
    simpa [c] using hs
  intro r hr
  have hrh : h.eval r = 0 := hr
  have hmultpos : 0 < h.rootMultiplicity r :=
    (Polynomial.rootMultiplicity_pos hhne).2 hr
  by_contra hmult
  have hmultTwo : 1 < h.rootMultiplicity r := by lia
  have hderRoot : h.derivative.IsRoot r :=
    ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hhne).1 hmultTwo).2
  have hplusEval : (h + C c).eval r ≠ 0 := by simp [hrh, hc.ne']
  have hminusEval : (h + C (-c)).eval r ≠ 0 := by simp [hrh, hc.ne']
  have hplusStrict := deriv2_mul_lt_deriv_sq_at_non_root hplus
    (by simpa using (lt_of_not_ge hhdegree).le) hplusEval
  have hminusStrict := deriv2_mul_lt_deriv_sq_at_non_root hminus
    (by rw [Polynomial.natDegree_add_C]; exact (lt_of_not_ge hhdegree).le) hminusEval
  simp [Polynomial.IsRoot.def] at hderRoot
  simp [hrh, hderRoot] at hplusStrict hminusStrict
  linarith

theorem schurSzegoComp_natDegree_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree = N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hfzero : f ≠ 0) :
    (schurSzegoComp N p f).natDegree = f.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_schurSzegoComp_le_right N p f
  · rw [coeff_schurSzegoComp, if_pos hfdegree, coeff_natDegree]
    exact div_ne_zero
      (mul_ne_zero
        (coeff_pos_of_roots_neg hpsplit hppos hproots
          (by simpa [hpdegree] using hfdegree)).ne'
        (leadingCoeff_ne_zero.mpr hfzero))
      (by exact_mod_cast (Nat.choose_pos hfdegree).ne')

theorem schurSzegoComp_hasPosLeadingCoeff_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree = N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hfpos : HasPosLeadingCoeff f) :
    HasPosLeadingCoeff (schurSzegoComp N p f) := by
  change 0 < (schurSzegoComp N p f).leadingCoeff
  rw [← coeff_natDegree,
    schurSzegoComp_natDegree_of_roots_neg hpdegree hpsplit hppos hproots hfdegree hfpos.ne_zero,
    coeff_schurSzegoComp, if_pos hfdegree, coeff_natDegree]
  exact div_pos (mul_pos
    (coeff_pos_of_roots_neg hpsplit hppos hproots
      (by simpa [hpdegree] using hfdegree)) hfpos)
    (by exact_mod_cast Nat.choose_pos hfdegree)

theorem schurSzegoComp_linear_combination (N : ℕ) (p f g : ℝ[X]) (α β : ℝ) :
    schurSzegoComp N p (C α * f + C β * g) =
      C α * schurSzegoComp N p f + C β * schurSzegoComp N p g := by
  simp only [schurSzegoComp_add_right, schurSzegoComp_C_mul_right]

/-- Scalar Wronskian orientation identity for Schur--Szegő composition. -/
theorem schurSzegoComp_wronskian_zero {N : ℕ} (hN : 1 ≤ N)
    (p f g : ℝ[X]) :
    (Polynomial.wronskian (schurSzegoComp N p f) (schurSzegoComp N p g)).eval 0 =
      (p.coeff 0 * p.coeff 1 / (N : ℝ)) * (Polynomial.wronskian f g).eval 0 := by
  have hv0 (q : ℝ[X]) : (schurSzegoComp N p q).eval 0 = p.coeff 0 * q.coeff 0 := by
    simp [← coeff_zero_eq_eval_zero, coeff_schurSzegoComp]
  have hv1 (q : ℝ[X]) : (schurSzegoComp N p q).derivative.eval 0 =
      p.coeff 1 * q.coeff 1 / (N : ℝ) := by
    simp [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_schurSzegoComp, hN]
  simp only [Polynomial.wronskian, eval_sub, eval_mul, hv0, hv1]
  simp only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.zero_add, Nat.cast_one, mul_one]
  ring

theorem schurSzegoComp_simpleNegativeRoots_of_roots_neg {N : ℕ} {p f : ℝ[X]}
    (hpdegree : p.natDegree = N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hf : SimpleNegativeRoots f)
    (hfpos : HasPosLeadingCoeff f) :
    SimpleNegativeRoots (schurSzegoComp N p f) := by
  have hne := schurSzegoComp_ne_zero_of_roots_neg hpdegree hpsplit hppos hproots hfdegree hf.1
  have hsplit := (schurSzegoComp_eq_zero_or_splits_of_roots_neg
    hpdegree.le hpsplit hppos hproots hfdegree hf.2.1).resolve_left hne
  have hsimple := schurSzegoComp_hasSimpleRoots_of_roots_neg hpdegree hpsplit hppos hproots
    hfdegree hf.2.1 hf.hasSimpleRoots
  have hpf := isPFPolynomial_of_roots_neg hf.2.1 hfpos hf.2.2.2
  have hp0 := coeff_zero_pos_of_roots_neg hpsplit hppos hproots
  have hf0 := coeff_zero_pos_of_roots_neg hf.2.1 hfpos hf.2.2.2
  have hout0 := schurSzegoComp_coeff_zero_pos (N := N) hp0 hf0
  have houtnonneg : HasNonnegCoeffs (schurSzegoComp N p f) := by
    intro k
    rw [coeff_schurSzegoComp]
    split_ifs with hk
    · exact div_nonneg (mul_nonneg
        ((isPFPolynomial_of_roots_neg hpsplit hppos hproots).hasNonnegCoeffs k)
        (hpf.hasNonnegCoeffs k)) (by positivity)
    · exact le_rfl
  refine ⟨hne, hsplit, hsimple.roots_nodup, ?_⟩
  intro r hr
  have hrle := roots_nonpos_of_hasNonnegCoeffs houtnonneg r hr
  refine lt_of_le_of_ne hrle ?_
  intro hrzero
  have hroot := (mem_roots hne).mp hr
  have hz : (schurSzegoComp N p f).coeff 0 = 0 := by
    simpa [hrzero, ← coeff_zero_eq_eval_zero] using hroot
  linarith

private private theorem strictRootInterl_wronskian_pos {f g : ℝ[X]}
    (hfg : StrictRootInterl f g) (hgdegree : 0 < g.natDegree) (t : ℝ) :
    0 < (Polynomial.wronskian f g).eval t := by
  rcases hfg.toStrictInterl.natDegree_eq_or_eq_succ with hsame | hsucc
  · have hstrict := StrictInterlSameDegree.of_strictInterl_of_no_common
      hfg.toStrictInterl hsame.symm hfg.no_common_root
    have hw := wronskian_pos_of_strictInterlSameDegree hfg.1 hfg.2.1 hgdegree hstrict t
    simp only [Polynomial.wronskian, eval_sub, eval_mul]
    nlinarith
  · have hsimple := hfg.hasSimpleRoots
    have hw := wronskian_pos_of_strictInterl_succ hfg.2.1 hfg.1 hsucc
      hfg.toStrictInterl hsimple.2.roots_nodup hsimple.1.roots_nodup
      (fun r hgr hfr => hfg.no_common_root r hfr hgr) t
    simp only [Polynomial.wronskian, eval_sub, eval_mul]
    nlinarith

/-- Strict oriented preservation under Schur--Szegő composition.
No simplicity hypothesis is imposed on the negative-root multiplier p. -/
theorem schurSzegoComp_strictRootInterl_of_roots_neg {N : ℕ} {p f g : ℝ[X]}
    (hN : 1 ≤ N) (hpdegree : p.natDegree = N)
    (hpsplit : p.Splits) (hppos : HasPosLeadingCoeff p)
    (hproots : ∀ r ∈ p.roots, r < 0)
    (hfdegree : f.natDegree ≤ N) (hgdegree : g.natDegree ≤ N)
    (hfg : StrictRootInterl f g)
    (hfroots : ∀ r ∈ f.roots, r < 0) (hgroots : ∀ r ∈ g.roots, r < 0) :
    StrictRootInterl (schurSzegoComp N p f) (schurSzegoComp N p g) := by
  let a := schurSzegoComp N p f
  let b := schurSzegoComp N p g
  have hafull : SimpleNegativeRoots a := schurSzegoComp_simpleNegativeRoots_of_roots_neg
    hpdegree hpsplit hppos hproots hfdegree
    ⟨hfg.toStrictInterl.1.1, hfg.toStrictInterl.1.2,
      hfg.hasSimpleRoots.1.roots_nodup, hfroots⟩ hfg.1
  have hbfull : SimpleNegativeRoots b := schurSzegoComp_simpleNegativeRoots_of_roots_neg
    hpdegree hpsplit hppos hproots hgdegree
    ⟨hfg.toStrictInterl.2.1.1, hfg.toStrictInterl.2.1.2,
      hfg.hasSimpleRoots.2.roots_nodup, hgroots⟩ hfg.2.1
  have hapos : HasPosLeadingCoeff a := schurSzegoComp_hasPosLeadingCoeff_of_roots_neg
    hpdegree hpsplit hppos hproots hfdegree hfg.1
  have hbpos : HasPosLeadingCoeff b := schurSzegoComp_hasPosLeadingCoeff_of_roots_neg
    hpdegree hpsplit hppos hproots hgdegree hfg.2.1
  have hadegree : a.natDegree = f.natDegree := schurSzegoComp_natDegree_of_roots_neg
    hpdegree hpsplit hppos hproots hfdegree hfg.toStrictInterl.1.1
  have hbdegree : b.natDegree = g.natDegree := schurSzegoComp_natDegree_of_roots_neg
    hpdegree hpsplit hppos hproots hgdegree hfg.toStrictInterl.2.1.1
  have hall := allComboRealRooted_of_strictInterl hfg.toStrictInterl
  have hcomboDegree (α β : ℝ) : (C α * f + C β * g).natDegree ≤ N :=
    (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le ..).trans hfdegree)
        ((natDegree_C_mul_le ..).trans hgdegree))
  have houtall : AllComboRealRooted a b := by
    intro α β
    have hs := schurSzegoComp_eq_zero_or_splits_of_roots_neg hpdegree.le hpsplit hppos hproots
      (hcomboDegree α β) (hall α β)
    rw [schurSzegoComp_linear_combination] at hs
    rcases hs with hz | hs
    · change (C α * a + C β * b).Splits
      rw [hz]
      simp
    · exact hs
  have hdeg : a.natDegree + 1 = b.natDegree ∨ a.natDegree = b.natDegree := by
    rw [hadegree, hbdegree]
    rcases hfg.toStrictInterl.natDegree_eq_or_eq_succ with hsame | hsucc
    · exact Or.inr hsame.symm
    · exact Or.inl hsucc.symm
  have hweakOr := strictInterl_of_allComboRealRooted
    hafull.1 hafull.2.1 hbfull.1 hbfull.2.1 houtall hdeg
  by_cases hgzero : g.natDegree = 0
  · have hfzero : f.natDegree = 0 := by
      have := hfg.toStrictInterl.natDegree_le
      lia
    have haroots : a.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hafull.2.1, hadegree, hfzero]
    have hbroots : b.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hbfull.2.1, hbdegree, hgzero]
    have hweak : StrictInterl a b := by
      rcases hweakOr with hab | hba
      · exact hab
      · exact hba.of_reverse_of_roots_sum_le (by lia) (by simp [haroots, hbroots])
    exact strictRootInterl_of_strictInterl_of_no_common_root hweak hapos hbpos (by
      intro r hr
      have := (mem_roots hafull.1).mpr hr.1
      simpa [haroots] using this)
  have hW (t : ℝ) := strictRootInterl_wronskian_pos hfg (Nat.pos_of_ne_zero hgzero) t
  have hsourceSimple :=
    ObreschkoffConverseInternal.combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
      hall (by
        intro t
        intro hz
        have hw := hW t
        simp only [ObreschkoffConverseInternal.wronskianPoly, eval_sub, eval_mul] at hz
        simp only [Polynomial.wronskian, eval_sub, eval_mul] at hw
        nlinarith)
  have houtno : ∀ r, ¬ (a.IsRoot r ∧ b.IsRoot r) := by
    intro r hr
    by_cases hfzero : f.natDegree = 0
    · have haroots : a.roots = 0 := by
        apply Multiset.card_eq_zero.mp
        rw [card_roots_of_splits hafull.2.1, hadegree, hfzero]
      have := (mem_roots hafull.1).mpr hr.1
      simpa [haroots] using this
    let α := b.derivative.eval r
    let β := -a.derivative.eval r
    have hα : α ≠ 0 := hbfull.hasSimpleRoots.eval_derivative_ne_zero hr.2
    have hβ : β ≠ 0 := neg_ne_zero.mpr
      (hafull.hasSimpleRoots.eval_derivative_ne_zero hr.1)
    have hinne : C α * f + C β * g ≠ 0 := by
      intro hz
      exact ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
        hfg.toStrictInterl.1.1 hfg.toStrictInterl.1.2 hfg.no_common_root
        (Nat.pos_of_ne_zero hfzero) hα hβ hz
    have hinsimple := ((hsourceSimple α β).resolve_left hinne).2
    have houtSimple := schurSzegoComp_hasSimpleRoots_of_roots_neg hpdegree hpsplit hppos hproots
      (hcomboDegree α β) (hall α β) hinsimple
    rw [schurSzegoComp_linear_combination] at houtSimple
    have houtRoot : (C α * a + C β * b).IsRoot r := by
      have har : a.eval r = 0 := hr.1
      have hbr : b.eval r = 0 := hr.2
      simp [Polynomial.IsRoot.def, har, hbr]
    have hderne := houtSimple.eval_derivative_ne_zero houtRoot
    apply hderne
    simp [α, β, a, b, derivative_add, derivative_C_mul]
    ring
  have hp0 := coeff_zero_pos_of_roots_neg hpsplit hppos hproots
  have hp1 := coeff_pos_of_roots_neg hpsplit hppos hproots
    (by simpa [hpdegree] using hN)
  have hscale : 0 < p.coeff 0 * p.coeff 1 / (N : ℝ) :=
    div_pos (mul_pos hp0 hp1) (by exact_mod_cast (show 0 < N by lia))
  have hWout : 0 < (Polynomial.wronskian a b).eval 0 := by
    dsimp [a, b]
    rw [schurSzegoComp_wronskian_zero hN]
    exact mul_pos hscale (hW 0)
  have hweak : StrictInterl a b := by
    rcases hweakOr with hab | hba
    · exact hab
    · have hreverse := wronskian_eval_nonneg_of_strictInterl hapos hbpos hba 0
      simp only [Polynomial.wronskian, eval_sub, eval_mul] at hreverse hWout
      nlinarith
  exact strictRootInterl_of_strictInterl_of_no_common_root hweak hapos hbpos houtno

end RealRooted.FactorialCompression
