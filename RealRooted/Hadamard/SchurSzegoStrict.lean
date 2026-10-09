import RealRooted.CriticalValueContinuation
import RealRooted.EulerOperator
import RealRooted.Hadamard.SchurSzegoSigns
import RealRooted.Interlacing.OuterDifference
import RealRooted.IteratedDerivativeShift
import RealRooted.MaWang.Strong
import RealRooted.ObreschkoffConverse
import RealRooted.SimpleRoots
import RealRooted.Wronskian.Forward
import RealRooted.Wronskian.WeakForward

/-!
# Strict interlacing under Schur--Szegő composition with a negative-root multiplier

Let `Q` be a polynomial of degree `n` with positive leading coefficient and only (real) negative
roots.  We prove that the finite Schur--Szegő composition `P ↦ schurSzegoComp n P Q` with `Q`

* has degree `P.natDegree`, positive leading coefficient and only negative roots when `P` does,
* preserves simple real roots (`hasSimpleRoots_schurSzegoComp_of_roots_neg`), and
* maps a strictly interlacing pair `f ≺ g` of polynomials of degree at most `n`, without common
  root, to a strictly interlacing pair without common root
  (`strictInterl_schurSzegoComp_of_roots_neg`).

The orientation of the output pair is fixed by the Wronskian identity
`W(f ∘ₙ Q, g ∘ₙ Q)(0) = Q₀ Q₁ / n * W(f, g)(0)`
(`wronskian_schurSzegoComp_eval_zero`).

The simple-root preservation follows Zhang, *Strict interlacing and a factorial compression
theorem* (SSRN 7510941): the output is a limit of real-rooted polynomials `P ± C ε`, and a
multiple root would contradict the Laguerre-type inequality `p'' p < p'²` at nonroots.  The
strict interlacing combines the Hermite--Kakeya--Obreschkoff theorem in both directions with the
Wronskian orientation.  The statement of Zhang's Theorem 2.2 for roots of multiplicity at most
one is a special case; see also Kostov (2010) for the multiplicity of the roots of Schur--Szegő
compositions.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ### Euler operator -/

/-- Schur--Szegő composition commutes with the Euler operator `θ = X d/dX` acting on the left
argument. -/
theorem schurSzegoComp_theta_left (n : ℕ) (f Q : ℝ[X]) :
    schurSzegoComp n (theta f) Q = theta (schurSzegoComp n f Q) := by
  ext k
  simp only [coeff_schurSzegoComp, coeff_theta]
  split_ifs <;> ring

/-- Schur--Szegő composition commutes with the Euler operator `θ = X d/dX` acting on the right
argument. -/
theorem schurSzegoComp_theta_right (n : ℕ) (f Q : ℝ[X]) :
    schurSzegoComp n f (theta Q) = theta (schurSzegoComp n f Q) := by
  rw [schurSzegoComp_comm, schurSzegoComp_theta_left, schurSzegoComp_comm]

/-! ### Coefficients, degree and roots of the image -/

private theorem coeff_pos_of_roots_neg {Q : ℝ[X]} (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q)
    (hneg : ∀ b ∈ Q.roots, b < 0) {k : ℕ} (hk : k ≤ Q.natDegree) : 0 < Q.coeff k :=
  (pos_iff_pos_of_mul_pos
    (leadingCoeff_mul_coeff_pos_of_roots_neg hQs hQpos.ne_zero hneg hk)).mp hQpos

private theorem hasNonnegCoeffs_of_roots_neg {Q : ℝ[X]} (hQs : Q.Splits)
    (hQpos : HasPosLeadingCoeff Q) (hneg : ∀ b ∈ Q.roots, b < 0) : HasNonnegCoeffs Q := by
  intro k
  rcases le_or_gt k Q.natDegree with hk | hk
  · exact (coeff_pos_of_roots_neg hQs hQpos hneg hk).le
  · rw [coeff_eq_zero_of_natDegree_lt hk]

/-- The coefficient of `P *ₙ Q` in degree `P.natDegree` is nonzero when `P ≠ 0`. -/
private theorem coeff_natDegree_schurSzegoComp_ne_zero {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hP0 : P ≠ 0) (hQ : Q.natDegree = n) (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q)
    (hneg : ∀ b ∈ Q.roots, b < 0) :
    (schurSzegoComp n P Q).coeff P.natDegree ≠ 0 := by
  rw [coeff_schurSzegoComp, ite_eq_left hP, coeff_natDegree]
  exact div_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP0)
    (coeff_pos_of_roots_neg hQs hQpos hneg (hQ ▸ hP)).ne')
    (by exact_mod_cast (Nat.choose_pos hP).ne')

/-- The Schur--Szegő composition with a multiplier `Q` of degree `n` with negative roots keeps the
degree of `P`. -/
theorem natDegree_schurSzegoComp_of_roots_neg {n : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree = n) (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q)
    (hneg : ∀ b ∈ Q.roots, b < 0) :
    (schurSzegoComp n P Q).natDegree = P.natDegree := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  exact natDegree_eq_of_le_of_coeff_ne_zero (natDegree_schurSzegoComp_le_left n P Q)
    (coeff_natDegree_schurSzegoComp_ne_zero hP hP0 hQ hQs hQpos hneg)

/-- The Schur--Szegő composition of a nonzero `P` of degree at most `n` with a multiplier of degree
`n` with negative roots is nonzero. -/
theorem schurSzegoComp_ne_zero_of_roots_neg {n : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ n)
    (hP0 : P ≠ 0) (hQ : Q.natDegree = n) (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q)
    (hneg : ∀ b ∈ Q.roots, b < 0) :
    schurSzegoComp n P Q ≠ 0 := fun h => by
  simpa [h] using coeff_natDegree_schurSzegoComp_ne_zero hP hP0 hQ hQs hQpos hneg

/-- The Schur--Szegő composition with a multiplier of degree `n` with negative roots preserves
positive leading coefficients. -/
theorem hasPosLeadingCoeff_schurSzegoComp_of_roots_neg {n : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ n) (hPpos : HasPosLeadingCoeff P) (hQ : Q.natDegree = n)
    (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q) (hneg : ∀ b ∈ Q.roots, b < 0) :
    HasPosLeadingCoeff (schurSzegoComp n P Q) := by
  change 0 < (schurSzegoComp n P Q).leadingCoeff
  rw [← coeff_natDegree, natDegree_schurSzegoComp_of_roots_neg hP hQ hQs hQpos hneg,
    coeff_schurSzegoComp, ite_eq_left hP, coeff_natDegree]
  exact div_pos (mul_pos hPpos (coeff_pos_of_roots_neg hQs hQpos hneg (hQ ▸ hP)))
    (by exact_mod_cast Nat.choose_pos hP)

/-- The Schur--Szegő composition with a multiplier with negative roots maps
polynomials with positive leading coefficient and only negative roots to polynomials with the
same properties; the roots stay strictly negative. -/
theorem roots_schurSzegoComp_neg_of_roots_neg {n : ℕ} {P Q : ℝ[X]}
    (hPs : P.Splits) (hPpos : HasPosLeadingCoeff P) (hPneg : ∀ r ∈ P.roots, r < 0)
    (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q) (hneg : ∀ b ∈ Q.roots, b < 0) :
    ∀ r ∈ (schurSzegoComp n P Q).roots, r < 0 := by
  intro r hr
  have hnonneg : HasNonnegCoeffs (schurSzegoComp n P Q) :=
    (hasNonnegCoeffs_of_roots_neg hPs hPpos hPneg).schurSzegoComp
      (hasNonnegCoeffs_of_roots_neg hQs hQpos hneg)
  refine lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs hnonneg r hr) fun hr0 => ?_
  have hne : schurSzegoComp n P Q ≠ 0 := fun h => by simp [h] at hr
  have hroot := (mem_roots hne).mp hr
  rw [hr0, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_schurSzegoComp, ite_eq_left (Nat.zero_le _)]
    at hroot
  have hP0 := coeff_pos_of_roots_neg hPs hPpos hPneg (Nat.zero_le _)
  have hQ0 := coeff_pos_of_roots_neg hQs hQpos hneg (Nat.zero_le _)
  simp only [Nat.choose_zero_right, Nat.cast_one, div_one] at hroot
  exact (mul_pos hP0 hQ0).ne' hroot

/-! ### Simple roots -/

/-- A simple real-rooted polynomial of positive degree admits two-sided constant perturbations
that stay real-rooted (openness of the real-rooted polynomials with simple roots). -/
private theorem exists_pos_add_C_splits {f : ℝ[X]} (hfdegree : f.natDegree ≠ 0)
    (hfsplit : f.Splits) (hfsimple : HasSimpleRoots f) :
    ∃ ε : ℝ, 0 < ε ∧ (f + C ε).Splits ∧ (f + C (-ε)).Splits := by
  obtain ⟨ξ, _hbase, hlocal⟩ :=
    exists_eventually_polynomial_root_branches (fun u : ℝ => f + C u) (t := 0)
      (D := f.natDegree) hfdegree
      (Filter.Eventually.of_forall fun u : ℝ => by rw [natDegree_add_C])
      (by simpa only [map_zero, add_zero] using hfsplit)
      (by simpa only [map_zero, add_zero] using hfsimple)
      (by
        intro x _
        have heval : (fun z : ℝ × ℝ => ((fun u : ℝ => f + C u) z.1).eval z.2) =
            fun z => f.eval z.2 + z.1 := by
          funext z
          simp only [eval_add, eval_C]
        rw [heval]
        exact (((Polynomial.contDiff_aeval f 1).comp contDiff_snd).add
          contDiff_fst).contDiffAt)
  have hsplits : ∀ᶠ u in nhds (0 : ℝ), (f + C u).Splits := hlocal.mono fun u hu => hu.1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hsplits
  refine ⟨δ / 2, half_pos hδ, hball ?_, hball ?_⟩ <;>
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
      using half_lt_self hδ

/-- **Simple roots are preserved** by Schur--Szegő composition with a multiplier of degree `n`
with positive leading coefficient and only negative roots.  The multiplier may have repeated
roots, and `P` may have roots anywhere on the real line.

The proof is by openness: a multiple root of the output would contradict `p'' p < p'²` at a
nonroot for the real-rooted outputs obtained from `P ± ε`. -/
theorem hasSimpleRoots_schurSzegoComp_of_roots_neg {n : ℕ} {P Q : ℝ[X]}
    (hP : P.natDegree ≤ n) (hPs : P.Splits) (hPsimple : HasSimpleRoots P)
    (hQ : Q.natDegree = n) (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q)
    (hneg : ∀ b ∈ Q.roots, b < 0) :
    HasSimpleRoots (schurSzegoComp n P Q) := by
  set h := schurSzegoComp n P Q with hh
  have hhne : h ≠ 0 :=
    schurSzegoComp_ne_zero_of_roots_neg hP hPsimple.ne_zero hQ hQs hQpos hneg
  by_cases hhdegree : h.natDegree ≤ 1
  · exact hasSimpleRoots_of_natDegree_le_one hhne hhdegree
  have hPdegree0 : P.natDegree ≠ 0 := by
    intro hPzero
    have hPC : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero hPzero
    rw [hh, hPC, schurSzegoComp_C_left, natDegree_C] at hhdegree
    exact hhdegree (Nat.zero_le _)
  obtain ⟨ε, hε, hPplus, hPminus⟩ := exists_pos_add_C_splits hPdegree0 hPs hPsimple
  have hQ0 : 0 < Q.coeff 0 := coeff_pos_of_roots_neg hQs hQpos hneg (Nat.zero_le _)
  have hc : 0 < ε * Q.coeff 0 := mul_pos hε hQ0
  have hplus : (h + C (ε * Q.coeff 0)).Splits := by
    have hs := splits_schurSzegoComp_of_roots_neg
      (by rw [natDegree_add_C]; exact hP) hPplus hQ.le hQs hneg
    rwa [schurSzegoComp_add_C_left] at hs
  have hminus : (h + C (-(ε * Q.coeff 0))).Splits := by
    have hs := splits_schurSzegoComp_of_roots_neg
      (by rw [natDegree_add_C]; exact hP) hPminus hQ.le hQs hneg
    rwa [schurSzegoComp_add_C_left, neg_mul] at hs
  intro r hr
  have hrh : h.eval r = 0 := hr
  by_contra hmult
  have hmultTwo : 1 < h.rootMultiplicity r := by
    have := (Polynomial.rootMultiplicity_pos hhne).2 hr
    lia
  have hderRoot : h.derivative.eval r = 0 :=
    ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hhne).1 hmultTwo).2
  have hplusStrict := deriv2_mul_lt_deriv_sq_at_non_root hplus
    (by rw [natDegree_add_C]; lia) (by rw [eval_add, eval_C, hrh, zero_add]; exact hc.ne')
  have hminusStrict := deriv2_mul_lt_deriv_sq_at_non_root hminus
    (by rw [natDegree_add_C]; lia)
    (by rw [eval_add, eval_C, hrh, zero_add]; exact neg_ne_zero.mpr hc.ne')
  simp only [derivative_add, derivative_C, add_zero, hderRoot, eval_add, eval_C, hrh, zero_add,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_neg] at hplusStrict hminusStrict
  linarith

/-! ### Strict interlacing -/

/-- **Wronskian orientation identity** for the finite Schur--Szegő composition: at `0`,
the Wronskian of the images is the Wronskian of the inputs scaled by `Q₀ Q₁ / n`. -/
theorem wronskian_schurSzegoComp_eval_zero {n : ℕ} (hn : n ≠ 0) (f g Q : ℝ[X]) :
    (wronskian (schurSzegoComp n f Q) (schurSzegoComp n g Q)).eval 0 =
      Q.coeff 0 * Q.coeff 1 / (n : ℝ) * (wronskian f g).eval 0 := by
  have hn1 : 1 ≤ n := by lia
  have hv0 (q : ℝ[X]) : (schurSzegoComp n q Q).eval 0 = q.coeff 0 * Q.coeff 0 := by
    simp [← coeff_zero_eq_eval_zero, coeff_schurSzegoComp]
  have hv1 (q : ℝ[X]) :
      (schurSzegoComp n q Q).derivative.eval 0 = q.coeff 1 * Q.coeff 1 / (n : ℝ) := by
    simp [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_schurSzegoComp, hn1]
  simp only [wronskian, eval_sub, eval_mul, hv0, hv1]
  simp only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.zero_add]
  ring

/-- The Wronskian of a strictly interlacing pair with positive leading coefficients, no common
root and `g` of positive degree is positive. -/
private theorem wronskian_eval_pos_of_strictInterl {f g : ℝ[X]} (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hfg : StrictInterl f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) (hgdegree : 0 < g.natDegree) (t : ℝ) :
    0 < (wronskian f g).eval t := by
  rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
  · have hstrict := StrictInterlSameDegree.of_strictInterl_of_no_common hfg hsame.symm hno
    have hw := wronskian_pos_of_strictInterlSameDegree hfpos hgpos hgdegree hstrict t
    simp only [wronskian, eval_sub, eval_mul]
    linarith
  · have hsimple := hfg.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2
    have hw := wronskian_pos_of_strictInterl_succ hgpos hfpos hsucc hfg
      hsimple.2.roots_nodup hsimple.1.roots_nodup (fun r hgr hfr => hno r hfr hgr) t
    simp only [wronskian, eval_sub, eval_mul]
    linarith

/-- **Strict interlacing is preserved** by Schur--Szegő composition with a multiplier `Q` of
degree `n` with positive leading coefficient and only negative roots.

If `f ≺ g` strictly interlace (with positive leading coefficients, degrees at most `n` and no
common root), so do `f *ₙ Q` and `g *ₙ Q`, in the same order, again without a common root.  Both
outputs then have simple roots (`StrictInterl.hasSimpleRoots_of_no_common_root`).  The orientation
is determined by `wronskian_schurSzegoComp_eval_zero`. -/
theorem strictInterl_schurSzegoComp_of_roots_neg {n : ℕ} {f g Q : ℝ[X]} (hn : n ≠ 0)
    (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ n)
    (hfpos : HasPosLeadingCoeff f) (hgpos : HasPosLeadingCoeff g)
    (hfg : StrictInterl f g) (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hQ : Q.natDegree = n) (hQs : Q.Splits) (hQpos : HasPosLeadingCoeff Q)
    (hneg : ∀ b ∈ Q.roots, b < 0) :
    StrictInterl (schurSzegoComp n f Q) (schurSzegoComp n g Q) ∧
      ∀ r, (schurSzegoComp n f Q).IsRoot r → ¬ (schurSzegoComp n g Q).IsRoot r := by
  set a := schurSzegoComp n f Q with ha
  set b := schurSzegoComp n g Q with hb
  have hsimple := hfg.hasSimpleRoots_of_no_common_root fun r hr => hno r hr.1 hr.2
  have hane : a ≠ 0 := schurSzegoComp_ne_zero_of_roots_neg hf hfg.1.1 hQ hQs hQpos hneg
  have hbne : b ≠ 0 := schurSzegoComp_ne_zero_of_roots_neg hg hfg.2.1.1 hQ hQs hQpos hneg
  have hasplit : a.Splits := splits_schurSzegoComp_of_roots_neg hf hfg.1.2 hQ.le hQs hneg
  have hbsplit : b.Splits := splits_schurSzegoComp_of_roots_neg hg hfg.2.1.2 hQ.le hQs hneg
  have hasimple : HasSimpleRoots a :=
    hasSimpleRoots_schurSzegoComp_of_roots_neg hf hfg.1.2 hsimple.1 hQ hQs hQpos hneg
  have hbsimple : HasSimpleRoots b :=
    hasSimpleRoots_schurSzegoComp_of_roots_neg hg hfg.2.1.2 hsimple.2 hQ hQs hQpos hneg
  have hapos : HasPosLeadingCoeff a :=
    hasPosLeadingCoeff_schurSzegoComp_of_roots_neg hf hfpos hQ hQs hQpos hneg
  have hbpos : HasPosLeadingCoeff b :=
    hasPosLeadingCoeff_schurSzegoComp_of_roots_neg hg hgpos hQ hQs hQpos hneg
  have hadegree : a.natDegree = f.natDegree :=
    natDegree_schurSzegoComp_of_roots_neg hf hQ hQs hQpos hneg
  have hbdegree : b.natDegree = g.natDegree :=
    natDegree_schurSzegoComp_of_roots_neg hg hQ hQs hQpos hneg
  have hall := allComboRealRooted_of_strictInterl hfg
  have hcomboDegree (α β : ℝ) : (C α * f + C β * g).natDegree ≤ n :=
    (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le ..).trans hf) ((natDegree_C_mul_le ..).trans hg))
  have houtall : AllComboRealRooted a b := fun α β => by
    have hs := splits_schurSzegoComp_of_roots_neg (hcomboDegree α β) (hall α β) hQ.le hQs hneg
    rwa [schurSzegoComp_C_mul_add_left] at hs
  have hdeg : a.natDegree + 1 = b.natDegree ∨ a.natDegree = b.natDegree := by
    rw [hadegree, hbdegree]
    rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
    · exact Or.inr hsame.symm
    · exact Or.inl hsucc.symm
  have hweakOr := strictInterl_of_allComboRealRooted hane hasplit hbne hbsplit houtall hdeg
  -- If `f` is constant, then `a` has no roots.
  have hno_of_f_const : f.natDegree = 0 → ∀ r, ¬ (a.IsRoot r ∧ b.IsRoot r) := by
    intro hfzero r hr
    have haroots : a.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hasplit, hadegree, hfzero]
    have := (mem_roots hane).mpr hr.1
    simp [haroots] at this
  by_cases hgzero : g.natDegree = 0
  · have hfzero : f.natDegree = 0 := by
      have := hfg.natDegree_le
      lia
    have haroots : a.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hasplit, hadegree, hfzero]
    have hbroots : b.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hbsplit, hbdegree, hgzero]
    refine ⟨?_, fun r hr hbr => hno_of_f_const hfzero r ⟨hr, hbr⟩⟩
    rcases hweakOr with hab | hba
    · exact hab
    · exact hba.of_reverse_of_roots_sum_le (by lia) (by simp [haroots, hbroots])
  have hW (t : ℝ) :=
    wronskian_eval_pos_of_strictInterl hfpos hgpos hfg hno (Nat.pos_of_ne_zero hgzero) t
  have hsourceSimple :=
    ObreschkoffConverseInternal.combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
      hall (fun t hz => by
        have hw := hW t
        simp only [ObreschkoffConverseInternal.wronskianPoly, eval_sub, eval_mul] at hz
        simp only [wronskian, eval_sub, eval_mul] at hw
        linarith)
  have houtno : ∀ r, ¬ (a.IsRoot r ∧ b.IsRoot r) := by
    intro r hr
    by_cases hfzero : f.natDegree = 0
    · exact hno_of_f_const hfzero r hr
    have hα : b.derivative.eval r ≠ 0 := hbsimple.eval_derivative_ne_zero hr.2
    have hβ : -a.derivative.eval r ≠ 0 := neg_ne_zero.mpr (hasimple.eval_derivative_ne_zero hr.1)
    have hinne : C (b.derivative.eval r) * f + C (-a.derivative.eval r) * g ≠ 0 := fun hz =>
      ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
        hfg.1.1 hfg.1.2 hno (Nat.pos_of_ne_zero hfzero) hα hβ hz
    have hinsimple := ((hsourceSimple _ _).resolve_left hinne).2
    have houtSimple := hasSimpleRoots_schurSzegoComp_of_roots_neg (hcomboDegree _ _) (hall _ _)
      hinsimple hQ hQs hQpos hneg
    rw [schurSzegoComp_C_mul_add_left] at houtSimple
    have houtRoot : (C (b.derivative.eval r) * a + C (-a.derivative.eval r) * b).IsRoot r := by
      simp only [IsRoot.def, eval_add, eval_mul, eval_C, hr.1.eq_zero, hr.2.eq_zero, mul_zero,
        add_zero]
    have hderne := houtSimple.eval_derivative_ne_zero houtRoot
    apply hderne
    simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, eval_add,
      eval_mul, eval_C]
    ring
  have hQ0 : 0 < Q.coeff 0 := coeff_pos_of_roots_neg hQs hQpos hneg (Nat.zero_le _)
  have hQ1 : 0 < Q.coeff 1 := coeff_pos_of_roots_neg hQs hQpos hneg (by lia)
  have hscale : 0 < Q.coeff 0 * Q.coeff 1 / (n : ℝ) :=
    div_pos (mul_pos hQ0 hQ1) (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have hWout : 0 < (wronskian a b).eval 0 := by
    rw [ha, hb, wronskian_schurSzegoComp_eval_zero hn]
    exact mul_pos hscale (hW 0)
  refine ⟨?_, fun r hr hbr => houtno r ⟨hr, hbr⟩⟩
  rcases hweakOr with hab | hba
  · exact hab
  · have hreverse := wronskian_eval_nonneg_of_strictInterl hapos hbpos hba 0
    simp only [wronskian, eval_sub, eval_mul] at hreverse hWout
    linarith

end RealRooted
