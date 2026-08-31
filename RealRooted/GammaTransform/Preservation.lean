import RealRooted.GammaTransform.RootMap

/-!
# Gamma-transform preservation

Real-rootedness, nonpositive-root, and minimal-degree transport for gamma
transforms.
-/

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted

lemma hasNonnegCoeffs_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    HasNonnegCoeffs (X - C r * (X + 1) ^ 2) := by
  have hneg : 0 ≤ -r := by simp_all
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using
    hasNonnegCoeffs_X.add
      (nonnegCoeffs_C_mul hneg (hasNonnegCoeffs_X_add_one.pow 2))

lemma isRealRooted_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    ((X - C r * (X + 1) ^ 2) ≠ 0 ∧ (X - C r * (X + 1) ^ 2).Splits) := by
  by_cases hr0 : r = 0
  · simp_all
  · set t : ℝ := -r with ht_def
    have hrlt : r < 0 := lt_of_le_of_ne hr hr0
    have ht_pos : 0 < t := by simp_all
    have hpoly :
        X - C r * (X + 1) ^ 2 = C t * X ^ 2 + C (2 * t + 1) * X + C t := by
      subst t
      ext n
      cases n with
      | zero =>
          simp [Polynomial.coeff_X_add_one_pow]
      | succ n =>
          cases n with
          | zero =>
              simp [Polynomial.coeff_X_add_one_pow]
              ring
          | succ n =>
              cases n with
              | zero =>
                  simp [Polynomial.coeff_X_add_one_pow, coeff_X, coeff_one]
              | succ n =>
                  have hpow0 : (((X + 1 : ℝ[X]) ^ 2).coeff (n + 3)) = 0 :=
                    Polynomial.coeff_eq_zero_of_natDegree_lt
                      (lt_of_le_of_lt (natDegree_X_add_one_pow_le 2) (by lia))
                  simp [coeff_X, coeff_one, hpow0]
    have hroots :
        (C t * X ^ 2 + C (2 * t + 1) * X + C t).roots =
          {(-(2 * t + 1) - Real.sqrt (t * 4 + 1)) / (2 * t),
            (-(2 * t + 1) + Real.sqrt (t * 4 + 1)) / (2 * t)} := by
      apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero' (a := t) (b := 2 * t + 1)
        (c := t) (ha := ne_of_gt ht_pos)).2
      grind
    rw [hpoly]
    refine ⟨?_, ?_⟩
    · intro hzero
      simp_all
    · rw [Polynomial.splits_iff_card_roots, hroots,
        Polynomial.natDegree_quadratic (ne_of_gt ht_pos)]
      simp

/-- The gamma transform preserves real-rootedness on nonnegative-coefficient
inputs whose degree fits the ambient floor `d / 2`. -/
theorem isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits) (hγnn : HasNonnegCoeffs γ) :
    ((gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits) := by
  let P : ℕ → Prop := fun n =>
    ∀ d : ℕ, ∀ γ : ℝ[X],
      γ.natDegree = n →
      γ.natDegree ≤ d / 2 →
      (γ ≠ 0 ∧ γ.Splits) →
      HasNonnegCoeffs γ →
      ((gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih d γ hγdeg_eq hbound hrr hnn
    by_cases hn0 : n = 0
    · have hγC : γ = C (γ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show γ.natDegree ≤ 0 by lia))
      rw [hγC]
      have hcoeff_ne : γ.coeff 0 ≠ 0 := by grind
      have hgt :
          gammaTransform d (C (γ.coeff 0)) = C (γ.coeff 0) * (X + 1) ^ d := by
        simpa [gammaBasisTerm_zero] using
          (gammaTransform_monomial d 0 (γ.coeff 0))
      rw [hgt]
      exact isRealRooted_C_mul
        (isRealRooted_X_add_one_pow d).1 (isRealRooted_X_add_one_pow d).2 hcoeff_ne
    · have hroots_pos : 0 < γ.roots.card := by
        rw [card_roots_of_splits hrr.2, hγdeg_eq]
        lia
      obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hr_root : γ.IsRoot r := (mem_roots hrr.1).mp hr_mem
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
      have hq' : γ = (X - C r) * q := by lia
      have hq_dvd : q ∣ γ := ⟨X - C r, by grind⟩
      have hq_ne : q ≠ 0 := by simp_all
      have hr_nonpos : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hrr.2 hnn r hr_mem
      have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hrr.1 hrr.2 hq_ne hq_dvd
      have hγ_pos : HasPosLeadingCoeff γ := hnn.pos_leadingCoeff hrr.1
      have hq_pos : HasPosLeadingCoeff q :=
        hasPosLeadingCoeff_of_X_sub_C_mul (r := r) (by simp_all)
      have hq_nn : HasNonnegCoeffs q :=
        hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
          hrr.1 hrr.2 hnn hq_rr.1 hq_rr.2 hq_pos hq_dvd
      have hqdeg_lt : q.natDegree < n := by
        have hmuldeg : γ.natDegree = q.natDegree + 1 := by
          rw [hq', natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          lia
        lia
      have hqbound : q.natDegree ≤ (d - 2) / 2 := by lia
      have hd : d = (d - 2) + 2 := by lia
      rw [hd, hq', gammaTransform_X_sub_C_mul_two hqbound r]
      have hgqf := isRealRooted_gammaQuadraticFactor hr_nonpos
      have hih := ih q.natDegree hqdeg_lt (d - 2) q rfl hqbound hq_rr hq_nn
      exact isRealRooted_mul hgqf.1 hgqf.2 hih.1 hih.2
  grind

theorem hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits) (hγnn : HasNonnegCoeffs γ) :
    HasRootsNonpos (gammaTransform d γ) := by
  intro r hr
  exact roots_nonpos_of_nonneg_coeffs
    (isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
      hγdeg hγ_ne hγ_splits hγnn).2
    (hasNonnegCoeffs_gammaTransform hγnn) r hr

theorem isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp_ne : (gammaTransform (2 * γ.natDegree) γ) ≠ 0)
    (hp_splits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ := by
  let P : ℕ → Prop := fun n =>
    ∀ γ : ℝ[X],
      γ.natDegree = n →
      ((gammaTransform (2 * n) γ) ≠ 0 ∧ (gammaTransform (2 * n) γ).Splits) →
      HasRootsNonpos (gammaTransform (2 * n) γ) →
      (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih δ hδdeg hpδ hpδ_nonpos
    have hδ0_main : δ ≠ 0 := fun hzero => by simp_all
    by_cases hn0 : n = 0
    · have hδC : δ = C (δ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show δ.natDegree ≤ 0 by lia))
      have hc : δ.coeff 0 ≠ 0 := by grind
      refine ⟨isRealRooted_of_deg_zero hδ0_main (by lia), ?_⟩
      intro r hr
      have : False := by
        rw [hδC] at hr
        simp at hr
      lia
    · by_cases hcoeff0 : δ.coeff 0 = 0
      · have hXdvd : X ∣ δ := Polynomial.X_dvd_iff.mpr hcoeff0
        obtain ⟨ζ, hδX⟩ := hXdvd
        have hζ0 : ζ ≠ 0 := by simp_all
        have hζdeg_succ : n = ζ.natDegree + 1 := by simp_all
        have hζdeg_lt : ζ.natDegree < n := by lia
        have hq_eq :
            gammaTransform (2 * n) δ = X * gammaTransform (2 * ζ.natDegree) ζ := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) (X * ζ) := by lia
            _ = gammaTransform (2 * ζ.natDegree + 2) (X * ζ) := by grind
            _ = X * gammaTransform (2 * ζ.natDegree) ζ :=
                  gammaTransform_X_mul_two (2 * ζ.natDegree) ζ
        have hq0 : gammaTransform (2 * ζ.natDegree) ζ ≠ 0 := by simp_all
        have hq_dvd :
            gammaTransform (2 * ζ.natDegree) ζ ∣ gammaTransform (2 * n) δ := by
          simp_all
        have hq_rr : ((gammaTransform (2 * ζ.natDegree) ζ) ≠ 0 ∧
          (gammaTransform (2 * ζ.natDegree) ζ).Splits) :=
          isRealRooted_of_dvd hpδ.1 hpδ.2 hq0 hq_dvd
        have hq_nonpos : HasRootsNonpos (gammaTransform (2 * ζ.natDegree) ζ) :=
          hasRootsNonpos_of_dvd hpδ_nonpos hpδ.1 hq_dvd hq0
        rcases (ih ζ.natDegree hζdeg_lt) ζ rfl hq_rr hq_nonpos with ⟨hζ_rr, hζ_nonpos⟩
        have hX_nonpos : HasRootsNonpos (X : ℝ[X]) := by
          simpa using hasRootsNonpos_X_sub_C (r := (0 : ℝ)) (by simp)
        refine ⟨?_, ?_⟩
        · simp_all
        · rw [hδX]
          exact hX_nonpos.mul hζ_nonpos (by simp) hζ_rr.1
      · have htop : δ.coeff n ≠ 0 := by
          have htop' : δ.coeff δ.natDegree ≠ 0 := by
            rw [Polynomial.coeff_natDegree]
            simp_all
          lia
        have htop_deg : (gammaTransform (2 * n) δ).natDegree = 2 * n :=
          Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
            (natDegree_gammaTransform_le (2 * n) δ)
            (by simp_all)
        have hroots_pos : 0 < (gammaTransform (2 * n) δ).roots.card := by
          rw [card_roots_of_splits hpδ.2, htop_deg]
          lia
        obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
        have hx_root : (gammaTransform (2 * n) δ).IsRoot x := (mem_roots hpδ.1).mp hx_mem
        have hx_nonpos : x ≤ 0 := hpδ_nonpos x hx_mem
        have hx_ne_neg_one : x ≠ -1 := by
          intro hx_eq
          have hx_root_neg_one : (gammaTransform (2 * n) δ).IsRoot (-1) := by lia
          exact htop ((gammaTransform_even_isRoot_neg_one_iff n δ).mp hx_root_neg_one)
        let y : ℝ := x / (1 + x) ^ 2
        have hy_nonpos : y ≤ 0 :=
          rootPullback_nonpos_of_gammaTransform hx_ne_neg_one hx_nonpos
        have hy_root : δ.IsRoot y := by
          dsimp [y]
          exact isRoot_gamma_of_isRoot_gammaTransform
            (d := 2 * n) (γ := δ) (by lia) hx_ne_neg_one hx_root
        obtain ⟨ε, hγ_fac0⟩ := dvd_iff_isRoot.mpr hy_root
        have hγ_fac : δ = (X - C y) * ε := by lia
        have hε0 : ε ≠ 0 := by simp_all
        have hεdeg_succ : n = ε.natDegree + 1 := by
          calc
            n = δ.natDegree := by lia
            _ = ((X - C y) * ε).natDegree := by lia
            _ = 1 + ε.natDegree := by
              rw [natDegree_mul (X_sub_C_ne_zero y) hε0, natDegree_X_sub_C]
            _ = ε.natDegree + 1 := by lia
        have hεdeg_lt : ε.natDegree < n := by lia
        have hq_eq :
            gammaTransform (2 * n) δ =
              (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε := by
          calc
            gammaTransform (2 * n) δ = gammaTransform (2 * n) ((X - C y) * ε) := by lia
            _ = gammaTransform (2 * ε.natDegree + 2) ((X - C y) * ε) := by grind
            _ = (X - C y * (X + 1) ^ 2) * gammaTransform (2 * ε.natDegree) ε :=
                  gammaTransform_X_sub_C_mul_two (γ := ε) (by lia) y
        have hq0 : gammaTransform (2 * ε.natDegree) ε ≠ 0 := by simp_all
        have hq_dvd :
            gammaTransform (2 * ε.natDegree) ε ∣ gammaTransform (2 * n) δ := by
          simp_all
        have hq_rr : ((gammaTransform (2 * ε.natDegree) ε) ≠ 0 ∧
          (gammaTransform (2 * ε.natDegree) ε).Splits) :=
          isRealRooted_of_dvd hpδ.1 hpδ.2 hq0 hq_dvd
        have hq_nonpos : HasRootsNonpos (gammaTransform (2 * ε.natDegree) ε) :=
          hasRootsNonpos_of_dvd hpδ_nonpos hpδ.1 hq_dvd hq0
        rcases (ih ε.natDegree hεdeg_lt) ε rfl hq_rr hq_nonpos with ⟨hε_rr, hε_nonpos⟩
        refine ⟨?_, ?_⟩
        · simp_all
        · rw [hγ_fac]
          exact (hasRootsNonpos_X_sub_C hy_nonpos).mul hε_nonpos (X_sub_C_ne_zero y) hε_rr.1
  grind

theorem isRealRooted_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp_ne : (gammaTransform (2 * γ.natDegree) γ) ≠ 0)
    (hp_splits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    (γ ≠ 0 ∧ γ.Splits) :=
  (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    hp_ne hp_splits hp_nonpos).1

theorem hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    {γ : ℝ[X]}
    (hp_ne : (gammaTransform (2 * γ.natDegree) γ) ≠ 0)
    (hp_splits : (gammaTransform (2 * γ.natDegree) γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform (2 * γ.natDegree) γ)) :
    HasRootsNonpos γ :=
  (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
    hp_ne hp_splits hp_nonpos).2

lemma hasRootsNonpos_gammaQuadraticFactor {r : ℝ} (hr : r ≤ 0) :
    HasRootsNonpos (X - C r * (X + 1) ^ 2) := by
  intro s hs
  exact roots_nonpos_of_nonneg_coeffs
    (isRealRooted_gammaQuadraticFactor hr).2
    (hasNonnegCoeffs_gammaQuadraticFactor hr)
    s hs

theorem isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hγ_ne : γ ≠ 0) (hγ_splits : γ.Splits) (hγ_nonpos : HasRootsNonpos γ) :
      ((gammaTransform d γ) ≠ 0 ∧
      (gammaTransform d γ).Splits) ∧
      HasRootsNonpos (gammaTransform d γ) := by
  let P : ℕ → Prop := fun n =>
    ∀ d : ℕ, ∀ γ : ℝ[X],
      γ.natDegree = n →
      γ.natDegree ≤ d / 2 →
      (γ ≠ 0 ∧ γ.Splits) →
      HasRootsNonpos γ →
      ((gammaTransform d γ) ≠ 0 ∧ (gammaTransform d γ).Splits) ∧
        HasRootsNonpos (gammaTransform d γ)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih d δ hδdeg hbound hδ_rr hδ_nonpos
    by_cases hn0 : n = 0
    · have hδC : δ = C (δ.coeff 0) := by
        simpa [hn0] using
          (Polynomial.eq_C_of_natDegree_le_zero (show δ.natDegree ≤ 0 by lia))
      have hcoeff_ne : δ.coeff 0 ≠ 0 := by grind
      have hgt :
          gammaTransform d (C (δ.coeff 0)) = C (δ.coeff 0) * (X + 1) ^ d := by
        simpa [gammaBasisTerm_zero] using
          (gammaTransform_monomial d 0 (δ.coeff 0))
      rw [hδC, hgt]
      refine ⟨isRealRooted_C_mul
        (isRealRooted_X_add_one_pow d).1 (isRealRooted_X_add_one_pow d).2 hcoeff_ne, ?_⟩
      intro r hr
      rw [roots_C_mul _ hcoeff_ne] at hr
      exact roots_nonpos_of_nonneg_coeffs
        (isRealRooted_X_add_one_pow d).2
        (hasNonnegCoeffs_X_add_one.pow d)
        r hr
    · have hroots_pos : 0 < δ.roots.card := by
        rw [card_roots_of_splits hδ_rr.2, hδdeg]
        lia
      obtain ⟨r, hr_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hr_root : δ.IsRoot r := (mem_roots hδ_rr.1).mp hr_mem
      have hr_nonpos : r ≤ 0 := hδ_nonpos r hr_mem
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr_root
      have hδq : δ = (X - C r) * q := by lia
      have hq_dvd : q ∣ δ := ⟨X - C r, by grind⟩
      have hq_ne : q ≠ 0 := by simp_all
      have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hδ_rr.1 hδ_rr.2 hq_ne hq_dvd
      have hq_nonpos : HasRootsNonpos q :=
        hasRootsNonpos_of_dvd hδ_nonpos hδ_rr.1 hq_dvd hq_ne
      have hqdeg_lt : q.natDegree < n := by
        have hmuldeg : δ.natDegree = q.natDegree + 1 := by
          rw [hδq, natDegree_mul (X_sub_C_ne_zero r) hq_ne, natDegree_X_sub_C]
          lia
        lia
      have hqbound : q.natDegree ≤ (d - 2) / 2 := by lia
      have hd : d = (d - 2) + 2 := by lia
      have ihq : ((gammaTransform (d - 2) q) ≠ 0 ∧
            (gammaTransform (d - 2) q).Splits) ∧
            HasRootsNonpos (gammaTransform (d - 2) q) :=
        ih q.natDegree hqdeg_lt (d - 2) q rfl hqbound hq_rr hq_nonpos
      rw [hd, hδq, gammaTransform_X_sub_C_mul_two hqbound r]
      refine ⟨?_, ?_⟩
      · exact isRealRooted_mul (isRealRooted_gammaQuadraticFactor hr_nonpos).1
          (isRealRooted_gammaQuadraticFactor hr_nonpos).2 ihq.1.1 ihq.1.2
      · exact (hasRootsNonpos_gammaQuadraticFactor hr_nonpos).mul ihq.2
          (isRealRooted_gammaQuadraticFactor hr_nonpos).1 ihq.1.1
  grind

lemma gammaTransform_even_shift (m k : ℕ) (γ : ℝ[X]) (hγ : γ.natDegree ≤ m) :
    gammaTransform (2 * (m + k)) γ =
      (X + 1) ^ (2 * k) * gammaTransform (2 * m) γ := by
  induction k with
  | zero =>
      lia
  | succ k ih =>
      have hhalf : (2 * (m + k)) / 2 = m + k := by lia
      have hstep : γ.natDegree ≤ (2 * (m + k)) / 2 := by lia
      calc
        gammaTransform (2 * (m + k.succ)) γ
            = gammaTransform (2 * (m + k) + 2) γ := by lia
        _ = (X + 1) ^ 2 * gammaTransform (2 * (m + k)) γ := by
              simpa using gammaTransform_pad_two (d := 2 * (m + k)) (γ := γ) hstep
        _ = (X + 1) ^ 2 * ((X + 1) ^ (2 * k) * gammaTransform (2 * m) γ) := by lia
        _ = ((X + 1) ^ 2 * (X + 1) ^ (2 * k)) * gammaTransform (2 * m) γ := by grind
        _ = (X + 1) ^ (2 + 2 * k) * gammaTransform (2 * m) γ := by grind
        _ = (X + 1) ^ (2 * (k + 1)) * gammaTransform (2 * m) γ := by lia

lemma gammaTransform_pad_to_minimal {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    gammaTransform d γ =
      (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by
  let m : ℕ := γ.natDegree
  let n : ℕ := d / 2
  have hm : m ≤ n := by lia
  have hshift :
      gammaTransform (2 * n) γ =
        (X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ := by
    have hshift' :=
      gammaTransform_even_shift (m := m) (k := n - m) (γ := γ) (by lia)
    simp_all
  rcases Nat.mod_two_eq_zero_or_one d with hd_even | hd_odd
  · grind
  · have hd : d = 2 * n + 1 := by lia
    have hpow : d - 2 * m = 1 + 2 * (n - m) := by lia
    calc
      gammaTransform d γ = gammaTransform (2 * n + 1) γ := by lia
      _ = (X + 1) * gammaTransform (2 * n) γ := gammaTransform_odd n γ
      _ = (X + 1) * ((X + 1) ^ (2 * (n - m)) * gammaTransform (2 * m) γ) := by lia
      _ = (X + 1) ^ (1 + 2 * (n - m)) * gammaTransform (2 * m) γ := by grind
      _ = (X + 1) ^ (d - 2 * m) * gammaTransform (2 * m) γ := by lia
      _ = (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ := by lia

lemma gammaTransform_minimal_dvd {d : ℕ} {γ : ℝ[X]}
    (hγdeg : γ.natDegree ≤ d / 2) :
    gammaTransform (2 * γ.natDegree) γ ∣ gammaTransform d γ := by
  refine ⟨(X + 1) ^ (d - 2 * γ.natDegree), ?_⟩
  calc
    gammaTransform d γ =
        (X + 1) ^ (d - 2 * γ.natDegree) * gammaTransform (2 * γ.natDegree) γ :=
      gammaTransform_pad_to_minimal (d := d) (γ := γ) hγdeg
    _ = gammaTransform (2 * γ.natDegree) γ * (X + 1) ^ (d - 2 * γ.natDegree) := by ring

theorem isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    {d : ℕ} {γ : ℝ[X]} (hγdeg : γ.natDegree ≤ d / 2)
    (hp_ne : (gammaTransform d γ) ≠ 0) (hp_splits : (gammaTransform d γ).Splits)
    (hp_nonpos : HasRootsNonpos (gammaTransform d γ)) :
    (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ := by
  let q : ℝ[X] := gammaTransform (2 * γ.natDegree) γ
  have hq0 : q ≠ 0 := by
    intro hq_zero
    have hγ0 : γ = 0 :=
      (gammaTransform_eq_zero_iff_of_natDegree_le
        (d := 2 * γ.natDegree) (γ := γ) (by lia)).mp (by lia)
    simp_all
  have hqdvd : q ∣ gammaTransform d γ := by
    simpa [q] using gammaTransform_minimal_dvd (d := d) (γ := γ) hγdeg
  have hq_rr : (q ≠ 0 ∧ q.Splits) := isRealRooted_of_dvd hp_ne hp_splits hq0 hqdvd
  have hq_nonpos : HasRootsNonpos q := hasRootsNonpos_of_dvd hp_nonpos hp_ne hqdvd hq0
  simpa [q] using
    (isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_minimal
      (γ := γ) hq_rr.1 hq_rr.2 hq_nonpos)

/-- Planning stub for the gamma-polynomial real-rootedness criterion.

The intended theorem is the standard equivalence: for a symmetric polynomial
`p` of ambient degree `d`, the gamma-polynomial is real-rooted with
nonpositive roots if and only if `p` is real-rooted with nonpositive roots.
The symmetry hypothesis is expressed using `IdTransform d p = p` so this file
can be built directly on top of `SymmetricDecomposition`. -/
def gammaRealRootedIffPolynomialRealRootedNonposStatement : Prop :=
  ∀ {d : ℕ} {p γ : ℝ[X]},
    γ.natDegree ≤ d / 2 →
    p.natDegree ≤ d →
    IdTransform d p = p →
    IsGammaExpansion d p γ →
    (((γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ) ↔
      ((p ≠ 0 ∧ p.Splits) ∧ HasRootsNonpos p))

theorem gammaRealRootedIffPolynomialRealRootedNonpos :
    gammaRealRootedIffPolynomialRealRootedNonposStatement := by
  intro d p γ hγdeg _ _ hGamma
  unfold IsGammaExpansion at hGamma
  subst p
  constructor
  · intro hγ
    exact isRealRooted_and_hasRootsNonpos_gammaTransform_of_isRealRooted_of_hasRootsNonpos
      (d := d) (γ := γ) hγdeg hγ.1.1 hγ.1.2 hγ.2
  · intro hp
    exact isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
      (d := d) (γ := γ) hγdeg hp.1.1 hp.1.2 hp.2



end RealRooted
