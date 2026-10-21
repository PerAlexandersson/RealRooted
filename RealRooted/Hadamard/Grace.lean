import RealRooted.AllCombo
import RealRooted.GraceHalfPlane
import RealRooted.Hadamard.Cubic
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Grace-theorem Schur--Szego proof

The apolar-twist identities, half-plane root argument, degree descent, and
checked finite Schur--Szego and finite Polya--Schur witnesses.
-/

theorem apolarEval_apolarTwist (n : Nat) (z : ℂ) (g : ℂ[X]) (w : ℂ) :
    apolarEval n (apolarTwist n z g) w =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℂ) * g.coeff i * (-z) ^ i * w ^ (n - i) := by
  unfold apolarEval
  rw [← Finset.sum_range_reflect
    (fun i ↦ (Nat.choose n i : ℂ) * g.coeff i * (-z) ^ i * w ^ (n - i)) (n + 1)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [coeff_apolarTwist, ite_eq_left hj']
  rw [show n + 1 - 1 - j = n - j by simp, show n - (n - j) = j by lia,
    neg_pow, Nat.choose_symm hj']
  ring

theorem apolarEval_apolarTwist_eq_mul (n : Nat) (z : ℂ) (g : ℂ[X]) {w : ℂ}
    (hw : w ≠ 0) :
    apolarEval n (apolarTwist n z g) w = w ^ n * apolarEval n g (-z / w) := by
  rw [apolarEval_apolarTwist, apolarEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hwi : w ^ (n - i) = w ^ n / w ^ i := by
    rw [eq_div_iff (pow_ne_zero i hw), ← pow_add, Nat.sub_add_cancel hi']
  rw [hwi, div_pow]
  grind

theorem isRoot_binomialLift_apolarTwist_iff (n : Nat) (z : ℂ) (g : ℂ[X]) {w : ℂ}
    (hw : w ≠ 0) :
    (binomialLift n (apolarTwist n z g)).IsRoot w ↔
      (binomialLift n g).IsRoot (-z / w) := by
  simp only [Polynomial.IsRoot, eval_binomialLift]
  rw [apolarEval_apolarTwist_eq_mul n z g hw]
  simp [*]

theorem exists_apolarTwist_root_of_grace_lowerHalf {n : Nat} {b : ℝ}
    {f g : ℂ[X]} {z : ℂ}
    (hf : (binomialLift n f).natDegree = n)
    (htw : (binomialLift n (apolarTwist n z g)).natDegree = n)
    (hcomp : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * f.coeff k * g.coeff k * z ^ k = 0)
    (hroots : (binomialLift n f).RootsIn (lowerHalf b)) :
    (binomialLift n (apolarTwist n z g)).HasRootIn (lowerHalf b) :=
  grace_apolarity_lowerHalf hf.le htw ((areApolar_apolarTwist_iff n f g z).2 hcomp) hroots

theorem exists_apolarTwist_root_of_grace_upperHalf {n : Nat} {b : ℝ}
    {f g : ℂ[X]} {z : ℂ}
    (hf : (binomialLift n f).natDegree = n)
    (htw : (binomialLift n (apolarTwist n z g)).natDegree = n)
    (hcomp : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * f.coeff k * g.coeff k * z ^ k = 0)
    (hroots : (binomialLift n f).RootsIn (upperHalf b)) :
    (binomialLift n (apolarTwist n z g)).HasRootIn (upperHalf b) :=
  grace_apolarity_upperHalf hf htw ((areApolar_apolarTwist_iff n f g z).2 hcomp) hroots

theorem eval_map_schurSzegoComp_eq_sum (n : Nat) (f p : ℝ[X])
    {F₀ P₀ : ℂ[X]}
    (hF : binomialLift n F₀ = f.map Complex.ofRealHom)
    (hP : binomialLift n P₀ = p.map Complex.ofRealHom)
    (z : ℂ) :
    ((schurSzegoComp n f p).map Complex.ofRealHom).eval z =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * F₀.coeff k * P₀.coeff k * z ^ k := by
  rw [Polynomial.eval_eq_sum_range' (n := n + 1)
    (Nat.lt_succ_of_le ((natDegree_map_le).trans (natDegree_schurSzegoComp_le n f p)))]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [coeff_map, coeff_schurSzegoComp_of_le hk']
  have hFk : (f.map Complex.ofRealHom).coeff k = (Nat.choose n k : ℂ) * F₀.coeff k := by
    rw [← hF, coeff_binomialLift, ite_eq_left hk']
  have hPk : (p.map Complex.ofRealHom).coeff k = (Nat.choose n k : ℂ) * P₀.coeff k := by
    rw [← hP, coeff_binomialLift, ite_eq_left hk']
  rw [coeff_map, Complex.ofRealHom_eq_coe] at hFk hPk
  have : (Nat.choose n k : ℂ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℂ) hk'
  rw [Complex.ofRealHom_eq_coe, Complex.ofReal_div, Complex.ofReal_mul]
  push_cast
  grind

theorem coeff_n_binomialLift_apolarTwist (n : Nat) (z : ℂ) {F₀ f : ℂ[X]}
    (hF : binomialLift n F₀ = f) :
    (binomialLift n (apolarTwist n z F₀)).coeff n = f.coeff 0 := by
  simpa [coeff_binomialLift, coeff_apolarTwist] using congrArg (fun p => p.coeff 0) hF

theorem natDegree_binomialLift_apolarTwist (n : Nat) (z : ℂ) {F₀ f : ℂ[X]}
    (hF : binomialLift n F₀ = f) (hf0 : f.coeff 0 ≠ 0) :
    (binomialLift n (apolarTwist n z F₀)).natDegree = n := by
  refine le_antisymm (natDegree_binomialLift_le n _) (Polynomial.le_natDegree_of_ne_zero ?_)
  rw [coeff_n_binomialLift_apolarTwist n z hF]
  exact hf0

theorem pf_complex_root_nonpos_real {f : ℝ[X]} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    {μ : ℂ} (hμ : (f.map Complex.ofRealHom).IsRoot μ) :
    μ.im = 0 ∧ μ.re ≤ 0 := by
  have hsplits : f.Splits := hf.eq_zero_or_splits.resolve_left hf0
  obtain ⟨r, rfl⟩ : μ ∈ Complex.ofRealHom.range := hsplits.mem_range_of_isRoot hf0 hμ
  have hr_root : f.IsRoot r := hμ.of_map Complex.ofReal_injective
  have : r ≤ 0 := hf.roots_nonpos r ((Polynomial.mem_roots hf0).mpr hr_root)
  simpa [Complex.ofRealHom_eq_coe] using this

theorem splits_complex_root_im_zero {p : ℝ[X]} (hp0 : p ≠ 0) (hsplit : p.Splits)
    {μ : ℂ} (hμ : (p.map Complex.ofRealHom).IsRoot μ) :
    μ.im = 0 := by
  obtain ⟨r, rfl⟩ : μ ∈ Complex.ofRealHom.range := hsplit.mem_range_of_isRoot hp0 hμ
  simp [Complex.ofRealHom_eq_coe]

theorem core_squeeze {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree = n)
    (hf00 : f.coeff 0 ≠ 0)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree = n) (hsplit : p.Splits) :
    (schurSzegoComp n f p).Splits := by
  refine Polynomial.splits_of_all_roots_real fun z hz => ?_
  obtain ⟨F₀, hF⟩ := exists_binomialLift_eq (f.map Complex.ofRealHom)
    (le_of_eq (by rw [natDegree_map_eq_of_injective Complex.ofReal_injective, hfdeg]))
  obtain ⟨P₀, hP⟩ := exists_binomialLift_eq (p.map Complex.ofRealHom)
    (le_of_eq (by rw [natDegree_map_eq_of_injective Complex.ofReal_injective, hpdeg]))
  have : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * F₀.coeff k * P₀.coeff k * z ^ k = 0 := by
    rw [← eval_map_schurSzegoComp_eq_sum n f p hF hP z]
    simp [*]
  by_cases hz0 : z = 0
  · simp [*]
  have hPdeg : (binomialLift n P₀).natDegree = n := by simp [*]
  have hf00c : (f.map Complex.ofRealHom).coeff 0 ≠ 0 := by simp [*]
  have hTwdeg : (binomialLift n (apolarTwist n z F₀)).natDegree = n :=
    natDegree_binomialLift_apolarTwist n z hF hf00c
  have hRootsLower : (binomialLift n P₀).RootsIn (lowerHalf 0) := fun w hw => by
    rw [hP] at hw
    simpa only [mem_lowerHalf] using (splits_complex_root_im_zero hp0 hsplit hw).le
  have hRootsUpper : (binomialLift n P₀).RootsIn (upperHalf 0) := fun w hw => by
    rw [hP] at hw
    simpa only [mem_upperHalf] using (splits_complex_root_im_zero hp0 hsplit hw).ge
  have hsum' : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * P₀.coeff k * F₀.coeff k * z ^ k = 0 := by grind
  obtain ⟨w, hwroot, hwmem⟩ :=
    exists_apolarTwist_root_of_grace_lowerHalf hPdeg hTwdeg hsum' hRootsLower
  obtain ⟨w', hw'root, hw'mem⟩ :=
    exists_apolarTwist_root_of_grace_upperHalf hPdeg hTwdeg hsum' hRootsUpper
  rw [mem_lowerHalf] at hwmem
  rw [mem_upperHalf] at hw'mem
  have hfn : f.coeff n ≠ 0 := hfdeg ▸ Polynomial.leadingCoeff_ne_zero.mpr hf0
  have hFn : F₀.coeff n = (f.map Complex.ofRealHom).coeff n := by
    simpa [coeff_binomialLift] using congrArg (fun q => q.coeff n) hF
  have hcoeff0 : (binomialLift n (apolarTwist n z F₀)).coeff 0 ≠ 0 := by
    rw [coeff_binomialLift, ite_eq_left (Nat.zero_le n), coeff_apolarTwist,
      ite_eq_left (Nat.zero_le n)]
    simp [*]
  have root_ne_zero {u : ℂ} (hu : (binomialLift n (apolarTwist n z F₀)).IsRoot u) :
      u ≠ 0 := by
    rintro rfl
    exact hcoeff0 (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hu)
  have hwne := root_ne_zero hwroot
  have hw'ne := root_ne_zero hw'root
  have hμ : (binomialLift n F₀).IsRoot (-z / w) :=
    (isRoot_binomialLift_apolarTwist_iff n z F₀ hwne).mp hwroot
  have hμ' : (binomialLift n F₀).IsRoot (-z / w') :=
    (isRoot_binomialLift_apolarTwist_iff n z F₀ hw'ne).mp hw'root
  rw [hF] at hμ hμ'
  obtain ⟨hμim, hμre⟩ := pf_complex_root_nonpos_real hf hf0 hμ
  obtain ⟨hμ'im, hμ're⟩ := pf_complex_root_nonpos_real hf hf0 hμ'
  set μ := -z / w with hμdef
  set μ' := -z / w' with hμ'def
  have hzμ : z = -(μ * w) := by simp [*]
  have hzμ' : z = -(μ' * w') := by grind
  have re_neg {u : ℂ} (huim : u.im = 0) (hure : u.re ≤ 0) (hu : u ≠ 0) : u.re < 0 :=
    lt_of_le_of_ne hure fun h => hu <| Complex.ext
      (by simpa only [Complex.zero_re] using h) (by simpa only [Complex.zero_im] using huim)
  have hμre0 := re_neg hμim hμre (fun h => hz0 (by simp [hzμ, h]))
  have hμ're0 := re_neg hμ'im hμ're (fun h => hz0 (by simp [hzμ', h]))
  have hzim : z.im = -(μ.re * w.im) := by
    simp [hzμ, Complex.mul_im, hμim]
  have hzim' : z.im = -(μ'.re * w'.im) := by
    simp [hzμ', Complex.mul_im, hμ'im]
  have : z.im ≤ 0 := by rw [hzim]; nlinarith [hwmem, hμre0]
  have : 0 ≤ z.im := by rw [hzim']; nlinarith [hw'mem, hμ're0]
  linarith

theorem schurSzegoComp_X_mul_left (n : Nat) (hn : 1 ≤ n) (f₁ p : ℝ[X]) :
    schurSzegoComp n (X * f₁) p =
      X * schurSzegoComp (n - 1) f₁ (C (n : ℝ)⁻¹ * derivative p) := by
  ext k
  rcases k with _ | k
  · rw [coeff_schurSzegoComp_of_le (Nat.zero_le n), coeff_X_mul_zero, zero_mul,
      zero_div, coeff_X_mul_zero]
  · rw [coeff_X_mul]
    by_cases hk : k ≤ n - 1
    · rw [coeff_schurSzegoComp_of_le (by lia : k + 1 ≤ n),
        coeff_schurSzegoComp_of_le hk, coeff_X_mul, coeff_C_mul, coeff_derivative]
      have : ((n - 1).choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hk
      have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
      have : (n.choose (k + 1) : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) (by lia)
      have hnat : n * (n - 1).choose k = n.choose (k + 1) * (k + 1) := by
        have := Nat.add_one_mul_choose_eq (n - 1) k
        simp_all
      have : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) = (n : ℝ) * ((n - 1).choose k : ℝ) := by
        exact_mod_cast hnat.symm
      grind
    · rw [coeff_schurSzegoComp_eq_zero_of_lt (by lia : n < k + 1),
        coeff_schurSzegoComp_eq_zero_of_lt (by lia : n - 1 < k)]

theorem schurSzegoComp_eq_diagonalOperator_pred (n : Nat) (hn : 1 ≤ n) (f p : ℝ[X])
    (hpn : p.coeff n = 0) :
    schurSzegoComp n f p =
      diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) (schurSzegoComp (n - 1) f p) := by
  ext k
  rw [coeff_diagonalOperator]
  by_cases hk : k ≤ n - 1
  · rw [coeff_schurSzegoComp_of_le (by lia : k ≤ n), coeff_schurSzegoComp_of_le hk]
    have : ((n - 1).choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) hk
    have : (n.choose k : ℝ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℝ) (by lia)
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hnat : (n - 1).choose k * n = n.choose k * (n - k) := by
      have := Nat.choose_mul_succ_eq (n - 1) k
      simp_all
    have : ((n - 1).choose k : ℝ) * (n : ℝ) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
      have := congrArg (Nat.cast (R := ℝ)) hnat
      push_cast [Nat.cast_sub (by lia : k ≤ n)] at this
      assumption
    grind
  · rw [coeff_schurSzegoComp_eq_zero_of_lt (by lia : n - 1 < k)]
    by_cases hkn : k = n
    · rw [hkn, coeff_schurSzegoComp_of_le (le_refl n)]
      simp [hpn]
    · rw [coeff_schurSzegoComp_eq_zero_of_lt (by lia : n < k), mul_zero]

theorem diagonalOperator_pred_eq_reflect_derivative (n : Nat) (hn : 1 ≤ n)
    (q : ℝ[X]) (hq : q.natDegree ≤ n) :
    diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) q =
      C (n : ℝ)⁻¹ * reflect (n - 1) (derivative (reflect n q)) := by
  ext k
  rw [coeff_diagonalOperator, coeff_C_mul, coeff_reflect]
  by_cases hk : k ≤ n - 1
  · rw [revAt_le hk, coeff_derivative, coeff_reflect, revAt_le (by lia : n - 1 - k + 1 ≤ n)]
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hidx : n - (n - 1 - k + 1) = k := by lia
    rw [hidx]
    have : ((n - 1 - k : ℕ) : ℝ) + 1 = (n : ℝ) - k := by
      push_cast [Nat.cast_sub (by assumption : k ≤ n - 1), Nat.cast_sub hn]
      ring
    grind
  · have hRHS : (derivative (reflect n q)).coeff (revAt (n - 1) k) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt <| by
        rw [revAt_eq_self_of_lt (by lia : n - 1 < k), (reflect n q).natDegree_derivative]
        have := Polynomial.natDegree_reflect_le (N := n) (p := q)
        simp_all
        lia
    rw [hRHS, mul_zero]
    by_cases k = n
    · simp [*]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < k)]; simp

theorem isPFPolynomial_of_X_mul {f₁ : ℝ[X]} (hp : IsPFPolynomial (X * f₁)) :
    IsPFPolynomial f₁ := by
  rcases eq_or_ne f₁ 0 with rfl | hf₁
  · simpa using hp
  have hX₁ : X * f₁ ≠ 0 := mul_ne_zero X_ne_zero hf₁
  exact IsPFPolynomial.of_realRooted_nonneg
    (fun k => by simpa using hp.hasNonnegCoeffs (k + 1))
    (isRealRooted_of_X_mul hX₁ (hp.eq_zero_or_splits.resolve_left hX₁)).2

theorem schurSzegoComp_X_mul_right (n : Nat) (hn : 1 ≤ n) (f p₁ : ℝ[X]) :
    schurSzegoComp n f (X * p₁) =
      X * schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p₁ := by
  simpa [schurSzegoComp_comm] using schurSzegoComp_X_mul_left n hn p₁ f

theorem splits_diagonalOperator_pred (n : Nat) (hn : 1 ≤ n) {q : ℝ[X]}
    (hq : q.natDegree ≤ n) (hsplit : q.Splits) :
    (diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) q).Splits := by
  rw [diagonalOperator_pred_eq_reflect_derivative n hn q hq]
  refine (Polynomial.Splits.C (R := ℝ) _).mul <|
    DegreeDropReversal.splits_reflect_of_splits
      (Polynomial.Splits.derivative ((DegreeDropReversal.splits_reflect_iff hq).2 hsplit)) ?_
  rw [(reflect n q).natDegree_derivative]
  simpa [max_eq_left hq] using
    Nat.sub_le_sub_right (Polynomial.natDegree_reflect_le (N := n) (p := q)) 1

theorem splits_schurSzegoComp_X_mul_left {n : Nat} (hn : 1 ≤ n) {f₁ p : ℝ[X]}
    (hinner : (schurSzegoComp (n - 1) f₁ (C (n : ℝ)⁻¹ * derivative p)).Splits) :
    (schurSzegoComp n (X * f₁) p).Splits := by
  rw [schurSzegoComp_X_mul_left n hn]
  exact Polynomial.Splits.mul Polynomial.Splits.X hinner

theorem splits_schurSzegoComp_X_mul_right {n : Nat} (hn : 1 ≤ n) {f p₁ : ℝ[X]}
    (hinner : (schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p₁).Splits) :
    (schurSzegoComp n f (X * p₁)).Splits := by
  rw [schurSzegoComp_X_mul_right n hn]
  exact Polynomial.Splits.mul Polynomial.Splits.X hinner

theorem isPFPolynomial_reflect {n : Nat} {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n) : IsPFPolynomial (reflect n f) := by
  rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse f hfdeg]
  exact (isPFPolynomial_X_pow _).mul hf.reverse

theorem splits_schurSzegoComp_of_isPF (n : Nat) :
    ∀ (f p : ℝ[X]), IsPFPolynomial f → f ≠ 0 → f.natDegree ≤ n →
      p ≠ 0 → p.natDegree ≤ n → p.Splits →
      (schurSzegoComp n f p).Splits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f p hf hf0 hfdeg hp0 hp hsplit
    by_cases htriv : (schurSzegoComp n f p).natDegree ≤ 1
    · by_cases hz : schurSzegoComp n f p = 0
      · simp [*]
      · exact (isRealRooted_of_natDegree_le_one hz htriv).2
    have hn1 : 1 ≤ n := by
      by_contra h
      push Not at h
      interval_cases n
      · exact htriv ((natDegree_schurSzegoComp_le 0 f p).trans (by simp [*]))
    by_cases hf00 : f.coeff 0 = 0
    · have hfX : f = X * f.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hf00
      have hf1pf : IsPFPolynomial f.divX := isPFPolynomial_of_X_mul (hfX ▸ hf)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative p).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (Polynomial.Splits.derivative hsplit)
      have hinner : (schurSzegoComp (n - 1) f.divX (C (n : ℝ)⁻¹ * derivative p)).Splits := by
        by_cases hq0 : C (n : ℝ)⁻¹ * derivative p = 0
        · simp [hq0]
        refine ih (n - 1) (by lia) f.divX (C (n : ℝ)⁻¹ * derivative p) hf1pf
          (fun h => hf0 (by rw [hfX, h]; simp)) ?_ hq0 ?_ hderiv_split
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; lia
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [p.natDegree_derivative]; simp [*])
      rw [hfX]
      exact splits_schurSzegoComp_X_mul_left hn1 hinner
    by_cases hp00 : p.coeff 0 = 0
    · have hpX : p = X * p.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hp00
      have hp1split : p.divX.Splits := (DegreeDropReversal.splits_X_mul_iff).mp (hpX ▸ hsplit)
      have hderiv_pf : IsPFPolynomial (C (n : ℝ)⁻¹ * derivative f) :=
        (hf.derivative).const_mul (by positivity)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative f).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (Polynomial.Splits.derivative
          (hf.eq_zero_or_splits.resolve_left hf0))
      have hinner : (schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p.divX).Splits := by
        by_cases hq0 : C (n : ℝ)⁻¹ * derivative f = 0
        · simp [hq0]
        refine ih (n - 1) (by lia) (C (n : ℝ)⁻¹ * derivative f) p.divX hderiv_pf
          hq0 ?_ (fun h => hp0 (by rw [hpX, h]; simp)) ?_ hp1split
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [f.natDegree_derivative]; simp [*])
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; lia
      rw [hpX]
      exact splits_schurSzegoComp_X_mul_right hn1 hinner
    by_cases hlt : f.natDegree < n ∧ p.natDegree < n
    · have hpn : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt.2
      rw [schurSzegoComp_eq_diagonalOperator_pred n hn1 f p hpn]
      refine splits_diagonalOperator_pred n hn1 ?_ ?_
      · exact (natDegree_schurSzegoComp_le (n - 1) f p).trans (by simp [*])
      · grind
    push Not at hlt
    have hRf_pf : IsPFPolynomial (reflect n f) := isPFPolynomial_reflect hf hfdeg
    have hRf_deg : (reflect n f).natDegree = n :=
      DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hfdeg hf00
    have hRf_ne : reflect n f ≠ 0 := by simp [*]
    have hRp_deg : (reflect n p).natDegree = n :=
      DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hp hp00
    have hRp_ne : reflect n p ≠ 0 := by simp [*]
    have hRp_split : (reflect n p).Splits :=
      DegreeDropReversal.splits_reflect_of_splits hsplit hp
    suffices hcore : (schurSzegoComp n (reflect n f) (reflect n p)).Splits by
      rw [← reflect_schurSzegoComp] at hcore
      exact (DegreeDropReversal.splits_reflect_iff (natDegree_schurSzegoComp_le n f p)).mp hcore
    by_cases hfn : f.natDegree = n
    · have hRf_coeff0 : (reflect n f).coeff 0 ≠ 0 := by
        rw [coeff_reflect, revAt_zero, ← hfn]
        exact Polynomial.leadingCoeff_ne_zero.mpr hf0
      exact core_squeeze hRf_pf hRf_ne hRf_deg hRf_coeff0 hRp_ne hRp_deg hRp_split
    · have hRf_coeff0 : (reflect n f).coeff 0 = 0 := by
        rw [coeff_reflect, revAt_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
      have hRfX : reflect n f = X * (reflect n f).divX :=
        DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hRf_coeff0
      have hRf1_pf : IsPFPolynomial (reflect n f).divX :=
        isPFPolynomial_of_X_mul (hRfX ▸ hRf_pf)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative (reflect n p)).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (Polynomial.Splits.derivative hRp_split)
      have hinner :
          (schurSzegoComp (n - 1) (reflect n f).divX
            (C (n : ℝ)⁻¹ * derivative (reflect n p))).Splits := by
        by_cases hq0 : C (n : ℝ)⁻¹ * derivative (reflect n p) = 0
        · simp [hq0]
        refine ih (n - 1) (by lia) (reflect n f).divX
          (C (n : ℝ)⁻¹ * derivative (reflect n p)) hRf1_pf
          (fun h => hRf_ne (by rw [hRfX, h]; simp)) ?_ hq0 ?_ hderiv_split
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hRf_deg]
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [(reflect n p).natDegree_derivative]; simp [*])
      rw [hRfX]
      exact splits_schurSzegoComp_X_mul_left hn1 hinner

/-- Nonzero finite Schur--Szegő composition theorem: `f` is a nonzero PF
polynomial, `p` is a nonzero real-rooted polynomial, both have degree at most
`n`, and the fixed-degree Schur--Szegő composition is either zero or
real-rooted. -/
theorem finiteSchurSzegoCompositionNonzero {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree ≤ n)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  Or.inr (splits_schurSzegoComp_of_isPF n f p hf hf0 hfdeg hp0 hpdeg hsplit)

/-- **Finite Schur--Szegő composition theorem.**

If `f` is a PF polynomial (only real, nonpositive zeros) of degree at most `n`
and `p` has only real zeros, then their fixed-degree Schur--Szegő composition
`schurSzegoComp n f p` again has only real zeros, unless it vanishes
identically.  The degenerate cases `f = 0` and `p = 0` make the composition
vanish; the remaining content is `finiteSchurSzegoCompositionNonzero`. -/
theorem finiteSchurSzegoComposition {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) (hsplit : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits := by
  by_cases hf0 : f = 0
  · simp [hf0, schurSzegoComp_zero_left]
  by_cases hp0 : p = 0
  · simp [hp0, schurSzegoComp_zero_right]
  exact finiteSchurSzegoCompositionNonzero hf hf0 hfdeg hp0 hpdeg hsplit

/-- Fixed-degree Schur--Szegő composition of two PF polynomials is again PF.

This is the zero-aware wrapper around `finiteSchurSzegoComposition`; coefficient
nonnegativity is preserved directly by the composition. -/
theorem IsPFPolynomial.schurSzegoComp
    {n : ℕ} {f p : ℝ[X]} (hf : IsPFPolynomial f)
    (hp : IsPFPolynomial p) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (schurSzegoComp n f p) := by
  refine IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hf.hasNonnegCoeffs.schurSzegoComp hp.hasNonnegCoeffs) ?_
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  exact finiteSchurSzegoComposition hf hfdeg hpdeg (hp.eq_zero_or_splits.resolve_left hp0)

/-- The backward direction of the finite Pólya--Schur theorem, obtained from the
finite Schur--Szegő composition theorem: the diagonal operator attached to
`gamma` acting on a polynomial `p` of degree at most `n` is exactly the
Schur--Szegő composition of the PF Jensen polynomial of `gamma` with `p`. -/
theorem isFiniteMultiplierSequence_of_isPFPolynomial_jensenPolynomial
    {n : ℕ} {gamma : ℕ → ℝ}
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFiniteMultiplierSequence n gamma := by
  intro p hp hsplit
  simpa [← schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp] using
    finiteSchurSzegoComposition hjensen (natDegree_jensenPolynomial_le n gamma) hp hsplit

/-- **Finite Pólya--Schur theorem** (nonnegative-coefficient convention): a nonnegative
diagonal sequence preserves real-rootedness up to degree `n` if and only if its degree-`n`
Jensen polynomial is PF. -/
theorem finitePolyaSchur_nonneg {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFiniteMultiplierSequence n gamma ↔ IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence hgamma,
    isFiniteMultiplierSequence_of_isPFPolynomial_jensenPolynomial⟩

/-- PF-preservation form of finite Pólya--Schur: for a nonnegative diagonal
sequence, preserving the PF cone up to degree `n` is equivalent to the degree
`n` Jensen polynomial being PF. -/
theorem isFinitePFMultiplierSequence_iff_jensenPolynomial {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k) :
    IsFinitePFMultiplierSequence n gamma ↔ IsPFPolynomial (jensenPolynomial n gamma) :=
  ⟨isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence, fun hjensen =>
    isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
      (isFiniteMultiplierSequence_of_isPFPolynomial_jensenPolynomial hjensen)⟩

end RealRooted
