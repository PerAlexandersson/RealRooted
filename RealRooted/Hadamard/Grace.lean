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
  rw [coeff_apolarTwist, if_pos hj']
  have he : n + 1 - 1 - j = n - j := by simp [*]
  rw [he]
  have hnn : n - (n - j) = j := by lia
  rw [hnn]
  have hnegz : (-z) ^ (n - j) = (-1 : ℂ) ^ (n - j) * z ^ (n - j) := by rw [neg_pow]
  rw [hnegz, Nat.choose_symm hj']
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
    (binomialLift n (apolarTwist n z g)).HasRootIn (lowerHalf b) := by
  have hap : AreApolar n f (apolarTwist n z g) :=
    (areApolar_apolarTwist_iff n f g z).2 hcomp
  exact grace_apolarity_lowerHalf hf.le htw hap hroots

theorem exists_apolarTwist_root_of_grace_upperHalf {n : Nat} {b : ℝ}
    {f g : ℂ[X]} {z : ℂ}
    (hf : (binomialLift n f).natDegree = n)
    (htw : (binomialLift n (apolarTwist n z g)).natDegree = n)
    (hcomp : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * f.coeff k * g.coeff k * z ^ k = 0)
    (hroots : (binomialLift n f).RootsIn (upperHalf b)) :
    (binomialLift n (apolarTwist n z g)).HasRootIn (upperHalf b) := by
  have hap : AreApolar n f (apolarTwist n z g) :=
    (areApolar_apolarTwist_iff n f g z).2 hcomp
  exact grace_apolarity_upperHalf hf htw hap hroots

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
    rw [← hF, coeff_binomialLift, if_pos hk']
  have hPk : (p.map Complex.ofRealHom).coeff k = (Nat.choose n k : ℂ) * P₀.coeff k := by
    rw [← hP, coeff_binomialLift, if_pos hk']
  rw [coeff_map, Complex.ofRealHom_eq_coe] at hFk hPk
  have : (Nat.choose n k : ℂ) ≠ 0 := Nat.cast_choose_ne_zero (R := ℂ) hk'
  rw [Complex.ofRealHom_eq_coe, Complex.ofReal_div, Complex.ofReal_mul]
  push_cast
  grind

theorem coeff_n_binomialLift_apolarTwist (n : Nat) (z : ℂ) {F₀ f : ℂ[X]}
    (hF : binomialLift n F₀ = f) :
    (binomialLift n (apolarTwist n z F₀)).coeff n = f.coeff 0 := by
  rw [coeff_binomialLift, if_pos (le_refl n), coeff_apolarTwist, if_pos (le_refl n)]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, one_mul]
  rw [← hF, coeff_binomialLift, if_pos (Nat.zero_le n)]
  simp

theorem natDegree_binomialLift_apolarTwist (n : Nat) (z : ℂ) {F₀ f : ℂ[X]}
    (hF : binomialLift n F₀ = f) (hf0 : f.coeff 0 ≠ 0) :
    (binomialLift n (apolarTwist n z F₀)).natDegree = n := by
  refine le_antisymm (natDegree_binomialLift_le n _) ?_
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_n_binomialLift_apolarTwist n z hF]
  simp [*]

theorem pf_complex_root_nonpos_real {f : ℝ[X]} (hf : IsPFPolynomial f) (hf0 : f ≠ 0)
    {μ : ℂ} (hμ : (f.map Complex.ofRealHom).IsRoot μ) :
    μ.im = 0 ∧ μ.re ≤ 0 := by
  have hsplits : f.Splits := hf.eq_zero_or_splits.resolve_left hf0
  obtain ⟨r, hr⟩ : μ ∈ Complex.ofRealHom.range := hsplits.mem_range_of_isRoot hf0 hμ
  have hr_root : f.IsRoot r := by
    have hev : (f.map Complex.ofRealHom).eval μ = 0 := hμ
    rw [← hr, Polynomial.eval_map, Polynomial.eval₂_hom] at hev
    simp_all
  have : r ≤ 0 := hf.roots_nonpos r ((Polynomial.mem_roots hf0).mpr hr_root)
  rw [← hr]
  refine ⟨by simp [Complex.ofRealHom_eq_coe], ?_⟩
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_re]
  grind

theorem splits_complex_root_im_zero {p : ℝ[X]} (hp0 : p ≠ 0) (hsplit : p.Splits)
    {μ : ℂ} (hμ : (p.map Complex.ofRealHom).IsRoot μ) :
    μ.im = 0 := by
  obtain ⟨r, hr⟩ : μ ∈ Complex.ofRealHom.range := hsplit.mem_range_of_isRoot hp0 hμ
  rw [← hr]
  simp [Complex.ofRealHom_eq_coe]

theorem core_squeeze {n : Nat} {f p : ℝ[X]}
    (hf : IsPFPolynomial f) (hf0 : f ≠ 0) (hfdeg : f.natDegree = n)
    (hf00 : f.coeff 0 ≠ 0)
    (hp0 : p ≠ 0) (hpdeg : p.natDegree = n) (hsplit : p.Splits) :
    (schurSzegoComp n f p).Splits := by
  apply Polynomial.splits_of_all_roots_real
  intro z hz
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
  have hPmap : binomialLift n P₀ = p.map Complex.ofRealHom := hP
  have hRootsLower : (binomialLift n P₀).RootsIn (lowerHalf 0) := fun w hw => by
    rw [mem_lowerHalf]
    rw [hPmap] at hw
    have := splits_complex_root_im_zero hp0 hsplit hw
    simp [*]
  have hRootsUpper : (binomialLift n P₀).RootsIn (upperHalf 0) := fun w hw => by
    rw [mem_upperHalf]
    rw [hPmap] at hw
    have := splits_complex_root_im_zero hp0 hsplit hw
    simp [*]
  have hsum' : ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * P₀.coeff k * F₀.coeff k * z ^ k = 0 := by grind
  obtain ⟨w, hwroot, hwmem⟩ :=
    exists_apolarTwist_root_of_grace_lowerHalf hPdeg hTwdeg hsum' hRootsLower
  obtain ⟨w', hw'root, hw'mem⟩ :=
    exists_apolarTwist_root_of_grace_upperHalf hPdeg hTwdeg hsum' hRootsUpper
  rw [mem_lowerHalf] at hwmem
  rw [mem_upperHalf] at hw'mem
  have : f.coeff n ≠ 0 := by
    rw [← hfdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf0
  have : F₀.coeff n = (f.map Complex.ofRealHom).coeff n := by
    have : (f.map Complex.ofRealHom).coeff n = (Nat.choose n n : ℂ) * F₀.coeff n := by
      rw [← hF, coeff_binomialLift, if_pos (le_refl n)]
    simp [*]
  have hcoeff0 : (binomialLift n (apolarTwist n z F₀)).coeff 0 ≠ 0 := by
    rw [coeff_binomialLift, if_pos (Nat.zero_le n), coeff_apolarTwist, if_pos (Nat.zero_le n)]
    simp [*]
  have hwne : w ≠ 0 := by
    rintro rfl
    apply hcoeff0
    have : (binomialLift n (apolarTwist n z F₀)).eval 0 = 0 := hwroot
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [*]
  have hw'ne : w' ≠ 0 := by
    rintro rfl
    apply hcoeff0
    have : (binomialLift n (apolarTwist n z F₀)).eval 0 = 0 := hw'root
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [*]
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
  have hμre0 : μ.re < 0 := by
    rcases lt_or_eq_of_le hμre with h | h
    · grind
    · exfalso; apply hz0
      have hμ0 : μ = 0 :=
        Complex.ext (by rw [Complex.zero_re, ← h]) (by rw [hμim, Complex.zero_im])
      grind
  have hμ're0 : μ'.re < 0 := by
    rcases lt_or_eq_of_le hμ're with h | h
    · grind
    · exfalso; apply hz0
      have hμ'0 : μ' = 0 :=
        Complex.ext (by rw [Complex.zero_re, ← h]) (by rw [hμ'im, Complex.zero_im])
      grind
  have hzim : z.im = -(μ.re * w.im) := by
    rw [hzμ]
    simp [Complex.mul_im, hμim]
  have hzim' : z.im = -(μ'.re * w'.im) := by
    rw [hzμ']
    simp [Complex.mul_im, hμ'im]
  have : z.im ≤ 0 := by
    rw [hzim]
    nlinarith [hwmem, hμre0]
  have : 0 ≤ z.im := by
    rw [hzim']
    nlinarith [hw'mem, hμ're0]
  linarith




theorem reflect_schurSzegoComp (n : Nat) (f p : ℝ[X]) :
    reflect n (schurSzegoComp n f p) =
      schurSzegoComp n (reflect n f) (reflect n p) := by
  ext k
  rw [coeff_reflect]
  by_cases hk : k ≤ n
  · rw [revAt_le hk, coeff_schurSzegoComp_of_le (Nat.sub_le n k),
      coeff_schurSzegoComp_of_le hk, coeff_reflect, coeff_reflect,
      revAt_le hk, Nat.choose_symm hk]
  · rw [coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_le hk),
      revAt_eq_self_of_lt (Nat.lt_of_not_le hk),
      coeff_schurSzegoComp_eq_zero_of_lt (Nat.lt_of_not_le hk)]

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
        have := congrArg (Nat.cast (R := ℝ)) hnat
        grind
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
  · have hRHS : (derivative (reflect n q)).coeff (revAt (n - 1) k) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [revAt_eq_self_of_lt (by lia : n - 1 < k)]
      calc (derivative (reflect n q)).natDegree
          = (reflect n q).natDegree - 1 := (reflect n q).natDegree_derivative
        _ ≤ n - 1 := by
            have := Polynomial.natDegree_reflect_le (N := n) (p := q)
            simp_all
        _ < k := by lia
    rw [hRHS, mul_zero]
    by_cases k = n
    · simp [*]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by lia : q.natDegree < k)]; simp

theorem isPFPolynomial_of_X_mul {f₁ : ℝ[X]} (hp : IsPFPolynomial (X * f₁)) :
    IsPFPolynomial f₁ := by
  by_cases hf1 : f₁ = 0
  · simp_all
  refine IsPFPolynomial.of_realRooted_nonneg ?_ ?_
  · intro k
    have := hp.hasNonnegCoeffs (k + 1)
    simp_all
  · have hXsplit : (X * f₁).Splits := hp.eq_zero_or_splits.resolve_left (by
      simp [mul_eq_zero, X_ne_zero, hf1])
    simp_all

theorem schurSzegoComp_X_mul_right (n : Nat) (hn : 1 ≤ n) (f p₁ : ℝ[X]) :
    schurSzegoComp n f (X * p₁) =
      X * schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p₁ := by
  rw [schurSzegoComp_comm, schurSzegoComp_X_mul_left n hn p₁ f, schurSzegoComp_comm]

theorem splits_diagonalOperator_pred (n : Nat) (hn : 1 ≤ n) {q : ℝ[X]}
    (hq : q.natDegree ≤ n) (hsplit : q.Splits) :
    (diagonalOperator (fun k ↦ ((n : ℝ) - k) / n) q).Splits := by
  rw [diagonalOperator_pred_eq_reflect_derivative n hn q hq]
  refine (Polynomial.Splits.C (R := ℝ) _).mul ?_
  · have hrq : (reflect n q).Splits :=
      (DegreeDropReversal.splits_reflect_iff hq).mpr hsplit
    have hder : (derivative (reflect n q)).Splits := splits_derivative hrq
    refine DegreeDropReversal.splits_reflect_of_splits hder ?_
    rw [(reflect n q).natDegree_derivative]
    have := Polynomial.natDegree_reflect_le (N := n) (p := q)
    simp_all

theorem splits_schurSzegoComp_X_mul_left {n : Nat} (hn : 1 ≤ n) {f₁ p : ℝ[X]}
    (hinner : (schurSzegoComp (n - 1) f₁ (C (n : ℝ)⁻¹ * derivative p)).Splits) :
    (schurSzegoComp n (X * f₁) p).Splits := by
  rw [schurSzegoComp_X_mul_left n hn f₁ p]
  simp [*]

theorem splits_schurSzegoComp_X_mul_right {n : Nat} (hn : 1 ≤ n) {f p₁ : ℝ[X]}
    (hinner : (schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p₁).Splits) :
    (schurSzegoComp n f (X * p₁)).Splits := by
  rw [schurSzegoComp_X_mul_right n hn f p₁]
  simp [*]

theorem isPFPolynomial_reflect {n : Nat} {f : ℝ[X]} (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n) : IsPFPolynomial (reflect n f) := by
  rw [DegreeDropReversal.reflect_eq_X_pow_mul_reverse f hfdeg]
  have : IsPFPolynomial f.reverse := hf.reverse
  clear hf hfdeg
  induction (n - f.natDegree) with
  | zero => simp [*]
  | succ m ih =>
    rw [pow_succ, mul_comm (X ^ m) X, mul_assoc]
    exact ih.X_mul

theorem splits_schurSzegoComp_of_isPF (n : Nat) :
    ∀ (f p : ℝ[X]), IsPFPolynomial f → f ≠ 0 → f.natDegree ≤ n →
      p ≠ 0 → p.natDegree ≤ n → p.Splits →
      (schurSzegoComp n f p).Splits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f p hf hf0 hfdeg _ hp hsplit
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
        (Polynomial.Splits.C (R := ℝ) _).mul (splits_derivative hsplit)
      have hinner : (schurSzegoComp (n - 1) f.divX (C (n : ℝ)⁻¹ * derivative p)).Splits := by
        by_cases hz : schurSzegoComp (n - 1) f.divX (C (n : ℝ)⁻¹ * derivative p) = 0
        · rw [hz]; simp
        refine ih (n - 1) (by lia) f.divX (C (n : ℝ)⁻¹ * derivative p) hf1pf ?_ ?_ ?_ ?_
          hderiv_split
        · grind
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; lia
        · intro h
          apply hz
          rw [schurSzegoComp_comm, schurSzegoComp_eq_diagonalOperator, h]
          simp
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [p.natDegree_derivative]; simp [*])
      have := splits_schurSzegoComp_X_mul_left hn1 (f₁ := f.divX) (p := p) hinner
      grind
    by_cases hp00 : p.coeff 0 = 0
    · have hpX : p = X * p.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hp00
      have hp1split : p.divX.Splits := (DegreeDropReversal.splits_X_mul_iff).mp (hpX ▸ hsplit)
      have hderiv_pf : IsPFPolynomial (C (n : ℝ)⁻¹ * derivative f) :=
        (hf.derivative).const_mul (by positivity)
      have hderiv_split : (C (n : ℝ)⁻¹ * derivative f).Splits :=
        (Polynomial.Splits.C (R := ℝ) _).mul (splits_derivative
          (hf.eq_zero_or_splits.resolve_left hf0))
      have hinner : (schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p.divX).Splits := by
        by_cases hz : schurSzegoComp (n - 1) (C (n : ℝ)⁻¹ * derivative f) p.divX = 0
        · rw [hz]; simp
        refine ih (n - 1) (by lia) (C (n : ℝ)⁻¹ * derivative f) p.divX hderiv_pf ?_ ?_ ?_ ?_
          hp1split
        · intro h; rw [h] at hz; simp at hz
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [f.natDegree_derivative]; simp [*])
        · grind
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]; lia
      have := splits_schurSzegoComp_X_mul_right hn1 (f := f)
        (p₁ := p.divX) hinner
      grind
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
        (Polynomial.Splits.C (R := ℝ) _).mul (splits_derivative hRp_split)
      have hinner :
          (schurSzegoComp (n - 1) (reflect n f).divX
            (C (n : ℝ)⁻¹ * derivative (reflect n p))).Splits := by
        by_cases hz : schurSzegoComp (n - 1) (reflect n f).divX
            (C (n : ℝ)⁻¹ * derivative (reflect n p)) = 0
        · rw [hz]; simp
        refine ih (n - 1) (by lia) (reflect n f).divX
          (C (n : ℝ)⁻¹ * derivative (reflect n p)) hRf1_pf ?_ ?_ ?_ ?_ hderiv_split
        · grind
        · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hRf_deg]
        · intro h; rw [h] at hz; simp at hz
        · exact (Polynomial.natDegree_C_mul_le _ _).trans
            (by rw [(reflect n p).natDegree_derivative]; simp [*])
      have := splits_schurSzegoComp_X_mul_left hn1 (f₁ := (reflect n f).divX)
        (p := reflect n p) hinner
      grind

/-- Nonzero finite Schur--Szegő composition theorem.  This is the substantive
classical leaf: `f` is a nonzero PF polynomial, `p` is a nonzero real-rooted
polynomial, both have degree at most `n`, and the fixed-degree Schur--Szegő
composition is either zero or real-rooted. -/
theorem finiteSchurSzegoCompositionNonzero :
    finiteSchurSzegoCompositionNonzeroStatement :=
  fun {n} {f} {p} hf hf0 hfdeg hp0 hp hsplit =>
    Or.inr (splits_schurSzegoComp_of_isPF n f p hf hf0 hfdeg hp0 hp hsplit)

/-- Finite Schur--Szegő composition theorem. The degenerate cases (`f = 0` or
`p = 0`, where the composition vanishes) are discharged by
`finiteSchurSzegoComposition_of_nonzero`; the remaining classical content is
`finiteSchurSzegoCompositionNonzero`. -/
theorem finiteSchurSzegoComposition : finiteSchurSzegoCompositionStatement :=
  finiteSchurSzegoComposition_of_nonzero finiteSchurSzegoCompositionNonzero

/-- Directly applicable form of the finite Schur--Szegő composition theorem:
for a PF polynomial `f` and a real-rooted polynomial `p`, both of degree at most
`n`, the fixed-degree Schur--Szegő composition is either zero or real-rooted. -/
theorem schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
    {n : ℕ} {f p : ℝ[X]}
    (hf : IsPFPolynomial f)
    (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n)
    (hp : p.Splits) :
    schurSzegoComp n f p = 0 ∨ (schurSzegoComp n f p).Splits :=
  finiteSchurSzegoComposition hf hfdeg hpdeg hp

/-- Fixed-degree Schur--Szegő composition of two PF polynomials is again PF.

This is the zero-aware wrapper around
`schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial`; coefficient
nonnegativity is preserved directly by the composition. -/
theorem IsPFPolynomial.schurSzegoComp
    {n : ℕ} {f p : ℝ[X]} (hf : IsPFPolynomial f)
    (hp : IsPFPolynomial p) (hfdeg : f.natDegree ≤ n)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (schurSzegoComp n f p) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hf.hasNonnegCoeffs.schurSzegoComp hp.hasNonnegCoeffs)
  by_cases hp0 : p = 0
  · subst p
    simp
  · exact schurSzegoComp_eq_zero_or_splits_of_isPFPolynomial
      hf hfdeg hpdeg (hp.eq_zero_or_splits.resolve_left hp0)

/-- The backward direction of the finite Pólya--Schur theorem, obtained from the
finite Schur--Szegő composition theorem. -/
theorem finitePolyaSchurNonnegBackward : finitePolyaSchurNonnegBackwardStatement :=
  finitePolyaSchurNonnegBackward_of_schurSzegoNonzero finiteSchurSzegoCompositionNonzero

/-- Classical finite Pólya--Schur theorem (nonnegative-coefficient convention).
The only remaining analytic obligation is isolated in
`finiteSchurSzegoComposition`. -/
theorem finitePolyaSchur_nonneg : finitePolyaSchurNonnegStatement :=
  finitePolyaSchur_nonneg_of_schurSzegoNonzero finiteSchurSzegoCompositionNonzero
end RealRooted
