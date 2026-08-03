import RealRooted.Polarization

/-!
# Rectangular polarization

This file defines the two-block polarization of `y ^ m * p(x * y)` used by
Gribinski--Marcus and proves that it is upper-half-plane stable when `p(x * y)`
is stable. The proof polarizes the right-variable slice and then the
left-variable slice.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

/-- The polarization of `y ^ m * p(x * y)` in `n` left variables and `m + n`
right variables. -/
def rectangularPolarization (m n : ℕ) (p : ℂ[X]) :
    MvPolynomial (Sum (Fin n) (Fin (m + n))) ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    MvPolynomial.C
        (p.coeff k / (n.choose k : ℂ) / ((m + n).choose (m + k) : ℂ)) *
      MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin n) ℂ k) *
      MvPolynomial.rename Sum.inr
        (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k))

/-- The rectangular polarization is multiaffine in both variable blocks. -/
theorem isMultiaffine_rectangularPolarization (m n : ℕ) (p : ℂ[X]) :
    MvPolynomial.IsMultiaffine (rectangularPolarization m n p) := by
  unfold rectangularPolarization
  apply MvPolynomial.IsMultiaffine.sum
  intro k hk
  rw [mul_assoc]
  apply MvPolynomial.IsMultiaffine.C_mul
  apply MvPolynomial.IsMultiaffine.mul_of_disjoint_vars
  · exact (MvPolynomial.IsMultiaffine.esymm k).rename Sum.inl_injective
  · exact (MvPolynomial.IsMultiaffine.esymm (m + k)).rename Sum.inr_injective
  · rw [Finset.disjoint_left]
    intro v hvleft hvright
    obtain ⟨i, hi, hiv⟩ := MvPolynomial.mem_vars_rename Sum.inl
      (MvPolynomial.esymm (Fin n) ℂ k) hvleft
    obtain ⟨j, hj, hjv⟩ := MvPolynomial.mem_vars_rename Sum.inr
      (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k)) hvright
    exact Sum.inl_ne_inr (hiv.trans hjv.symm)

/-- Evaluation formula for the rectangular polarization. -/
theorem eval_rectangularPolarization (m n : ℕ) (p : ℂ[X])
    (z : Sum (Fin n) (Fin (m + n)) → ℂ) :
    MvPolynomial.eval z (rectangularPolarization m n p) =
      ∑ k ∈ Finset.range (n + 1),
        p.coeff k / (n.choose k : ℂ) / ((m + n).choose (m + k) : ℂ) *
          (Finset.univ.val.map (z ∘ Sum.inl)).esymm k *
          (Finset.univ.val.map (z ∘ Sum.inr)).esymm (m + k) := by
  simp only [rectangularPolarization, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show MvPolynomial.eval (z ∘ Sum.inl)
        (MvPolynomial.esymm (Fin n) ℂ k) =
      (Finset.univ.val.map (z ∘ Sum.inl)).esymm k by
        exact MvPolynomial.aeval_esymm_eq_multiset_esymm
          (Fin n) ℂ k (z ∘ Sum.inl),
    show MvPolynomial.eval (z ∘ Sum.inr)
        (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k)) =
      (Finset.univ.val.map (z ∘ Sum.inr)).esymm (m + k) by
        exact MvPolynomial.aeval_esymm_eq_multiset_esymm
          (Fin (m + n)) ℂ (m + k) (z ∘ Sum.inr)]

/-- The left-variable polynomial obtained after fixing the right variables. -/
def rectangularLeftSlice (m n : ℕ) (p : ℂ[X])
    (y : Fin (m + n) → ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.monomial k
      (p.coeff k / ((m + n).choose (m + k) : ℂ) *
        (Finset.univ.val.map y).esymm (m + k))

theorem coeff_rectangularLeftSlice_of_le (m n : ℕ) (p : ℂ[X])
    (y : Fin (m + n) → ℂ) {k : ℕ} (hk : k ≤ n) :
    (rectangularLeftSlice m n p y).coeff k =
      p.coeff k / ((m + n).choose (m + k) : ℂ) *
        (Finset.univ.val.map y).esymm (m + k) := by
  unfold rectangularLeftSlice
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, hjk]
  · simp [hk]

theorem natDegree_rectangularLeftSlice_le (m n : ℕ) (p : ℂ[X])
    (y : Fin (m + n) → ℂ) :
    (rectangularLeftSlice m n p y).natDegree ≤ n := by
  unfold rectangularLeftSlice
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- Evaluating the rectangular polarization is the same as polarizing its
left slice. -/
theorem eval_rectangularPolarization_eq_eval_polarization_leftSlice
    (m n : ℕ) (p : ℂ[X]) (x : Fin n → ℂ) (y : Fin (m + n) → ℂ) :
    MvPolynomial.eval (Sum.elim x y) (rectangularPolarization m n p) =
      MvPolynomial.eval x (polarization n (rectangularLeftSlice m n p y)) := by
  rw [eval_rectangularPolarization, polarization, eval_reducedPolarization]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  unfold binomialUnlift
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · rw [Polynomial.coeff_monomial_same,
      coeff_rectangularLeftSlice_of_le m n p y hkn]
    ring
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, hjk]
  · simp [hkn]

/-- The right-variable polynomial obtained after setting all left variables
equal to `x`. -/
def rectangularRightSlice (m n : ℕ) (p : ℂ[X]) (x : ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.monomial (m + k) (p.coeff k * x ^ k)

theorem coeff_rectangularRightSlice_add_of_le (m n : ℕ) (p : ℂ[X])
    (x : ℂ) {k : ℕ} (hk : k ≤ n) :
    (rectangularRightSlice m n p x).coeff (m + k) = p.coeff k * x ^ k := by
  unfold rectangularRightSlice
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, Nat.add_left_cancel_iff, hjk]
  · simp [hk]

theorem coeff_rectangularRightSlice_eq_zero_of_lt (m n : ℕ) (p : ℂ[X])
    (x : ℂ) {j : ℕ} (hj : j < m) :
    (rectangularRightSlice m n p x).coeff j = 0 := by
  unfold rectangularRightSlice
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_monomial, if_neg]
  exact (hj.trans_le (Nat.le_add_right m k)).ne'

theorem natDegree_rectangularRightSlice_le (m n : ℕ) (p : ℂ[X]) (x : ℂ) :
    (rectangularRightSlice m n p x).natDegree ≤ m + n := by
  unfold rectangularRightSlice
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) m)

theorem natDegree_rectangularRightSlice_eq {m n : ℕ} {p : ℂ[X]}
    (hpdeg : p.natDegree = n) (hplead : p.leadingCoeff ≠ 0)
    {x : ℂ} (hx : x ≠ 0) :
    (rectangularRightSlice m n p x).natDegree = m + n := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_rectangularRightSlice_le m n p x) ?_
  rw [coeff_rectangularRightSlice_add_of_le m n p x le_rfl]
  apply mul_ne_zero
  · simpa [← hpdeg] using hplead
  · exact pow_ne_zero n hx

/-- The right slice has diagonal specialization `y ^ m * p(x * y)`. -/
theorem eval_rectangularRightSlice {m n : ℕ} {p : ℂ[X]}
    (hp : p.natDegree ≤ n) (x y : ℂ) :
    (rectangularRightSlice m n p x).eval y = y ^ m * p.eval (x * y) := by
  unfold rectangularRightSlice
  rw [Polynomial.eval_finsetSum,
    p.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hp)]
  simp only [Polynomial.eval_monomial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem upperHalfPlaneStable_rectangularRightSlice
    {m n : ℕ} {p : ℂ[X]} (hpdeg : p.natDegree ≤ n)
    (hstable : MvUpperHalfPlaneStable (xyLift p)) {x : ℂ} (hx : 0 < x.im) :
    ∀ y : ℂ, 0 < y.im → (rectangularRightSlice m n p x).eval y ≠ 0 := by
  intro y hy
  rw [eval_rectangularRightSlice hpdeg]
  apply mul_ne_zero
  · exact pow_ne_zero m (fun hzero => by
      rw [hzero] at hy
      simp at hy)
  · have hxy := hstable ![x, y] (by
      intro i
      fin_cases i
      · simpa using hx
      · simpa using hy)
    simpa using hxy

/-- The left slice is obtained by evaluating the polarization of the right
slice at the fixed right variables. -/
theorem eval_rectangularLeftSlice_eq_eval_polarization_rightSlice
    (m n : ℕ) (p : ℂ[X]) (x : ℂ) (y : Fin (m + n) → ℂ) :
    (rectangularLeftSlice m n p y).eval x =
      MvPolynomial.eval y
        (polarization (m + n) (rectangularRightSlice m n p x)) := by
  unfold rectangularLeftSlice
  rw [Polynomial.eval_finsetSum, eval_polarization]
  simp only [Polynomial.eval_monomial]
  conv_rhs =>
    rw [show m + n + 1 = m + (n + 1) by lia, Finset.sum_range_add]
  have hfirst :
      ∑ j ∈ Finset.range m,
          (rectangularRightSlice m n p x).coeff j /
              ((m + n).choose j : ℂ) *
            (Finset.univ.val.map y).esymm j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [coeff_rectangularRightSlice_eq_zero_of_lt
      m n p x (Finset.mem_range.mp hj)]
    simp
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_rectangularRightSlice_add_of_le m n p x
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  ring

theorem natDegree_rectangularLeftSlice_eq
    {m n : ℕ} {p : ℂ[X]} (hpdeg : p.natDegree = n)
    (hplead : p.leadingCoeff ≠ 0) {y : Fin (m + n) → ℂ}
    (hy : ∀ i, 0 < (y i).im) :
    (rectangularLeftSlice m n p y).natDegree = n := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_rectangularLeftSlice_le m n p y) ?_
  rw [coeff_rectangularLeftSlice_of_le m n p y le_rfl]
  have hpcoeff : p.coeff n ≠ 0 := by
    simpa [← hpdeg] using hplead
  have hyne : ∀ i, y i ≠ 0 := fun i hzero => by
    have hi := hy i
    rw [hzero] at hi
    simp at hi
  have hcard : (Finset.univ.val.map y).card = m + n := by simp
  have hesymm : (Finset.univ.val.map y).esymm (m + n) ≠ 0 := by
    have heq :
        (Finset.univ.val.map y).esymm (m + n) =
          (Finset.univ.val.map y).prod := by
      calc
        (Finset.univ.val.map y).esymm (m + n) =
            (Finset.univ.val.map y).esymm
              (Finset.univ.val.map y).card := by
          exact congrArg (Finset.univ.val.map y).esymm hcard.symm
        _ = (Finset.univ.val.map y).prod :=
          esymm_card_eq_prod (Finset.univ.val.map y)
    rw [heq]
    simp [hyne]
  simpa using mul_ne_zero hpcoeff hesymm

theorem upperHalfPlaneStable_rectangularLeftSlice
    {m n : ℕ} {p : ℂ[X]} (hpdeg : p.natDegree = n)
    (hplead : p.leadingCoeff ≠ 0)
    (hstable : MvUpperHalfPlaneStable (xyLift p))
    {y : Fin (m + n) → ℂ} (hy : ∀ i, 0 < (y i).im) :
    ∀ x : ℂ, 0 < x.im → (rectangularLeftSlice m n p y).eval x ≠ 0 := by
  intro x hx
  rw [eval_rectangularLeftSlice_eq_eval_polarization_rightSlice]
  exact mvUpperHalfPlaneStable_polarization
    (natDegree_rectangularRightSlice_eq hpdeg hplead (fun hzero => by
      rw [hzero] at hx
      simp at hx)).le
    (upperHalfPlaneStable_rectangularRightSlice hpdeg.le hstable hx) y hy

/-- Rectangular polarization preserves upper-half-plane stability. This is the
two-block specialization of the polarization theorem needed in
Gribinski--Marcus, Theorem 2.6. -/
theorem mvUpperHalfPlaneStable_rectangularPolarization
    {m n : ℕ} {p : ℂ[X]} (hpdeg : p.natDegree = n)
    (hplead : p.leadingCoeff ≠ 0)
    (hstable : MvUpperHalfPlaneStable (xyLift p)) :
    MvUpperHalfPlaneStable (rectangularPolarization m n p) := by
  intro z hz
  have hz_elim : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by
    funext i
    cases i <;> rfl
  rw [hz_elim, eval_rectangularPolarization_eq_eval_polarization_leftSlice]
  apply mvUpperHalfPlaneStable_polarization
  · exact (natDegree_rectangularLeftSlice_eq hpdeg hplead
      (fun i => hz (Sum.inr i))).le
  · exact upperHalfPlaneStable_rectangularLeftSlice hpdeg hplead hstable
      (fun i => hz (Sum.inr i))
  · exact fun i => hz (Sum.inl i)

end

end RealRooted
