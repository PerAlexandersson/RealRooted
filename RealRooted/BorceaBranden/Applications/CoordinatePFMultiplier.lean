import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.BorceaBranden.Applications.HomogenizeStable
import RealRooted.MultiplierSequence.PolyaSchur.Factorial

/-!
# Coordinate PF multipliers

The finite-symbol coordinate tensorization used here is the coordinate form of
the stability-preserver theorem of Borcea--Brändén, Invent. Math. 177 (2009),
541--569, Theorem 1.1.
-/

open scoped BigOperators

namespace RealRooted.BorceaBranden

noncomputable section

open Polynomial

/-- Apply a real diagonal sequence to one exponent coordinate of a complex
multivariate polynomial. -/
def coordinateDiagonalOperator {σ : Type*} (gamma : ℕ → ℝ) (q : σ)
    (p : _root_.MvPolynomial σ ℂ) : _root_.MvPolynomial σ ℂ :=
  p.coeff.sum fun m a => _root_.MvPolynomial.monomial m ((gamma (m q) : ℂ) * a)

@[simp]
theorem coeff_coordinateDiagonalOperator {σ : Type*} (gamma : ℕ → ℝ) (q : σ)
    (p : _root_.MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    (coordinateDiagonalOperator gamma q p).coeff m =
      (gamma (m q) : ℂ) * p.coeff m := by
  classical
  rw [coordinateDiagonalOperator, _root_.MvPolynomial.sum_def,
    _root_.MvPolynomial.coeff_sum]
  by_cases hm : m ∈ p.support
  · simp [hm, _root_.MvPolynomial.coeff_monomial]
  · have hcoeff : p.coeff m = 0 := by
      exact Finsupp.notMem_support_iff.mp hm
    simp [hm, hcoeff, _root_.MvPolynomial.coeff_monomial]

/-- The coordinate diagonal action on a monomial. -/
theorem coordinateDiagonalOperator_monomial {σ : Type*} (gamma : ℕ → ℝ) (q : σ)
    (m : σ →₀ ℕ) (a : ℂ) :
    coordinateDiagonalOperator gamma q (_root_.MvPolynomial.monomial m a) =
      _root_.MvPolynomial.monomial m ((gamma (m q) : ℂ) * a) := by
  classical
  ext n
  by_cases hnm : n = m
  · subst n
    simp [coeff_coordinateDiagonalOperator, _root_.MvPolynomial.coeff_monomial]
  · simp [coeff_coordinateDiagonalOperator, _root_.MvPolynomial.coeff_monomial,
      Ne.symm hnm]

/-- The complex-linear restriction of a coordinate diagonal action to a
coordinate-wise degree box. -/
def coordinateDiagonalOperatorDegreeBox {σ : Type*} [Fintype σ]
    (gamma : ℕ → ℝ) (q : σ) (κ : σ → ℕ) :
    _root_.MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] _root_.MvPolynomial σ ℂ where
  toFun p := coordinateDiagonalOperator gamma q p.1
  map_add' p r := by
    ext m
    simp
    ring
  map_smul' c p := by
    ext m
    simp [_root_.MvPolynomial.smul_eq_C_mul]
    ring

/-- The degree-box map acts on its canonical monomial basis by the coordinate
multiplier. -/
theorem coordinateDiagonalOperatorDegreeBox_basis {σ : Type*} [Fintype σ]
    (gamma : ℕ → ℝ) (q : σ) (κ : σ → ℕ)
    (m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i}) :
    coordinateDiagonalOperatorDegreeBox gamma q κ
        (_root_.MvPolynomial.basisDegreeOfLE κ m) =
      _root_.MvPolynomial.monomial m.1 ((gamma (m.1 q) : ℂ)) := by
  change coordinateDiagonalOperator gamma q
      ((_root_.MvPolynomial.basisDegreeOfLE κ m :
        _root_.MvPolynomial.degreeOfLE σ ℂ κ) : _root_.MvPolynomial σ ℂ) = _
  rw [_root_.MvPolynomial.coe_basisDegreeOfLE]
  simp [coordinateDiagonalOperator_monomial]

/-- The finite algebraic symbol of the coordinate diagonal action, before
regrouping its spectator coordinates. -/
theorem algebraicSymbol_coordinateDiagonalOperatorDegreeBox_eq_sum
    {σ : Type*} [Fintype σ] (gamma : ℕ → ℝ) (q : σ) (κ : σ → ℕ) :
    _root_.MvPolynomial.algebraicSymbol κ
        (coordinateDiagonalOperatorDegreeBox gamma q κ) =
      ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
        _root_.MvPolynomial.C (_root_.MvPolynomial.boxChoose κ m.1 : ℂ) *
          _root_.MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ)
            (_root_.MvPolynomial.monomial m.1 ((gamma (m.1 q) : ℂ))) *
          _root_.MvPolynomial.rightComplementMonomial κ m.1 := by
  rw [_root_.MvPolynomial.algebraicSymbol_eq_sum]
  apply Fintype.sum_congr
  intro m
  rw [coordinateDiagonalOperatorDegreeBox_basis]

/-- The padded homogeneous Jensen symbol in a selected coordinate. -/
def coordinateJensenSymbol {σ : Type*} (d : ℕ) (gamma : ℕ → ℝ) (q : σ) :
    _root_.MvPolynomial (σ ⊕ σ) ℂ :=
  ∑ k : Fin (d + 1),
    _root_.MvPolynomial.C (d.choose k : ℂ) *
      _root_.MvPolynomial.C (gamma k : ℂ) *
        _root_.MvPolynomial.X (Sum.inl q) ^ (k : ℕ) *
          _root_.MvPolynomial.X (Sum.inr q) ^ (d - k)

/-- The tensor-product form of the coordinate diagonal symbol. -/
def coordinateDiagonalSymbol {σ : Type*} [Fintype σ] (d : ℕ) (gamma : ℕ → ℝ)
    (q : σ) (κ : σ → ℕ) : _root_.MvPolynomial (σ ⊕ σ) ℂ :=
  letI := Classical.decEq σ
  coordinateJensenSymbol d gamma q *
    ∏ i ∈ Finset.univ.erase q,
      (_root_.MvPolynomial.X (Sum.inl i) +
        _root_.MvPolynomial.X (Sum.inr i)) ^ κ i

/-- The finite symbol factors into the homogeneous Jensen symbol and the
spectator-coordinate factors. -/
theorem algebraicSymbol_coordinateDiagonalOperatorDegreeBox
    {σ : Type*} [Fintype σ] (d : ℕ) (gamma : ℕ → ℝ) (q : σ) (κ : σ → ℕ)
    (hκ : κ q = d) :
    _root_.MvPolynomial.algebraicSymbol κ
        (coordinateDiagonalOperatorDegreeBox gamma q κ) =
      coordinateDiagonalSymbol d gamma q κ := by
  classical
  rw [algebraicSymbol_coordinateDiagonalOperatorDegreeBox_eq_sum]
  let g : (i : σ) → Fin (κ i + 1) → _root_.MvPolynomial (σ ⊕ σ) ℂ :=
    fun i k =>
      _root_.MvPolynomial.C ((κ i).choose (k : ℕ) : ℂ) *
        _root_.MvPolynomial.X (Sum.inl i) ^ (k : ℕ) *
          _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - k) *
            if i = q then _root_.MvPolynomial.C (gamma (k : ℕ) : ℂ) else 1
  calc
    (∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
        _root_.MvPolynomial.C (_root_.MvPolynomial.boxChoose κ m.1 : ℂ) *
          _root_.MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ)
            (_root_.MvPolynomial.monomial m.1 ((gamma (m.1 q) : ℂ))) *
          _root_.MvPolynomial.rightComplementMonomial κ m.1) =
        ∑ x : (∀ i, Fin (κ i + 1)), ∏ i, g i (x i) := by
      apply Fintype.sum_equiv (MvPolynomial.degreeOfLEIndexEquiv κ)
      intro m
      simp only [MvPolynomial.boxChoose, Nat.cast_prod, map_prod, map_natCast,
        MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, MvPolynomial.algHom_C,
        MvPolynomial.algebraMap_eq, map_pow, MvPolynomial.rename_X,
        MvPolynomial.rightComplementMonomial, mul_ite, mul_one,
        MvPolynomial.degreeOfLEIndexEquiv, Equiv.coe_fn_mk, g]
      have hif (i : σ) :
          (if i = q then
              ((κ i).choose (m.1 i) : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
                _root_.MvPolynomial.X (Sum.inl i) ^ m.1 i *
                  _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - m.1 i) *
                _root_.MvPolynomial.C (gamma (m.1 i) : ℂ)
            else
              ((κ i).choose (m.1 i) : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
                _root_.MvPolynomial.X (Sum.inl i) ^ m.1 i *
                _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - m.1 i)) =
          (((κ i).choose (m.1 i) : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
              _root_.MvPolynomial.X (Sum.inl i) ^ m.1 i *
              _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - m.1 i)) *
            (if i = q then _root_.MvPolynomial.C (gamma (m.1 i) : ℂ) else 1) := by
        by_cases hi : i = q <;> simp [hi]
      rw [show
          (∏ i,
            if i = q then
                ((κ i).choose (m.1 i) : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
                    _root_.MvPolynomial.X (Sum.inl i) ^ m.1 i *
                  _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - m.1 i) *
                    _root_.MvPolynomial.C (gamma (m.1 i) : ℂ)
              else
                ((κ i).choose (m.1 i) : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
                    _root_.MvPolynomial.X (Sum.inl i) ^ m.1 i *
                  _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - m.1 i)) =
            ∏ i,
              (((κ i).choose (m.1 i) : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
                  _root_.MvPolynomial.X (Sum.inl i) ^ m.1 i *
                _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - m.1 i)) *
                (if i = q then _root_.MvPolynomial.C (gamma (m.1 i) : ℂ) else 1) by
          apply Finset.prod_congr rfl
          intro i _hi
          exact hif i]
      rw [Finset.prod_mul_distrib]
      have hgamma :
          (∏ i, if i = q then
              _root_.MvPolynomial.C (gamma (m.1 i) : ℂ)
            else (1 : _root_.MvPolynomial (σ ⊕ σ) ℂ)) =
            _root_.MvPolynomial.C (gamma (m.1 q) : ℂ) := by
        rw [Finset.prod_eq_single q]
        · simp
        · intro i hi hiq
          simp [hiq]
        · simp
      rw [hgamma]
      simp_rw [Finset.prod_mul_distrib]
      ring
    _ = ∏ i, ∑ k : Fin (κ i + 1), g i k := by
      rw [Fintype.prod_sum]
    _ = coordinateDiagonalSymbol d gamma q κ := by
      have hq :
          (∑ k : Fin (κ q + 1), g q k) = coordinateJensenSymbol d gamma q := by
        rw [coordinateJensenSymbol]
        rw [← hκ]
        apply Finset.sum_congr rfl
        intro k _hk
        simp [g]
        ring
      have hspect (i : σ) (hi : i ≠ q) :
          (∑ k : Fin (κ i + 1), g i k) =
            (_root_.MvPolynomial.X (Sum.inl i) +
              _root_.MvPolynomial.X (Sum.inr i)) ^ κ i := by
        have hfactor :
            (_root_.MvPolynomial.X (Sum.inl i) +
                _root_.MvPolynomial.X (Sum.inr i)) ^ κ i =
              ∑ k : Fin (κ i + 1),
                _root_.MvPolynomial.X (Sum.inl i) ^ (k : ℕ) *
                  _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - k) *
                    _root_.MvPolynomial.C ((κ i).choose k : ℂ) := by
          rw [add_pow]
          rw [Fin.sum_univ_eq_sum_range
            (fun k : ℕ =>
              _root_.MvPolynomial.X (Sum.inl i) ^ k *
                _root_.MvPolynomial.X (Sum.inr i) ^ (κ i - k) *
                  _root_.MvPolynomial.C ((κ i).choose k : ℂ)) (κ i + 1)]
          simp
        simp only [map_natCast, mul_ite, mul_one, hi, ↓reduceIte, g]
        rw [hfactor]
        apply Finset.sum_congr rfl
        intro k _hk
        have hchoose :
            ((κ i).choose (k : ℕ) : _root_.MvPolynomial (σ ⊕ σ) ℂ) =
              _root_.MvPolynomial.C ((κ i).choose (k : ℕ) : ℂ) :=
          (map_natCast
            (_root_.MvPolynomial.C : ℂ →+* _root_.MvPolynomial (σ ⊕ σ) ℂ)
            ((κ i).choose (k : ℕ))).symm
        rw [hchoose]
        ring
      rw [coordinateDiagonalSymbol]
      rw [← Finset.prod_erase_mul Finset.univ
        (fun i => ∑ k : Fin (κ i + 1), g i k) (Finset.mem_univ q)]
      rw [hq]
      calc
        (∏ i ∈ Finset.univ.erase q, ∑ k : Fin (κ i + 1), g i k) *
              coordinateJensenSymbol d gamma q =
            coordinateJensenSymbol d gamma q *
              ∏ i ∈ Finset.univ.erase q, ∑ k : Fin (κ i + 1), g i k := by ring
        _ = coordinateJensenSymbol d gamma q *
              ∏ i ∈ Finset.univ.erase q,
                (_root_.MvPolynomial.X (Sum.inl i) +
                  _root_.MvPolynomial.X (Sum.inr i)) ^ κ i := by
          congr 1
          apply Finset.prod_congr rfl
          intro i hi
          exact hspect i (Finset.ne_of_mem_erase hi)

/-- The padded Jensen symbol is a renamed complexified homogenization. -/
theorem coordinateJensenSymbol_eq_rename_complexifyMv_homogenize
    {σ : Type*} (d : ℕ) (gamma : ℕ → ℝ) (q : σ) :
    coordinateJensenSymbol d gamma q =
      _root_.MvPolynomial.rename
      (Fin.cases (Sum.inl q) (fun _ => Sum.inr q))
        (complexifyMv ((jensenPolynomial d gamma).homogenize d)) := by
  rw [Polynomial.homogenize_eq_sum_range_C_mul_X_pow
    (natDegree_jensenPolynomial_le d gamma)]
  simp only [coordinateJensenSymbol, map_natCast, Nat.reduceAdd, complexifyMv,
    coeff_jensenPolynomial, Fin.isValue, map_sum, map_mul, MvPolynomial.map_C,
    Complex.ofRealHom_eq_coe, map_pow, MvPolynomial.map_X, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, MvPolynomial.rename_X, Fin.cases_zero]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      (d.choose k : _root_.MvPolynomial (σ ⊕ σ) ℂ) *
        _root_.MvPolynomial.C (gamma k : ℂ) *
          _root_.MvPolynomial.X (Sum.inl q) ^ k *
            _root_.MvPolynomial.X (Sum.inr q) ^ (d - k)) (d + 1)]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  have hcases :
      Fin.induction (Sum.inl q) (fun _ _ => Sum.inr q) (1 : Fin 2) = Sum.inr q := rfl
  simp only [hxle, ↓reduceIte, Complex.ofReal_mul, Complex.ofReal_natCast, MvPolynomial.C_mul,
    map_natCast, Fin.cases, Nat.reduceAdd, Fin.isValue]
  rw [hcases]
  ring

/-- A PF Jensen polynomial gives the fixed-degree coordinate stability
preserver on every finite spectator degree box. -/
theorem coordinateDiagonalOperatorDegreeBox_preserves_stability
    {σ : Type*} [Fintype σ] (d : ℕ) (gamma : ℕ → ℝ) (q : σ) (κ : σ → ℕ)
    (hκ : κ q = d)
    (hJ : IsPFPolynomial (jensenPolynomial d gamma))
    (p : _root_.MvPolynomial.degreeOfLE σ ℂ κ)
    (hp : MvUpperHalfPlaneStable p.1) :
      MvUpperHalfPlaneStableOrZero
      (coordinateDiagonalOperatorDegreeBox gamma q κ p) := by
  classical
  by_cases hzero : jensenPolynomial d gamma = 0
  · left
    ext m
    change (coordinateDiagonalOperator gamma q p.1).coeff m = 0
    rw [coeff_coordinateDiagonalOperator]
    by_cases hm : m ∈ p.1.support
    · have hmκ := (_root_.MvPolynomial.mem_degreeOfLE_iff_degreeOf p.1).mp p.2 q
      have hmle := (_root_.MvPolynomial.degreeOf_le_iff.mp hmκ) m hm
      have hm_d : m q ≤ d := by simpa [hκ] using hmle
      rw [(jensenPolynomial_eq_zero_iff.mp hzero) (m q) hm_d]
      simp
    · have hcoeff : p.1.coeff m = 0 := Finsupp.notMem_support_iff.mp hm
      simp [hcoeff]
  · have hsplit : (jensenPolynomial d gamma).Splits :=
      hJ.eq_zero_or_splits.resolve_left hzero
    have hhom : MvUpperHalfPlaneStable
        (complexifyMv ((jensenPolynomial d gamma).homogenize d)) :=
      homogenize_stable_of_splits_nonpos_of_natDegree_le
        (natDegree_jensenPolynomial_le d gamma) hzero hsplit hJ.roots_nonpos
    have hJsymbol : MvUpperHalfPlaneStable (coordinateJensenSymbol d gamma q) := by
      rw [coordinateJensenSymbol_eq_rename_complexifyMv_homogenize]
      exact hhom.rename
    have hspectator : MvUpperHalfPlaneStableOrZero
        (∏ i ∈ Finset.univ.erase q,
          (_root_.MvPolynomial.X (Sum.inl i) +
            _root_.MvPolynomial.X (Sum.inr i)) ^ κ i) := by
      apply MvUpperHalfPlaneStableOrZero.finset_prod
      intro i _hi
      simpa using (MvUpperHalfPlaneStable.mul_X_add_X_pow
        (MvUpperHalfPlaneStable.one (sigma := σ ⊕ σ))
        (Sum.inl i) (Sum.inr i) (κ i)).orZero
    have hsymbol : MvUpperHalfPlaneStable
        (_root_.MvPolynomial.algebraicSymbol κ
          (coordinateDiagonalOperatorDegreeBox gamma q κ)) := by
      rw [algebraicSymbol_coordinateDiagonalOperatorDegreeBox d gamma q κ hκ]
      rcases hspectator with hzero | hspectator
      · have hne :
            (∏ i ∈ Finset.univ.erase q,
              (_root_.MvPolynomial.X (Sum.inl i) +
                _root_.MvPolynomial.X (Sum.inr i)) ^ κ i) ≠
              (0 : _root_.MvPolynomial (σ ⊕ σ) ℂ) := by
          apply Finset.prod_ne_zero_iff.mpr
          intro i _hi
          apply pow_ne_zero
          intro hsum
          have hcoeff := congrArg
            (fun r : _root_.MvPolynomial (σ ⊕ σ) ℂ =>
              r.coeff (Finsupp.single (Sum.inl i) 1)) hsum
          simp at hcoeff
        exact (hne hzero).elim
      · exact hJsymbol.mul hspectator
    exact finiteSymbol_preserves_stability_general κ
      (coordinateDiagonalOperatorDegreeBox gamma q κ) hsymbol p hp

/-- A PF Jensen polynomial makes the coordinate diagonal action preserve
upper-half-plane stability without any degree bounds on spectator variables. -/
theorem coordinateDiagonalOperator_preserves_stability
    {σ : Type*} [Finite σ] (d : ℕ) (gamma : ℕ → ℝ) (q : σ)
    (hJ : IsPFPolynomial (jensenPolynomial d gamma))
    {p : _root_.MvPolynomial σ ℂ} (hpq : p.degreeOf q ≤ d)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStableOrZero (coordinateDiagonalOperator gamma q p) := by
  classical
  have := Fintype.ofFinite σ
  let κ : σ → ℕ := fun i => if i = q then d else p.degreeOf i
  have hκ : κ q = d := by simp [κ]
  have hpκ : p ∈ _root_.MvPolynomial.degreeOfLE σ ℂ κ := by
    rw [_root_.MvPolynomial.mem_degreeOfLE_iff_degreeOf]
    intro i
    by_cases hi : i = q
    · simpa [κ, hi] using hpq
    · simp [κ, hi]
  let pκ : _root_.MvPolynomial.degreeOfLE σ ℂ κ := ⟨p, hpκ⟩
  have hresult := coordinateDiagonalOperatorDegreeBox_preserves_stability
    d gamma q κ hκ hJ pκ hp
  rcases hresult with hzero | hstable
  · left
    exact hzero
  · right
    exact hstable

/-- An infinite PF multiplier sequence tensorizes in every coordinate. -/
theorem IsPFMultiplierSequence.coordinateDiagonalOperator_preserves_stability
    {σ : Type*} [Finite σ] {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (d : ℕ) (q : σ)
    {p : _root_.MvPolynomial σ ℂ} (hpq : p.degreeOf q ≤ d)
    (hp : MvUpperHalfPlaneStable p) :
    MvUpperHalfPlaneStableOrZero (coordinateDiagonalOperator gamma q p) :=
  RealRooted.BorceaBranden.coordinateDiagonalOperator_preserves_stability d gamma q
    (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence hgamma d) hpq hp

/-- The descending-factorial sequence is a PF multiplier sequence. -/
theorem isPFMultiplierSequence_descFactorial (n : ℕ) :
    IsPFMultiplierSequence (fun k => (n.descFactorial k : ℝ)) := by
  have h := (isPFPolynomial_X_add_one.pow n).isPFMultiplierSequence_factorial_mul_coeff
  rw [show (fun k => (n.descFactorial k : ℝ)) =
      (fun k => (k.factorial : ℝ) * ((X + 1 : ℝ[X]) ^ n).coeff k) by
    funext k
    rw [coeff_X_add_one_pow, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring]
  exact h

end

end RealRooted.BorceaBranden
