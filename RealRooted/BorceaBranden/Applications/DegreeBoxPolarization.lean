import RealRooted.BorceaBranden.FiniteSymbolBasis
import RealRooted.BorceaBranden.FiniteSymbolDegree
import RealRooted.Polarization

/-!
# Source polarization for degree-box operators

This file implements the source-side operator lift from Borcea--Brändén,
equation (2.2), for a one-variable degree-`n` source box. The lift first
diagonalizes a multiaffine input and then applies the original operator.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- Lift an operator with a one-variable degree-`n` source to a multiaffine
`Fin n` source by precomposing with diagonal projection. -/
def sourcePolarizedOperator {τ : Type*} (n : ℕ)
    (T : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    MvPolynomial.degreeOfLE (Fin n) ℂ (fun _ => 1) →ₗ[ℂ]
      MvPolynomial τ ℂ :=
  T.comp (diagonalProjectionDegreeBox n)

/-- Source-side equation (2.2): restricting the lifted operator along source
polarization reconstructs the original operator. -/
theorem sourcePolarizedOperator_comp_polarizationDegreeBoxLinearMap
    {τ : Type*} {n : ℕ}
    (T : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    (sourcePolarizedOperator n T).comp
      (polarizationDegreeBoxLinearMap n) = T := by
  apply LinearMap.ext
  intro q
  change T (diagonalProjectionDegreeBox n
    (polarizationDegreeBoxLinearMap n q)) = T q
  rw [diagonalProjectionDegreeBox_comp_polarizationDegreeBoxLinearMap q]

/-- The source-polarized operator sends a multiaffine basis monomial to the
original operator applied to the one-variable basis monomial of the same total
degree. This is the basis-level content of Borcea--Branden Lemma 2.5. -/
theorem sourcePolarizedOperator_basisDegreeOfLE
    {τ : Type*} {n : ℕ}
    (T : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ)
    (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    sourcePolarizedOperator n T
        (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m) =
      T (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
        (diagonalDegreeBoxIndex m)) := by
  change T (diagonalProjectionDegreeBox n
    (MvPolynomial.basisDegreeOfLE (R := ℂ) (fun _ : Fin n => 1) m)) = _
  rw [diagonalProjectionDegreeBox_basisDegreeOfLE]

/-- Reindex a sum over multiaffine exponent vectors by their finite supports.
This is the subset reindexing in the source-side proof of Lemma 2.5. -/
theorem sum_degreeOneExponent_eq_sum_finset
    {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1} → M) :
    ∑ m, f m =
      ∑ s : Finset (Fin n),
        f ((degreeOneExponentEquivFinset (Fin n)).symm s) := by
  apply Fintype.sum_equiv (degreeOneExponentEquivFinset (Fin n))
  intro m
  simp

/-- Partition a sum over subsets of `Fin n` by subset cardinality. -/
theorem sum_finset_eq_sum_powersetCard
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : Finset (Fin n) → M) :
    ∑ s, f s =
      ∑ k ∈ Finset.range (n + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f s := by
  simpa using
    Finset.sum_powerset (Finset.univ : Finset (Fin n)) f

/-- Summing a cardinality-dependent contribution over subsets of `Fin n`
produces the corresponding binomial coefficients. -/
theorem sum_finset_cardFunction
    {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ s : Finset (Fin n), g s.card =
      ∑ k ∈ Finset.range (n + 1), n.choose k • g k := by
  rw [sum_finset_eq_sum_powersetCard]
  apply Finset.sum_congr rfl
  intro k hk
  simpa using
    Finset.sum_powersetCard k (Finset.univ : Finset (Fin n)) g

/-- The coefficient grouping for multiaffine source exponents: one term for
each zero-one exponent vector becomes `choose n k` copies of the contribution
of total degree `k`. -/
theorem sum_degreeOneExponent_degreeFunction
    {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}, g m.1.degree =
      ∑ k ∈ Finset.range (n + 1), n.choose k • g k := by
  rw [sum_degreeOneExponent_eq_sum_finset]
  simpa using sum_finset_cardFunction n g

end

end RealRooted.BorceaBranden

namespace MvPolynomial

/-- The coefficient of source degree `k`, after viewing a polynomial in
`tau ⊕ Fin 1` as a polynomial in the single source variable with coefficients
in the output-variable ring `MvPolynomial tau ℂ`. -/
/- Source audit: Borcea--Branden, "The Lee--Yang and Polya--Schur Programs. I",
Proposition 2.4, equation (2.2), and Lemma 2.5. This extracts the coefficient
of the source monomial `z^k` while retaining the output-variable polynomial. -/
noncomputable def sourceCoefficient {τ : Type*}
    (P : MvPolynomial (τ ⊕ Fin 1) ℂ) (k : ℕ) : MvPolynomial τ ℂ :=
  (sumAlgEquiv ℂ (Fin 1) τ
    (rename (Equiv.sumComm τ (Fin 1)) P)).coeff
      (Finsupp.single default k)

/-- Polarize only the single source variable of a polynomial whose output
variables are indexed by `τ`.

This is the one-source-coordinate instance of Borcea--Brändén's operator
`Π↑` from Proposition 2.4 and Lemma 2.5: the source coefficient of degree `k`
is divided by `choose n k`, and the source monomial is replaced by the
elementary symmetric polynomial `e_k` in the `Fin n` source block. -/
/- This is exactly the paper's source polarization `Pi^up`: the coefficient of
`z^k` is divided by `choose n k` and `z^k` is replaced by the elementary
symmetric polynomial `e_k` in the new source block. -/
noncomputable def sourceBlockPolarization {τ : Type*} (n : ℕ)
    (P : MvPolynomial (τ ⊕ Fin 1) ℂ) :
    MvPolynomial (τ ⊕ Fin n) ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    C ((n.choose k : ℂ)⁻¹) *
      rename Sum.inl (sourceCoefficient P k) *
        rename Sum.inr (esymm (Fin n) ℂ k)

private theorem
    coeff_uniqueAlgEquiv_specializeLeft_eq_eval_sourceCoefficient
    {τ : Type*} (P : MvPolynomial (τ ⊕ Fin 1) ℂ)
    (x : τ → ℂ) (k : ℕ) :
    ((MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
      (_root_.RealRooted.specializeLeft x P)).coeff k =
      MvPolynomial.eval x (sourceCoefficient P k) := by
  have hspecial :
      _root_.RealRooted.specializeLeft x P =
        MvPolynomial.map (MvPolynomial.eval x)
          (sumAlgEquiv ℂ (Fin 1) τ
            (rename (Equiv.sumComm τ (Fin 1)) P)) := by
    unfold _root_.RealRooted.specializeLeft
    change
      (MvPolynomial.aeval
          (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)) P =
        ((MvPolynomial.mapAlgHom (MvPolynomial.aeval x)).comp
          ((sumAlgEquiv ℂ (Fin 1) τ).toAlgHom.comp
            (rename (Equiv.sumComm τ (Fin 1))))) P
    congr 1
    apply MvPolynomial.algHom_ext
    rintro (i | i) <;>
      simp [Function.comp_def, Equiv.sumComm_apply]
  rw [MvPolynomial.coeff_uniqueAlgEquiv, hspecial,
    MvPolynomial.coeff_map]
  change
    MvPolynomial.eval x
        ((sumAlgEquiv ℂ (Fin 1) τ
          (rename (Equiv.sumComm τ (Fin 1)) P)).coeff
            (Finsupp.single default k)) =
      MvPolynomial.eval x (sourceCoefficient P k)
  rfl

/- Borcea--Branden, arXiv:0809.0401, Proposition 2.4 and equation (2.2).
Specializing the output block commutes with source polarization. The ambient
degree cap remains `n`, even when specialization lowers the source degree. -/
theorem specializeLeft_sourceBlockPolarization
    {τ : Type*} (n : ℕ) (P : MvPolynomial (τ ⊕ Fin 1) ℂ)
    (x : τ → ℂ) :
    _root_.RealRooted.specializeLeft x
        (sourceBlockPolarization n P) =
      _root_.RealRooted.polarization n
        (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
          (_root_.RealRooted.specializeLeft x P)) := by
  let p : Polynomial ℂ :=
    (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1))
      (_root_.RealRooted.specializeLeft x P)
  have hpcoeff (k : ℕ) :
      p.coeff k = MvPolynomial.eval x (sourceCoefficient P k) :=
    coeff_uniqueAlgEquiv_specializeLeft_eq_eval_sourceCoefficient P x k
  have houtput (q : MvPolynomial τ ℂ) :
      MvPolynomial.aeval
          (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)
          (rename (Sum.inl : τ → τ ⊕ Fin n) q) =
        C (MvPolynomial.eval x q) := by
    rw [MvPolynomial.aeval_rename]
    change
      MvPolynomial.aeval (MvPolynomial.C ∘ x) q =
        C (MvPolynomial.eval x q)
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add q r hq hr => rw [map_add, hq, hr, map_add]
    | mul_X q i hq =>
        rw [map_mul, MvPolynomial.aeval_X, hq, map_mul,
          MvPolynomial.eval_X]
  have hsource (q : MvPolynomial (Fin n) ℂ) :
      MvPolynomial.aeval
          (Sum.elim (MvPolynomial.C ∘ x) MvPolynomial.X)
          (rename (Sum.inr : Fin n → τ ⊕ Fin n) q) =
        q := by
    rw [MvPolynomial.aeval_rename]
    change MvPolynomial.aeval MvPolynomial.X q = q
    exact MvPolynomial.aeval_X_left_apply q
  change
    _root_.RealRooted.specializeLeft x
        (sourceBlockPolarization n P) =
      _root_.RealRooted.polarization n p
  unfold sourceBlockPolarization _root_.RealRooted.specializeLeft
  rw [map_sum]
  unfold _root_.RealRooted.polarization
    _root_.RealRooted.reducedPolarization
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, houtput, hsource]
  have hbinom :
      (_root_.RealRooted.binomialUnlift n p).coeff k =
        p.coeff k / (n.choose k : ℂ) := by
    unfold _root_.RealRooted.binomialUnlift
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · simp only [Polynomial.coeff_monomial_same]
    · intro j hj hjk
      simp [Polynomial.coeff_monomial, hjk]
    · intro hknot
      exact (hknot hk).elim
  rw [hbinom, hpcoeff]
  simp only [div_eq_mul_inv, map_mul]
  ring

/- Borcea--Branden, arXiv:0809.0401, Proposition 2.4. Apply upper-half-plane
polarization stability fiberwise after specializing the output block. The
ambient source-degree cap remains `n` after specialization. -/
theorem mvUpperHalfPlaneStable_sourceBlockPolarization
    {τ : Type*} {n : ℕ}
    {P : MvPolynomial (τ ⊕ Fin 1) ℂ}
    (hdeg : P.degreeOf (Sum.inr default) ≤ n)
    (hstable : _root_.RealRooted.MvUpperHalfPlaneStable P) :
    _root_.RealRooted.MvUpperHalfPlaneStable
      (sourceBlockPolarization n P) := by
  intro z hz
  let x : τ → ℂ := fun i => z (Sum.inl i)
  let y : Fin n → ℂ := fun i => z (Sum.inr i)
  let p : Polynomial ℂ :=
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
      (_root_.RealRooted.specializeLeft x P)
  have hx : ∀ i, 0 < (x i).im :=
    fun i => hz (Sum.inl i)
  have hy : ∀ i, 0 < (y i).im :=
    fun i => hz (Sum.inr i)
  have hpdeg : p.natDegree ≤ n := by
    exact
      (_root_.RealRooted.natDegree_uniqueAlgEquiv_specializeLeft_le_degreeOf
        x P).trans hdeg
  have hspecial :
      _root_.RealRooted.MvUpperHalfPlaneStable
        (_root_.RealRooted.specializeLeft x P) :=
    hstable.specializeLeft hx
  have hpstable :
      ∀ w : ℂ, 0 < w.im → p.eval w ≠ 0 := by
    intro w hw
    change
      Polynomial.eval₂ (RingHom.id ℂ) w
        (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
          (_root_.RealRooted.specializeLeft x P)) ≠ 0
    rw [MvPolynomial.eval₂_const_uniqueAlgEquiv]
    exact hspecial (fun _ => w) (fun _ => hw)
  have hpolar :
      _root_.RealRooted.MvUpperHalfPlaneStable
        (_root_.RealRooted.polarization n p) :=
    _root_.RealRooted.mvUpperHalfPlaneStable_polarization
      hpdeg hpstable
  have hfiber :
      _root_.RealRooted.MvUpperHalfPlaneStable
        (_root_.RealRooted.specializeLeft x
          (sourceBlockPolarization n P)) := by
    rw [specializeLeft_sourceBlockPolarization]
    exact hpolar
  have hnonzero := hfiber y hy
  rw [_root_.RealRooted.eval_specializeLeft] at hnonzero
  have hxy : Sum.elim x y = z := by
    funext i
    cases i <;> rfl
  simpa only [hxy] using hnonzero

/-- Extracting a source coefficient commutes with a finite sum. -/
theorem sourceCoefficient_sum {τ ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (τ ⊕ Fin 1) ℂ) (k : ℕ) :
    sourceCoefficient (∑ i ∈ s, f i) k =
      ∑ i ∈ s, sourceCoefficient (f i) k := by
  simp [sourceCoefficient, map_sum, coeff_sum]

/-- Extract the source coefficient of an output polynomial times one source
monomial. -/
theorem sourceCoefficient_rename_mul_X_pow {τ : Type*}
    (q : MvPolynomial τ ℂ) (r k : ℕ) :
    sourceCoefficient
        (rename (Sum.inl : τ → τ ⊕ Fin 1) q *
          X (Sum.inr default) ^ r) k =
      if k = r then q else 0 := by
  have hpoly :
      (sumAlgEquiv ℂ (Fin 1) τ)
          (rename (Equiv.sumComm τ (Fin 1))
            (rename (Sum.inl : τ → τ ⊕ Fin 1) q *
              X (Sum.inr default) ^ r)) =
        C q * X default ^ r := by
    simp only [map_mul, map_pow, rename_X, rename_rename,
      Equiv.sumComm_apply]
    change (sumAlgEquiv ℂ (Fin 1) τ)
          (rename (Sum.inr : τ → Fin 1 ⊕ τ) q) *
        (sumAlgEquiv ℂ (Fin 1) τ) (X (Sum.inl default)) ^ r =
      C q * X default ^ r
    rw [show (sumAlgEquiv ℂ (Fin 1) τ)
        (rename (Sum.inr : τ → Fin 1 ⊕ τ) q) = C q by
      simpa using DFunLike.congr_fun
        (sumAlgEquiv_comp_rename_inr ℂ (Fin 1) τ) q]
    simp
  unfold sourceCoefficient
  rw [hpoly, coeff_C_mul, coeff_X_pow]
  simp [eq_comm]

/-- Extract the source coefficient when the output coefficient has an
additional scalar factor. -/
theorem sourceCoefficient_C_mul_rename_mul_X_pow {τ : Type*}
    (a : ℂ) (q : MvPolynomial τ ℂ) (r k : ℕ) :
    sourceCoefficient
        (C a * rename (Sum.inl : τ → τ ⊕ Fin 1) q *
          X (Sum.inr default) ^ r) k =
      if k = r then C a * q else 0 := by
  have hterm :
      C a * rename (Sum.inl : τ → τ ⊕ Fin 1) q *
          X (Sum.inr default) ^ r =
        rename Sum.inl (C a * q) * X (Sum.inr default) ^ r := by
    simp
  rw [hterm, sourceCoefficient_rename_mul_X_pow]

/-- In a degree-`n` algebraic-symbol-shaped sum, source degree `r` selects the
unique operator term indexed by `n - r`. -/
theorem sourceCoefficient_symbol_sum {τ : Type*} (n r : ℕ)
    (hr : r ≤ n) (q : ℕ → MvPolynomial τ ℂ) :
    sourceCoefficient
        (∑ k ∈ Finset.range (n + 1),
          C (n.choose k : ℂ) * rename Sum.inl (q k) *
            X (Sum.inr default) ^ (n - k)) r =
      C (n.choose (n - r) : ℂ) * q (n - r) := by
  rw [sourceCoefficient_sum]
  rw [Finset.sum_eq_single (n - r)]
  · rw [sourceCoefficient_C_mul_rename_mul_X_pow]
    simp [Nat.sub_sub_self hr]
  · intro k hk hne
    rw [sourceCoefficient_C_mul_rename_mul_X_pow]
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hnr : r ≠ n - k := by
      intro heq
      apply hne
      lia
    rw [if_neg hnr]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.sub_le n r)))).elim

/-- Identify all polarized source variables while leaving output variables
unchanged. -/
def sourceDiagonalVariableMap {τ : Type*} {n : ℕ} :
    τ ⊕ Fin n → τ ⊕ Fin 1
  | Sum.inl i => Sum.inl i
  | Sum.inr _ => Sum.inr default

/-- Diagonalizing source variables leaves the output-variable block
unchanged. -/
@[simp] theorem rename_sourceDiagonalVariableMap_rename_inl
    {τ : Type*} {n : ℕ} (p : MvPolynomial τ ℂ) :
    rename (sourceDiagonalVariableMap (τ := τ) (n := n))
        (rename (Sum.inl : τ → τ ⊕ Fin n) p) =
      rename (Sum.inl : τ → τ ⊕ Fin 1) p := by
  rw [rename_rename]
  rfl

/-- Diagonalizing a complementary zero-one source monomial records only its
complementary total degree. -/
theorem rename_rightComplementMonomial_one
    {τ : Type*} {n : ℕ} (m : Fin n →₀ ℕ)
    (hm : ∀ i, m i ≤ 1) :
    rename (sourceDiagonalVariableMap (τ := τ) (n := n))
        (rightComplementMonomial (R := ℂ) (τ := τ)
          (fun _ : Fin n => 1) m) =
      X (Sum.inr default) ^ (n - m.degree) := by
  rw [rightComplementMonomial_eq_prod]
  simp only [map_prod, map_pow, rename_X, sourceDiagonalVariableMap]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simpa using Finsupp.sum_one_sub_eq_card_sub_degree m hm

end MvPolynomial

namespace RealRooted.BorceaBranden

noncomputable section

open MvPolynomial

/-- The source-degree coefficient of a one-variable finite algebraic symbol.

This is the coefficient calculation on the right-hand side of
Borcea--Brändén Lemma 2.5: source degree `r` corresponds to operator degree
`n - r`, with coefficient `choose n (n - r)`. -/
theorem sourceCoefficient_algebraicSymbol_finOne
    {τ : Type*} (n r : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ)
    (hr : r ≤ n) :
    sourceCoefficient (algebraicSymbol (fun _ : Fin 1 => n) T) r =
      C (n.choose (n - r) : ℂ) *
        T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
          (finOneDegreeIndex n (n - r))) := by
  rw [algebraicSymbol_finOne_eq_sum_range]
  exact sourceCoefficient_symbol_sum n r hr fun k =>
    T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
      (finOneDegreeIndex n k))

lemma finOneDegreeIndex_degree_eq_diagonalDegreeBoxIndex
    {n : ℕ} (m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1}) :
    finOneDegreeIndex n m.1.degree = diagonalDegreeBoxIndex m := by
  have hm_degree : m.1.degree ≤ n := by
    rw [← card_support_eq_degree_of_le_one m.1 m.2]
    simpa using Finset.card_le_univ m.1.support
  apply (degreeOfLEFinOneEquiv n).injective
  apply Fin.ext
  simp [finOneDegreeIndex, degreeOfLEFinOneEquiv_val,
    diagonalDegreeBoxIndex,
    Nat.min_eq_left hm_degree]

/-- Summation over finite subsets is invariant under taking complements. -/
private theorem sum_finset_compl
    {M α : Type*} [AddCommMonoid M] [Fintype α] [DecidableEq α]
    (f : Finset α → M) :
    ∑ s : Finset α, f sᶜ = ∑ s, f s := by
  let e : Finset α ≃ Finset α :=
    { toFun := fun s => sᶜ
      invFun := fun s => sᶜ
      left_inv := compl_compl
      right_inv := compl_compl }
  exact e.sum_comp f

/-- Complement reindexing exchanges a support cardinality with its codimension. -/
private theorem sum_finset_card_compl
    {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : ℕ → Finset (Fin n) → M) :
    ∑ s : Finset (Fin n), f s.card sᶜ =
      ∑ s, f (n - s.card) s := by
  rw [← sum_finset_compl (fun s : Finset (Fin n) =>
    f (n - s.card) s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.card_compl]
  simp only [Fintype.card_fin]
  have hs : s.card ≤ n := by simpa using Finset.card_le_univ s
  rw [Nat.sub_sub_self hs]

/-- A degree-one exponent's complementary monomial is indexed by the complement
of the corresponding finite support. -/
@[simp]
private theorem rightComplementMonomial_one_degreeOneExponentEquivFinset_symm
    {τ R : Type*} [CommSemiring R] (n : ℕ) (s : Finset (Fin n)) :
    rightComplementMonomial (R := R) (τ := τ) (fun _ : Fin n => 1)
        ((degreeOneExponentEquivFinset (Fin n)).symm s).1 =
      rename (Sum.inr : Fin n → τ ⊕ Fin n) (∏ i ∈ sᶜ, X i) := by
  rw [rightComplementMonomial_one_eq_support_compl
    ((degreeOneExponentEquivFinset (Fin n)).symm s).1
    ((degreeOneExponentEquivFinset (Fin n)).symm s).2]
  have hsupp :
      ((degreeOneExponentEquivFinset (Fin n)).symm s).1.support = s :=
    (degreeOneExponentEquivFinset (Fin n)).apply_symm_apply s
  rw [hsupp]

/-- Grouping squarefree monomials by support cardinality gives `esymm`. -/
private theorem sum_finset_card_prod_eq_sum_esymm
    {τ : Type*} (n : ℕ) (q : ℕ → MvPolynomial τ ℂ) :
    (∑ s : Finset (Fin n),
      rename (Sum.inl : τ → τ ⊕ Fin n) (q (n - s.card)) *
        rename Sum.inr (∏ i ∈ s, X i)) =
      ∑ r ∈ Finset.range (n + 1),
        rename (Sum.inl : τ → τ ⊕ Fin n) (q (n - r)) *
          rename Sum.inr (esymm (Fin n) ℂ r) := by
  rw [sum_finset_eq_sum_powersetCard]
  apply Finset.sum_congr rfl
  intro r _
  rw [esymm, map_sum, Finset.mul_sum]
  simp only [map_prod, rename_X]
  apply Finset.sum_congr rfl
  intro s hs
  rw [(Finset.mem_powersetCard.mp hs).2]

/-- Complementing zero-one exponent supports and grouping by cardinality gives
the elementary-symmetric expansion used in Borcea--Branden, Lemma 2.5. -/
private theorem sum_degreeOneExponent_rightComplementMonomial_eq_sum_esymm
    {τ : Type*} (n : ℕ) (q : ℕ → MvPolynomial τ ℂ) :
    (∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1},
      rename (Sum.inl : τ → τ ⊕ Fin n) (q m.1.degree) *
        rightComplementMonomial (R := ℂ) (τ := τ)
          (fun _ : Fin n => 1) m.1) =
      ∑ r ∈ Finset.range (n + 1),
        rename (Sum.inl : τ → τ ⊕ Fin n) (q (n - r)) *
          rename Sum.inr (esymm (Fin n) ℂ r) := by
  rw [sum_degreeOneExponent_eq_sum_finset]
  simp only [degree_degreeOneExponentEquivFinset_symm,
    rightComplementMonomial_one_degreeOneExponentEquivFinset_symm]
  rw [sum_finset_card_compl n (fun k s =>
    rename (Sum.inl : τ → τ ⊕ Fin n) (q k) *
      rename Sum.inr (∏ i ∈ s, X i))]
  exact sum_finset_card_prod_eq_sum_esymm n q

/-- The multiaffine symbol of the lifted operator before source diagonalization.
This is the left-hand expansion in Borcea--Branden, Lemma 2.5. -/
theorem algebraicSymbol_sourcePolarizedOperator_eq_sum
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    algebraicSymbol (fun _ : Fin n => 1)
        (sourcePolarizedOperator n T) =
      ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1},
        rename (Sum.inl : τ → τ ⊕ Fin n)
            (T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
              (diagonalDegreeBoxIndex m))) *
          rightComplementMonomial (R := ℂ) (τ := τ)
            (fun _ : Fin n => 1) m.1 := by
  rw [algebraicSymbol_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [boxChoose_one_of_le_one m.1 m.2,
    sourcePolarizedOperator_basisDegreeOfLE]
  simp

/-- Expanding the paper's `Pi^up` on the one-variable symbol cancels the
binomial coefficient and replaces each source monomial by `e_r`. -/
theorem sourceBlockPolarization_algebraicSymbol_finOne_eq_sum
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    sourceBlockPolarization n
        (algebraicSymbol (fun _ : Fin 1 => n) T) =
      ∑ r ∈ Finset.range (n + 1),
        rename (Sum.inl : τ → τ ⊕ Fin n)
            (T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
              (finOneDegreeIndex n (n - r)))) *
          rename Sum.inr (esymm (Fin n) ℂ r) := by
  unfold sourceBlockPolarization
  apply Finset.sum_congr rfl
  intro r hr
  have hr_le : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  rw [sourceCoefficient_algebraicSymbol_finOne n r T hr_le]
  rw [Nat.choose_symm hr_le]
  have hchoose : n.choose r ≠ 0 := (Nat.choose_pos hr_le).ne'
  rw [map_mul]
  simp only [rename_C]
  rw [← mul_assoc, ← C_mul]
  simp [hchoose]

/-- Borcea--Branden, Lemma 2.5: source polarization of an operator polarizes
its finite algebraic symbol in the source-variable block. -/
theorem algebraicSymbol_sourcePolarizedOperator
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    algebraicSymbol (fun _ : Fin n => 1)
        (sourcePolarizedOperator n T) =
      sourceBlockPolarization n
        (algebraicSymbol (fun _ : Fin 1 => n) T) := by
  rw [algebraicSymbol_sourcePolarizedOperator_eq_sum,
    sourceBlockPolarization_algebraicSymbol_finOne_eq_sum]
  simpa only [← finOneDegreeIndex_degree_eq_diagonalDegreeBoxIndex] using
    sum_degreeOneExponent_rightComplementMonomial_eq_sum_esymm n
      (fun k => T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
        (finOneDegreeIndex n k)))

/-- Borcea--Brändén, Lemma 2.5 and Proposition 2.4: stability of a finite
algebraic symbol is preserved when its single source variable is polarized
into a multiaffine source block. -/
theorem mvUpperHalfPlaneStable_algebraicSymbol_sourcePolarizedOperator
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ)
    (hstable :
      MvUpperHalfPlaneStable
        (algebraicSymbol (fun _ : Fin 1 => n) T)) :
    MvUpperHalfPlaneStable
      (algebraicSymbol (fun _ : Fin n => 1)
        (sourcePolarizedOperator n T)) := by
  simpa only [algebraicSymbol_sourcePolarizedOperator] using
    MvPolynomial.mvUpperHalfPlaneStable_sourceBlockPolarization
      (MvPolynomial.degreeOf_algebraicSymbol_inr_le
        (fun _ : Fin 1 => n) T default)
      hstable

/-- Termwise form of the source-polarized algebraic symbol after identifying
all polarized source variables. -/
theorem rename_algebraicSymbol_sourcePolarizedOperator_eq_sum
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    MvPolynomial.rename
        (MvPolynomial.sourceDiagonalVariableMap (τ := τ) (n := n))
        (algebraicSymbol (fun _ : Fin n => 1)
          (sourcePolarizedOperator n T)) =
      ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1},
        rename (Sum.inl : τ → τ ⊕ Fin 1)
            (T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
              (diagonalDegreeBoxIndex m))) *
          X (Sum.inr default) ^ (n - m.1.degree) := by
  classical
  rw [algebraicSymbol, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [map_mul, rename_C]
  rw [boxChoose_one_of_le_one m.1 m.2, Nat.cast_one, map_one,
    one_mul, MvPolynomial.rename_sourceDiagonalVariableMap_rename_inl,
    sourcePolarizedOperator_basisDegreeOfLE,
    MvPolynomial.rename_rightComplementMonomial_one m.1 m.2]

/-- Diagonal consequence of the source-side Borcea--Brändén Lemma 2.5 route:
identifying the multiaffine source variables recovers the original degree-box
symbol.  The full Lemma 2.5 identity before diagonalization is strictly
stronger and uses `MvPolynomial.sourceBlockPolarization`. -/
theorem rename_algebraicSymbol_sourcePolarizedOperator
    {τ : Type*} (n : ℕ)
    (T : degreeOfLE (Fin 1) ℂ (fun _ => n) →ₗ[ℂ]
      MvPolynomial τ ℂ) :
    MvPolynomial.rename
        (MvPolynomial.sourceDiagonalVariableMap (τ := τ) (n := n))
        (algebraicSymbol (fun _ : Fin n => 1)
          (sourcePolarizedOperator n T)) =
      algebraicSymbol (fun _ : Fin 1 => n) T := by
  classical
  let g : ℕ → MvPolynomial (τ ⊕ Fin 1) ℂ := fun k =>
    rename (Sum.inl : τ → τ ⊕ Fin 1)
        (T (basisDegreeOfLE (R := ℂ) (fun _ : Fin 1 => n)
          (finOneDegreeIndex n k))) *
      X (Sum.inr default) ^ (n - k)
  calc
    MvPolynomial.rename
          (MvPolynomial.sourceDiagonalVariableMap (τ := τ) (n := n))
          (algebraicSymbol (fun _ : Fin n => 1)
            (sourcePolarizedOperator n T)) =
        ∑ m : {m : Fin n →₀ ℕ // ∀ i, m i ≤ 1},
          g m.1.degree := by
      rw [rename_algebraicSymbol_sourcePolarizedOperator_eq_sum]
      apply Finset.sum_congr rfl
      intro m _
      simp only [g]
      rw [finOneDegreeIndex_degree_eq_diagonalDegreeBoxIndex]
    _ = ∑ k ∈ Finset.range (n + 1), n.choose k • g k :=
      sum_degreeOneExponent_degreeFunction n g
    _ = algebraicSymbol (fun _ : Fin 1 => n) T := by
      rw [algebraicSymbol_finOne_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      simp [g, mul_assoc]

end

end RealRooted.BorceaBranden
