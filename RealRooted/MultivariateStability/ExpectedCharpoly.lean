module

public import RealRooted.MultivariateStability.MixedCharacteristic
public import RealRooted.Mathlib.LinearAlgebra.Matrix.RankOneExpectation

/-!
# Expected characteristic polynomials of rank-one sums

Marcus–Spielman–Srivastava, *Interlacing families II*, Theorem 4.1: for independent random
vectors `vᵢ` with finitely supported distributions, `E det (x I - Σᵢ vᵢ vᵢᵀ)` is the mixed
characteristic polynomial `μ[A₁, …, Aₘ]` of the second moments `Aᵢ = E[vᵢ vᵢᵀ]`
(`expectedCharpoly_eq_mixedCharacteristic`, issue #1294).  The proof was found by Aristotle
and adapted to the repository definitions.
-/

@[expose] public noncomputable section

open Matrix MvPolynomial Polynomial
open scoped BigOperators

namespace RealRooted.MixedCharacteristic

/-! ## Finite independent random vectors -/

/-- The second-moment matrix `E[v vᵀ] = Σⱼ p j • v j v jᵀ` of a finite distribution. -/
def secondMoment {n : ℕ} {ι : Type} [Fintype ι] (v : ι → Fin n → ℝ) (p : ι → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ j, p j • Matrix.vecMulVec (v j) (v j)

/-- `E det (x I - Σᵢ vᵢ vᵢᵀ)`: the expectation over the product distribution on
`∏ᵢ ι i` (independent `vᵢ`) of the characteristic polynomial of `Σᵢ vᵢ vᵢᵀ`. -/
def expectedCharpoly {m n : ℕ} (ι : Fin m → Type) [∀ i, Fintype (ι i)]
    (v : ∀ i, ι i → Fin n → ℝ) (p : ∀ i, ι i → ℝ) : ℝ[X] :=
  ∑ s : (i : Fin m) → ι i,
    (∏ i, p i (s i)) •
      (∑ i, Matrix.vecMulVec (v i (s i)) (v i (s i))).charpoly

/-! ## Auxiliary multivariate lemmas -/

section MvAux

variable {σ : Type*} [DecidableEq σ]

/-- Substitute `X i ↦ 0`. -/
private def zeroAt (i : σ) : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ :=
  MvPolynomial.aeval fun j => if j = i then 0 else MvPolynomial.X j

/-- View a multivariate polynomial as a polynomial in `X i`. -/
private def toPolyAt (i : σ) : MvPolynomial σ ℝ →ₐ[ℝ] Polynomial (MvPolynomial σ ℝ) :=
  MvPolynomial.aeval fun j => if j = i then Polynomial.X else Polynomial.C (MvPolynomial.X j)

private lemma pderiv_zeroAt {i j : σ} (h : j ≠ i) (P : MvPolynomial σ ℝ) :
    MvPolynomial.pderiv j (zeroAt i P) = zeroAt i (MvPolynomial.pderiv j P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [zeroAt]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    by_cases hk : k = i
    · subst hk
      simp [zeroAt, MvPolynomial.pderiv_X, h]
    · simp [zeroAt, hk, MvPolynomial.pderiv_X, Pi.single_apply]

private lemma eval_toPolyAt (i : σ) (P : MvPolynomial σ ℝ) :
    (toPolyAt i P).eval 0 = zeroAt i P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [toPolyAt, zeroAt, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, map_mul, Polynomial.eval_mul, hp]
    by_cases hk : k = i <;> simp [toPolyAt, zeroAt, hk]

private lemma derivative_toPolyAt (i : σ) (P : MvPolynomial σ ℝ) :
    Polynomial.derivative (toPolyAt i P) = toPolyAt i (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [toPolyAt, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, map_add, smul_eq_mul,
      smul_eq_mul, map_mul, map_mul]
    by_cases hk : k = i
    · subst hk; simp [toPolyAt, MvPolynomial.pderiv_X]; ring
    · simp [toPolyAt, hk, MvPolynomial.pderiv_X]; ring

private lemma zeroAt_oneSubPderiv {i j : σ} (h : j ≠ i) (P : MvPolynomial σ ℝ) :
    zeroAt i (oneSubPderiv j P) = oneSubPderiv j (zeroAt i P) := by
  simp [oneSubPderiv, map_sub, pderiv_zeroAt h]

private lemma zeroAt_oneSubPderivList (i : σ) (l : List σ) (hi : i ∉ l)
    (P : MvPolynomial σ ℝ) :
    zeroAt i (oneSubPderivList l P) = oneSubPderivList l (zeroAt i P) := by
  induction l generalizing P with
  | nil => rfl
  | cons j l ih =>
    have hj : j ≠ i := fun h => hi (h ▸ List.mem_cons_self)
    have hl : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    rw [oneSubPderivList_cons, oneSubPderivList_cons, ih hl, zeroAt_oneSubPderiv hj]

omit [DecidableEq σ] in
private lemma oneSubPderivList_sum {κ : Type*} [Fintype κ] (l : List σ) (c : κ → ℝ)
    (P : κ → MvPolynomial σ ℝ) :
    oneSubPderivList l (∑ j, c j • P j) = ∑ j, c j • oneSubPderivList l (P j) := by
  induction l generalizing P with
  | nil => rfl
  | cons a l ih =>
    simp only [oneSubPderivList_cons]
    have : oneSubPderiv a (∑ j, c j • P j) = ∑ j, c j • oneSubPderiv a (P j) := by
      simp [oneSubPderiv, map_sum, smul_sub, Finset.sum_sub_distrib]
    rw [this, ih]

private lemma aeval_zeroAt (e : σ → ℝ[X]) (i : σ) (he : e i = 0)
    (P : MvPolynomial σ ℝ) :
    MvPolynomial.aeval e (zeroAt i P) = MvPolynomial.aeval e P := by
  have : (MvPolynomial.aeval e).comp (zeroAt i) = MvPolynomial.aeval e := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i
    · subst hj; simp [zeroAt, he]
    · simp [zeroAt, hj]
  exact congrArg (fun F => F P) this

variable [Fintype σ] {n : ℕ}

/-- `C B0 + Σ X k * C (B k)`. -/
private def Qmat (B0 : Matrix (Fin n) (Fin n) ℝ)
    (B : σ → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ) :=
  Matrix.of fun a b => MvPolynomial.C (B0 a b) + ∑ k, MvPolynomial.X k * MvPolynomial.C (B k a b)

private lemma toPolyAt_Qmat (i : σ) (B0 : Matrix (Fin n) (Fin n) ℝ)
    (B : σ → Matrix (Fin n) (Fin n) ℝ) :
    (toPolyAt i).mapMatrix (Qmat B0 B) =
      (Qmat B0 (Function.update B i 0)).map Polynomial.C +
        (Polynomial.X : Polynomial (MvPolynomial σ ℝ)) •
          ((B i).map MvPolynomial.C).map Polynomial.C := by
  refine Matrix.ext fun a b => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Qmat, Matrix.of_apply, map_add, map_sum,
    map_mul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 : ∀ k, toPolyAt i (MvPolynomial.X k) * toPolyAt i (MvPolynomial.C (B k a b)) =
      (if k = i then Polynomial.X * Polynomial.C (MvPolynomial.C (B i a b)) else 0) +
        Polynomial.C (MvPolynomial.X k) *
          Polynomial.C (MvPolynomial.C (Function.update B i 0 k a b)) := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [toPolyAt, Polynomial.algebraMap_apply]
    · simp [toPolyAt, hk, Polynomial.algebraMap_apply]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [toPolyAt, Polynomial.algebraMap_apply]
  ring

omit [DecidableEq σ] in
private lemma Qmat_sub (B0 : Matrix (Fin n) (Fin n) ℝ)
    (B : σ → Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) :
    Qmat (B0 - Matrix.vecMulVec u u) B =
      Qmat B0 B - (Matrix.vecMulVec u u).map MvPolynomial.C := by
  refine Matrix.ext fun a b => ?_
  simp [Qmat]
  ring

/-- Applying `(1 - ∂ᵢ)` and then setting `Xᵢ = 0` gives the expected rank-one update. -/
private lemma zeroAt_oneSubPderiv_Qdet (i : σ) (B0 : Matrix (Fin n) (Fin n) ℝ)
    (B : σ → Matrix (Fin n) (Fin n) ℝ) {κ : Type} [Fintype κ]
    (v : κ → Fin n → ℝ) (p : κ → ℝ)
    (hp : ∑ j, p j = 1) (hB : B i = secondMoment v p) :
    zeroAt i (oneSubPderiv i (Qmat B0 B).det) =
      ∑ j, p j • (Qmat (B0 - Matrix.vecMulVec (v j) (v j)) (Function.update B i 0)).det := by
  rw [oneSubPderiv, ← eval_toPolyAt, map_sub, ← derivative_toPolyAt, AlgHom.map_det,
    toPolyAt_Qmat, Matrix.eval_one_sub_derivative_det_add_X_smul, hB, secondMoment]
  simp only [Qmat_sub, MvPolynomial.smul_eq_C_mul]
  rw [Matrix.expected_det_sub_vecMulVec MvPolynomial.C _ v p hp]

/-- Independence: averaging over coordinate `i` separately. -/
private lemma indep_sum {τ : Type*} [Fintype τ] [DecidableEq τ]
    (ι : τ → Type) [∀ i, Fintype (ι i)]
    (p : ∀ i, ι i → ℝ) (i : τ) (hp : ∑ a, p i a = 1) {V : Type*} [AddCommMonoid V]
    [Module ℝ V] (f : ι i → (∀ j, ι j) → V)
    (hf : ∀ a b s, f a (Function.update s i b) = f a s) :
    ∑ a, p i a • ∑ s, (∏ j, p j (s j)) • f a s =
      ∑ s, (∏ j, p j (s j)) • f (s i) s := by
  have hprod : ∀ (s : ∀ j, ι j) (a : ι i),
      p i (s i) * ∏ j, p j (Function.update s i a j) = p i a * ∏ j, p j (s j) := by
    intro s a
    rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => p j (s j))]
    simp only [Function.update_self]
    have : ∏ j ∈ {i}ᶜ, p j (Function.update s i a j) = ∏ j ∈ {i}ᶜ, p j (s j) :=
      Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (by simpa using hj)]
    rw [this]; ring
  let Φ : ι i × (∀ j, ι j) ≃ ι i × (∀ j, ι j) :=
    { toFun := fun x => (x.2 i, Function.update x.2 i x.1)
      invFun := fun x => (x.2 i, Function.update x.2 i x.1)
      left_inv := fun x => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun x => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  let G : ι i × (∀ j, ι j) → V := fun x => p i x.1 • (∏ j, p j (x.2 j)) • f x.1 x.2
  have hL : ∑ a, p i a • ∑ s, (∏ j, p j (s j)) • f a s = ∑ x, G x := by
    rw [Fintype.sum_prod_type]
    simp only [G, Finset.smul_sum]
  rw [hL, ← Equiv.sum_comp Φ G, Fintype.sum_prod_type]
  have hG : ∀ a s, G (Φ (a, s)) = p i a • (∏ j, p j (s j)) • f (s i) s := by
    intro a s
    simp only [G, Φ, Equiv.coe_fn_mk, hf, smul_smul, hprod]
  simp only [hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_smul, hp, one_smul]

/-- The general induction statement, peeling one independent vector at a time. -/
private theorem main_general {τ : Type*} [Fintype τ] [DecidableEq τ] {n : ℕ}
    (ι : τ → Type)
    [∀ i, Fintype (ι i)] (v : ∀ i, ι i → Fin n → ℝ) (p : ∀ i, ι i → ℝ)
    (hp1 : ∀ i, ∑ j, p i j = 1) (l : List τ) (hl : l.Nodup) :
    ∀ (B0 : Matrix (Fin n) (Fin n) ℝ) (B : τ → Matrix (Fin n) (Fin n) ℝ)
      (e : τ → ℝ[X]),
      (∀ i ∈ l, e i = 0) → (∀ i ∈ l, B i = secondMoment (v i) (p i)) →
      MvPolynomial.aeval e (oneSubPderivList l (Qmat B0 B).det) =
        ∑ s : (∀ i, ι i), (∏ i, p i (s i)) •
          (Matrix.of fun a b => Polynomial.C ((B0 -
            (l.map fun i => Matrix.vecMulVec (v i (s i)) (v i (s i))).sum) a b) +
              ∑ k, e k * Polynomial.C (B k a b)).det := by
  induction l with
  | nil =>
    intro B0 B e _ _
    simp only [List.map_nil, List.sum_nil, sub_zero]
    rw [← Finset.sum_smul, ← Fintype.prod_sum, Finset.prod_congr rfl fun i _ => hp1 i,
      Finset.prod_const_one, one_smul]
    change MvPolynomial.aeval e (Qmat B0 B).det = _
    rw [AlgHom.map_det]
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [Qmat, Polynomial.algebraMap_eq]
  | cons i l ih =>
    intro B0 B e he hB
    obtain ⟨hi, hl'⟩ := List.nodup_cons.mp hl
    have he' : ∀ k ∈ l, e k = 0 := fun k hk => he k (List.mem_cons_of_mem _ hk)
    have hB' : ∀ k ∈ l, Function.update B i 0 k = secondMoment (v k) (p k) := by
      intro k hk
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      rw [Function.update_of_ne hki]
      exact hB k (List.mem_cons_of_mem _ hk)
    rw [oneSubPderivList_cons, ← aeval_zeroAt e i (he i List.mem_cons_self),
      zeroAt_oneSubPderivList i l hi,
      zeroAt_oneSubPderiv_Qdet i B0 B (v i) (p i) (hp1 i) (hB i List.mem_cons_self),
      oneSubPderivList_sum, map_sum]
    simp only [map_smul, ih hl' _ _ e he' hB']
    have hupd : ∀ a b, ∑ k, e k * Polynomial.C (Function.update B i 0 k a b) =
        ∑ k, e k * Polynomial.C (B k a b) := by
      intro a b
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · subst hk; simp [he k List.mem_cons_self]
      · rw [Function.update_of_ne hk]
    simp only [hupd]
    have key := indep_sum ι p i (hp1 i) (fun a s =>
      (Matrix.of fun a' b' => Polynomial.C ((B0 - Matrix.vecMulVec (v i a) (v i a) -
        (l.map fun k => Matrix.vecMulVec (v k (s k)) (v k (s k))).sum) a' b') +
          ∑ k, e k * Polynomial.C (B k a' b')).det) (by
        intro a b s
        have : (l.map fun k => Matrix.vecMulVec (v k (Function.update s i b k))
            (v k (Function.update s i b k))) =
            l.map fun k => Matrix.vecMulVec (v k (s k)) (v k (s k)) := by
          refine List.map_congr_left fun k hk => ?_
          have hki : k ≠ i := fun h => hi (h ▸ hk)
          rw [Function.update_of_ne hki]
        simp only [this])
    refine key.trans ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [List.map_cons, List.sum_cons, sub_sub]

end MvAux

/-! ## Extending the distributions to the `x` variable -/

/-- Index types extended by a trivial `Unit` distribution at the `x` variable. -/
private def extIdx {m : ℕ} (ι : Fin m → Type) : Fin 1 ⊕ Fin m → Type :=
  Sum.elim (fun _ => Unit) ι

private instance instFintypeExtIdx {m : ℕ} (ι : Fin m → Type) [∀ i, Fintype (ι i)] :
    ∀ i, Fintype (extIdx ι i)
  | Sum.inl _ => inferInstanceAs (Fintype Unit)
  | Sum.inr j => inferInstanceAs (Fintype (ι j))

/-- Vectors extended by `0` at the `x` variable. -/
private def extV {m n : ℕ} {ι : Fin m → Type} (v : ∀ i, ι i → Fin n → ℝ) :
    ∀ i, extIdx ι i → Fin n → ℝ
  | Sum.inl _ => fun _ => 0
  | Sum.inr j => v j

/-- Probabilities extended by `1` at the `x` variable. -/
private def extP {m : ℕ} {ι : Fin m → Type} (p : ∀ i, ι i → ℝ) :
    ∀ i, extIdx ι i → ℝ
  | Sum.inl _ => fun _ => 1
  | Sum.inr j => p j

/-- Forget the trivial coordinate. -/
private def extEquiv {m : ℕ} (ι : Fin m → Type) : (∀ i, extIdx ι i) ≃ (∀ i, ι i) where
  toFun s i := s (Sum.inr i)
  invFun s i := match i with
    | Sum.inl _ => ()
    | Sum.inr j => s j
  left_inv s := by
    funext i
    rcases i with i | i
    · rfl
    · rfl
  right_inv s := rfl

/-! ## Main theorem (MSS, Theorem 4.1) -/

/-- Marcus--Spielman--Srivastava, Theorem 4.1: for independent random vectors `vᵢ` with
finitely supported distributions and `Aᵢ = E[vᵢ vᵢᵀ]`,
`E det (x I - Σ vᵢ vᵢᵀ) = μ[A₁, …, A_m](x)`. -/
theorem expectedCharpoly_eq_mixedCharacteristic {m n : ℕ}
    (ι : Fin m → Type) [∀ i, Fintype (ι i)]
    (v : ∀ i, ι i → Fin n → ℝ) (p : ∀ i, ι i → ℝ)
    (hp1 : ∀ i, ∑ j, p i j = 1) :
    expectedCharpoly ι v p = mixedCharacteristic (fun i => secondMoment (v i) (p i)) := by
  classical
  set l : List (Fin 1 ⊕ Fin m) := List.ofFn fun i : Fin m => (Sum.inr i : Fin 1 ⊕ Fin m)
    with hl
  set e : Fin 1 ⊕ Fin m → ℝ[X] := fun i => Polynomial.C (outputWeights m i) * Polynomial.X
    with he
  have hnodup : l.Nodup := List.nodup_ofFn.mpr Sum.inr_injective
  have hmem : ∀ i ∈ l, ∃ j : Fin m, i = Sum.inr j := by
    intro i hi
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi
    exact ⟨j, hj.symm⟩
  have he0 : ∀ i ∈ l, e i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := hmem i hi
    simp [he, outputWeights]
  have hB : ∀ i ∈ l, pencilMatrices (fun i => secondMoment (v i) (p i)) i =
      secondMoment (extV v i) (extP p i) := by
    intro i hi
    obtain ⟨j, rfl⟩ := hmem i hi
    rfl
  have hp1' : ∀ i, ∑ j, extP p i j = 1 := by
    intro i
    rcases i with i | i
    · change ∑ _j : Unit, (1 : ℝ) = 1
      simp
    · exact hp1 i
  have hmain := main_general (extIdx ι) (extV v) (extP p) hp1' l hnodup 0
    (pencilMatrices fun i => secondMoment (v i) (p i)) e he0 hB
  have hpencil : pencil (fun i => secondMoment (v i) (p i)) =
      (Qmat 0 (pencilMatrices fun i => secondMoment (v i) (p i))).det := by
    unfold pencil
    congr 1
  have hcpr : ∀ P, commonPhaseRestriction (outputWeights m) P = MvPolynomial.aeval e P := by
    intro P
    simp [commonPhaseRestriction, he, MvPolynomial.aeval_def, Polynomial.algebraMap_eq]
  have hop : operatorList m = l := by
    rw [hl]
    rfl
  unfold mixedCharacteristic mixedCharacteristicMv
  rw [hcpr, hpencil, hop, hmain, expectedCharpoly]
  symm
  refine Fintype.sum_equiv (extEquiv ι) _ _ fun s => ?_
  congr 1
  · rw [Fintype.prod_sum_type]
    change (∏ _ : Fin 1, (1 : ℝ)) * (∏ i, p i (s (Sum.inr i))) =
      ∏ i, p i (s (Sum.inr i))
    simp only [Finset.prod_const_one, one_mul]
  · rw [Matrix.charpoly]
    congr 1
    refine Matrix.ext fun a b => ?_
    simp only [hl, List.map_ofFn, List.sum_ofFn, Matrix.of_apply, Fintype.sum_sum_type,
      Matrix.charmatrix_apply, he, outputWeights, pencilMatrices]
    have hext : ∀ i, extEquiv ι s i = s (Sum.inr i) := fun _ => rfl
    simpa [extV, hext, Matrix.one_apply, Matrix.diagonal_apply, sub_eq_add_neg] using
      (add_comm _ _)

end RealRooted.MixedCharacteristic
