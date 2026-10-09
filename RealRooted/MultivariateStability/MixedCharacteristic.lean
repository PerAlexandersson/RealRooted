import RealRooted.DeterminantalStability
import RealRooted.LiebSokalBoundary
import RealRooted.HomogeneousStability
import RealRooted.AffineLineRestriction
import RealRooted.MultivariateStability.SamePhase

open Matrix MvPolynomial
open scoped BigOperators MatrixOrder

noncomputable section

namespace RealRooted.MixedCharacteristic

/-!
# Mixed characteristic polynomials: stages 1--2

Following Marcus--Spielman--Srivastava, *Interlacing families II: mixed
characteristic polynomials and the Kadison--Singer problem*, Ann. of Math. (2)
182 (2015), we use the mixed-characteristic construction defined immediately
after Theorem 4.1 and its real-rootedness conclusion in Corollary 4.4.  Our
sign convention is

`det(x I + Σ z_i A_i)` followed by `∏ (1 - ∂_{z_i})`.

The singleton left block below is `x`; the right block contains the matrix
parameters.  Definitions 5.3 (above roots) and 5.4 (barrier functions), and
Theorem 5.1, concern the barrier argument.  In particular, the barrier bound,
which is the main theorem of issue #950, is not proved in this module.

The output variable is the singleton left block and the matrix parameters are
the right block.  This makes the `z = 0` specialization a common-phase
restriction with weights `1` on the output variable and `0` on the parameters.
-/

private def operatorList (m : ℕ) : List (Sum (Fin 1) (Fin m)) :=
  List.ofFn (fun i : Fin m => Sum.inr i)

private def pencilMatrices (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Sum (Fin 1) (Fin m) → Matrix (Fin n) (Fin n) ℝ
  | Sum.inl _ => 1
  | Sum.inr j => As j

private def pencil (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Sum (Fin 1) (Fin m)) ℝ :=
  realDetPencil 0 (pencilMatrices As)

private theorem pencil_homogeneous
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (pencil As).IsHomogeneous n := by
  unfold pencil realDetPencil
  let M : Matrix (Fin n) (Fin n)
      (MvPolynomial (Sum (Fin 1) (Fin m)) ℝ) := fun i j =>
    MvPolynomial.C ((0 : Matrix (Fin n) (Fin n) ℝ) i j) +
      ∑ k : Sum (Fin 1) (Fin m),
        MvPolynomial.X k * MvPolynomial.C (pencilMatrices As k i j)
  change Matrix.det M |>.IsHomogeneous n
  have hentry : ∀ i j, (M i j).IsHomogeneous 1 := by
    intro i j
    dsimp [M]
    simp only [map_zero, zero_add]
    apply MvPolynomial.IsHomogeneous.sum
    intro k hk
    simpa [mul_comm] using
      (MvPolynomial.isHomogeneous_X ℝ k).C_mul (pencilMatrices As k i j)
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  change (MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℝ)) *
    ∏ i, M (σ i) i).IsHomogeneous n
  have hp : (∏ i, M (σ i) i).IsHomogeneous
      (∑ i : Fin n, 1) := by
    apply MvPolynomial.IsHomogeneous.prod
    intro i hi
    simpa using (hentry (σ i) i)
  have hm :=
    (MvPolynomial.isHomogeneous_C (Fin 1 ⊕ Fin m)
      (((Equiv.Perm.sign σ : ℤ) : ℝ))).mul hp
  simpa using hm

private theorem totalDegree_pderiv_le
    {σ : Type*} {P : MvPolynomial σ ℝ} (i : σ) :
    (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro m hm
  have hcoeff : (MvPolynomial.pderiv i P).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hPcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro hzero
    simp [hzero] at hcoeff
  have hmem : m + Finsupp.single i 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hPcoeff
  have hle := Finset.le_sup (s := P.support)
    (f := fun s => s.sum fun _ e => e) hmem
  change m.sum (fun _ e => e) ≤ _
  calc
    m.sum (fun _ e => e) ≤ (m + Finsupp.single i 1).sum (fun _ e => e) := by
      simp [Finsupp.sum_add_index]
    _ ≤ P.support.sup (fun s => s.sum fun _ e => e) := hle

private theorem oneSubPderiv_sub_le
    {σ : Type*} {H P : MvPolynomial σ ℝ} {n : ℕ}
    (hH : H.IsHomogeneous n) (hP : (P - H).totalDegree ≤ n - 1) (i : σ) :
    (oneSubPderiv i P - H).totalDegree ≤ n - 1 := by
  classical
  have hderivH : (MvPolynomial.pderiv i H).totalDegree ≤ n - 1 := by
    unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro m hm
    have hcoeff : (MvPolynomial.pderiv i H).coeff m ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hcoeff
    have hHcoeff : H.coeff (m + Finsupp.single i 1) ≠ 0 := by
      intro hzero
      simp [hzero] at hcoeff
    have hmem : m + Finsupp.single i 1 ∈ H.support :=
      MvPolynomial.mem_support_iff.mpr hHcoeff
    have hhom := hH.degree_eq_sum_deg_support hmem
    have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) =
        m.sum (fun _ e => e) + 1 := by
      classical
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_single_index]
        simp
      · intro a ha
        simp
      · intro a ha b₁ b₂
        simp
    have hle : m.sum (fun _ e => e) + 1 ≤ n := by
      rw [← hsum]
      exact hhom.symm.le
    change m.sum (fun _ e => e) ≤ n - 1
    exact Nat.le_sub_of_add_le hle
  have hderivP : (MvPolynomial.pderiv i P).totalDegree ≤ n - 1 := by
    rw [show P = H + (P - H) by ring]
    rw [map_add]
    calc
      (MvPolynomial.pderiv i H + MvPolynomial.pderiv i (P - H)).totalDegree ≤
          max (MvPolynomial.pderiv i H).totalDegree
            (MvPolynomial.pderiv i (P - H)).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ n - 1 := by
        refine max_le hderivH ?_
        exact (totalDegree_pderiv_le i).trans hP
  rw [oneSubPderiv]
  rw [show P - MvPolynomial.pderiv i P - H =
      (P - H) - MvPolynomial.pderiv i P by ring]
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hP hderivP)

private theorem oneSubPderivList_sub_le
    {σ : Type*} {H P : MvPolynomial σ ℝ} {n : ℕ}
    (hH : H.IsHomogeneous n) (hP : (P - H).totalDegree ≤ n - 1) (l : List σ) :
    (oneSubPderivList l P - H).totalDegree ≤ n - 1 := by
  induction l generalizing P with
  | nil => simpa only [oneSubPderivList_nil] using hP
  | cons i l ih =>
    rw [oneSubPderivList_cons]
    exact ih (oneSubPderiv_sub_le hH hP i)

private theorem pderiv_eq_zero_of_isHomogeneous_zero
    {σ : Type*} {H : MvPolynomial σ ℝ} (hH : H.IsHomogeneous 0) (i : σ) :
    MvPolynomial.pderiv i H = 0 := by
  classical
  ext m
  rw [MvPolynomial.coeff_pderiv]
  by_cases hcoeff : H.coeff (m + Finsupp.single i 1) = 0
  · simp [hcoeff]
  · have hmem : m + Finsupp.single i 1 ∈ H.support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hhom := hH.degree_eq_sum_deg_support hmem
    have hsumzero :
        ∑ x ∈ (m + Finsupp.single i 1).support,
          ((m + Finsupp.single i 1 : σ →₀ ℕ) x) = 0 := hhom.symm
    have hi : i ∈ (m + Finsupp.single i 1).support := by
      rw [Finsupp.mem_support_iff]
      simp
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      (show (0 : ℕ) ≤ (m + Finsupp.single i 1 : σ →₀ ℕ) x by
        exact Nat.zero_le _))).mp hsumzero
    have hfalse : False := by
      have hi0 := hzero i hi
      simp at hi0
    exact hfalse.elim

private theorem oneSubPderiv_isHomogeneous_zero
    {σ : Type*} {H : MvPolynomial σ ℝ} (hH : H.IsHomogeneous 0) (i : σ) :
    oneSubPderiv i H = H := by
  unfold oneSubPderiv
  rw [pderiv_eq_zero_of_isHomogeneous_zero hH i]
  simp

private def outputWeights (m : ℕ) : Sum (Fin 1) (Fin m) → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- The multivariate polynomial before the final `z = 0` specialization. -/
def mixedCharacteristicMv (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    MvPolynomial (Sum (Fin 1) (Fin m)) ℝ :=
  oneSubPderivList (operatorList m) (pencil As)

/-- The mixed characteristic polynomial of the real square matrices `As`.

The singleton output coordinate represents `x`; every `Sum.inr` coordinate is
specialized to zero by the zero weights in `outputWeights`.
-/
def mixedCharacteristic (As : Fin m → Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  commonPhaseRestriction (outputWeights m) (mixedCharacteristicMv As)

private theorem commonPhaseRestriction_eq_realAffineLineRestriction
    {σ : Type*} (wt : σ → ℝ) (P : MvPolynomial σ ℝ) :
    commonPhaseRestriction wt P =
      realAffineLineRestriction (fun _ => 0) wt P := by
  unfold commonPhaseRestriction realAffineLineRestriction
  apply MvPolynomial.eval₂Hom_congr rfl
  · funext i
    simp
  · rfl

private theorem eval_realDetPencil
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Sum (Fin 1) (Fin m) → Matrix (Fin n) (Fin n) ℝ)
    (z : Sum (Fin 1) (Fin m) → ℝ) :
    MvPolynomial.eval z (realDetPencil A B) =
      (A + ∑ k, z k • B k).det := by
  unfold realDetPencil
  erw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change MvPolynomial.eval z
      (MvPolynomial.C (A i j) + ∑ k, MvPolynomial.X k * MvPolynomial.C (B k i j)) = _
  simp [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]

private theorem pencil_ne_zero
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) : pencil As ≠ 0 := by
  intro hzero
  have hzeroC : complexifyMv (pencil As) = 0 := by
    simp [hzero, complexifyMv]
  change complexifyMv (realDetPencil 0 (pencilMatrices As)) = 0 at hzeroC
  rw [complexifyMv_realDetPencil] at hzeroC
  have hEval := congrArg
    (MvPolynomial.eval (fun i : Sum (Fin 1) (Fin m) =>
      match i with
      | Sum.inl _ => (1 : ℂ)
      | Sum.inr _ => 0)) hzeroC
  rw [eval_detPencil] at hEval
  simp [pencilMatrices] at hEval

private theorem pencil_real_stable
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) :
    MvRealStable (pencil As) := by
  apply mvRealStable_realDetPencil
    (A := 0)
    (B := pencilMatrices As)
  · simp [Matrix.IsHermitian]
  · intro i
    cases i with
    | inl i => exact Matrix.PosSemidef.one
    | inr i => exact hAs i
  exact fun hzero => pencil_ne_zero As (by
    simpa only [complexifyMv] using
      (MvPolynomial.map_injective Complex.ofRealHom
        Complex.ofRealHom.injective hzero))

/-- The determinantal input is real stable for positive semidefinite data. -/
theorem mvRealStable_mixedCharacteristicMv
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) :
    MvRealStable (mixedCharacteristicMv As) := by
  exact (pencil_real_stable As hAs).oneSubPderivList (operatorList m)

/-- The mixed characteristic polynomial is split for positive semidefinite data. -/
theorem mixedCharacteristic_splits
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) :
    (mixedCharacteristic As).Splits := by
  exact (mvRealStable_mixedCharacteristicMv As hAs).samePhaseStable
    (outputWeights m) (by
      intro i
      cases i <;> simp [outputWeights])

private theorem mixedCharacteristic_natDegree_eq
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (mixedCharacteristic As).natDegree = n ∧
      (mixedCharacteristic As).coeff n = 1 := by
  let H : MvPolynomial (Sum (Fin 1) (Fin m)) ℝ := pencil As
  let Q : MvPolynomial (Sum (Fin 1) (Fin m)) ℝ := mixedCharacteristicMv As
  have hH : H.IsHomogeneous n := by
    exact pencil_homogeneous As
  have hQ : (Q - H).totalDegree ≤ n - 1 := by
    apply oneSubPderivList_sub_le hH
    simp [H]
  have hcommon (P : MvPolynomial (Sum (Fin 1) (Fin m)) ℝ) :
      commonPhaseRestriction (outputWeights m) P =
        realAffineLineRestriction (fun _ => 0) (outputWeights m) P :=
    commonPhaseRestriction_eq_realAffineLineRestriction _ _
  have hzero : MvPolynomial.eval (fun i : Sum (Fin 1) (Fin m) =>
      outputWeights m i) H = 1 := by
    change MvPolynomial.eval (fun i : Sum (Fin 1) (Fin m) =>
      match i with
      | Sum.inl _ => (1 : ℝ)
      | Sum.inr _ => 0) (pencil As) = 1
    rw [show pencil As = realDetPencil 0 (pencilMatrices As) by rfl]
    rw [eval_realDetPencil]
    simp [pencilMatrices]
  by_cases hn : n = 0
  · have hQeq : Q = H := by
      have hH0 : H.IsHomogeneous 0 := hn ▸ hH
      change oneSubPderivList (operatorList m) (pencil As) = pencil As
      induction operatorList m with
      | nil => simp
      | cons i l ih =>
        rw [oneSubPderivList_cons]
        rw [oneSubPderiv_isHomogeneous_zero hH0 i]
        exact ih
    have hcoeff :
      (commonPhaseRestriction (outputWeights m) Q).coeff n = 1 := by
      rw [hQeq, hcommon]
      rw [RealRooted.MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction hH]
      simpa using hzero
    have hnat : (commonPhaseRestriction (outputWeights m) Q).natDegree = n := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · rw [hQeq, hcommon]
        exact RealRooted.MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
          hH _ _
      · rw [hcoeff]
        norm_num
    exact ⟨hnat, hcoeff⟩
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hDdeg :
        (commonPhaseRestriction (outputWeights m) (Q - H)).natDegree ≤ n - 1 := by
      rw [hcommon]
      exact (MvPolynomial.natDegree_affineLineRestriction_le _ _ _).trans hQ
    have hHdeg :
        (commonPhaseRestriction (outputWeights m) H).natDegree ≤ n := by
      rw [hcommon]
      exact RealRooted.MvPolynomial.IsHomogeneous.natDegree_realAffineLineRestriction_le
        hH _ _
    have hQdeg :
        (commonPhaseRestriction (outputWeights m) Q).natDegree ≤ n := by
      have heq : commonPhaseRestriction (outputWeights m) Q =
          commonPhaseRestriction (outputWeights m) H +
            commonPhaseRestriction (outputWeights m) (Q - H) := by
        unfold commonPhaseRestriction
        rw [← map_add]
        congr 1
        ring
      rw [heq]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le hHdeg (hDdeg.trans (Nat.sub_le _ _)))
    have hcoeffD :
        (commonPhaseRestriction (outputWeights m) (Q - H)).coeff n = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt hDdeg (Nat.sub_lt hnpos (by decide)))
    have hcoeff :
        (commonPhaseRestriction (outputWeights m) Q).coeff n = 1 := by
      rw [show commonPhaseRestriction (outputWeights m) Q =
          commonPhaseRestriction (outputWeights m) H +
            commonPhaseRestriction (outputWeights m) (Q - H) by
        unfold commonPhaseRestriction
        rw [← map_add]
        congr 1
        ring, Polynomial.coeff_add, hcoeffD]
      rw [hcommon, RealRooted.MvPolynomial.IsHomogeneous.coeff_realAffineLineRestriction hH]
      simpa using hzero
    have hnat : (commonPhaseRestriction (outputWeights m) Q).natDegree = n :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hQdeg (by
        rw [hcoeff]
        norm_num)
    exact ⟨hnat, hcoeff⟩

/-- The determinant construction is monic of degree `n`, without positivity
assumptions on the matrix parameters. -/
theorem mixedCharacteristic_monic
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (mixedCharacteristic As).Monic := by
  have hdata := mixedCharacteristic_natDegree_eq As
  unfold Polynomial.Monic
  rw [← Polynomial.coeff_natDegree, hdata.1]
  exact hdata.2

/-- The mixed characteristic polynomial has the matrix-size degree. -/
theorem natDegree_mixedCharacteristic
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    (mixedCharacteristic As).natDegree = n := by
  exact (mixedCharacteristic_natDegree_eq As).1

/-- The real-rootedness statement for PSD data, including nonvanishing. -/
theorem isRealRooted_mixedCharacteristic
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) :
    mixedCharacteristic As ≠ 0 ∧ (mixedCharacteristic As).Splits := by
  refine ⟨?_, mixedCharacteristic_splits As hAs⟩
  have hmonic := mixedCharacteristic_monic As
  intro hzero
  rw [hzero, Polynomial.Monic] at hmonic
  simp at hmonic

/-- The one-by-one, one-matrix case is the sanity check `μ[x + za] = x`. -/
theorem mixedCharacteristic_fin_one_fin_one
    (A : Matrix (Fin 1) (Fin 1) ℝ) :
    mixedCharacteristic (m := 1) (n := 1) (fun _ => A) =
      Polynomial.X - Polynomial.C (A 0 0) := by
  have hp : pencil (m := 1) (n := 1) (fun _ => A) =
      MvPolynomial.X (Sum.inl (0 : Fin 1)) * MvPolynomial.C 1 +
        MvPolynomial.X (Sum.inr (0 : Fin 1)) *
          MvPolynomial.C (A 0 0) := by
    unfold pencil realDetPencil
    let M : Matrix (Fin 1) (Fin 1) (MvPolynomial (Sum (Fin 1) (Fin 1)) ℝ) :=
      fun i j => MvPolynomial.C ((0 : Matrix (Fin 1) (Fin 1) ℝ) i j) +
        ∑ k : Sum (Fin 1) (Fin 1),
          MvPolynomial.X k * MvPolynomial.C (pencilMatrices (fun _ => A) k i j)
    change Matrix.det M = _
    rw [Matrix.det_fin_one M]
    simp [M, pencilMatrices]
  rw [show mixedCharacteristic (m := 1) (n := 1) (fun _ => A) =
      commonPhaseRestriction (outputWeights 1)
        (oneSubPderivList (operatorList 1)
          (pencil (m := 1) (n := 1) (fun _ => A)) :
          MvPolynomial (Sum (Fin 1) (Fin 1)) ℝ) by rfl]
  rw [hp]
  simp [commonPhaseRestriction, operatorList, oneSubPderiv,
    outputWeights]

/-- Two coordinate rank-one projections give the explicit polynomial
`(X - 1)^2`.
-/
theorem mixedCharacteristic_two_rank_one :
    mixedCharacteristic (m := 2) (n := 2)
      (fun i : Fin 2 => match i with
      | 0 => Matrix.diagonal ![1, 0]
      | 1 => Matrix.diagonal ![0, 1]) =
      (Polynomial.X - Polynomial.C 1) ^ 2 := by
  let x : MvPolynomial (Sum (Fin 1) (Fin 2)) ℝ :=
    MvPolynomial.X (Sum.inl 0)
  let y : MvPolynomial (Sum (Fin 1) (Fin 2)) ℝ :=
    MvPolynomial.X (Sum.inr 0)
  let z : MvPolynomial (Sum (Fin 1) (Fin 2)) ℝ :=
    MvPolynomial.X (Sum.inr 1)
  let P : MvPolynomial (Sum (Fin 1) (Fin 2)) ℝ :=
    x ^ 2 + x * y + x * z + y * z
  have hp : pencil (m := 2) (n := 2)
      (fun i : Fin 2 => match i with
      | 0 => Matrix.diagonal ![1, 0]
      | 1 => Matrix.diagonal ![0, 1]) = P := by
    unfold pencil realDetPencil
    let M : Matrix (Fin 2) (Fin 2)
        (MvPolynomial (Sum (Fin 1) (Fin 2)) ℝ) := fun i j =>
      MvPolynomial.C ((0 : Matrix (Fin 2) (Fin 2) ℝ) i j) +
        ∑ k : Sum (Fin 1) (Fin 2),
          MvPolynomial.X k *
            MvPolynomial.C ((pencilMatrices (fun i : Fin 2 => match i with
              | 0 => Matrix.diagonal ![1, 0]
              | 1 => Matrix.diagonal ![0, 1]) k) i j)
    change Matrix.det M = _
    rw [Matrix.det_fin_two M]
    simp [M, pencilMatrices]
    ring
  have hy : MvPolynomial.pderiv (Sum.inr (0 : Fin 2)) P = x + z := by
    simp [P, x, y, z]
  have hz : MvPolynomial.pderiv (Sum.inr (1 : Fin 2)) P = x + y := by
    simp [P, x, y, z]
  have hsecond : MvPolynomial.pderiv (Sum.inr (1 : Fin 2)) (P - (x + z)) =
      x + y - 1 := by
    rw [map_sub, hz]
    simp [x, z]
  unfold mixedCharacteristic mixedCharacteristicMv
  rw [hp]
  have hop : operatorList 2 =
      [Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)] := by
    decide
  rw [hop]
  rw [oneSubPderivList_cons, oneSubPderivList_cons]
  simp only [oneSubPderivList_nil]
  rw [show oneSubPderiv (Sum.inr (0 : Fin 2)) P = P - (x + z) by
    rw [oneSubPderiv, hy]]
  rw [oneSubPderiv, hsecond]
  simp [commonPhaseRestriction, outputWeights, x, y, z, P]
  ring

end RealRooted.MixedCharacteristic
