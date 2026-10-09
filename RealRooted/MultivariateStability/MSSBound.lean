import RealRooted.MultivariateStability.BarrierStart
import RealRooted.MultivariateStability.BarrierUpdate
import RealRooted.MultivariateStability.Diagonal
import RealRooted.MultivariateStability.MixedCharacteristic

open Matrix MvPolynomial
open scoped BigOperators MatrixOrder

namespace RealRooted.MixedCharacteristic

noncomputable section

/-!
# The Marcus–Spielman–Srivastava root bound

Let `A_1, …, A_m` be real positive semidefinite `n × n` matrices with `Σ A_i = 1` and
`tr A_i ≤ ε`.  Then every root of the mixed characteristic polynomial
`μ[A](x) = Π_i (1 − ∂_{z_i}) det(x·1 + Σ z_i A_i) |_{z = 0}` is at most `(1 + √ε)²`
(`mixedCharacteristic_roots_le_optimized`; A. W. Marcus, D. A. Spielman and N. Srivastava,
*Interlacing families II*, Ann. of Math. 182 (2015), Theorem 5.1).

The proof follows MSS §5.  With `Σ A_i = 1`, `μ(x)` is the diagonal value of
`Q = Π (1 − ∂_i) det(Σ y_i A_i)` (`mixedCharacteristic_eq_diagonal`, Lemma 5.2: the operators
`1 − ∂_i` commute with the translation `y = z + x·1`).  At `t·1` every barrier
`Φ_i = ∂_i log det` equals `tr A_i / t ≤ ε / t` (`BarrierStart`); each step `1 − ∂_i` moves the
point by `δ = 1/(1 − ε/t)` in coordinate `i` and keeps it above the roots without increasing any
barrier (`BarrierUpdate`, Lemma 5.11, proved through the Pick-function route of `BarrierCross`
instead of the Helton–Vinnikov theorem).  So all roots of `μ` are at most `t + δ`, and
`t = ε + √ε` gives `(1 + √ε)²`.
-/

private def stageIndices {m : ℕ} (k : ℕ) (hk : k ≤ m) : List (Fin m) :=
  List.ofFn (fun i : Fin k => ⟨i.1, Nat.lt_of_lt_of_le i.isLt hk⟩)

private theorem stageIndices_succ {m k : ℕ} (hk : k + 1 ≤ m) :
    stageIndices (k + 1) hk =
      stageIndices k (Nat.le_trans (Nat.le_succ k) hk) ++
        [⟨k, Nat.lt_of_succ_le hk⟩] := by
  rw [stageIndices, List.ofFn_succ_last]
  congr 1

private def stage {m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    (k : ℕ) → k ≤ m → MvPolynomial (Fin m) ℝ
  | k, hk => oneSubPderivList (stageIndices k hk) P

private theorem oneSubPderivList_append {m : ℕ} {l₁ l₂ : List (Fin m)}
    (P : MvPolynomial (Fin m) ℝ) :
    oneSubPderivList (l₁ ++ l₂) P =
      oneSubPderivList l₂ (oneSubPderivList l₁ P) := by
  induction l₁ generalizing P with
  | nil => simp only [List.nil_append, oneSubPderivList_nil]
  | cons i l ih =>
      simp only [List.cons_append, oneSubPderivList_cons]
      exact ih (oneSubPderiv i P)

private theorem stage_succ {m k : ℕ} (P : MvPolynomial (Fin m) ℝ) (hk : k + 1 ≤ m) :
    stage P (k + 1) hk =
      oneSubPderiv ⟨k, Nat.lt_of_succ_le hk⟩
        (stage P k (Nat.le_trans (Nat.le_succ k) hk)) := by
  simp only [stage, stageIndices_succ, oneSubPderivList_append,
    oneSubPderivList_cons, oneSubPderivList_nil]

private theorem stage_zero {m : ℕ} (P : MvPolynomial (Fin m) ℝ) (hk : 0 ≤ m) :
    stage P 0 hk = P := by
  change oneSubPderivList [] P = P
  simp only [oneSubPderivList_nil]

private def point {m : ℕ} (t δ : ℝ) (k : ℕ) (_hk : k ≤ m) : Fin m → ℝ :=
  fun i => t + if i.1 < k then δ else 0

private theorem point_zero {m : ℕ} (t δ : ℝ) (hm : 0 ≤ m) :
    point t δ 0 hm = fun _ : Fin m => t := by
  funext i
  simp only [point, Nat.not_lt_zero, ↓reduceIte, add_zero]

private theorem point_succ {m k : ℕ} (t δ : ℝ) (hk : k + 1 ≤ m) :
    point t δ (k + 1) hk =
      point t δ k (Nat.le_trans (Nat.le_succ k) hk) +
        δ • Function.update (0 : Fin m → ℝ) ⟨k, Nat.lt_of_succ_le hk⟩ 1 := by
  funext i
  simp only [point, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i.1 = k
  · have hieq : i = ⟨k, Nat.lt_of_succ_le hk⟩ := Fin.ext hi
    rw [hieq, Function.update_apply]
    simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte, mul_one, add_zero]
  · by_cases hlt : i.1 < k
    · have hlt' : i.1 < k + 1 := Nat.lt_trans hlt (Nat.lt_succ_self k)
      have hji : (⟨k, Nat.lt_of_succ_le hk⟩ : Fin m) ≠ i := by
        intro h
        exact hi (Fin.ext_iff.mp h.symm)
      rw [Function.update_apply]
      have hij : i ≠ (⟨k, Nat.lt_of_succ_le hk⟩ : Fin m) := Ne.symm hji
      simp only [hlt, hlt', ↓reduceIte, hij, Pi.zero_apply, mul_zero, add_zero]
    · have hlt' : ¬i.1 < k + 1 := by
        intro h
        exact hi (Nat.eq_of_lt_succ_of_not_lt h hlt)
      have hji : (⟨k, Nat.lt_of_succ_le hk⟩ : Fin m) ≠ i := by
        intro h
        exact hi (Fin.ext_iff.mp h.symm)
      rw [Function.update_apply]
      have hij : i ≠ (⟨k, Nat.lt_of_succ_le hk⟩ : Fin m) := Ne.symm hji
      simp only [hlt, hlt', ↓reduceIte, hij, Pi.zero_apply, mul_zero, add_zero]

private theorem point_full {m : ℕ} (t δ : ℝ) :
    point t δ m (le_refl m) = fun _ : Fin m => t + δ := by
  funext i
  have hi : i.1 < m := i.isLt
  simp only [point, hi, ↓reduceIte]

private theorem diagonal_ne_zero_of_aboveRoots {m : ℕ}
    {P : MvPolynomial (Fin m) ℝ} {c : ℝ}
    (habove : AboveRoots P (fun _ => c)) : MvPolynomial.diagonal P ≠ 0 := by
  intro hzero
  have hpos := habove (fun _ => 0) (fun _ => le_rfl)
  have hadd : (fun _ : Fin m => c) + (fun _ => 0) = fun _ => c := by
    funext i
    simp only [Pi.add_apply, add_zero]
  rw [hadd] at hpos
  have hdiag : 0 < (MvPolynomial.diagonal P).eval c := by
    rw [MvPolynomial.eval_diagonal]
    exact hpos
  rw [hzero, Polynomial.eval_zero] at hdiag
  exact (lt_irrefl 0 hdiag).elim

/-- Above a constant point, the diagonal has no root to its right. -/
theorem diagonal_eval_ne_zero_of_aboveRoots {m : ℕ}
    {P : MvPolynomial (Fin m) ℝ} {c x : ℝ}
  (habove : AboveRoots P (fun _ => c)) (hcx : c < x) :
    (MvPolynomial.diagonal P).eval x ≠ 0 := by
  have hpos := habove (fun _ => x - c) (fun _ => (sub_nonneg.mpr hcx.le))
  have hadd : (fun _ : Fin m => c) + (fun _ => x - c) = fun _ => x := by
    funext i
    dsimp
    ring
  rw [hadd] at hpos
  rw [MvPolynomial.eval_diagonal]
  exact hpos.ne'

private theorem induction_step {m : ℕ} {P : MvPolynomial (Fin m) ℝ}
    {t δ ε : ℝ} (hδ : 0 < δ) (hthreshold : ε / t ≤ 1 - 1 / δ)
    (hstable : MvRealStable P) (habove : AboveRoots P (point t δ 0 (Nat.zero_le m)))
    (hbarrier : ∀ i, barrier i P (point t δ 0 (Nat.zero_le m)) ≤ ε / t) :
    ∀ k (hk : k ≤ m),
      MvRealStable (stage P k hk) ∧
        AboveRoots (stage P k hk) (point t δ k hk) ∧
          ∀ i, barrier i (stage P k hk) (point t δ k hk) ≤ ε / t := by
  intro k
  induction k with
  | zero =>
      intro hk
      refine ⟨hstable, ?_, ?_⟩
      · simpa only [stage_zero, point_zero t δ (Nat.zero_le m)] using habove
      · intro i
        simpa only [stage_zero, point_zero t δ (Nat.zero_le m)] using hbarrier i
  | succ k ih =>
      intro hk
      have hk_le : k ≤ m := Nat.le_trans (Nat.le_succ k) hk
      obtain ⟨hstable_k, habove_k, hbarrier_k⟩ := ih hk_le
      let j : Fin m := ⟨k, Nat.lt_of_succ_le hk⟩
      have hbarrier_j : barrier j (stage P k hk_le) (point t δ k hk_le) ≤
          1 - 1 / δ := (hbarrier_k j).trans hthreshold
      have habove_succ := aboveRoots_sub_pderiv_of_barrier_le
        hstable_k habove_k hδ hbarrier_j
      have hstable_succ := hstable_k.oneSubPderiv j
      refine ⟨?_, ?_, ?_⟩
      · simpa only [stage_succ, j] using hstable_succ
      · simpa only [stage_succ, j, oneSubPderiv, point_succ] using habove_succ
      · intro i
        have hbarrier_succ := barrier_sub_pderiv_le_of_barrier_le (i := i)
          hstable_k habove_k hδ hbarrier_j
        have hbound := hbarrier_succ.trans (hbarrier_k i)
        simpa only [stage_succ, j, oneSubPderiv, point_succ] using hbound

/-- The ordered MSS updates keep the final diagonal roots at most `t + δ`. -/
theorem diagonal_roots_le_of_mss_induction {m : ℕ}
    {P : MvPolynomial (Fin m) ℝ} {t δ ε : ℝ}
    (hδ : 0 < δ) (hthreshold : ε / t ≤ 1 - 1 / δ)
    (hstable : MvRealStable P) (habove : AboveRoots P (point t δ 0 (Nat.zero_le m)))
    (hbarrier : ∀ i, barrier i P (point t δ 0 (Nat.zero_le m)) ≤ ε / t) :
    ∀ r ∈ (MvPolynomial.diagonal (stage P m (le_refl m))).roots, r ≤ t + δ := by
  obtain ⟨_, habove_m, _⟩ :=
    induction_step hδ hthreshold hstable habove hbarrier m (le_refl m)
  have hpoint : point t δ m (le_refl m) = fun _ : Fin m => t + δ := point_full t δ
  have habove_const : AboveRoots (stage P m (le_refl m)) (fun _ => t + δ) := by
    rw [← hpoint]
    exact habove_m
  have hdiag_ne : MvPolynomial.diagonal (stage P m (le_refl m)) ≠ 0 :=
    diagonal_ne_zero_of_aboveRoots habove_const
  intro r hr
  have hroot : (MvPolynomial.diagonal (stage P m (le_refl m))).IsRoot r :=
    (Polynomial.mem_roots hdiag_ne).mp hr
  by_contra hnot
  have hlt : t + δ < r := lt_of_not_ge hnot
  exact diagonal_eval_ne_zero_of_aboveRoots habove_const hlt
    (Polynomial.IsRoot.def.mp hroot)

/-- The determinant-pencil instance of the ordered MSS root endpoint. -/
theorem determinant_diagonal_roots_le {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) (hsum : ∑ i, As i = 1)
    {t δ ε : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hthreshold : ε / t ≤ 1 - 1 / δ)
    (htrace : ∀ i, (As i).trace ≤ ε) :
    ∀ r ∈ (MvPolynomial.diagonal
      (stage (realDetPencil 0 As) m (le_refl m))).roots, r ≤ t + δ := by
  have hPne : realDetPencil 0 As ≠ 0 := by
    intro hzero
    have hpos := realDetPencil_aboveRoots As hAs hsum ht
    have hpos0 := hpos (fun _ => 0) (fun _ => le_rfl)
    have hadd : (fun _ : Fin m => t) + (fun _ => 0) = fun _ => t := by
      funext i
      simp only [Pi.add_apply, add_zero]
    rw [hadd] at hpos0
    rw [hzero] at hpos0
    simp [MvPolynomial.eval] at hpos0
  have hcomplex : complexifyMv (realDetPencil 0 As) ≠ 0 := by
    intro hzero
    apply hPne
    exact MvPolynomial.map_injective Complex.ofRealHom
      Complex.ofRealHom.injective hzero
  have hstable : MvRealStable (realDetPencil 0 As) := by
    apply mvRealStable_realDetPencil 0 As
    · simp [Matrix.IsHermitian]
    · exact hAs
    · exact hcomplex
  have habove : AboveRoots (realDetPencil 0 As)
      (point t δ 0 (Nat.zero_le m)) := by
    simpa only [point_zero t δ (Nat.zero_le m)] using
      realDetPencil_aboveRoots As hAs hsum ht
  have hbarrier : ∀ i, barrier i (realDetPencil 0 As)
      (point t δ 0 (Nat.zero_le m)) ≤ ε / t := by
    intro i
    simpa only [point_zero t δ (Nat.zero_le m)] using
      realDetPencil_barrier_le_of_trace_le As hsum i ht (htrace i)
  exact diagonal_roots_le_of_mss_induction hδ hthreshold hstable habove hbarrier

/-! The remaining optimization is independent of the polynomial argument. -/

/-- At `t = ε + √ε`, the MSS update endpoint is `(1 + √ε)²`. -/
private theorem optimized_endpoint {ε : ℝ} (hε : 0 < ε) :
    ε + Real.sqrt ε + 1 / (1 - ε / (ε + Real.sqrt ε)) =
      (1 + Real.sqrt ε) ^ 2 := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsquare : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  have ht : 0 < ε + Real.sqrt ε := by positivity
  have hratio : ε / (ε + Real.sqrt ε) < 1 := by
    apply (div_lt_one ht).2
    linarith
  have hden : 0 < 1 - ε / (ε + Real.sqrt ε) := sub_pos.mpr hratio
  have hδ : 1 / (1 - ε / (ε + Real.sqrt ε)) = 1 + Real.sqrt ε := by
    apply (div_eq_iff hden.ne').2
    field_simp [ht.ne']
    nlinarith
  rw [hδ]
  nlinarith

/-! The exact reciprocal choice in MSS gives the threshold required above. -/

/-- For `0 ≤ ε < t`, the MSS update size is positive and satisfies its threshold. -/
private theorem update_parameter {ε t : ℝ} (hε : 0 ≤ ε) (hεt : ε < t) :
    let δ := 1 / (1 - ε / t)
    0 < δ ∧ ε / t ≤ 1 - 1 / δ := by
  dsimp
  have ht : 0 < t := lt_of_le_of_lt hε hεt
  have hratio : ε / t < 1 := (div_lt_one ht).mpr hεt
  have hden : 0 < 1 - ε / t := sub_pos.mpr hratio
  constructor
  · exact one_div_pos.mpr hden
  · have hinv : 1 / (1 / (1 - ε / t)) = 1 - ε / t := by
      rw [one_div_div]
      norm_num
    rw [hinv]
    linarith

private def shift {m : ℕ} :
    MvPolynomial (Fin m) ℝ →+* MvPolynomial (Sum (Fin 1) (Fin m)) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin m => MvPolynomial.X (Sum.inr i) +
      MvPolynomial.X (Sum.inl 0))

private theorem pderiv_shift {m : ℕ} (i : Fin m)
    (P : MvPolynomial (Fin m) ℝ) :
    MvPolynomial.pderiv (Sum.inr i) (shift P) =
      shift (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [shift, MvPolynomial.eval₂Hom_C, MvPolynomial.pderiv_C, map_zero]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P j hP =>
      rw [map_mul, MvPolynomial.pderiv_mul, hP]
      by_cases hji : j = i
      · subst j
        have hXi : shift (MvPolynomial.X i) =
            MvPolynomial.X (Sum.inr i) + MvPolynomial.X (Sum.inl 0) := by
          simp only [shift, MvPolynomial.eval₂Hom_X']
        have hpXi : MvPolynomial.pderiv (Sum.inr i)
            (MvPolynomial.X (Sum.inr i) + MvPolynomial.X (Sum.inl 0)) =
              (1 : MvPolynomial (Sum (Fin 1) (Fin m)) ℝ) := by
          rw [Derivation.map_add, MvPolynomial.pderiv_X_self,
            MvPolynomial.pderiv_X_of_ne (i := Sum.inr i) (j := Sum.inl 0) (by simp)]
          simp only [add_zero]
        rw [hXi, hpXi]
        simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X_self]
        simp only [map_mul, mul_one]
        rw [hXi]
      · have hXj : shift (MvPolynomial.X j) =
            MvPolynomial.X (Sum.inr j) + MvPolynomial.X (Sum.inl 0) := by
          simp only [shift, MvPolynomial.eval₂Hom_X']
        have hpXj : MvPolynomial.pderiv (Sum.inr i)
            (MvPolynomial.X (Sum.inr j) + MvPolynomial.X (Sum.inl 0)) =
              (0 : MvPolynomial (Sum (Fin 1) (Fin m)) ℝ) := by
          rw [Derivation.map_add,
            MvPolynomial.pderiv_X_of_ne (i := Sum.inr i) (j := Sum.inr j)
              (by simpa using hji),
            MvPolynomial.pderiv_X_of_ne (i := Sum.inr i) (j := Sum.inl 0) (by simp)]
          simp only [zero_add]
        rw [hXj, hpXj]
        simp only [MvPolynomial.pderiv_mul, map_add,
          MvPolynomial.pderiv_X_of_ne hji]
        simp only [map_mul, map_zero]
        rw [hXj]

private theorem oneSubPderiv_shift {m : ℕ} (i : Fin m)
    (P : MvPolynomial (Fin m) ℝ) :
    oneSubPderiv (Sum.inr i) (shift P) = shift (oneSubPderiv i P) := by
  simp only [oneSubPderiv, map_sub, pderiv_shift]

private theorem oneSubPderivList_shift {m : ℕ} (l : List (Fin m))
    (P : MvPolynomial (Fin m) ℝ) :
    oneSubPderivList (l.map Sum.inr) (shift P) =
      shift (oneSubPderivList l P) := by
  induction l generalizing P with
  | nil => simp only [List.map_nil, oneSubPderivList_nil]
  | cons i l ih =>
      simp only [List.map_cons, oneSubPderivList_cons, oneSubPderiv_shift]
      exact ih (oneSubPderiv i P)

private theorem eval_shift {m : ℕ} (x : ℝ) (P : MvPolynomial (Fin m) ℝ) :
    MvPolynomial.eval (fun k : Sum (Fin 1) (Fin m) =>
      match k with
      | Sum.inl _ => x
      | Sum.inr _ => 0) (shift P) =
      MvPolynomial.eval (fun _ : Fin m => x) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp only [shift, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, MvPolynomial.eval_mul, hP]
      simp only [shift, MvPolynomial.eval₂Hom_X', map_add,
        MvPolynomial.eval_X, MvPolynomial.eval_mul, zero_add]

private theorem shift_realDetPencil {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) (hsum : ∑ i, As i = 1) :
    shift (realDetPencil 0 As) = realDetPencil 0 (fun k => match k with
      | Sum.inl _ => 1
      | Sum.inr i => As i) := by
  let φ : MvPolynomial (Fin m) ℝ →+* MvPolynomial (Sum (Fin 1) (Fin m)) ℝ :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : Fin m => MvPolynomial.X (Sum.inr i) +
        MvPolynomial.X (Sum.inl 0))
  change φ (realDetPencil 0 As) = realDetPencil 0 (fun k => match k with
    | Sum.inl _ => 1
    | Sum.inr i => As i)
  let M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) ℝ) := fun i j =>
    MvPolynomial.C ((0 : Matrix (Fin n) (Fin n) ℝ) i j) +
      ∑ k, MvPolynomial.X k * MvPolynomial.C (As k i j)
  let N : Matrix (Fin n) (Fin n)
      (MvPolynomial (Sum (Fin 1) (Fin m)) ℝ) := fun i j =>
    MvPolynomial.C ((0 : Matrix (Fin n) (Fin n) ℝ) i j) + ∑ k,
      MvPolynomial.X k * MvPolynomial.C ((match k with
        | Sum.inl _ => 1
        | Sum.inr k => As k) i j)
  change φ M.det = N.det
  rw [RingHom.map_det φ M]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change φ (M i j) = N i j
  have hsum_entry := congr_fun (congr_fun hsum i) j
  by_cases hij : i = j
  · subst j
    simp only [M, N, φ, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      map_add, map_sum, map_mul, MvPolynomial.eval₂Hom_C]
    rw [Fintype.sum_sum_type]
    simp only [Fin.isValue, Fin.sum_univ_one]
    rw [← hsum_entry]
    rw [Matrix.sum_apply, map_sum]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    ring
  · simp only [M, N, φ, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      map_add, map_sum, map_mul, MvPolynomial.eval₂Hom_C]
    rw [Fintype.sum_sum_type]
    simp only [Fin.isValue, Fin.sum_univ_one]
    rw [← hsum_entry]
    rw [Matrix.sum_apply, map_sum]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    ring

/-- Pointwise MSS Lemma 5.2 bridge between the mixed characteristic polynomial
    and the translated determinant-pencil stage. -/
theorem mixedCharacteristic_eval_bridge {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) (hsum : ∑ i, As i = 1) (x : ℝ) :
    (mixedCharacteristic As).eval x =
      (MvPolynomial.diagonal (stage (realDetPencil 0 As) m (le_refl m))).eval x := by
  have hpoly : MixedCharacteristic.mixedCharacteristicMv As =
      shift (stage (realDetPencil 0 As) m (le_refl m)) := by
    have hmv : MixedCharacteristic.mixedCharacteristicMv As =
        oneSubPderivList (List.ofFn (fun i : Fin m => Sum.inr i))
          (realDetPencil 0 (fun k => match k with
            | Sum.inl _ => 1
            | Sum.inr i => As i)) := by
      rfl
    rw [hmv]
    rw [← shift_realDetPencil As hsum]
    have hlist : List.ofFn (fun i : Fin m => Sum.inr i) =
        (List.ofFn (fun i : Fin m => i)).map
          (Sum.inr : Fin m → Sum (Fin 1) (Fin m)) := by
      rw [List.map_ofFn]
      rfl
    rw [hlist]
    rw [oneSubPderivList_shift]
    rfl
  have hweight : mixedCharacteristic As =
      commonPhaseRestriction (fun k : Sum (Fin 1) (Fin m) =>
        match k with
        | Sum.inl _ => 1
        | Sum.inr _ => 0) (MixedCharacteristic.mixedCharacteristicMv As) := by
    rfl
  rw [hweight, commonPhaseRestriction_eval, hpoly]
  calc
    _ = MvPolynomial.eval (fun k : Sum (Fin 1) (Fin m) =>
        match k with
        | Sum.inl _ => x
        | Sum.inr _ => 0) (shift (stage (realDetPencil 0 As) m (le_refl m))) := by
      apply congrArg (fun f : Sum (Fin 1) (Fin m) → ℝ =>
        MvPolynomial.eval f (shift (stage (realDetPencil 0 As) m (le_refl m))))
      funext k
      cases k <;> simp
    _ = MvPolynomial.eval (fun _ : Fin m => x)
        (stage (realDetPencil 0 As) m (le_refl m)) := eval_shift x _
    _ = _ := by rw [MvPolynomial.eval_diagonal]

/-- The mixed-characteristic polynomial is the diagonal specialization of the
    translated determinant-pencil stage. -/
theorem mixedCharacteristic_eq_diagonal {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ) (hsum : ∑ i, As i = 1) :
    mixedCharacteristic As =
      MvPolynomial.diagonal (stage (realDetPencil 0 As) m (le_refl m)) := by
  apply Polynomial.funext
  intro x
  exact mixedCharacteristic_eval_bridge As hsum x

/-- The MSS root endpoint for PSD summands with identity sum. -/
theorem mixedCharacteristic_roots_le {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) (hsum : ∑ i, As i = 1)
    {t δ ε : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hthreshold : ε / t ≤ 1 - 1 / δ)
    (htrace : ∀ i, (As i).trace ≤ ε) :
    ∀ r ∈ (mixedCharacteristic As).roots, r ≤ t + δ := by
  rw [mixedCharacteristic_eq_diagonal As hsum]
  exact determinant_diagonal_roots_le As hAs hsum ht hδ hthreshold htrace

/-- The optimized `(1 + √ε)²` MSS root bound. -/
theorem mixedCharacteristic_roots_le_optimized {n m : ℕ}
    (As : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hAs : ∀ i, (As i).PosSemidef) (hsum : ∑ i, As i = 1)
    {ε : ℝ} (hε : 0 < ε) (htrace : ∀ i, (As i).trace ≤ ε)
    :
    ∀ r ∈ (mixedCharacteristic As).roots,
      r ≤ (1 + Real.sqrt ε) ^ 2 := by
  let t : ℝ := ε + Real.sqrt ε
  let δ : ℝ := 1 / (1 - ε / t)
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hεt : ε < t := by
    dsimp [t]
    linarith
  have hparam : 0 < δ ∧ ε / t ≤ 1 - 1 / δ := by
    simpa only [δ] using update_parameter hε.le hεt
  have hroots := mixedCharacteristic_roots_le As hAs hsum ht
    hparam.1 hparam.2 htrace
  intro r hr
  have hroot := hroots r hr
  calc
    r ≤ t + δ := hroot
    _ = (1 + Real.sqrt ε) ^ 2 := by
      dsimp [t, δ]
      exact optimized_endpoint hε

end

end RealRooted.MixedCharacteristic
