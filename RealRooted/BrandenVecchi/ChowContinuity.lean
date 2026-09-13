import RealRooted.BrandenVecchi.ChowToeplitz
import RealRooted.PFPolynomial.Closure

/-!
# Fixed-rank locality and continuity of Chow polynomials

The rank-`n` Chow data use only the lower-triangular block with row index at
most `n`.  This file records that finite dependence and its coefficientwise
continuity consequence, independently of positivity and infinite products.
-/

open Filter Polynomial Topology

namespace RealRooted.BrandenVecchi

noncomputable section

/-- Two lower-triangular matrices agree on the finite block through row `n`. -/
def ChowBlockEq {R : Type*} (n : ℕ)
    (A B : LowerTriangularMatrix R) : Prop :=
  ∀ i, i ≤ n → ∀ j, j ≤ i → A i j = B i j

theorem ChowBlockEq.mono {R : Type*} {A B : LowerTriangularMatrix R}
    {m n : ℕ} (h : ChowBlockEq n A B) (hmn : m ≤ n) :
    ChowBlockEq m A B := by
  intro i hi j hj
  exact h i (hi.trans hmn) j hj

/-- The rank-`n` Chow-derangement polynomial depends only on the finite block
through row `n`. -/
theorem chowDerangement_eq_of_blockEq {R : Type*} [CommRing R]
    {A B : LowerTriangularMatrix R} :
    ∀ n, ChowBlockEq n A B →
      chowDerangement A n = chowDerangement B n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hblock
      cases n with
      | zero => simp
      | succ n =>
          rw [chowDerangement_succ, chowDerangement_succ]
          apply congrArg (fun p : R[X] => X * chowS n p)
          apply Finset.sum_congr rfl
          intro k hk
          rw [hblock (n + 1) le_rfl k (Nat.le_of_lt k.isLt)]
          rw [ih k k.isLt (hblock.mono (Nat.le_of_lt k.isLt))]

/-- The rank-`n` Chow polynomial depends only on the finite block through row
`n`. -/
theorem chowPolynomial_eq_of_blockEq {R : Type*} [CommRing R]
    {A B : LowerTriangularMatrix R} (n : ℕ)
    (hblock : ChowBlockEq n A B) :
    chowPolynomial A n = chowPolynomial B n := by
  rw [chowPolynomial_eq, chowPolynomial_eq]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [hblock n le_rfl k hkn]
  rw [chowDerangement_eq_of_blockEq k (hblock.mono hkn)]

/-- Toeplitz Chow-derangement data at rank `n` use only symbol coefficients
through index `n`. -/
theorem chowDerangement_toeplitz_eq_of_prefix
    {R : Type*} [CommRing R] {a b : ℕ → R} (n : ℕ)
    (hab : ∀ k, k ≤ n → a k = b k) :
    chowDerangement (RealRooted.toeplitz a) n =
      chowDerangement (RealRooted.toeplitz b) n := by
  apply chowDerangement_eq_of_blockEq n
  intro i hi j hj
  simp [RealRooted.toeplitz_apply, hj, hab (i - j) ((Nat.sub_le i j).trans hi)]

/-- Toeplitz Chow data at rank `n` use only symbol coefficients through index
`n`. -/
theorem chowPolynomial_toeplitz_eq_of_prefix
    {R : Type*} [CommRing R] {a b : ℕ → R} (n : ℕ)
    (hab : ∀ k, k ≤ n → a k = b k) :
    chowPolynomial (RealRooted.toeplitz a) n =
      chowPolynomial (RealRooted.toeplitz b) n := by
  apply chowPolynomial_eq_of_blockEq n
  intro i hi j hj
  simp [RealRooted.toeplitz_apply, hj, hab (i - j) ((Nat.sub_le i j).trans hi)]

/-- Both fixed-rank Chow outputs have the uniform degree bounds needed by the
root-continuity APIs. -/
theorem chow_fixedRank_degree_bounds {R : Type*} [CommRing R]
    (A : LowerTriangularMatrix R) (n : ℕ) :
    (chowDerangement A n).natDegree ≤ n ∧
      (chowPolynomial A n).natDegree ≤ n :=
  ⟨natDegree_chowDerangement_le A n, natDegree_chowPolynomial_le A n⟩

private theorem coeff_divByMonic_X_sub_one_eq_sum_Icc
    (q : ℝ[X]) {N : ℕ} (hq : q.natDegree ≤ N) (j : ℕ) :
    (q /ₘ (X - C (1 : ℝ))).coeff j =
      ∑ i ∈ Finset.Icc (j + 1) N, q.coeff i := by
  rw [Polynomial.coeff_divByMonic_X_sub_C]
  simp only [one_pow, one_mul]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hq⟩
  · intro i hiN hiDegree
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    by_contra hi
    apply hiDegree
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hiN).1, Nat.le_of_not_gt hi⟩

/-- Each coefficient of `chowS n p` is a finite linear combination of
coefficients of `p` when `p` has degree at most `n`. -/
theorem coeff_chowS_eq_sum (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) (j : ℕ) :
    (Polynomial.chowS n p).coeff j =
      ∑ i ∈ Finset.Icc (j + 1) n,
        (p.coeff (Polynomial.revAt n i) - p.coeff i) := by
  rw [Polynomial.chowS]
  change ((p.reflect n - p) /ₘ (X - C (1 : ℝ))).coeff j = _
  have hreflect : (p.reflect n).natDegree ≤ n := by
    simpa [max_eq_left hp] using
      (Polynomial.natDegree_reflect_le (N := n) (p := p))
  rw [coeff_divByMonic_X_sub_one_eq_sum_Icc _
    ((Polynomial.natDegree_sub_le _ _).trans
      (max_le hreflect hp))]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_reflect]

/-- On a uniformly bounded degree slice, every coefficient of `chowS` is a
continuous function of the input coefficients. -/
theorem tendsto_coeff_chowS
    {ι : Type*} {l : Filter ι} {p : ι → ℝ[X]} {p₀ : ℝ[X]}
    (n : ℕ) (hdeg : ∀ a, (p a).natDegree ≤ n)
    (hdeg₀ : p₀.natDegree ≤ n)
    (hcoeff : ∀ j, Tendsto (fun a => (p a).coeff j) l (𝓝 (p₀.coeff j)))
    (j : ℕ) :
    Tendsto (fun a => (Polynomial.chowS n (p a)).coeff j) l
      (𝓝 ((Polynomial.chowS n p₀).coeff j)) := by
  simp_rw [coeff_chowS_eq_sum n _ (hdeg _), coeff_chowS_eq_sum n p₀ hdeg₀]
  exact tendsto_finsetSum _ fun i _ => (hcoeff _).sub (hcoeff i)

/-- Entrywise convergence on the finite block through row `n` gives
coefficientwise convergence of the rank-`n` Chow-derangement polynomial. -/
theorem tendsto_coeff_chowDerangement_of_block
    {ι : Type*} {l : Filter ι}
    (A : ι → LowerTriangularMatrix ℝ) (A₀ : LowerTriangularMatrix ℝ) :
    ∀ n,
      (∀ (i : ℕ), i ≤ n → ∀ (j : ℕ), j ≤ i →
        Tendsto (fun a => A a i j) l (𝓝 (A₀ i j))) →
      ∀ d, Tendsto (fun a => (chowDerangement (A a) n).coeff d) l
        (𝓝 ((chowDerangement A₀ n).coeff d)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hA d
      cases n with
      | zero =>
          simp only [chowDerangement_zero]
          exact tendsto_const_nhds
      | succ n =>
          let P : ι → ℝ[X] := fun a => ∑ k : Fin (n + 1),
            C (A a (n + 1) k) * chowDerangement (A a) k
          let P₀ : ℝ[X] := ∑ k : Fin (n + 1),
            C (A₀ (n + 1) k) * chowDerangement A₀ k
          have hPdegree : ∀ a, (P a).natDegree ≤ n := by
            intro a
            refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
              (fun k : Fin (n + 1) =>
                C (A a (n + 1) k) * chowDerangement (A a) k) ?_
            intro k _
            exact (Polynomial.natDegree_C_mul_le _ _).trans
              ((natDegree_chowDerangement_le (A a) k).trans
                (Nat.lt_succ_iff.mp k.isLt))
          have hP₀degree : P₀.natDegree ≤ n := by
            refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ
              (fun k : Fin (n + 1) =>
                C (A₀ (n + 1) k) * chowDerangement A₀ k) ?_
            intro k _
            exact (Polynomial.natDegree_C_mul_le _ _).trans
              ((natDegree_chowDerangement_le A₀ k).trans
                (Nat.lt_succ_iff.mp k.isLt))
          have hPcoeff : ∀ e, Tendsto (fun a => (P a).coeff e) l
              (𝓝 (P₀.coeff e)) := by
            intro e
            simp only [P, P₀, Polynomial.finsetSum_coeff,
              Polynomial.coeff_C_mul]
            refine tendsto_finsetSum _ fun k _ => ?_
            exact (hA (n + 1) le_rfl k (Nat.le_of_lt k.isLt)).mul
              (ih k k.isLt
                (fun i hi j hj =>
                  hA i (hi.trans (Nat.le_of_lt k.isLt)) j hj) e)
          simp only [chowDerangement_succ]
          change Tendsto
            (fun a => (X * Polynomial.chowS n (P a)).coeff d) l
            (𝓝 ((X * Polynomial.chowS n P₀).coeff d))
          cases d with
          | zero =>
              simp only [Polynomial.coeff_X_mul_zero]
              exact tendsto_const_nhds
          | succ d =>
              simp only [Polynomial.coeff_X_mul]
              exact tendsto_coeff_chowS n hPdegree hP₀degree hPcoeff d

/-- Entrywise convergence on the finite block through row `n` gives
coefficientwise convergence of the rank-`n` Chow polynomial. -/
theorem tendsto_coeff_chowPolynomial_of_block
    {ι : Type*} {l : Filter ι}
    (A : ι → LowerTriangularMatrix ℝ) (A₀ : LowerTriangularMatrix ℝ)
    (n : ℕ)
    (hA : ∀ (i : ℕ), i ≤ n → ∀ (j : ℕ), j ≤ i →
      Tendsto (fun a => A a i j) l (𝓝 (A₀ i j)))
    (d : ℕ) :
    Tendsto (fun a => (chowPolynomial (A a) n).coeff d) l
      (𝓝 ((chowPolynomial A₀ n).coeff d)) := by
  simp only [chowPolynomial_eq, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (hA n le_rfl k hkn).mul
    (tendsto_coeff_chowDerangement_of_block A A₀ k
      (fun i hi j hj => hA i (hi.trans hkn) j hj) d)

/-- Coordinatewise convergence of a Toeplitz symbol through index `n` gives
coefficientwise convergence of its rank-`n` Chow-derangement polynomial. -/
theorem tendsto_coeff_chowDerangement_toeplitz
    {ι : Type*} {l : Filter ι} (a : ι → ℕ → ℝ) (a₀ : ℕ → ℝ)
    (n : ℕ)
    (ha : ∀ k, k ≤ n → Tendsto (fun x => a x k) l (𝓝 (a₀ k)))
    (d : ℕ) :
    Tendsto
      (fun x => (chowDerangement (RealRooted.toeplitz (a x)) n).coeff d) l
      (𝓝 ((chowDerangement (RealRooted.toeplitz a₀) n).coeff d)) := by
  apply tendsto_coeff_chowDerangement_of_block _ _ n
  intro i hi j hj
  simpa [RealRooted.toeplitz_apply, hj] using
    ha (i - j) ((Nat.sub_le i j).trans hi)

/-- Coordinatewise convergence of a Toeplitz symbol through index `n` gives
coefficientwise convergence of its rank-`n` Chow polynomial. -/
theorem tendsto_coeff_chowPolynomial_toeplitz
    {ι : Type*} {l : Filter ι} (a : ι → ℕ → ℝ) (a₀ : ℕ → ℝ)
    (n : ℕ)
    (ha : ∀ k, k ≤ n → Tendsto (fun x => a x k) l (𝓝 (a₀ k)))
    (d : ℕ) :
    Tendsto
      (fun x => (chowPolynomial (RealRooted.toeplitz (a x)) n).coeff d) l
      (𝓝 ((chowPolynomial (RealRooted.toeplitz a₀) n).coeff d)) := by
  apply tendsto_coeff_chowPolynomial_of_block _ _ n
  intro i hi j hj
  simpa [RealRooted.toeplitz_apply, hj] using
    ha (i - j) ((Nat.sub_le i j).trans hi)

end

end RealRooted.BrandenVecchi
