import RealRooted.DifferentialBlocks
import RealRooted.ElementaryDifferential
import RealRooted.RectangularConvolution
import RealRooted.RectangularPolarizationComplement

/-!
# Rectangular convolution differential identity

This file proves that the complementary rectangular polarization acting by
negative partial differentiation on the direct rectangular polarization
specializes to the rectangular additive convolution.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

private theorem triangle_reindex
    {A : Type*} [AddCommMonoid A] (n : ℕ) (F : ℕ → ℕ → A) :
    ∑ i ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1), (if i ≤ k then F i k else 0) =
      ∑ K ∈ Finset.range (n + 1),
        ∑ a ∈ Finset.range (K + 1), F (K - a) (n - a) := by
  rw [← Finset.sum_product (Finset.range (n + 1))
    (Finset.range (n + 1))
    (fun x => if x.1 ≤ x.2 then F x.1 x.2 else 0)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_sigma']
  apply Finset.sum_bij
      (fun x _ => ⟨n - x.2 + x.1, n - x.2⟩)
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_product] at hx
    rw [Finset.mem_sigma]
    simp only [Finset.mem_range]
    have hx1le : x.1 ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hx.1.1)
    have hx2le : x.2 ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hx.1.2)
    have hcancel : n - x.2 + x.2 = n := Nat.sub_add_cancel hx2le
    constructor <;> lia
  · intro x₁ hx₁ x₂ hx₂ heq
    rw [Finset.mem_filter, Finset.mem_product] at hx₁ hx₂
    have hfst := congrArg Sigma.fst heq
    have hsnd := congrArg (fun z => z.2) heq
    have hx₁le : x₁.2 ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hx₁.1.2)
    have hx₂le : x₂.2 ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hx₂.1.2)
    have hcancel₁ : n - x₁.2 + x₁.2 = n :=
      Nat.sub_add_cancel hx₁le
    have hcancel₂ : n - x₂.2 + x₂.2 = n :=
      Nat.sub_add_cancel hx₂le
    apply Prod.ext
    · dsimp at hfst hsnd
      lia
    · dsimp at hsnd
      lia
  · intro y hy
    rw [Finset.mem_sigma] at hy
    rcases y with ⟨K, a⟩
    simp only [Finset.mem_range] at hy
    let x : ℕ × ℕ := (K - a, n - a)
    have haK : a ≤ K := Nat.lt_succ_iff.mp hy.2
    have hKn : K ≤ n := Nat.lt_succ_iff.mp hy.1
    have han : a ≤ n := haK.trans hKn
    refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product]
      simp only [Finset.mem_range, x]
      constructor
      · constructor <;> lia
      · lia
    · apply Sigma.ext
      · dsimp [x]
        rw [Nat.sub_sub_self han]
        lia
      · simp [x, Nat.sub_sub_self han]
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_product] at hx
    have hx2le : x.2 ≤ n :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hx.1.2)
    simp [Nat.sub_sub_self hx2le]

private theorem rename_esymm_const
    {R tau : Type*} [CommSemiring R] (N j : ℕ) (v : tau) :
    MvPolynomial.rename (fun _ : Fin N => v)
        (MvPolynomial.esymm (Fin N) R j) =
      Nat.choose N j • MvPolynomial.X v ^ j := by
  rw [MvPolynomial.esymm]
  simp only [map_sum, map_prod, MvPolynomial.rename_X]
  calc
    ∑ t ∈ Finset.univ.powersetCard j,
        ∏ _x ∈ t, MvPolynomial.X v =
      ∑ _t ∈ Finset.univ.powersetCard j,
        MvPolynomial.X v ^ j := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]

private theorem rectangularDifferentialTerm
    (m n i k : ℕ) (hi : i ≤ k) (a b : ℂ) :
    applyNegDifferential
        (MvPolynomial.C a *
          (MvPolynomial.rename Sum.inl
              (MvPolynomial.esymm (Fin n) ℂ i) *
            MvPolynomial.rename Sum.inr
              (MvPolynomial.esymm (Fin (m + n)) ℂ i)))
        (MvPolynomial.C b *
          (MvPolynomial.rename Sum.inl
              (MvPolynomial.esymm (Fin n) ℂ k) *
            MvPolynomial.rename Sum.inr
              (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k)))) =
      MvPolynomial.C
          a * MvPolynomial.C b *
        (MvPolynomial.rename Sum.inl
            (MvPolynomial.C ((-1 : ℂ) ^ i) *
              ((Nat.choose (n + i - k) i) •
                MvPolynomial.esymm (Fin n) ℂ (k - i))) *
          MvPolynomial.rename Sum.inr
            (MvPolynomial.C ((-1 : ℂ) ^ i) *
              ((Nat.choose (n + i - k) i) •
                MvPolynomial.esymm (Fin (m + n)) ℂ (m + k - i)))) := by
  have himk : i ≤ m + k := hi.trans (Nat.le_add_left k m)
  rw [applyNegDifferential_C_mul_left,
    applyNegDifferential_C_mul_right,
    applyNegDifferential_sumBlockFactorization,
    applyNegDifferential_esymm, if_pos hi,
    applyNegDifferential_esymm, if_pos himk]
  simp only [Fintype.card_fin, map_mul, MvPolynomial.rename_C,
    map_nsmul]
  rw [show n + i - k = m + n + i - (m + k) by lia]
  rw [show m + k - i = m + (k - i) by lia]
  ring

/-- Diagonal specialization sending the left block to `X 0` and the right block
to `X 1`. -/
def rectangularDiagonal {m n : ℕ} :
    Sum (Fin n) (Fin (m + n)) → Fin 2 :=
  Sum.elim (fun _ => 0) (fun _ => 1)

private theorem rectangularDifferentialTerm_diagonal
    (m n i k : ℕ) (hi : i ≤ k) (a b : ℂ) :
    MvPolynomial.rename rectangularDiagonal
        (applyNegDifferential
          (MvPolynomial.C a *
            (MvPolynomial.rename Sum.inl
                (MvPolynomial.esymm (Fin n) ℂ i) *
              MvPolynomial.rename Sum.inr
                (MvPolynomial.esymm (Fin (m + n)) ℂ i)))
          (MvPolynomial.C b *
            (MvPolynomial.rename Sum.inl
                (MvPolynomial.esymm (Fin n) ℂ k) *
              MvPolynomial.rename Sum.inr
                (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k))))) =
      MvPolynomial.C a * MvPolynomial.C b *
        (MvPolynomial.C ((-1 : ℂ) ^ i) *
            ((Nat.choose (n + i - k) i) •
              ((Nat.choose n (k - i)) •
                MvPolynomial.X 0 ^ (k - i))) *
          (MvPolynomial.C ((-1 : ℂ) ^ i) *
            ((Nat.choose (n + i - k) i) •
              ((Nat.choose (m + n) (m + k - i)) •
                MvPolynomial.X 1 ^ (m + k - i))))) := by
  rw [rectangularDifferentialTerm m n i k hi]
  simp only [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_rename,
    map_nsmul]
  have hinl :
      rectangularDiagonal ∘ (Sum.inl : Fin n → Sum (Fin n) (Fin (m + n))) =
        fun _ => (0 : Fin 2) := rfl
  have hinr :
      rectangularDiagonal ∘
          (Sum.inr : Fin (m + n) → Sum (Fin n) (Fin (m + n))) =
        fun _ => (1 : Fin 2) := rfl
  rw [hinl, hinr]
  rw [rename_esymm_const, rename_esymm_const]

private theorem collect_nsmul
    {sigma : Type*} (a b s : ℂ) (D L U : ℕ)
    (P Q : MvPolynomial sigma ℂ) :
    MvPolynomial.C a * MvPolynomial.C b *
        (MvPolynomial.C s * (D • (L • P)) *
          (MvPolynomial.C s * (D • (U • Q)))) =
      MvPolynomial.C
          (a * b * s ^ 2 * (D : ℂ) ^ 2 * (L : ℂ) * (U : ℂ)) *
        P * Q := by
  simp only [nsmul_eq_mul]
  have hD : (D : MvPolynomial sigma ℂ) = MvPolynomial.C (D : ℂ) :=
    (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial sigma ℂ) D).symm
  have hL : (L : MvPolynomial sigma ℂ) = MvPolynomial.C (L : ℂ) :=
    (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial sigma ℂ) L).symm
  have hU : (U : MvPolynomial sigma ℂ) = MvPolynomial.C (U : ℂ) :=
    (map_natCast (MvPolynomial.C : ℂ →+* MvPolynomial sigma ℂ) U).symm
  rw [hD, hL, hU]
  have hcoeff :
      (MvPolynomial.C
          (a * b * s ^ 2 * (D : ℂ) ^ 2 * (L : ℂ) * (U : ℂ)) :
          MvPolynomial sigma ℂ) =
        MvPolynomial.C a * MvPolynomial.C b *
          MvPolynomial.C s * MvPolynomial.C s *
          MvPolynomial.C (D : ℂ) * MvPolynomial.C (D : ℂ) *
          MvPolynomial.C (L : ℂ) * MvPolynomial.C (U : ℂ) := by
    simp only [← map_mul]
    congr 1
    ring
  rw [hcoeff]
  ring

private theorem rectangularDifferentialTerm_diagonal_collected
    (m n i k : ℕ) (hi : i ≤ k) (a b : ℂ) :
    MvPolynomial.rename rectangularDiagonal
        (applyNegDifferential
          (MvPolynomial.C a *
            (MvPolynomial.rename Sum.inl
                (MvPolynomial.esymm (Fin n) ℂ i) *
              MvPolynomial.rename Sum.inr
                (MvPolynomial.esymm (Fin (m + n)) ℂ i)))
          (MvPolynomial.C b *
            (MvPolynomial.rename Sum.inl
                (MvPolynomial.esymm (Fin n) ℂ k) *
              MvPolynomial.rename Sum.inr
                (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k))))) =
      MvPolynomial.C
          (a * b * (Nat.choose (n + i - k) i : ℂ) ^ 2 *
            (Nat.choose n (k - i) : ℂ) *
            (Nat.choose (m + n) (m + k - i) : ℂ)) *
        MvPolynomial.X 0 ^ (k - i) *
        MvPolynomial.X 1 ^ (m + k - i) := by
  rw [rectangularDifferentialTerm_diagonal m n i k hi,
    collect_nsmul]
  have hsign : ((-1 : ℂ) ^ i) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, mul_one]

private theorem rectangularDifferentialTerm_diagonal_ite
    (m n i k : ℕ) (a b : ℂ) :
    MvPolynomial.rename rectangularDiagonal
        (applyNegDifferential
          (MvPolynomial.C a *
            (MvPolynomial.rename Sum.inl
                (MvPolynomial.esymm (Fin n) ℂ i) *
              MvPolynomial.rename Sum.inr
                (MvPolynomial.esymm (Fin (m + n)) ℂ i)))
          (MvPolynomial.C b *
            (MvPolynomial.rename Sum.inl
                (MvPolynomial.esymm (Fin n) ℂ k) *
              MvPolynomial.rename Sum.inr
                (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k))))) =
      if i ≤ k then
        MvPolynomial.C
            (a * b * (Nat.choose (n + i - k) i : ℂ) ^ 2 *
              (Nat.choose n (k - i) : ℂ) *
              (Nat.choose (m + n) (m + k - i) : ℂ)) *
          MvPolynomial.X 0 ^ (k - i) *
          MvPolynomial.X 1 ^ (m + k - i)
      else 0 := by
  by_cases hi : i ≤ k
  · rw [if_pos hi]
    exact rectangularDifferentialTerm_diagonal_collected m n i k hi a b
  · rw [if_neg hi, applyNegDifferential_C_mul_left,
      applyNegDifferential_C_mul_right,
      applyNegDifferential_sumBlockFactorization,
      applyNegDifferential_esymm, if_neg hi]
    simp

private def reciprocalRectangularTerm
    (m n : ℕ) (q : ℂ[X]) (i : ℕ) :
    MvPolynomial (Sum (Fin n) (Fin (m + n))) ℂ :=
  MvPolynomial.C
      (q.coeff (n - i) / (n.choose i : ℂ) /
        ((m + n).choose i : ℂ)) *
    MvPolynomial.rename Sum.inl
      (MvPolynomial.esymm (Fin n) ℂ i) *
    MvPolynomial.rename Sum.inr
      (MvPolynomial.esymm (Fin (m + n)) ℂ i)

private def rectangularTerm
    (m n : ℕ) (p : ℂ[X]) (k : ℕ) :
    MvPolynomial (Sum (Fin n) (Fin (m + n))) ℂ :=
  MvPolynomial.C
      (p.coeff k / (n.choose k : ℂ) /
        ((m + n).choose (m + k) : ℂ)) *
    MvPolynomial.rename Sum.inl
      (MvPolynomial.esymm (Fin n) ℂ k) *
    MvPolynomial.rename Sum.inr
      (MvPolynomial.esymm (Fin (m + n)) ℂ (m + k))

private theorem reciprocalRectangularPolarization_eq_sum_terms
    (m n : ℕ) (q : ℂ[X]) :
    reciprocalRectangularPolarization m n q =
      ∑ i ∈ Finset.range (n + 1),
        reciprocalRectangularTerm m n q i := by
  rw [reciprocalRectangularPolarization_explicit]
  rfl

private theorem rectangularPolarization_eq_sum_terms
    (m n : ℕ) (p : ℂ[X]) :
  rectangularPolarization m n p =
      ∑ k ∈ Finset.range (n + 1), rectangularTerm m n p k := by
  unfold rectangularPolarization rectangularTerm
  rfl

private theorem rectangularDifferential_eq_doubleSum
    (m n : ℕ) (p q : ℂ[X]) :
    applyNegDifferential
        (reciprocalRectangularPolarization m n q)
        (rectangularPolarization m n p) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          applyNegDifferential
            (reciprocalRectangularTerm m n q i)
            (rectangularTerm m n p k) := by
  rw [reciprocalRectangularPolarization_eq_sum_terms,
    rectangularPolarization_eq_sum_terms,
    applyNegDifferential_doubleSum]

private def rectangularDifferentialDiagonalCore
    (m n : ℕ) (p q : ℂ[X]) (i k : ℕ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C
      ((q.coeff (n - i) / (n.choose i : ℂ) /
            ((m + n).choose i : ℂ)) *
        (p.coeff k / (n.choose k : ℂ) /
            ((m + n).choose (m + k) : ℂ)) *
        (Nat.choose (n + i - k) i : ℂ) ^ 2 *
        (Nat.choose n (k - i) : ℂ) *
        (Nat.choose (m + n) (m + k - i) : ℂ)) *
    MvPolynomial.X 0 ^ (k - i) *
    MvPolynomial.X 1 ^ (m + k - i)

private def rectangularDifferentialDiagonalSummand
    (m n : ℕ) (p q : ℂ[X]) (i k : ℕ) :
    MvPolynomial (Fin 2) ℂ :=
  if i ≤ k then rectangularDifferentialDiagonalCore m n p q i k else 0

private theorem rectangularDifferentialDiagonalSummand_triangle
    (m n : ℕ) (p q : ℂ[X]) :
    ∑ i ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          rectangularDifferentialDiagonalSummand m n p q i k =
      ∑ K ∈ Finset.range (n + 1),
        ∑ a ∈ Finset.range (K + 1),
          rectangularDifferentialDiagonalCore m n p q
            (K - a) (n - a) := by
  unfold rectangularDifferentialDiagonalSummand
  exact triangle_reindex n
    (rectangularDifferentialDiagonalCore m n p q)

private theorem rectangularDifferential_expansion
    (m n : ℕ) (p q : ℂ[X]) :
    MvPolynomial.rename rectangularDiagonal
        (applyNegDifferential
          (reciprocalRectangularPolarization m n q)
          (rectangularPolarization m n p)) =
      ∑ i ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          rectangularDifferentialDiagonalSummand m n p q i k := by
  rw [rectangularDifferential_eq_doubleSum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold rectangularDifferentialDiagonalSummand
  simpa [rectangularDifferentialDiagonalCore,
    reciprocalRectangularTerm, rectangularTerm, mul_assoc] using
    rectangularDifferentialTerm_diagonal_ite m n i k
      (q.coeff (n - i) / (n.choose i : ℂ) /
        ((m + n).choose i : ℂ))
      (p.coeff k / (n.choose k : ℂ) /
        ((m + n).choose (m + k) : ℂ))

private theorem rectangularWeight_eq_gamma
    (m n i k : ℕ) (hi : i ≤ k) (hk : k ≤ n) :
    ((Nat.choose (n + i - k) i : ℂ) ^ 2 /
          ((Nat.choose n i : ℂ) * (Nat.choose (m + n) i : ℂ) *
            (Nat.choose n k : ℂ) *
            (Nat.choose (m + n) (m + k) : ℂ))) *
        (Nat.choose n (k - i) : ℂ) *
        (Nat.choose (m + n) (m + k - i) : ℂ) =
      (rectangularConvolutionGamma m n (n - k) i : ℂ) := by
  have hik : i ≤ n := hi.trans hk
  have hmk : m + k ≤ m + n := Nat.add_le_add_left hk m
  have hki : k - i ≤ n := (Nat.sub_le k i).trans hk
  have hmki : m + k - i ≤ m + n := by lia
  have hinner : i ≤ n + i - k := by lia
  unfold rectangularConvolutionGamma
  push_cast
  rw [show n - (n - k) = k by lia,
    show n + m - (n - k) = m + k by lia]
  rw [Nat.cast_choose ℂ hinner, Nat.cast_choose ℂ hik,
    Nat.cast_choose ℂ (hik.trans (Nat.le_add_left n m)),
    Nat.cast_choose ℂ hk, Nat.cast_choose ℂ hmk,
    Nat.cast_choose ℂ hki, Nat.cast_choose ℂ hmki]
  have f0 : ∀ p : ℕ, (Nat.factorial p : ℂ) ≠ 0 := fun p =>
    Nat.cast_ne_zero.mpr (Nat.factorial_pos p).ne'
  field_simp [f0]
  rw [show n + i - k - i = n - k by lia,
    show m + n - (m + k) = n - k by lia,
    show n - (k - i) = n + i - k by lia,
    show m + n - (m + k - i) = n + i - k by lia]
  ring_nf

private theorem rectangularSeparatedWeight_eq_gamma
    (m n i k : ℕ) (hi : i ≤ k) (hk : k ≤ n) :
    ((1 : ℂ) / (n.choose i : ℂ) /
          ((m + n).choose i : ℂ)) *
        ((1 : ℂ) / (n.choose k : ℂ) /
          ((m + n).choose (m + k) : ℂ)) *
        (Nat.choose (n + i - k) i : ℂ) ^ 2 *
        (Nat.choose n (k - i) : ℂ) *
        (Nat.choose (m + n) (m + k - i) : ℂ) =
      (rectangularConvolutionGamma m n (n - k) i : ℂ) := by
  rw [← rectangularWeight_eq_gamma m n i k hi hk]
  have hik : i ≤ n := hi.trans hk
  have hiM : i ≤ m + n := hik.trans (Nat.le_add_left n m)
  have hmk : m + k ≤ m + n := Nat.add_le_add_left hk m
  have hni : (n.choose i : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hik).ne'
  have hMi : ((m + n).choose i : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hiM).ne'
  have hnk : (n.choose k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have hMk : ((m + n).choose (m + k) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hmk).ne'
  field_simp [hni, hMi, hnk, hMk]

private theorem xyLift_rectangularAdditiveConvolution_expansion
    (m n : ℕ) (f g : ℝ[X]) :
    MvPolynomial.X 1 ^ m *
        xyLift ((rectangularAdditiveConvolution m n f g).map
          Complex.ofRealHom) =
      ∑ K ∈ Finset.range (n + 1),
        MvPolynomial.C
            (rectangularConvolutionCoeff m n f g K : ℂ) *
          MvPolynomial.X 0 ^ (n - K) *
          MvPolynomial.X 1 ^ (m + n - K) := by
  unfold rectangularAdditiveConvolution xyLift
  rw [Polynomial.map_sum, Polynomial.eval₂_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  have hKn : K ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hK)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]
  change MvPolynomial.X 1 ^ m *
      (MvPolynomial.C (rectangularConvolutionCoeff m n f g K : ℂ) *
        (MvPolynomial.X 0 * MvPolynomial.X 1) ^ (n - K)) = _
  rw [show m + n - K = m + (n - K) by lia, pow_add]
  ring

private theorem rectangularDifferentialDiagonalCore_reindex
    (m n K a : ℕ) (hK : K ≤ n) (ha : a ≤ K)
    (f g : ℝ[X]) :
    rectangularDifferentialDiagonalCore m n
        (f.map Complex.ofRealHom) (g.map Complex.ofRealHom)
        (K - a) (n - a) =
      MvPolynomial.C
          ((rectangularConvolutionGamma m n a (K - a) *
            f.coeff (n - a) * g.coeff (n - (K - a)) : ℝ) : ℂ) *
        MvPolynomial.X 0 ^ (n - K) *
        MvPolynomial.X 1 ^ (m + n - K) := by
  have hi : K - a ≤ n - a := Nat.sub_le_sub_right hK a
  have hk : n - a ≤ n := Nat.sub_le n a
  have hka : n - (n - a) = a := Nat.sub_sub_self (ha.trans hK)
  have hdegree : n - a - (K - a) = n - K := by lia
  have hma : m + (n - a) = m + n - a := by lia
  have hMdegree : m + n - a - (K - a) = m + n - K := by lia
  unfold rectangularDifferentialDiagonalCore
  rw [Polynomial.coeff_map, Polynomial.coeff_map,
    hdegree, show m + (n - a) - (K - a) = m + n - K by lia]
  change MvPolynomial.C
      (((g.coeff (n - (K - a)) : ℂ) /
            (n.choose (K - a) : ℂ) /
            ((m + n).choose (K - a) : ℂ)) *
        ((f.coeff (n - a) : ℂ) /
            (n.choose (n - a) : ℂ) /
            ((m + n).choose (m + (n - a)) : ℂ)) *
        (Nat.choose (n + (K - a) - (n - a)) (K - a) : ℂ) ^ 2 *
        (Nat.choose n (n - K) : ℂ) *
        (Nat.choose (m + n) (m + n - K) : ℂ)) *
      MvPolynomial.X 0 ^ (n - K) *
      MvPolynomial.X 1 ^ (m + n - K) = _
  have hw := rectangularSeparatedWeight_eq_gamma
    m n (K - a) (n - a) hi hk
  rw [hka, hdegree, hma, hMdegree] at hw
  have hcoeff :
      ((g.coeff (n - (K - a)) : ℂ) /
            (n.choose (K - a) : ℂ) /
            ((m + n).choose (K - a) : ℂ)) *
        ((f.coeff (n - a) : ℂ) /
            (n.choose (n - a) : ℂ) /
            ((m + n).choose (m + n - a) : ℂ)) *
        (Nat.choose (n + (K - a) - (n - a)) (K - a) : ℂ) ^ 2 *
        (Nat.choose n (n - K) : ℂ) *
        (Nat.choose (m + n) (m + n - K) : ℂ) =
          (rectangularConvolutionGamma m n a (K - a) : ℂ) *
            (f.coeff (n - a) : ℂ) *
            (g.coeff (n - (K - a)) : ℂ) := by
    calc
      _ = (g.coeff (n - (K - a)) : ℂ) *
          (f.coeff (n - a) : ℂ) *
          (((1 : ℂ) / (n.choose (K - a) : ℂ) /
                ((m + n).choose (K - a) : ℂ)) *
            ((1 : ℂ) / (n.choose (n - a) : ℂ) /
                ((m + n).choose (m + n - a) : ℂ)) *
            (Nat.choose (n + (K - a) - (n - a)) (K - a) : ℂ) ^ 2 *
            (Nat.choose n (n - K) : ℂ) *
            (Nat.choose (m + n) (m + n - K) : ℂ)) := by ring
      _ = _ := by rw [hw]; ring
  rw [hma, hcoeff]
  push_cast
  rfl

private theorem rectangularConvolutionCoeff_monomial_expansion
    (m n K : ℕ) (f g : ℝ[X]) :
    MvPolynomial.C (rectangularConvolutionCoeff m n f g K : ℂ) *
        MvPolynomial.X (0 : Fin 2) ^ (n - K) *
        MvPolynomial.X (1 : Fin 2) ^ (m + n - K) =
      ∑ a ∈ Finset.range (K + 1),
        MvPolynomial.C
            ((rectangularConvolutionGamma m n a (K - a) *
              f.coeff (n - a) * g.coeff (n - (K - a)) : ℝ) : ℂ) *
          MvPolynomial.X (0 : Fin 2) ^ (n - K) *
          MvPolynomial.X (1 : Fin 2) ^ (m + n - K) := by
  unfold rectangularConvolutionCoeff
  push_cast
  rw [map_sum, Finset.sum_mul, Finset.sum_mul]

/-- The differential pairing of complementary rectangular polarizations
specializes to the rectangular additive convolution. This is the algebraic
identity used in Gribinski--Marcus, Theorem 2.3. -/
theorem rectangularDifferential_diagonal_identity
    (m n : ℕ) (f g : ℝ[X]) :
    MvPolynomial.rename rectangularDiagonal
        (applyNegDifferential
          (reciprocalRectangularPolarization m n
            (g.map Complex.ofRealHom))
          (rectangularPolarization m n (f.map Complex.ofRealHom))) =
      MvPolynomial.X 1 ^ m *
        xyLift ((rectangularAdditiveConvolution m n f g).map
          Complex.ofRealHom) := by
  rw [rectangularDifferential_expansion]
  rw [rectangularDifferentialDiagonalSummand_triangle m n
    (f.map Complex.ofRealHom) (g.map Complex.ofRealHom)]
  rw [xyLift_rectangularAdditiveConvolution_expansion]
  apply Finset.sum_congr rfl
  intro K hK
  have hKn : K ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hK)
  calc
    _ = ∑ a ∈ Finset.range (K + 1),
        MvPolynomial.C
            ((rectangularConvolutionGamma m n a (K - a) *
              f.coeff (n - a) * g.coeff (n - (K - a)) : ℝ) : ℂ) *
          MvPolynomial.X (0 : Fin 2) ^ (n - K) *
          MvPolynomial.X (1 : Fin 2) ^ (m + n - K) := by
            apply Finset.sum_congr rfl
            intro a ha
            simpa only using
              rectangularDifferentialDiagonalCore_reindex
                m n K a hKn
                  (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) f g
    _ = _ :=
      (rectangularConvolutionCoeff_monomial_expansion m n K f g).symm

end

end RealRooted
