module

public import RealRooted.BorceaBranden.Transcendental.RealClassificationCore

@[expose] public section

open Filter Topology

noncomputable section

namespace RealRooted.BorceaBranden

variable {σ : Type} [Fintype σ]

omit [Fintype σ] in
private theorem preservesRealStabilityOnDegreeBox_of_preservesRealStability
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : PreservesRealStability T) (κ : σ → ℕ) :
    PreservesRealStabilityOnDegreeBox κ
      (T.comp (MvPolynomial.degreeOfLE σ ℝ κ).subtype) := by
  intro p hp
  exact hT p.1 hp

omit [Fintype σ] in
private theorem not_hasStableRankTwoRepresentation_of_bad_polynomial
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (p : MvPolynomial σ ℝ) (hp : ¬MvRealStableOrZero (T p))
    (κ : σ → ℕ) (hpκ : ∀ i, p.degreeOf i ≤ κ i) :
    ¬HasStableRankTwoRepresentation κ
      (T.comp (MvPolynomial.degreeOfLE σ ℝ κ).subtype) := by
  intro hrank
  let q : MvPolynomial.degreeOfLE σ ℝ κ :=
    ⟨p, (MvPolynomial.mem_degreeOfLE_iff_degreeOf p).2 hpκ⟩
  obtain ⟨α, β, P, Q, hall, hrepr⟩ := hrank
  apply hp
  have hq := hrepr q
  change T p = (α q) • P + (β q) • Q at hq
  rw [hq, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  exact hall (α q) (β q)

/-- Necessity in real Borcea--Brändén Theorem 1.4
(arXiv:0809.0401): a global real stability preserver has the stable
rank-at-most-two form, or one of its two signed transcendental symbols lies in
the real stable-limit class. -/
theorem rankTwo_or_signedTranscendentalSymbol_stableLimit_of_preservesRealStability
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : PreservesRealStability T) :
    HasGlobalStableRankTwoRepresentation T ∨
      IsRealStableLimit (realTranscendentalSymbolPolynomial T) ∨
      IsRealStableLimit
        (negRightFamily (realTranscendentalSymbolPolynomial T)) := by
  classical
  by_cases hrange : ∀ p, MvRealStableOrZero (T p)
  · exact Or.inl
      (hasStableRankTwoRangeRepresentation_of_forall_realStableOrZero T hrange)
  · obtain ⟨p, hp⟩ := not_forall.mp hrange
    let N := p.totalDegree
    let Pos : ℕ → Prop := fun m =>
      MvRealStable
        (MvPolynomial.algebraicSymbol (fun i => constExp σ (m + 1) i)
          (T.comp (MvPolynomial.degreeOfLE σ ℝ
            (fun i => constExp σ (m + 1) i)).subtype))
    let Neg : ℕ → Prop := fun m =>
      MvRealStable
        (MvPolynomial.algebraicSymbolNegRight
          (fun i => constExp σ (m + 1) i)
          (T.comp (MvPolynomial.degreeOfLE σ ℝ
            (fun i => constExp σ (m + 1) i)).subtype))
    have hsign : ∀ m, N ≤ m → Pos m ∨ Neg m := by
      intro m hm
      let β := constExp σ (m + 1)
      have hpreserves :=
        preservesRealStabilityOnDegreeBox_of_preservesRealStability
          T hT (fun i => β i)
      have hpβ : ∀ i, p.degreeOf i ≤ β i := by
        intro i
        change p.degreeOf i ≤ m + 1
        exact (MvPolynomial.degreeOf_le_totalDegree p i).trans
          (hm.trans (Nat.le_succ m))
      have hnrank : ¬HasStableRankTwoRepresentation (fun i => β i)
          (T.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype) :=
        not_hasStableRankTwoRepresentation_of_bad_polynomial T p hp _ hpβ
      have hfinite :=
        (preservesRealStabilityOnDegreeBox_iff_rankTwo_or_symbol_or_negRight
          (fun i => β i)
          (T.comp (MvPolynomial.degreeOfLE σ ℝ (fun i => β i)).subtype)).1
          hpreserves
      rcases hfinite with hRank | hPositive | hNegative
      · exact (hnrank hRank).elim
      · exact Or.inl hPositive
      · exact Or.inr hNegative
    by_cases hpos : ∀ M, ∃ m, M ≤ m ∧ Pos m
    · right
      left
      let b : ℕ → ℕ := fun k => Nat.find (hpos (max N k))
      have hbSpec : ∀ k, max N k ≤ b k ∧ Pos (b k) := fun k =>
        Nat.find_spec (hpos (max N k))
      have hb : Tendsto b atTop atTop := by
        rw [tendsto_atTop]
        intro a
        filter_upwards [eventually_ge_atTop a] with k hk
        exact hk.trans ((le_max_right N k).trans (hbSpec k).1)
      apply isRealStableLimit_of_cofinal_constExp_realGlue_stableOrZero
        (realTranscendentalSymbolPolynomial T) b hb
      intro k
      apply realGlue_stableOrZero_of_algebraicSymbol_realStable
      exact (hbSpec k).2
    · right
      right
      obtain ⟨M, hM⟩ := not_forall.mp hpos
      have hEventuallyNeg : ∀ m, max N M ≤ m → Neg m := by
        intro m hm
        have hmN : N ≤ m := (le_max_left N M).trans hm
        have hmM : M ≤ m := (le_max_right N M).trans hm
        rcases hsign m hmN with hPositive | hNegative
        · exact (hM ⟨m, hmM, hPositive⟩).elim
        · exact hNegative
      let b : ℕ → ℕ := fun k => k + max N M
      have hb : Tendsto b atTop atTop := tendsto_add_atTop_nat (max N M)
      apply isRealStableLimit_of_cofinal_constExp_realGlue_stableOrZero
        (negRightFamily (realTranscendentalSymbolPolynomial T)) b hb
      intro k
      apply
        realGlue_negRight_stableOrZero_of_algebraicSymbolNegRight_realStable
      exact hEventuallyNeg (b k) (Nat.le_add_left _ _)

/-- **Real Borcea--Brändén Theorem 1.4** (arXiv:0809.0401).
A real linear operator preserves multivariate real stability exactly when it
has the stable rank-at-most-two form, or one of its two signed
transcendental symbols belongs to the real stable-limit class. -/
theorem preservesRealStability_iff_rankTwo_or_signedTranscendentalSymbol_stableLimit
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ) :
    PreservesRealStability T ↔
      HasGlobalStableRankTwoRepresentation T ∨
        IsRealStableLimit (realTranscendentalSymbolPolynomial T) ∨
        IsRealStableLimit
          (negRightFamily (realTranscendentalSymbolPolynomial T)) := by
  constructor
  · exact rankTwo_or_signedTranscendentalSymbol_stableLimit_of_preservesRealStability T
  · rintro (hRank | hPositive | hNegative)
    · exact hRank.preservesRealStability
    · exact preservesRealStability_of_realTranscendentalSymbol_stableLimit T hPositive
    · exact
        preservesRealStability_of_negRight_transcendentalSymbol_stableLimit
          T hNegative

end RealRooted.BorceaBranden
