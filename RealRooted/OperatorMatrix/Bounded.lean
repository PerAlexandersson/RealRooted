module

public import RealRooted.OperatorMatrix.LocalToGlobal
import RealRooted.OperatorMatrix.Composition
import RealRooted.AffineFamily.PF

/-!
# Degree-bounded ordered-PF operator matrices

We restrict the inputs of the existing ordered-PF predicates, while leaving output degrees
unrestricted. The local-to-global theorem includes every ordered rectangle. Its sufficiency
proof reduces to the unbounded theorem by freezing each input coordinate and precomposing
with evaluation at one. Nonnegative rescaling preserves the input cap.

Source: unpublished manuscript, `independent-coupled-operators.md`, Section 8, at revision
`d86187d` of `real-zero-preservers`; RealRooted issues #1763 and #2150.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- An operator matrix preserves ordered PF vectors whose coordinates have degree at most `N`.
There is no output degree restriction. -/
def PreservesOrderedPFUpTo {m n : ℕ} (N : ℕ)
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ f, IsOrderedPF f → (∀ j, (f j).natDegree ≤ N) → IsOrderedPF (apply M f)

/-- A two-by-two block preserves ordered PF inputs through degree `N`, with unrestricted output
degrees. Zero inputs, repeated roots and degree loss are included. -/
def PreservesOrderedPFPairUpTo (N : ℕ) (a b c d : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ f g, IsPFPolynomial f → IsPFPolynomial g → Interl f g →
    f.natDegree ≤ N → g.natDegree ≤ N →
    IsPFPolynomial (a f + b g) ∧ IsPFPolynomial (c f + d g) ∧
      Interl (a f + b g) (c f + d g)

/-- An unbounded ordered-PF pair preserver works at every input cap. -/
theorem PreservesOrderedPFPair.upTo {a b c d : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (h : PreservesOrderedPFPair a b c d) (N : ℕ) :
    PreservesOrderedPFPairUpTo N a b c d :=
  fun f g hf hg hfg _ _ => h f g hf hg hfg

/-- Preservation at a larger cap implies preservation at a smaller cap. -/
theorem PreservesOrderedPFPairUpTo.of_le {N K : ℕ} {a b c d : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (h : PreservesOrderedPFPairUpTo N a b c d) (hKN : K ≤ N) :
    PreservesOrderedPFPairUpTo K a b c d :=
  fun f g hf hg hfg hfK hgK => h f g hf hg hfg (hfK.trans hKN) (hgK.trans hKN)

/-- Universal preservation is equivalent to preservation at every common degree cap. -/
theorem preservesOrderedPFPair_iff_forall_upTo (a b c d : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPFPair a b c d ↔ ∀ N, PreservesOrderedPFPairUpTo N a b c d := by
  refine ⟨fun h N => h.upTo N, ?_⟩
  intro h f g hf hg hfg
  exact h (max f.natDegree g.natDegree) f g hf hg hfg (le_max_left _ _) (le_max_right _ _)

/-- At a fixed cap, a two-by-two matrix predicate agrees with the pair predicate. -/
theorem PreservesOrderedPFUpTo.two_two_iff (N : ℕ)
    (M : Fin 2 → Fin 2 → ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPFUpTo N M ↔
      PreservesOrderedPFPairUpTo N (M 0 0) (M 0 1) (M 1 0) (M 1 1) := by
  constructor
  · intro h f g hf hg hfg hfN hgN
    have hout := h ![f, g] ((isOrderedPF_pair_iff f g).mpr ⟨hf, hg, hfg⟩)
      (by intro j; fin_cases j <;> assumption)
    exact ⟨by simpa [apply, Fin.sum_univ_two] using hout.1 0,
      by simpa [apply, Fin.sum_univ_two] using hout.1 1,
      by simpa [apply, Fin.sum_univ_two] using hout.2 0 1 (by decide)⟩
  · intro h f hf hfN
    have hout := h (f 0) (f 1) (hf.1 0) (hf.1 1) (hf.2 0 1 (by decide)) (hfN 0) (hfN 1)
    have heq : apply M f = ![M 0 0 (f 0) + M 0 1 (f 1),
        M 1 0 (f 0) + M 1 1 (f 1)] := by
      ext i
      fin_cases i <;> simp [apply, Fin.sum_univ_two]
    rw [heq]
    exact (isOrderedPF_pair_iff _ _).mpr hout

/-- Bounded pair preservation is equivalent to coordinate PF preservation and PF preservation
of every positive affine output pencil. The input cap is unchanged by the pencil test. -/
theorem PreservesOrderedPFPairUpTo.iff_affine (N : ℕ)
    (a b c d : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPFPairUpTo N a b c d ↔
      ∀ f g, IsPFPolynomial f → IsPFPolynomial g → Interl f g →
        f.natDegree ≤ N → g.natDegree ≤ N →
        IsPFPolynomial (a f + b g) ∧ IsPFPolynomial (c f + d g) ∧
          ∀ s t : ℝ, 0 < s → 0 < t →
            IsPFPolynomial ((C s * X + C t) * (a f + b g) + (c f + d g)) := by
  constructor
  · intro h f g hf hg hfg hfN hgN
    obtain ⟨h₁, h₂, h₁₂⟩ := h f g hf hg hfg hfN hgN
    exact ⟨h₁, h₂, (interl_iff_isPFPolynomial_affine h₁ h₂).mp h₁₂⟩
  · intro h f g hf hg hfg hfN hgN
    obtain ⟨h₁, h₂, haff⟩ := h f g hf hg hfg hfN hgN
    exact ⟨h₁, h₂, (interl_iff_isPFPolynomial_affine h₁ h₂).mpr haff⟩

/-- Bounded ordered-PF preservation is equivalent to bounded preservation by every ordered
rectangle, including nonadjacent rows and columns. -/
theorem PreservesOrderedPFUpTo.iff_forall_blocks_of_two_le {m n : ℕ} (N : ℕ)
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    PreservesOrderedPFUpTo N M ↔
      ∀ i k j l, i < k → j < l →
        PreservesOrderedPFPairUpTo N (M i j) (M i l) (M k j) (M k l) := by
  classical
  constructor
  · intro h i k j l hik hjl f g hf hg hfg hfN hgN
    let v : Fin n → ℝ[X] := fun q => if q = j then f else if q = l then g else 0
    have hv : IsOrderedPF v := by
      constructor
      · intro q
        dsimp [v]
        split
        · exact hf
        · split
          · exact hg
          · exact IsPFPolynomial.zero
      · intro q r hqr
        by_cases hqj : q = j
        · by_cases hrl : r = l
          · simpa [v, hqj, hrl, hjl.ne'] using hfg
          · have hrj : r ≠ j := by grind
            simp [v, hqj, hrl, hrj, interl_zero_right]
        · by_cases hql : q = l
          · have hrl : r ≠ l := by grind
            have hrj : r ≠ j := by grind
            simp [v, hql, hrl, hrj, hjl.ne', interl_zero_right]
          · simp [v, hqj, hql, interl_zero_left]
    have hvN : ∀ q, (v q).natDegree ≤ N := by
      intro q
      dsimp [v]
      split
      · exact hfN
      · split
        · exact hgN
        · simp
    have heq (r : Fin m) : apply M v r = M r j f + M r l g := by
      simp only [apply, v]
      calc
        _ = ∑ q, ((if q = j then M r q f else 0) +
            if q = l then M r q g else 0) := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hqj : q = j <;> by_cases hql : q = l <;> simp_all
        _ = _ := by simp [Finset.sum_add_distrib]
    have hout := h v hv hvN
    exact ⟨by simpa [heq] using hout.1 i, by simpa [heq] using hout.1 k,
      by simpa [heq] using hout.2 i k hik⟩
  · intro hblock f hf hfN
    let E : Fin n → ℝ[X] →ₗ[ℝ] ℝ[X] :=
      fun j => (Polynomial.aeval (1 : ℝ)).toLinearMap.smulRight (f j)
    have hE (j : Fin n) (p : ℝ[X]) : E j p = C (p.eval 1) * f j := by
      simp [E, smul_eq_C_mul]
    let A : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X] := fun i j => (M i j).comp (E j)
    have hA : PreservesOrderedPF A := by
      rw [PreservesOrderedPF.iff_forall_blocks_of_two_le A hm hn]
      intro i k j l hik hjl p q hp hq _
      have hp₁ : 0 ≤ p.eval 1 := hp.hasNonnegCoeffs.eval_nonneg (by positivity)
      have hq₁ : 0 ≤ q.eval 1 := hq.hasNonnegCoeffs.eval_nonneg (by positivity)
      have hpf := (IsPFPolynomial.of_C_nonneg hp₁).mul (hf.1 j)
      have hqf := (IsPFPolynomial.of_C_nonneg hq₁).mul (hf.1 l)
      have horder := ((hf.2 j l hjl).C_mul_left_of_nonneg hp₁).C_mul_right_of_nonneg hq₁
      simpa only [A, LinearMap.comp_apply, hE] using hblock i k j l hik hjl _ _ hpf hqf
        horder ((natDegree_C_mul_le _ _).trans (hfN j))
        ((natDegree_C_mul_le _ _).trans (hfN l))
    have hone : IsOrderedPF (fun _ : Fin n => (1 : ℝ[X])) :=
      ⟨fun _ => IsPFPolynomial.one, fun _ _ _ => IsPFPolynomial.one.interl_self⟩
    have hAf : apply A (fun _ => 1) = apply M f := by
      funext i
      simp [apply, A, hE]
    rw [← hAf]
    exact hA _ hone

end RealRooted.OperatorMatrix
