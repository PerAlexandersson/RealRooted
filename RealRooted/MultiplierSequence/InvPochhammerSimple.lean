module

public import RealRooted.Hadamard.SchurSzegoSimple
public import RealRooted.MultiplierSequence.InvPochhammer

/-!
# Simple roots under reciprocal-Pochhammer transforms

The reciprocal-Pochhammer diagonal operator preserves the degree and splitting
of a nonzero split polynomial.  If the input has nonzero constant coefficient,
then every output root is simple.  The multiplicity argument uses
Kostov--Shapiro, *On Schur--Szegő composition of polynomials*, Theorem 6(ii).
-/

public noncomputable section

open Polynomial

namespace RealRooted

private theorem diagonalOperator_inv_ascPochhammer_ne_zero
    {α : ℝ} (hα : 0 < α) {p : ℝ[X]} (hp : p ≠ 0) :
    diagonalOperator (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) p ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hzero
  rw [coeff_diagonalOperator, Polynomial.coeff_natDegree, coeff_zero] at hcoeff
  exact mul_ne_zero (inv_ne_zero (ascPochhammer_pos p.natDegree α hα).ne')
    (Polynomial.leadingCoeff_ne_zero.mpr hp) hcoeff

/-- For `α > 0`, the reciprocal-Pochhammer diagonal operator preserves the
degree of every nonzero real polynomial. -/
theorem natDegree_diagonalOperator_inv_ascPochhammer
    {α : ℝ} (hα : 0 < α) {p : ℝ[X]} (hp : p ≠ 0) :
    (diagonalOperator (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) p).natDegree =
      p.natDegree := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_diagonalOperator_le _ _)
  rw [coeff_diagonalOperator, Polynomial.coeff_natDegree]
  exact mul_ne_zero (inv_ne_zero (ascPochhammer_pos p.natDegree α hα).ne')
    (Polynomial.leadingCoeff_ne_zero.mpr hp)

/-- For `α > 0`, the reciprocal-Pochhammer diagonal operator sends a split
polynomial with nonzero constant coefficient to a split polynomial. -/
theorem splits_diagonalOperator_inv_ascPochhammer
    {α : ℝ} (hα : 0 < α) {p : ℝ[X]} (hp : p.Splits)
    (h0 : p.eval 0 ≠ 0) :
    (diagonalOperator (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) p).Splits := by
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at h0
  have hmult : IsMultiplierSequence
      (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) :=
    (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp
      (isPFMultiplierSequence_inv_ascPochhammer hα)).1
  rcases hmult.diagonalOperator_eq_zero_or_splits hp with hzero | hsplits
  · exact (diagonalOperator_inv_ascPochhammer_ne_zero hα hp0 hzero).elim
  · exact hsplits

/-- For `α > 0`, the reciprocal-Pochhammer diagonal operator separates every
nonzero root of a split polynomial.  Thus, when the input has nonzero constant
coefficient, all output roots are simple.  This is the finite
Schur--Szegő-composition corollary of Kostov--Shapiro, *On Schur--Szegő
composition of polynomials*, Theorem 6(ii). -/
theorem hasSimpleRoots_diagonalOperator_inv_ascPochhammer
    {α : ℝ} (hα : 0 < α) {p : ℝ[X]}
    (hp : p.Splits) (h0 : p.eval 0 ≠ 0) :
    HasSimpleRoots
      (diagonalOperator (fun k => ((ascPochhammer ℝ k).eval α)⁻¹) p) := by
  let γ : ℕ → ℝ := fun k => ((ascPochhammer ℝ k).eval α)⁻¹
  let n := p.natDegree
  let Q := jensenPolynomial n γ
  let L := generalizedLaguerre n (α - 1)
  let c := (ascPochhammer ℝ n).eval α
  have hp0 : p ≠ 0 := by
    intro hpzero
    simp [hpzero] at h0
  have hc : c ≠ 0 := by
    exact (ascPochhammer_pos n α hα).ne'
  have hscaled : C c * Q = L := by
    exact C_mul_jensenPolynomial_inv_ascPochhammer hα n
  have hQeq : Q = C c⁻¹ * L := by
    calc
      Q = C c⁻¹ * (C c * Q) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
      _ = C c⁻¹ * L := by rw [hscaled]
  have hQ0 : Q ≠ 0 := by
    rw [hQeq]
    exact mul_ne_zero (C_ne_zero.mpr (inv_ne_zero hc))
      (monic_generalizedLaguerre n (α - 1)).ne_zero
  have hQdegree : Q.natDegree = n := by
    have hdegree := congrArg Polynomial.natDegree hscaled
    simpa only [Polynomial.natDegree_C_mul hc, L,
      natDegree_generalizedLaguerre] using hdegree
  have hQsplits : Q.Splits := by
    rw [hQeq]
    exact (generalizedLaguerre_splits n (by linarith)).C_mul _
  have hQroots : Q.roots = L.roots := by
    rw [hQeq, Polynomial.roots_C_mul _ (inv_ne_zero hc)]
  have hQneg : ∀ b ∈ Q.roots, b < 0 := by
    intro b hb
    apply generalizedLaguerre_roots_neg n (α := α - 1) (by linarith) b
    rwa [← hQroots]
  have hQsimple : HasSimpleRoots Q := by
    apply HasSimpleRoots.of_roots_nodup hQ0
    rw [hQroots]
    exact generalizedLaguerre_roots_nodup n (α := α - 1) (by linarith)
  have hcomp : schurSzegoComp n p Q = diagonalOperator γ p := by
    rw [schurSzegoComp_comm]
    exact schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le le_rfl
  have hout0 : diagonalOperator γ p ≠ 0 :=
    diagonalOperator_inv_ascPochhammer_ne_zero hα hp0
  intro r hr
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    have hcoeff : (diagonalOperator γ p).coeff 0 = 0 := by
      simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hr
    rw [coeff_diagonalOperator] at hcoeff
    simp only [γ, ascPochhammer_zero, eval_one, inv_one, one_mul] at hcoeff
    exact h0 (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hcoeff)
  have hpos : 0 < (diagonalOperator γ p).rootMultiplicity r :=
    (Polynomial.rootMultiplicity_pos hout0).mpr hr
  by_contra hne
  have hmult : 1 < (schurSzegoComp n p Q).rootMultiplicity r := by
    rw [hcomp]
    lia
  obtain ⟨a, b, _ha, _hb, _hpa, hqb, _hsum, _hrab, heq⟩ :=
    exists_forced_factors_of_rootMultiplicity_schurSzegoComp
      (n := n) (P := p) (Q := Q) rfl hp hQdegree hQsplits hQneg r hr0 hmult
  have hpbound : p.rootMultiplicity a ≤ n :=
    Polynomial.rootMultiplicity_le_natDegree p a
  rw [hQsimple b hqb] at heq
  lia

end RealRooted
