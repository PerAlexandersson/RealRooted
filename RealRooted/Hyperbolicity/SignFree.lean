module

import RealRooted.Hyperbolicity
public import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic
public import RealRooted.MultivariateStability
public import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
import RealRooted.MultivariateStability.JumpSystem

/-!
# Sign-free top components and boundary hyperbolicity

The top homogeneous component of a real stable polynomial is real stable, with no
coefficient-sign hypothesis (`MvRealStable.homogeneousComponent_totalDegree`): for finitely many
variables this is the initial-form theorem for weights `-1`
(`JumpSystem.Stable.weightedHomogeneousComponent`), and the general case reduces to it through
`MvPolynomial.exists_fin_rename`.  Its value at a strictly positive vector is therefore nonzero,
and the exact ordinary homogenization is hyperbolic in every boundary direction `(0, b)`
(`MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary`).  This is item A of issue #954;
the earlier versions assuming nonnegative coefficients are
`MvRealStable.homogeneousComponent_totalDegree_of_hasNonnegCoeffs` and
`MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary_of_hasNonnegCoeffs`.
-/

public section

open Polynomial

namespace RealRooted

noncomputable section

private theorem weight_neg_one_eq_neg_degree {n : ℕ} (d : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ => (-1 : ℤ)) d = -(d.degree : ℤ) := by
  rw [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum]
  push_cast
  simp

/-- For finitely many variables, the top homogeneous component of a
real-stable polynomial is real stable, with no coefficient-sign hypothesis. -/
private theorem MvRealStable.homogeneousComponent_totalDegree_fin
    {n : ℕ} {P : MvPolynomial (Fin n) ℝ} (hst : MvRealStable P) :
    MvRealStable
      (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  let w : Fin n → ℤ := fun _ => -1
  have hmin : ∀ d ∈ P.support,
      -(P.totalDegree : ℤ) ≤ Finsupp.weight w d := by
    intro d hd
    rw [show Finsupp.weight w d = -(d.degree : ℤ) by
      simpa [w] using weight_neg_one_eq_neg_degree d]
    apply neg_le_neg
    exact_mod_cast MvPolynomial.le_totalDegree hd
  obtain ⟨d, hd, hdegree⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hst.ne_zero) (fun e => e.degree)
  have htotal : P.totalDegree = d.degree := by
    have hfun :
        (fun e : Fin n →₀ ℕ => e.sum fun _ k => k) =
          fun e => e.degree := by
      funext e
      rw [Finsupp.degree_apply]
      rfl
    rw [MvPolynomial.totalDegree, hfun]
    exact hdegree
  have hex : ∃ d ∈ P.support,
      Finsupp.weight w d = -(P.totalDegree : ℤ) := by
    refine ⟨d, hd, ?_⟩
    rw [show Finsupp.weight w d = -(d.degree : ℤ) by
      simpa [w] using weight_neg_one_eq_neg_degree d, htotal]
  have hstable : JumpSystem.Stable
      (MvPolynomial.weightedHomogeneousComponent w
        (-(P.totalDegree : ℤ)) P) :=
    JumpSystem.Stable.weightedHomogeneousComponent hst w
      (-(P.totalDegree : ℤ)) hmin hex
  have heq :
      MvPolynomial.weightedHomogeneousComponent w
          (-(P.totalDegree : ℤ)) P =
        MvPolynomial.homogeneousComponent P.totalDegree P := by
    ext e
    rw [MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_homogeneousComponent]
    rw [show Finsupp.weight w e = -(e.degree : ℤ) by
      simpa [w] using weight_neg_one_eq_neg_degree e]
    simp
  rw [heq] at hstable
  exact hstable

private theorem totalDegree_rename_of_injective
    {R σ τ : Type*} [CommSemiring R] (f : σ → τ)
    (hf : Function.Injective f) (P : MvPolynomial σ R) :
    (MvPolynomial.rename f P).totalDegree = P.totalDegree := by
  have h := MvPolynomial.weightedTotalDegree_rename_of_injective
    (R := R) (e := f) (w := (1 : τ → ℕ)) (P := P) hf
  have hcomp : (1 : τ → ℕ) ∘ f = (1 : σ → ℕ) := rfl
  rw [MvPolynomial.weightedTotalDegree_one, hcomp,
    MvPolynomial.weightedTotalDegree_one] at h
  exact h

/-- For an arbitrary variable type, the top homogeneous component of a real-stable polynomial is
real stable, with no coefficient-sign hypothesis. -/
theorem MvRealStable.homogeneousComponent_totalDegree
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P) :
    MvRealStable (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  obtain ⟨n, f, hf, Q, rfl⟩ := MvPolynomial.exists_fin_rename P
  rw [totalDegree_rename_of_injective f hf Q,
    ← MvPolynomial.rename_homogeneousComponent]
  exact ((hst.of_rename hf).homogeneousComponent_totalDegree_fin).rename f

/-- For an arbitrary variable type, the top homogeneous component of a real-stable polynomial
does not vanish on a coordinatewise strictly positive real vector. -/
theorem MvRealStable.eval_homogeneousComponent_totalDegree_ne_zero
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    MvPolynomial.eval b
      (MvPolynomial.homogeneousComponent P.totalDegree P) ≠ 0 := by
  let H := MvPolynomial.homogeneousComponent P.totalDegree P
  have hHstable : MvRealStable H := by
    simpa [H] using hst.homogeneousComponent_totalDegree
  have hHhom : (complexifyMv H).IsHomogeneous P.totalDegree := by
    exact (MvPolynomial.homogeneousComponent_isHomogeneous
      P.totalDegree P).map Complex.ofRealHom
  intro heval
  have hevalH : MvPolynomial.eval b H = 0 := by
    simpa [H] using heval
  have hcomplexEval :
      MvPolynomial.eval (fun i => (b i : ℂ)) (complexifyMv H) = 0 := by
    change MvPolynomial.eval (Complex.ofRealHom ∘ b)
      (MvPolynomial.map Complex.ofRealHom H) = 0
    rw [← MvPolynomial.map_eval Complex.ofRealHom b H]
    simp [hevalH]
  have hnonzero := hHstable (fun i => Complex.I * (b i : ℂ)) fun i => by
    simpa using hb i
  apply hnonzero
  rw [hHhom.eval_smul, hcomplexEval, mul_zero]

/-- For an arbitrary variable type, exact ordinary homogenization is hyperbolic in every
direction that is positive on the original coordinates and zero on the homogenizing coordinate,
with no coefficient-sign hypothesis. -/
theorem MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary
    {σ : Type*} {P : MvPolynomial σ ℝ} (hst : MvRealStable P)
    (b : σ → ℝ) (hb : ∀ i, 0 < b i) :
    (MvPolynomial.ordinaryHomogenization P P.totalDegree).HyperbolicAt
      (fun o => Option.elim o 0 b) :=
  hst.ordinaryHomogenization_hyperbolicAt_boundary_of_top
    hst.homogeneousComponent_totalDegree b hb
    (hst.eval_homogeneousComponent_totalDegree_ne_zero b hb)

/-! ### Sign-free boundary hyperbolicity: examples from issue #954 -/

example :
    let P : MvPolynomial (Fin 1) ℝ :=
      MvPolynomial.X 0 - MvPolynomial.C 1
    (MvPolynomial.ordinaryHomogenization P P.totalDegree).HyperbolicAt
      (fun o => Option.elim o 0 (fun _ => 1)) := by
  dsimp only
  apply MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary
  · intro z hz
    change ∀ i, 0 < (z i).im at hz
    simp only [complexifyMv, map_sub, MvPolynomial.map_X,
      MvPolynomial.map_C, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    intro hzero
    have him := congrArg Complex.im hzero
    have him0 : (z 0).im = 0 := by simpa using him
    exact (hz 0).ne' him0
  · simp

example :
    let P : MvPolynomial (Fin 2) ℝ :=
      MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C 1
    (MvPolynomial.ordinaryHomogenization P P.totalDegree).HyperbolicAt
      (fun o => Option.elim o 0 (fun _ => 1)) := by
  dsimp only
  apply MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary
  · intro z hz
    change ∀ i, 0 < (z i).im at hz
    simp only [complexifyMv, map_sub, map_mul, MvPolynomial.map_X,
      MvPolynomial.map_C, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    intro hzero
    have hmul : z 0 * z 1 = 1 := by
      simpa using sub_eq_zero.mp hzero
    have hz0 : z 0 ≠ 0 := fun h => by
      rw [h, zero_mul] at hmul
      exact zero_ne_one hmul
    have hone : (z 0)⁻¹ * z 0 = 1 := inv_mul_cancel₀ hz0
    have hz1 : z 1 = (z 0)⁻¹ := by
      calc
        z 1 = 1 * z 1 := by simp
        _ = ((z 0)⁻¹ * z 0) * z 1 := by rw [hone]
        _ = (z 0)⁻¹ * (z 0 * z 1) := by rw [mul_assoc]
        _ = (z 0)⁻¹ := by rw [hmul, mul_one]
    have hinvneg : ((z 0)⁻¹).im < 0 := by
      simpa [one_div] using
        (Complex.one_div_sub_im_neg (w := z 0) (r := 0) (by
          simpa using hz 0))
    have hz1pos := hz 1
    rw [hz1] at hz1pos
    exact (not_lt_of_ge hz1pos.le) hinvneg
  · simp

example :
    let P : MvPolynomial (Fin 1) ℝ := MvPolynomial.C (-1)
    (MvPolynomial.ordinaryHomogenization P P.totalDegree).HyperbolicAt
      (fun o => Option.elim o 0 (fun _ => 1)) := by
  dsimp only
  apply MvRealStable.ordinaryHomogenization_hyperbolicAt_boundary
  · simpa using
      (MvRealStable.one.C_mul (by norm_num : (-1 : ℝ) ≠ 0) :
        MvRealStable (MvPolynomial.C (-1) * 1 :
          MvPolynomial (Fin 1) ℝ))
  · simp

end

end RealRooted
