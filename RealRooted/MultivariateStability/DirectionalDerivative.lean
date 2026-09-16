import RealRooted.LiebSokalPointwise
import RealRooted.MultivariateStability.Specialization

/-!
# Directional derivatives of stable polynomials

This file derives weak stability of a nonnegative directional derivative from
the stable directional-derivative pencil.  The proof differentiates the
pencil only in its fresh affine coordinate, so it does not require general
degree-box polarization.
-/

namespace RealRooted

open scoped BigOperators

/-- The directional derivative of a fresh affine-coordinate extension splits
into directional derivatives of its two endpoints. -/
theorem directionalPDeriv_add_X_mul_rename_some
    {σ R : Type*} [Fintype σ] [CommSemiring R]
    (c : σ → R) (t : R) (P Q : MvPolynomial σ R) :
    directionalPDeriv (fun o : Option σ => o.elim t c)
        (MvPolynomial.rename some P + MvPolynomial.X none *
          MvPolynomial.rename some Q) =
      MvPolynomial.rename some (directionalPDeriv c P + MvPolynomial.C t * Q) +
        MvPolynomial.X none * MvPolynomial.rename some (directionalPDeriv c Q) := by
  classical
  have hPnone : MvPolynomial.pderiv none (MvPolynomial.rename some P) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hnone
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some P hnone
    exact (Option.some_ne_none i) hi
  have hQnone : MvPolynomial.pderiv none (MvPolynomial.rename some Q) = 0 := by
    apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
    intro hnone
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some Q hnone
    exact (Option.some_ne_none i) hi
  have hPsome (i : σ) :
      MvPolynomial.pderiv (some i) (MvPolynomial.rename some P) =
        MvPolynomial.rename some (MvPolynomial.pderiv i P) := by
    exact MvPolynomial.pderiv_rename (Option.some_injective σ) i P
  have hQsome (i : σ) :
      MvPolynomial.pderiv (some i) (MvPolynomial.rename some Q) =
        MvPolynomial.rename some (MvPolynomial.pderiv i Q) := by
    exact MvPolynomial.pderiv_rename (Option.some_injective σ) i Q
  have hXsome (i : σ) :
      MvPolynomial.pderiv (some i)
        (MvPolynomial.X none : MvPolynomial (Option σ) R) = 0 :=
    MvPolynomial.pderiv_X_of_ne (Ne.symm (Option.some_ne_none i))
  rw [directionalPDeriv, Fintype.sum_option]
  simp_rw [map_add, MvPolynomial.pderiv_mul]
  simp only [Option.elim_none, Option.elim_some, hPnone, hQnone,
    MvPolynomial.pderiv_X_self, hPsome, hQsome, hXsome, zero_mul,
    zero_add, mul_zero, add_zero, one_mul, directionalPDeriv, map_mul,
    map_sum, MvPolynomial.rename_C, Finset.mul_sum]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hsum :
      (∑ i : σ, MvPolynomial.C (c i) * (MvPolynomial.X none *
        MvPolynomial.rename some (MvPolynomial.pderiv i Q))) =
      ∑ i : σ, MvPolynomial.X none * (MvPolynomial.C (c i) *
        MvPolynomial.rename some (MvPolynomial.pderiv i Q)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  calc
    _ = (∑ i : σ, MvPolynomial.C (c i) *
          MvPolynomial.rename some (MvPolynomial.pderiv i P)) +
        (MvPolynomial.C t * MvPolynomial.rename some Q +
          ∑ i : σ, MvPolynomial.X none * (MvPolynomial.C (c i) *
            MvPolynomial.rename some (MvPolynomial.pderiv i Q))) :=
      add_left_comm _ _ _
    _ = _ := (add_assoc _ _ _).symm

/-- A nonnegative directional derivative of an upper-half-plane stable
polynomial is either zero or upper-half-plane stable. -/
theorem MvUpperHalfPlaneStable.directionalPDeriv_zero_or
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (c : σ → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    MvUpperHalfPlaneStableOrZero
      (directionalPDeriv (fun i => (c i : ℂ)) P) := by
  classical
  let D := directionalPDeriv (fun i => (c i : ℂ)) P
  let pencil : MvPolynomial (Option σ) ℂ :=
    MvPolynomial.rename some P + MvPolynomial.X none *
      MvPolynomial.rename some D
  have hpencil : MvUpperHalfPlaneStable pencil := by
    exact hP.directionalPDeriv_pencil c hc
  have hbaseVars : none ∉ (MvPolynomial.rename some P).vars := by
    intro hnone
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some P hnone
    exact (Option.some_ne_none i) hi
  have hderivVars : none ∉ (MvPolynomial.rename some D).vars := by
    intro hnone
    obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename some D hnone
    exact (Option.some_ne_none i) hi
  have hbaseDegree : (MvPolynomial.rename some P).degreeOf none = 0 :=
    not_ne_iff.mp ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.not).mp hbaseVars)
  have hderivDegree : (MvPolynomial.rename some D).degreeOf none = 0 :=
    not_ne_iff.mp ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.not).mp hderivVars)
  have hpencilDegree : pencil.degreeOf none ≤ 1 := by
    apply (MvPolynomial.degreeOf_add_le none _ _).trans
    apply max_le
    · simp [hbaseDegree]
    · apply (MvPolynomial.degreeOf_mul_le none _ _).trans
      simp [hderivDegree]
  have hpderiv := hpencil.pderiv_zero_or_of_degreeOf_le_one none hpencilDegree
  have hpderivEq : MvPolynomial.pderiv none pencil =
      MvPolynomial.rename some D := by
    have hbasePDeriv := MvPolynomial.pderiv_eq_zero_of_notMem_vars hbaseVars
    have hderivPDeriv := MvPolynomial.pderiv_eq_zero_of_notMem_vars hderivVars
    simp [pencil, hbasePDeriv, hderivPDeriv]
  rw [hpderivEq] at hpderiv
  exact MvUpperHalfPlaneStableOrZero.of_rename hpderiv
    (Option.some_injective σ)

/-- A nonnegative directional derivative of a real stable polynomial is
either zero or real stable. -/
theorem MvRealStable.directionalPDeriv_zero_or
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) (c : σ → ℝ) (hc : ∀ i, 0 ≤ c i) :
    MvRealStableOrZero (directionalPDeriv c P) := by
  rw [mvRealStableOrZero_iff_complexifyMv]
  unfold MvRealStable at hP
  have h := MvUpperHalfPlaneStable.directionalPDeriv_zero_or hP c hc
  simpa [complexifyMv, directionalPDeriv, MvPolynomial.pderiv_map] using h

/-- The sum of all partial derivatives of a real stable polynomial is either
zero or real stable. -/
theorem MvRealStable.sum_pderiv_zero_or
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℝ}
    (hP : MvRealStable P) :
    MvRealStableOrZero (∑ i : σ, MvPolynomial.pderiv i P) := by
  simpa [directionalPDeriv] using
    hP.directionalPDeriv_zero_or (fun _ => (1 : ℝ)) fun _ => zero_le_one

/-- Differentiating a stable fresh affine-coordinate extension in a
nonnegative direction produces another weakly stable affine extension. -/
theorem MvRealStable.affineExtension_directionalPDeriv_zero_or
    {σ : Type*} [Fintype σ] {P Q : MvPolynomial σ ℝ}
    (hPQ : MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some Q))
    (c : σ → ℝ) (t : ℝ) (hc : ∀ i, 0 ≤ c i) (ht : 0 ≤ t) :
    MvRealStableOrZero
      (MvPolynomial.rename some
          (directionalPDeriv c P + MvPolynomial.C t * Q) +
        MvPolynomial.X none *
          MvPolynomial.rename some (directionalPDeriv c Q)) := by
  have hweights : ∀ o : Option σ, 0 ≤ o.elim t c := by
    intro o
    cases o with
    | none => exact ht
    | some i => exact hc i
  have hderiv := hPQ.directionalPDeriv_zero_or
    (fun o : Option σ => o.elim t c) hweights
  rw [directionalPDeriv_add_X_mul_rename_some] at hderiv
  exact hderiv

/-- Every real specialization of a differentiated stable affine extension is
weakly stable. -/
theorem MvRealStable.affineExtension_directionalPDeriv_specialize
    {σ : Type*} [Fintype σ] {P Q : MvPolynomial σ ℝ}
    (hPQ : MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some Q))
    (c : σ → ℝ) (t s : ℝ) (hc : ∀ i, 0 ≤ c i) (ht : 0 ≤ t) :
    MvRealStableOrZero
      (directionalPDeriv c P + MvPolynomial.C t * Q +
        MvPolynomial.C s * directionalPDeriv c Q) := by
  exact (hPQ.affineExtension_directionalPDeriv_zero_or c t hc ht).affineExtension_specialize s

/-- The affine extension obtained by a nonnegative directional derivative is
stable whenever it is nonzero. -/
theorem MvRealStable.affineExtension_directionalPDeriv
    {σ : Type*} [Fintype σ] {P Q : MvPolynomial σ ℝ}
    (hPQ : MvRealStable
      (MvPolynomial.rename some P + MvPolynomial.X none *
        MvPolynomial.rename some Q))
    (c : σ → ℝ) (t : ℝ) (hc : ∀ i, 0 ≤ c i) (ht : 0 ≤ t)
    (hne : MvPolynomial.rename some
          (directionalPDeriv c P + MvPolynomial.C t * Q) +
        MvPolynomial.X none *
          MvPolynomial.rename some (directionalPDeriv c Q) ≠ 0) :
    MvRealStable
      (MvPolynomial.rename some
          (directionalPDeriv c P + MvPolynomial.C t * Q) +
        MvPolynomial.X none *
          MvPolynomial.rename some (directionalPDeriv c Q)) := by
  rcases hPQ.affineExtension_directionalPDeriv_zero_or c t hc ht with hzero | hstable
  · exact (hne hzero).elim
  · exact hstable

end RealRooted
