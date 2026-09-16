import RealRooted.Hyperbolicity
import RealRooted.Multiaffine.AffineEulerCore
import RealRooted.MultivariateStability.AllCombo
import RealRooted.MultivariateStability.DirectionalDerivative
import RealRooted.MultivariateStability.HomogeneousPencilWronskian
import RealRooted.MultivariateStability.Rayleigh

/-!
# Stability of affine Euler cores

This module realizes the affine Euler operator as a dehomogenized
directional derivative.  Homogenization and the directional-derivative
pencil then place a stable polynomial and its affine Euler core in one
weakly stable real span.
-/

namespace RealRooted

open scoped BigOperators

noncomputable section

/-- Dehomogenizing the all-ones derivative of a homogeneous polynomial gives
the affine Euler core of its dehomogenization. -/
theorem MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one
    {σ R : Type*} [Fintype σ] [CommRing R]
    {H : MvPolynomial (Option σ) R} {d : Nat}
    (hH : H.IsHomogeneous d) :
    MvPolynomial.dehomogenize
        (directionalPDeriv (fun _ : Option σ => (1 : R)) H) =
      MvPolynomial.affineEulerCore id (d : R)
        (MvPolynomial.dehomogenize H) := by
  rw [directionalPDeriv, Fintype.sum_option, map_add, map_sum]
  simp_rw [map_mul, map_one, one_mul]
  rw [hH.dehomogenize_pderiv_none]
  simp_rw [MvPolynomial.dehomogenize_pderiv_some]
  unfold MvPolynomial.affineEulerCore MvPolynomial.eulerOperator
  simp only [id_eq]

/-- Dehomogenizing the all-ones derivative of a degree-`d` ordinary
homogenization gives the degree-`d` affine Euler core. -/
theorem dehomogenize_directionalPDeriv_ordinaryHomogenization
    {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (d : Nat) (hdeg : P.totalDegree ≤ d) :
    MvPolynomial.dehomogenize
        (directionalPDeriv (fun _ : Option σ => (1 : R))
          (MvPolynomial.ordinaryHomogenization P d)) =
      MvPolynomial.affineEulerCore id (d : R) P := by
  rw [MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one
    (MvPolynomial.ordinaryHomogenization_isHomogeneous P d),
    MvPolynomial.dehomogenize_ordinaryHomogenization_of_totalDegree_le
      P hdeg]

/-- The affine Euler core inherited from a homogeneous Rayleigh polynomial
has the directional-derivative Wronskian orientation against its
dehomogenization. -/
theorem MvPolynomial.IsRayleigh.eval_coordinateWronskian_affineEulerCore_nonneg
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hH : H.IsRayleigh) (hhom : H.IsHomogeneous d) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.dehomogenize H))
        (MvPolynomial.dehomogenize H) i) := by
  intro i x
  rw [← MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hhom,
    ← MvPolynomial.dehomogenize_coordinateWronskian_some,
    MvPolynomial.eval_dehomogenize]
  exact hH.eval_coordinateWronskian_directionalPDeriv_nonneg
    (fun _ : Option σ => (1 : Real)) (fun _ => zero_le_one)
    (some i) (fun o => Option.elim o 1 x)

/-- For a stable multiaffine homogeneous polynomial, the affine Euler core
has the directional-derivative Wronskian orientation against its
dehomogenization. -/
theorem MvRealStable.eval_coordinateWronskian_affineEulerCore_nonneg
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hstable : MvRealStable H) (hma : MvPolynomial.IsMultiaffine H)
    (hhom : H.IsHomogeneous d) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.dehomogenize H))
        (MvPolynomial.dehomogenize H) i) :=
  MvPolynomial.IsRayleigh.eval_coordinateWronskian_affineEulerCore_nonneg
    (hstable.isRayleigh_of_isMultiaffine hma) hhom

/-- The all-ones directional derivative lowers homogeneous degree by one. -/
theorem MvPolynomial.IsHomogeneous.directionalPDeriv_one
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hhom : H.IsHomogeneous d) :
    (directionalPDeriv (fun _ : σ => (1 : Real)) H).IsHomogeneous
      (d - 1) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  simpa [directionalPDeriv] using hhom.pderiv (i := i)

/-- The all-ones directional derivative preserves coefficient
nonnegativity. -/
theorem MvPolynomial.HasNonnegCoeffs.directionalPDeriv_one
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real}
    (hnn : H.HasNonnegCoeffs) :
    (directionalPDeriv (fun _ : σ => (1 : Real)) H).HasNonnegCoeffs := by
  apply MvPolynomial.HasNonnegCoeffs.sum
  intro i hi
  simpa [directionalPDeriv] using hnn.pderiv i

/-- The all-ones directional derivative of a positive-degree stable
homogeneous polynomial with nonnegative coefficients is nonzero. -/
theorem MvRealStable.directionalPDeriv_one_ne_zero
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    directionalPDeriv (fun _ : σ => (1 : Real)) H ≠ 0 := by
  let D := directionalPDeriv (fun _ : σ => (1 : Real)) H
  intro hzero
  have hD_eval : MvPolynomial.eval (fun _ : σ => (1 : Real)) D = 0 := by
    rw [show D = 0 by exact hzero]
    simp
  have heuler := congrArg
    (MvPolynomial.eval (fun _ : σ => (1 : Real)))
    hhom.sum_X_mul_pderiv
  have hH_eval : 0 < MvPolynomial.eval (fun _ : σ => (1 : Real)) H :=
    hnn.eval_pos hstable.ne_zero fun _ => zero_lt_one
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    one_mul, map_nsmul] at heuler
  have hD_eval' : MvPolynomial.eval (fun _ : σ => (1 : Real)) D =
      ∑ i : σ, MvPolynomial.eval (fun _ : σ => (1 : Real))
        (MvPolynomial.pderiv i H) := by
    simp [D, directionalPDeriv]
  rw [← hD_eval', hD_eval] at heuler
  have hdpos : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  simp only [nsmul_eq_mul] at heuler
  nlinarith

/-- The all-ones directional derivative of a positive-degree stable
homogeneous polynomial with nonnegative coefficients is stable. -/
theorem MvRealStable.directionalPDeriv_one
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    MvRealStable (directionalPDeriv (fun _ : σ => (1 : Real)) H) := by
  rcases hstable.directionalPDeriv_zero_or
      (fun _ : σ => (1 : Real)) (fun _ => zero_le_one) with hzero | hderiv
  · exact ((hstable.directionalPDeriv_one_ne_zero hnn hhom hd) hzero).elim
  · exact hderiv

/-- A nonzero nonnegative directional derivative of a homogeneous stable
polynomial is Wronskian-oriented against the polynomial. -/
theorem MvRealStable.eval_coordinateWronskian_directionalPDeriv_nonneg_of_nonzero
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (b : σ → Real) (hb : ∀ i, 0 ≤ b i)
    (hD0 : directionalPDeriv b H ≠ 0) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian (directionalPDeriv b H) H i) := by
  let D := directionalPDeriv b H
  have hDhom : D.IsHomogeneous (d - 1) := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa [D, directionalPDeriv] using (hhom.pderiv (i := i)).C_mul (b i)
  have hDnn : MvPolynomial.HasNonnegCoeffs D := by
    apply MvPolynomial.HasNonnegCoeffs.sum
    intro i hi
    exact (MvPolynomial.HasNonnegCoeffs.C (hb i)).mul (hnn.pderiv i)
  have hpencil := hstable.directionalPDeriv_pencil b hb
  exact hpencil.eval_coordinateWronskian_nonneg_of_homogeneous_affineExtension
    hhom hDhom hnn hDnn hstable.ne_zero hD0

/-- A positive-degree homogeneous stable polynomial with nonnegative
coefficients has its all-ones directional derivative Wronskian-oriented
against it, without any multiaffineness hypothesis. -/
theorem MvRealStable.eval_coordinateWronskian_directionalPDeriv_one_nonneg
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (directionalPDeriv (fun _ : σ => (1 : Real)) H) H i) := by
  exact hstable.eval_coordinateWronskian_directionalPDeriv_nonneg_of_nonzero
    hnn hhom (fun _ : σ => (1 : Real)) (fun _ => zero_le_one)
      (hstable.directionalPDeriv_one_ne_zero hnn hhom hd)

/-- Two successive all-ones directional derivatives inherit the same
Wronskian orientation. -/
theorem MvRealStable.eval_coordinateWronskian_directionalPDeriv_one_twice_nonneg
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : 1 < d) :
    let D := directionalPDeriv (fun _ : σ => (1 : Real)) H
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (directionalPDeriv (fun _ : σ => (1 : Real)) D) D i) := by
  let D := directionalPDeriv (fun _ : σ => (1 : Real)) H
  have hDhom : D.IsHomogeneous (d - 1) :=
    MvPolynomial.IsHomogeneous.directionalPDeriv_one hhom
  have hDnn : MvPolynomial.HasNonnegCoeffs D :=
    MvPolynomial.HasNonnegCoeffs.directionalPDeriv_one hnn
  have hDstable : MvRealStable D :=
    hstable.directionalPDeriv_one hnn hhom (by lia)
  exact hDstable.eval_coordinateWronskian_directionalPDeriv_one_nonneg
    hDnn hDhom (by lia)

/-- For a positive-degree homogeneous stable polynomial with nonnegative
coefficients, `D H + D² H` is Wronskian-oriented against `H + D H`, where
`D` is the all-ones directional derivative. -/
theorem
    MvRealStable.eval_coordinateWronskian_directionalPDeriv_one_add_nonneg
    {σ : Type*} [Fintype σ] {H : MvPolynomial σ Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    let D := directionalPDeriv (fun _ : σ => (1 : Real)) H
    let E := directionalPDeriv (fun _ : σ => (1 : Real)) D
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian (D + E) (H + D) i) := by
  classical
  dsimp only
  let D := directionalPDeriv (fun _ : σ => (1 : Real)) H
  let E := directionalPDeriv (fun _ : σ => (1 : Real)) D
  let K : MvPolynomial (Option σ) Real :=
    MvPolynomial.rename some H + MvPolynomial.X none *
      MvPolynomial.rename some D
  let L := directionalPDeriv
    (fun o : Option σ => o.elim 0 (fun _ => (1 : Real))) K
  have hDhom : D.IsHomogeneous (d - 1) :=
    MvPolynomial.IsHomogeneous.directionalPDeriv_one hhom
  have hDnn : MvPolynomial.HasNonnegCoeffs D :=
    MvPolynomial.HasNonnegCoeffs.directionalPDeriv_one hnn
  have hKhom : K.IsHomogeneous d := by
    apply hhom.rename_isHomogeneous.add
    have hmul := (MvPolynomial.isHomogeneous_X Real
      (none : Option σ)).mul
        (hDhom.rename_isHomogeneous (f := some))
    simpa [K, Nat.add_sub_of_le (Nat.one_le_iff_ne_zero.mpr hd)] using hmul
  have hKnn : MvPolynomial.HasNonnegCoeffs K := by
    exact (hnn.rename_of_injective (Option.some_injective σ)).add
      ((MvPolynomial.HasNonnegCoeffs.X none).mul
        (hDnn.rename_of_injective (Option.some_injective σ)))
  have hKstable : MvRealStable K := by
    exact hstable.directionalPDeriv_pencil
      (fun _ : σ => (1 : Real)) fun _ => zero_le_one
  have hL : L = MvPolynomial.rename some D + MvPolynomial.X none *
      MvPolynomial.rename some E := by
    simpa [K, L, D, E] using directionalPDeriv_add_X_mul_rename_some
      (fun _ : σ => (1 : Real)) 0 H D
  have hD0 : D ≠ 0 :=
    hstable.directionalPDeriv_one_ne_zero hnn hhom hd
  have hL0 : L ≠ 0 := by
    intro hzero
    have hspecialize := congrArg
      (MvPolynomial.specializeAt (none : Option σ) 0) hzero
    rw [hL, specializeAt_none_add_X_mul_rename_some] at hspecialize
    simp only [map_zero, zero_mul, add_zero] at hspecialize
    exact hD0 (MvPolynomial.rename_injective some
      (Option.some_injective σ) hspecialize)
  have hLorient :=
    hKstable.eval_coordinateWronskian_directionalPDeriv_nonneg_of_nonzero
      hKnn hKhom
      (fun o : Option σ => o.elim 0 (fun _ => (1 : Real)))
      (by intro o; cases o <;> simp) hL0
  change ∀ i x, 0 ≤ MvPolynomial.eval x
    (MvPolynomial.coordinateWronskian L K i) at hLorient
  intro i x
  let y : Option σ → Real := fun o => o.elim 1 x
  have hy : Function.update y none 1 = y := by
    funext o
    cases o <;> simp [y]
  have h := hLorient (some i) y
  have hspecialized :
      MvPolynomial.specializeAt none 1
          (MvPolynomial.coordinateWronskian L K (some i)) =
        MvPolynomial.rename some
          (MvPolynomial.coordinateWronskian (D + E) (H + D) i) := by
    rw [MvPolynomial.specializeAt_coordinateWronskian_of_ne
      (Option.some_ne_none i), hL]
    simp only [K, specializeAt_none_add_X_mul_rename_some, map_one, one_mul]
    exact MvPolynomial.coordinateWronskian_rename some
      (Option.some_injective σ) (D + E) (H + D) i
  have heval := congrArg (MvPolynomial.eval y) hspecialized
  rw [MvPolynomial.eval_specializeAt, hy, MvPolynomial.eval_rename] at heval
  simpa [y] using heval ▸ h

/-- A positive-degree homogeneous stable polynomial with nonnegative
coefficients gives an oriented affine Euler core after dehomogenization. -/
theorem MvRealStable.eval_coordinateWronskian_affineEulerCore_nonneg_of_nonnegative
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.dehomogenize H))
        (MvPolynomial.dehomogenize H) i) := by
  intro i x
  rw [← MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hhom,
    ← MvPolynomial.dehomogenize_coordinateWronskian_some,
    MvPolynomial.eval_dehomogenize]
  exact hstable.eval_coordinateWronskian_directionalPDeriv_one_nonneg
    hnn hhom hd (some i) (fun o => Option.elim o 1 x)

/-- A homogeneous stable polynomial with nonnegative coefficients also
orients the affine Euler core of its first affine Euler core. -/
theorem
    MvRealStable.eval_coordinateWronskian_affineEulerCore_iterate_nonneg_of_nonnegative
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : 1 < d) :
    let P := MvPolynomial.dehomogenize H
    let D := MvPolynomial.affineEulerCore id (d : Real) P
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id ((d - 1 : Nat) : Real) D)
        D i) := by
  dsimp only
  let E := directionalPDeriv (fun _ : Option σ => (1 : Real)) H
  have hEhom : E.IsHomogeneous (d - 1) :=
    MvPolynomial.IsHomogeneous.directionalPDeriv_one hhom
  intro i x
  rw [show MvPolynomial.affineEulerCore id (d : Real)
        (MvPolynomial.dehomogenize H) = MvPolynomial.dehomogenize E by
        simpa [E] using
          (MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hhom).symm,
    ← MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hEhom,
    ← MvPolynomial.dehomogenize_coordinateWronskian_some,
    MvPolynomial.eval_dehomogenize]
  exact hstable.eval_coordinateWronskian_directionalPDeriv_one_twice_nonneg
    hnn hhom hd (some i) (fun o => Option.elim o 1 x)

/-- After dehomogenization, the affine Euler core of the first core is
Wronskian-oriented against the sum of the source and its first core. -/
theorem
    MvRealStable.eval_coordinateWronskian_affineEulerCore_add_nonneg_of_nonnegative
    {σ : Type*} [Fintype σ]
    {H : MvPolynomial (Option σ) Real} {d : Nat}
    (hstable : MvRealStable H) (hnn : MvPolynomial.HasNonnegCoeffs H)
    (hhom : H.IsHomogeneous d) (hd : d ≠ 0) :
    let P := MvPolynomial.dehomogenize H
    let D := MvPolynomial.affineEulerCore id (d : Real) P
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (MvPolynomial.affineEulerCore id (d : Real) D) (P + D) i) := by
  dsimp only
  let G := directionalPDeriv (fun _ : Option σ => (1 : Real)) H
  let E := directionalPDeriv (fun _ : Option σ => (1 : Real)) G
  have hGhom : G.IsHomogeneous (d - 1) :=
    MvPolynomial.IsHomogeneous.directionalPDeriv_one hhom
  have hGdehom : MvPolynomial.dehomogenize G =
      MvPolynomial.affineEulerCore id (d : Real)
        (MvPolynomial.dehomogenize H) := by
    simpa [G] using
      MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hhom
  have hEdehom : MvPolynomial.dehomogenize E =
      MvPolynomial.affineEulerCore id ((d - 1 : Nat) : Real)
        (MvPolynomial.dehomogenize G) := by
    simpa [E] using
      MvPolynomial.IsHomogeneous.dehomogenize_directionalPDeriv_one hGhom
  have hcoeff : (d : Real) = ((d - 1 : Nat) : Real) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)).symm
  intro i x
  rw [show MvPolynomial.affineEulerCore id (d : Real)
          (MvPolynomial.affineEulerCore id (d : Real)
            (MvPolynomial.dehomogenize H)) =
        MvPolynomial.dehomogenize (G + E) by
      rw [map_add, hEdehom, hGdehom, hcoeff,
        MvPolynomial.affineEulerCore_add_one],
    show MvPolynomial.dehomogenize H +
          MvPolynomial.affineEulerCore id (d : Real)
            (MvPolynomial.dehomogenize H) =
        MvPolynomial.dehomogenize (H + G) by rw [map_add, hGdehom],
    ← MvPolynomial.dehomogenize_coordinateWronskian_some,
    MvPolynomial.eval_dehomogenize]
  exact
    hstable.eval_coordinateWronskian_directionalPDeriv_one_add_nonneg
      hnn hhom hd (some i) (fun o => Option.elim o 1 x)

/-- Dehomogenization preserves weak real stability without a homogeneity
hypothesis, since it is boundary specialization at the real value one. -/
theorem MvRealStableOrZero.dehomogenize_general
    {σ : Type*} {P : MvPolynomial (Option σ) Real}
    (hP : MvRealStableOrZero P) :
    MvRealStableOrZero (MvPolynomial.dehomogenize P) := by
  have hspecialize := hP.specializeAt_general none 1
  rw [MvPolynomial.specializeAt_none_one_eq_rename_some_dehomogenize]
    at hspecialize
  exact MvRealStableOrZero.of_rename hspecialize
    (Option.some_injective σ)

/-- A stable polynomial with nonnegative coefficients and its admissible
affine Euler core lie in one weakly stable real span. -/
theorem MvRealStable.allCombo_affineEulerCore
    {σ : Type*} [Fintype σ] {P : MvPolynomial σ Real} {d : Nat}
    (hP : MvRealStable P) (hnn : MvPolynomial.HasNonnegCoeffs P)
    (hdeg : P.totalDegree ≤ d) :
    AllComboMvRealStableOrZero P
      (MvPolynomial.affineEulerCore id (d : Real) P) := by
  let H := MvPolynomial.ordinaryHomogenization P d
  let D := directionalPDeriv (fun _ : Option σ => (1 : Real)) H
  have hH : MvRealStable H :=
    hP.ordinaryHomogenization_of_totalDegree_le hnn hP.ne_zero hdeg
  have hDcore : MvPolynomial.dehomogenize D =
      MvPolynomial.affineEulerCore id (d : Real) P := by
    exact dehomogenize_directionalPDeriv_ordinaryHomogenization P d hdeg
  apply allComboMvRealStableOrZero_of_affine
  · rw [← hDcore]
    exact (hH.directionalPDeriv_zero_or
      (fun _ : Option σ => (1 : Real)) fun _ => zero_le_one).dehomogenize_general
  · intro t
    have hpencil := hH.directionalPDeriv_pencil
      (fun _ : Option σ => (1 : Real)) fun _ => zero_le_one
    have haffine := hpencil.affineExtension_specialize_zero_or t
    have hdehom := haffine.dehomogenize_general
    have hC : MvPolynomial.dehomogenize
        (MvPolynomial.C t : MvPolynomial (Option σ) Real) =
        MvPolynomial.C t := by
      simp [MvPolynomial.dehomogenize]
    rw [map_add, map_mul, hC,
      MvPolynomial.dehomogenize_ordinaryHomogenization_of_totalDegree_le
        P hdeg, hDcore] at hdehom
    exact hdehom

end

end RealRooted
