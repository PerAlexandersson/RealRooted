import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Specializing one variable of a multivariate polynomial

This file defines scalar specialization while retaining the ambient variable
type, together with its evaluation and coefficient-map interfaces.
-/

namespace MvPolynomial

/-- Replace one variable by a scalar while retaining the ambient variable
type. -/
noncomputable def specializeAt {σ R : Type*} [CommSemiring R]
    (i : σ) (c : R) (P : MvPolynomial σ R) : MvPolynomial σ R := by
  classical
  exact MvPolynomial.aeval
    (Function.update MvPolynomial.X i (MvPolynomial.C c)) P

@[simp] theorem specializeAt_zero {σ R : Type*} [CommSemiring R]
    (i : σ) (c : R) :
    specializeAt i c (0 : MvPolynomial σ R) = 0 := by
  simp [specializeAt]

@[simp] theorem specializeAt_C {σ R : Type*} [CommSemiring R]
    (i : σ) (c r : R) :
    specializeAt i c (MvPolynomial.C r : MvPolynomial σ R) =
      MvPolynomial.C r := by
  simp [specializeAt]

@[simp] theorem specializeAt_X {σ R : Type*} [CommSemiring R]
    [DecidableEq σ]
    (i j : σ) (c : R) :
    specializeAt i c (MvPolynomial.X j : MvPolynomial σ R) =
      if j = i then MvPolynomial.C c else MvPolynomial.X j := by
  classical
  by_cases hji : j = i <;> simp [specializeAt, hji]

@[simp] theorem specializeAt_add {σ R : Type*} [CommSemiring R]
    (i : σ) (c : R) (P Q : MvPolynomial σ R) :
    specializeAt i c (P + Q) = specializeAt i c P + specializeAt i c Q := by
  simp [specializeAt]

@[simp] theorem specializeAt_sub {σ R : Type*} [CommRing R]
    (i : σ) (c : R) (P Q : MvPolynomial σ R) :
    specializeAt i c (P - Q) = specializeAt i c P - specializeAt i c Q := by
  simp [specializeAt]

@[simp] theorem specializeAt_mul {σ R : Type*} [CommSemiring R]
    (i : σ) (c : R) (P Q : MvPolynomial σ R) :
    specializeAt i c (P * Q) = specializeAt i c P * specializeAt i c Q := by
  simp [specializeAt]

@[simp] theorem specializeAt_pow {σ R : Type*} [CommSemiring R]
    (i : σ) (c : R) (P : MvPolynomial σ R) (n : ℕ) :
    specializeAt i c (P ^ n) = specializeAt i c P ^ n := by
  simp [specializeAt]

/-- Evaluation after scalar specialization is evaluation at the updated
assignment. -/
@[simp] theorem eval_specializeAt {σ R : Type*} [CommSemiring R]
    [DecidableEq σ]
    (i : σ) (c : R) (P : MvPolynomial σ R) (z : σ → R) :
    MvPolynomial.eval z (specializeAt i c P) =
      MvPolynomial.eval (Function.update z i c) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      by_cases hji : j = i
      · subst j
        simp [hP]
      · simp [hP, hji]

/-- Scalar specialization commutes with mapping coefficients. -/
theorem map_specializeAt {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (i : σ) (c : R) (P : MvPolynomial σ R) :
    MvPolynomial.map f (specializeAt i c P) =
      specializeAt i (f c) (MvPolynomial.map f P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      by_cases hji : j = i <;> simp [hji, hP]

/-- Specialize the coordinates in an ordered list at values supplied by `c`.
Repeated coordinates are allowed and are processed in list order. -/
noncomputable def specializeAtList {σ R : Type*} [CommSemiring R]
    (c : σ → R) (l : List σ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  l.foldl (fun Q i => specializeAt i (c i) Q) P

@[simp] theorem specializeAtList_nil {σ R : Type*} [CommSemiring R]
    (c : σ → R) (P : MvPolynomial σ R) :
    specializeAtList c [] P = P :=
  rfl

@[simp] theorem specializeAtList_cons {σ R : Type*} [CommSemiring R]
    (c : σ → R) (i : σ) (l : List σ) (P : MvPolynomial σ R) :
    specializeAtList c (i :: l) P =
      specializeAtList c l (specializeAt i (c i) P) :=
  rfl

@[simp] theorem specializeAtList_zero {σ R : Type*} [CommSemiring R]
    (c : σ → R) (l : List σ) :
    specializeAtList c l (0 : MvPolynomial σ R) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [specializeAtList_cons, ih]

/-- Ordered scalar specialization commutes with mapping coefficients. -/
theorem map_specializeAtList {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (c : σ → R) (l : List σ) (P : MvPolynomial σ R) :
    MvPolynomial.map f (specializeAtList c l P) =
      specializeAtList (fun i => f (c i)) l (MvPolynomial.map f P) := by
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      simp only [specializeAtList_cons]
      rw [ih, map_specializeAt]

end MvPolynomial
