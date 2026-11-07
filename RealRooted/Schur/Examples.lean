module

import RealRooted.Schur.Rectangular
import RealRooted.Schur.ConstantColumns

/-! # Regression examples for signed Schur substitutions

The two-column example checks the sign for a moving coordinate of parity opposite
to the rectangle height. The empty-width case checks the determinant convention.
-/

open Polynomial Matrix
open RealRooted.Schur

example : rectangularElementarySubstitution (Finset.univ : Finset (Fin 4))
    (fun _ => 1) 3 2 0 = 1 := by
  simp [rectangularElementarySubstitution, checkerboardPencil]

example : rectangularElementarySubstitution (Finset.univ : Finset (Fin 4))
    (fun _ => 1) 3 2 2 = X + C 10 := by
  norm_num [rectangularElementarySubstitution, checkerboardPencil, Matrix.det_fin_two,
    elementaryMatrix, RealRooted.toeplitz, elementaryPolynomial, columnIndex,
    activeMatrix, checkerboard, Fin.prod_univ_succ, Polynomial.coeff_mul,
    Polynomial.coeff_one_add_X_pow]
  norm_num [Nat.choose, Polynomial.C_ofNat]
  ring

example (m : ℕ) :
    (elementarySubstitution (Finset.univ : Finset (Fin 4)) (fun _ => 1)
      (repeatColumns (fun _ : Fin 1 => 2) m)
      (repeatColumns (fun _ : Fin 1 => 0) m) 2).Splits := by
  exact (repeatColumns_isRealRooted_of_constant_height
    (Finset.univ : Finset (Fin 4)) (fun _ => 1) (by simp)
    antitone_const antitone_const 2 (by simp) (by norm_num) m).2
