module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.Tactic
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

public section

/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

/-!
# Oscillatory matrices

This file starts the upstream-shaped infrastructure for the classical oscillation
criterion.  Fallat--Woerdeman, Theorem 2, says that a totally nonnegative matrix
is oscillatory exactly when it is nonsingular and its first sub- and
superdiagonal entries are positive.

The local graph-theoretic part of that criterion is independent of total
nonnegativity: a nonnegative matrix indexed by a nontrivial finite chain is
irreducible when both adjacent diagonals are positive.  The one-dimensional
case additionally needs a positive entry; total nonnegativity and a nonzero
determinant supply it.

The remaining oscillation and leading-principal interlacing argument requires
the Li--Mathias Whitney reduction preserving the endpoint principal-section
spectrum, or the equivalent Gantmacher--Krein nodal theorem.  It is not claimed
here.

## Main results

* `Matrix.isIrreducible_of_nonneg_of_adjacent_pos`
* `Matrix.IsTotallyNonneg.isIrreducible_of_det_ne_zero_of_adjacent_pos`
-/

open Quiver

namespace Quiver

private noncomputable def pathFromZeroFin {n : ℕ} [Quiver (Fin (n + 1))]
    (hforward : ∀ i : Fin n, Nonempty (i.castSucc ⟶ i.succ)) :
    ∀ j : Fin (n + 1), Path 0 j := fun j =>
  Nat.rec
    (motive := fun m => ∀ hm : m < n + 1,
      Path 0 (⟨m, hm⟩ : Fin (n + 1)))
    (fun _ => Path.nil)
    (fun m ih hm => by
      let i : Fin n := ⟨m, by lia⟩
      exact (ih (by lia)).cons (hforward i).some)
    j.val j.isLt

private noncomputable def pathToZeroFin {n : ℕ} [Quiver (Fin (n + 1))]
    (hbackward : ∀ i : Fin n, Nonempty (i.succ ⟶ i.castSucc)) :
    ∀ j : Fin (n + 1), Path j 0 := fun j =>
  Nat.rec
    (motive := fun m => ∀ hm : m < n + 1,
      Path (⟨m, hm⟩ : Fin (n + 1)) 0)
    (fun _ => Path.nil)
    (fun m ih hm => by
      let i : Fin n := ⟨m, by lia⟩
      exact (hbackward i).some.toPath.comp (ih (by lia)))
    j.val j.isLt

private theorem isStronglyConnected_fin_of_adjacent {n : ℕ}
    [Quiver (Fin (n + 1))]
    (hforward : ∀ i : Fin n, Nonempty (i.castSucc ⟶ i.succ))
    (hbackward : ∀ i : Fin n, Nonempty (i.succ ⟶ i.castSucc)) :
    IsStronglyConnected (Fin (n + 1)) := by
  intro i j
  exact ⟨(pathToZeroFin hbackward i).comp (pathFromZeroFin hforward j)⟩

private theorem isSStronglyConnected_fin_of_adjacent {n : ℕ}
    [Quiver (Fin (n + 2))]
    (hforward : ∀ i : Fin (n + 1), Nonempty (i.castSucc ⟶ i.succ))
    (hbackward : ∀ i : Fin (n + 1), Nonempty (i.succ ⟶ i.castSucc)) :
    IsSStronglyConnected (Fin (n + 2)) :=
  IsStronglyConnected.isSStronglyConnected_of_hom
    (isStronglyConnected_fin_of_adjacent hforward hbackward)
    (hforward 0).some

end Quiver

namespace Matrix

/-- A nonnegative matrix on a finite chain of cardinality at least two is
irreducible when all entries immediately above and below the diagonal are
positive. -/
theorem isIrreducible_of_nonneg_of_adjacent_pos {n : ℕ}
    {R : Type*} [Ring R] [LinearOrder R]
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) R}
    (hA : ∀ i j, 0 ≤ A i j)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    A.IsIrreducible := by
  refine ⟨hA, ?_⟩
  letI : Quiver (Fin (n + 2)) := toQuiver A
  exact Quiver.isSStronglyConnected_fin_of_adjacent
    (fun i => ⟨PLift.up (hsuper i)⟩) (fun i => ⟨PLift.up (hsub i)⟩)

/-- The nonsingular TN adjacent-diagonal criterion implies irreducibility.

This is the graph-theoretic part of the classical oscillation criterion.  No
claim that a power is totally positive, that compounds are primitive, or that
principal-section characteristic polynomials interlace is made here. -/
theorem IsTotallyNonneg.isIrreducible_of_det_ne_zero_of_adjacent_pos
    {n : ℕ} {R : Type*} [CommRing R] [LinearOrder R]
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin n, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin n, 0 < A i.succ i.castSucc) :
    A.IsIrreducible := by
  cases n with
  | zero =>
      refine ⟨hA.nonneg, ?_⟩
      intro i j
      rw [Fin.eq_zero i, Fin.eq_zero j]
      have hne : A 0 0 ≠ 0 := by
        simpa [Matrix.det_fin_one] using hdet
      have hpos : 0 < A 0 0 :=
        lt_of_le_of_ne (hA.nonneg 0 0) hne.symm
      letI : Quiver (Fin 1) := toQuiver A
      exact ⟨(show (0 : Fin 1) ⟶ 0 from PLift.up hpos).toPath, by simp⟩
  | succ n =>
      exact isIrreducible_of_nonneg_of_adjacent_pos hA.nonneg hsuper hsub

end Matrix
