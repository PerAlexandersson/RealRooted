/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Transforms.BrandenE.Basic
public import RealRooted.RootLocation.Basic
import RealRooted.Transforms.BrandenE.RootDomain
import Mathlib.Tactic

/-!
# Products of interval-rooted Brändén transforms

We iterate the diamond-product theorem with its exterior-ray root bound.
See Brändén, arXiv:math/0403364v2, Theorem 3.13 and equation (4.1).
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted

/-- Finite products of alphabets whose `E` images are rooted in `[-1,0]` have the same property. -/
theorem isRealRootedIn_brandenE_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, IsRealRootedIn (Set.Icc (-1) 0) (brandenE (f i))) :
    IsRealRootedIn (Set.Icc (-1) 0) (brandenE (∏ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : brandenE (1 : ℝ[X]) = 1 := by simpa using brandenE_X_pow (R := ℝ) 0
    simpa only [Finset.prod_empty, he] using
      (IsRealRootedIn.one : IsRealRootedIn (Set.Icc (-1) 0) (1 : ℝ[X]))
  | @insert i s hi ih =>
    rw [prod_insert hi]
    exact isRealRootedIn_Icc_brandenE_mul (hf i (mem_insert_self _ _))
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

end RealRooted
