/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# A splitting polynomial as a product over a vector of its roots

A polynomial `f` over a field that splits is `C f.leadingCoeff * ∏ i, (X - C (r i))` for a vector
`r : Fin f.natDegree → K` whose entries are the roots of `f` with multiplicity.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- A splitting polynomial is its leading coefficient times the product of `X - C (r i)` over a
vector `r` of its roots, listed with multiplicity. -/
theorem Splits.exists_fin_eq_C_mul_prod {f : K[X]} (hf : f.Splits) :
    ∃ r : Fin f.natDegree → K, Finset.univ.val.map r = f.roots ∧
      f = C f.leadingCoeff * ∏ i, (X - C (r i)) := by
  have hcard : Multiset.card f.roots = f.natDegree := splits_iff_card_roots.1 hf
  have hl : f.roots.toList.length = f.natDegree := by simp [hcard]
  have hmap : Finset.univ.val.map (fun i : Fin f.natDegree =>
      f.roots.toList.get (Fin.cast hl.symm i)) = f.roots := by
    rw [Fin.univ_val_map, ← List.ofFn_congr hl f.roots.toList.get, List.ofFn_get,
      Multiset.coe_toList]
  obtain ⟨r, hr⟩ : ∃ r : Fin f.natDegree → K, Finset.univ.val.map r = f.roots := ⟨_, hmap⟩
  refine ⟨r, hr, ?_⟩
  conv_lhs => rw [hf.eq_prod_roots]
  rw [← hr, Multiset.map_map]
  rfl

end Polynomial
