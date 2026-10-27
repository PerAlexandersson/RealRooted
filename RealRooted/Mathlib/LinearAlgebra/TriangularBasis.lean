/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel

/-!
# Triangular linear maps under a unitriangular change of generators

This file gives a basis-free formulation of triangularity using the span of
strictly lower generators.  It is convenient when the two generating families
are related by unitriangular expansions but are not bundled as `Basis` values.
-/

@[expose] public section

namespace LinearMap

noncomputable section

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [Preorder ι]

/-- The span of generators whose indices are strictly below `i`. -/
def lowerSpan (b : ι → M) (i : ι) : Submodule R M :=
  Submodule.span R (b '' Set.Iio i)

/-- A linear map acts triangularly on `b` with diagonal `c` when the remainder
at every generator belongs to the span of the strictly lower generators. -/
def IsTriangularOn (f : M →ₗ[R] M) (b : ι → M) (c : ι → R) : Prop :=
  ∀ i, f (b i) - c i • b i ∈ lowerSpan (R := R) b i

theorem lowerSpan_mono (b : ι → M) {i j : ι} (hij : i < j) :
    lowerSpan (R := R) b i ≤ lowerSpan (R := R) b j := by
  apply Submodule.span_mono
  rintro _ ⟨k, hki, rfl⟩
  exact ⟨k, hki.trans hij, rfl⟩

/-- Two mutually unitriangular families have the same strict lower spans. -/
theorem lowerSpan_eq_of_unitriangular {b d : ι → M}
    (hbd : ∀ i, b i - d i ∈ lowerSpan (R := R) d i)
    (hdb : ∀ i, d i - b i ∈ lowerSpan (R := R) b i) (i : ι) :
    lowerSpan (R := R) b i = lowerSpan (R := R) d i := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hji, rfl⟩
    change b j ∈ lowerSpan (R := R) d i
    have hrem := lowerSpan_mono (R := R) d hji (hbd j)
    have hgen : d j ∈ lowerSpan (R := R) d i :=
      Submodule.subset_span ⟨j, hji, rfl⟩
    simpa only [sub_add_cancel] using
      (lowerSpan (R := R) d i).add_mem hrem hgen
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hji, rfl⟩
    change d j ∈ lowerSpan (R := R) b i
    have hrem := lowerSpan_mono (R := R) b hji (hdb j)
    have hgen : b j ∈ lowerSpan (R := R) b i :=
      Submodule.subset_span ⟨j, hji, rfl⟩
    simpa only [sub_add_cancel] using
      (lowerSpan (R := R) b i).add_mem hrem hgen

/-- A triangular linear map preserves every strict lower span. -/
theorem IsTriangularOn.mapsTo_lowerSpan {f : M →ₗ[R] M} {b : ι → M}
    {c : ι → R} (hf : f.IsTriangularOn b c) (i : ι) :
    Set.MapsTo f (lowerSpan (R := R) b i) (lowerSpan (R := R) b i) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, hji, rfl⟩
      have hrem := lowerSpan_mono (R := R) b hji (hf j)
      have hdiag : c j • b j ∈ lowerSpan (R := R) b i := by
        apply Submodule.smul_mem
        exact Submodule.subset_span ⟨j, hji, rfl⟩
      change f (b j) ∈ lowerSpan (R := R) b i
      simpa only [sub_add_cancel] using
        (lowerSpan (R := R) b i).add_mem hrem hdiag
  | zero => simp
  | add x y _ _ hx hy =>
      simpa using (lowerSpan (R := R) b i).add_mem hx hy
  | smul r x _ hx =>
      simpa using (lowerSpan (R := R) b i).smul_mem r hx

/-- Triangularity and its diagonal are unchanged by a unitriangular change of
generators that induces the same strict lower spans. -/
theorem IsTriangularOn.change_generators {f : M →ₗ[R] M}
    {b d : ι → M} {c : ι → R} (hf : f.IsTriangularOn b c)
    (hspan : ∀ i, lowerSpan (R := R) b i = lowerSpan (R := R) d i)
    (hchange : ∀ i, d i - b i ∈ lowerSpan (R := R) b i) :
    f.IsTriangularOn d c := by
  intro i
  have hmap := hf.mapsTo_lowerSpan i (hchange i)
  rw [map_sub] at hmap
  have hsmul : c i • (d i - b i) ∈ lowerSpan (R := R) b i :=
    (lowerSpan (R := R) b i).smul_mem (c i) (hchange i)
  rw [← hspan i]
  have hbase := hf i
  convert (lowerSpan (R := R) b i).add_mem hbase
    ((lowerSpan (R := R) b i).sub_mem hmap hsmul) using 1
  rw [smul_sub]
  abel

/-- A mutually unitriangular change of generators preserves triangularity and
its diagonal. -/
theorem IsTriangularOn.change_generators_of_unitriangular
    {f : M →ₗ[R] M} {b d : ι → M} {c : ι → R}
    (hf : f.IsTriangularOn b c)
    (hbd : ∀ i, b i - d i ∈ lowerSpan (R := R) d i)
    (hdb : ∀ i, d i - b i ∈ lowerSpan (R := R) b i) :
    f.IsTriangularOn d c :=
  hf.change_generators (lowerSpan_eq_of_unitriangular hbd hdb) hdb

end

end LinearMap
