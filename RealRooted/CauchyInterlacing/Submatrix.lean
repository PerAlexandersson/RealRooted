import RealRooted.CauchyInterlacing

/-!
# Eigenvalue bounds for arbitrary principal submatrices

This file extends the one-coordinate Cauchy interlacing API to the one-sided
bound needed for principal submatrices selected by an arbitrary injective map.
The proof uses the already formalized Courant--Fischer theorem directly.
-/

open Matrix

namespace RealRooted

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Extend a vector by zero along an injective coordinate selection. -/
noncomputable def embedSubmatrix {d N : ℕ} (f : Fin d → Fin N)
    (x : Fin d → 𝕜) : Fin N → 𝕜 :=
  Function.extend f x 0

@[simp]
theorem embedSubmatrix_apply {d N : ℕ} (f : Fin d → Fin N)
    (hf : Function.Injective f) (x : Fin d → 𝕜) (i : Fin d) :
    embedSubmatrix f x (f i) = x i := by
  exact hf.extend_apply x 0 i

private theorem sum_embedSubmatrix {d N : ℕ} (f : Fin d → Fin N)
    (hf : Function.Injective f) (g : Fin N → 𝕜)
    (hg : ∀ j, j ∉ Finset.univ.image f → g j = 0) :
    ∑ j, g j = ∑ i, g (f i) := by
  rw [← Finset.sum_image hf.injOn]
  exact (Finset.sum_subset (Finset.image_subset_iff.mpr fun _ _ => Finset.mem_univ _)
    (fun j _ hj => hg j (by simpa using hj))).symm

/-- The quadratic form of a principal submatrix is the quadratic form of the
full matrix on the corresponding zero-extended vector. -/
theorem submatrix_dotProduct_mulVec_embedSubmatrix {d N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (f : Fin d → Fin N)
    (hf : Function.Injective f) (x : Fin d → 𝕜) :
    star x ⬝ᵥ (A.submatrix f f).mulVec x =
      star (embedSubmatrix f x) ⬝ᵥ A.mulVec (embedSubmatrix f x) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.submatrix_apply]
  rw [sum_embedSubmatrix f hf]
  · apply Finset.sum_congr rfl
    intro i _
    rw [embedSubmatrix_apply f hf]
    congr 1
    rw [sum_embedSubmatrix f hf]
    · apply Finset.sum_congr rfl
      intro j _
      rw [embedSubmatrix_apply f hf]
    · intro j hj
      have hnot : ¬∃ i, f i = j := by
        simpa [Finset.mem_image] using hj
      have hz : embedSubmatrix f x j = 0 := by
        simpa [embedSubmatrix] using
          (Function.extend_apply' x (0 : Fin N → 𝕜) j hnot)
      simp [hz]
  · intro j hj
    have hnot : ¬∃ i, f i = j := by
      simpa [Finset.mem_image] using hj
    have hz : embedSubmatrix f x j = 0 := by
      simpa [embedSubmatrix] using
        (Function.extend_apply' x (0 : Fin N → 𝕜) j hnot)
    simp [hz]

/-- Zero extension preserves the Hermitian squared norm. -/
theorem embedSubmatrix_dotProduct_self {d N : ℕ} (f : Fin d → Fin N)
    (hf : Function.Injective f) (x : Fin d → 𝕜) :
    star (embedSubmatrix f x) ⬝ᵥ embedSubmatrix f x = star x ⬝ᵥ x := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_embedSubmatrix f hf]
  · apply Finset.sum_congr rfl
    intro i _
    rw [embedSubmatrix_apply f hf]
  · intro j hj
    have hnot : ¬∃ i, f i = j := by
      simpa [Finset.mem_image] using hj
    have hz : embedSubmatrix f x j = 0 := by
      simpa [embedSubmatrix] using
        (Function.extend_apply' x (0 : Fin N → 𝕜) j hnot)
    simp [hz]

/-- The Rayleigh quotient of a principal submatrix agrees with that of the
full matrix on a zero-extended vector. -/
theorem rayleigh_submatrix_embedSubmatrix {d N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (f : Fin d → Fin N)
    (hf : Function.Injective f) (x : Fin d → 𝕜) :
    rayleigh (A.submatrix f f) x = rayleigh A (embedSubmatrix f x) := by
  rw [rayleigh, rayleigh, submatrix_dotProduct_mulVec_embedSubmatrix A f hf,
    embedSubmatrix_dotProduct_self f hf]

/-- Zero extension along an injective coordinate selection as a linear map. -/
noncomputable def embedSubmatrixₗ {d N : ℕ} (f : Fin d → Fin N)
    (hf : Function.Injective f) :
    (Fin d → 𝕜) →ₗ[𝕜] (Fin N → 𝕜) where
  toFun := embedSubmatrix f
  map_add' x y := by
    classical
    funext j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      simp [embedSubmatrix, hf.extend_apply]
    · rw [show embedSubmatrix f (x + y) j = 0 by
        simpa [embedSubmatrix] using
          (Function.extend_apply' (x + y) (0 : Fin N → 𝕜) j hj)]
      simp only [Pi.add_apply]
      rw [show embedSubmatrix f x j = 0 by
        simpa [embedSubmatrix] using
          (Function.extend_apply' x (0 : Fin N → 𝕜) j hj)]
      rw [show embedSubmatrix f y j = 0 by
        simpa [embedSubmatrix] using
          (Function.extend_apply' y (0 : Fin N → 𝕜) j hj)]
      simp
  map_smul' c x := by
    classical
    funext j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      simp [embedSubmatrix, hf.extend_apply]
    · rw [show embedSubmatrix f (c • x) j = 0 by
        simpa [embedSubmatrix] using
          (Function.extend_apply' (c • x) (0 : Fin N → 𝕜) j hj)]
      simp only [Pi.smul_apply, RingHom.id_apply]
      rw [show embedSubmatrix f x j = 0 by
        simpa [embedSubmatrix] using
          (Function.extend_apply' x (0 : Fin N → 𝕜) j hj)]
      simp

@[simp]
theorem embedSubmatrixₗ_apply {d N : ℕ} (f : Fin d → Fin N)
    (hf : Function.Injective f) (x : Fin d → 𝕜) :
    embedSubmatrixₗ f hf x = embedSubmatrix f x :=
  rfl

theorem embedSubmatrixₗ_injective {d N : ℕ} (f : Fin d → Fin N)
    (hf : Function.Injective f) :
    Function.Injective (embedSubmatrixₗ (𝕜 := 𝕜) f hf) := fun x y hxy => by
  funext i
  have := congr_fun hxy (f i)
  simpa [embedSubmatrix_apply f hf] using this

/-- An arbitrary principal submatrix cannot have its `k`-th decreasing
eigenvalue above the `k`-th decreasing eigenvalue of the full matrix. -/
theorem sortedEigenvalues_submatrix_le {d N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian)
    (f : Fin d → Fin N) (hf : Function.Injective f) (k : Fin d) :
    sortedEigenvalues (A.submatrix f f) (hA.submatrix f) k ≤
      sortedEigenvalues A hA
        (Fin.castLE (by simpa using Fintype.card_le_of_injective f hf) k) := by
  have hdN : d ≤ N := by
    simpa using Fintype.card_le_of_injective f hf
  let E := embedSubmatrixₗ (𝕜 := 𝕜) f hf
  obtain ⟨W, hWcard, hW⟩ :=
    (courant_fischer 𝕜 (A.submatrix f f) (hA.submatrix f) k).1
  have hE : Function.Injective E := embedSubmatrixₗ_injective f hf
  have hcard : Module.finrank 𝕜 (W.map E) = (k : ℕ) + 1 := by
    rw [← hWcard]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective E hE W).symm
  obtain ⟨z, hz, hz0, hzR⟩ :=
    (courant_fischer 𝕜 A hA (Fin.castLE hdN k)).2
      (W.map E) (by simpa using hcard)
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
  refine (hW x hx ?_).trans ?_
  · intro hx0
    subst x
    exact hz0 (map_zero E)
  · simpa [E, rayleigh_submatrix_embedSubmatrix A f hf] using hzR

end RealRooted
