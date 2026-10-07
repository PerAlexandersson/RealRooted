import RealRooted.CauchyInterlacing.Polynomial

/-!
# Weyl interlacing for rank-one perturbations

If `A` is Hermitian and `v` is a vector, the eigenvalues of `A + v v*` interlace those of `A`:
writing both in decreasing order, `λₖ(A) ≤ λₖ(A + v v*) ≤ λₖ₋₁(A)`.  The proof uses the
Courant–Fischer principle `courant_fischer`: adding `v v*` can only raise Rayleigh quotients,
and it does not change them on the hyperplane orthogonal to `v`.

## References

* H. Weyl, *Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller
  Differentialgleichungen*, Math. Ann. 71 (1912).
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, Theorem 4.3.9.
-/

open Matrix Polynomial
open scoped ComplexOrder

namespace RealRooted

variable {𝕜 : Type*} [RCLike 𝕜]

theorem isHermitian_vecMulVec_star {N : ℕ} (v : Fin N → 𝕜) :
    (vecMulVec v (star v)).IsHermitian := by
  rw [IsHermitian, conjTranspose_vecMulVec, star_star]

private theorem dotProduct_add_vecMulVec_mulVec {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (v x : Fin N → 𝕜) :
    star x ⬝ᵥ (A + vecMulVec v (star v)) *ᵥ x =
      star x ⬝ᵥ A *ᵥ x + star (star v ⬝ᵥ x) * (star v ⬝ᵥ x) := by
  rw [add_mulVec, dotProduct_add, vecMulVec_mulVec, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  simp [dotProduct, star_sum, mul_comm]

private theorem re_dotProduct_self_nonneg {N : ℕ} (x : Fin N → 𝕜) :
    0 ≤ RCLike.re (star x ⬝ᵥ x) :=
  (RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg x)).1

/-- Adding `v v*` does not decrease Rayleigh quotients. -/
theorem rayleigh_le_rayleigh_add_vecMulVec {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (v x : Fin N → 𝕜) : rayleigh A x ≤ rayleigh (A + vecMulVec v (star v)) x := by
  rw [rayleigh, rayleigh, dotProduct_add_vecMulVec_mulVec, map_add]
  refine div_le_div_of_nonneg_right ?_ (re_dotProduct_self_nonneg x)
  simp only [RCLike.star_def, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, neg_mul,
    sub_neg_eq_add, le_add_iff_nonneg_right]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- On the hyperplane orthogonal to `v`, adding `v v*` does not change Rayleigh quotients. -/
theorem rayleigh_add_vecMulVec_of_dotProduct_eq_zero {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) {v x : Fin N → 𝕜} (hx : star v ⬝ᵥ x = 0) :
    rayleigh (A + vecMulVec v (star v)) x = rayleigh A x := by
  rw [rayleigh, rayleigh, dotProduct_add_vecMulVec_mulVec, hx, mul_zero, add_zero]

/-- **Weyl monotonicity**: the eigenvalues of `A + v v*` dominate those of `A`. -/
theorem sortedEigenvalues_le_add_vecMulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : A.IsHermitian) (v : Fin N → 𝕜) (hB : (A + vecMulVec v (star v)).IsHermitian)
    (k : Fin N) : sortedEigenvalues A hA k ≤ sortedEigenvalues _ hB k := by
  obtain ⟨W, hW, hWA⟩ := (courant_fischer 𝕜 A hA k).1
  obtain ⟨x, hxW, hx0, hxB⟩ := (courant_fischer 𝕜 _ hB k).2 W hW
  exact (hWA x hxW hx0).trans ((rayleigh_le_rayleigh_add_vecMulVec A v x).trans hxB)

/-- **Weyl interlacing**: the eigenvalues of `A + v v*` are at most the previous eigenvalues
of `A`. -/
theorem sortedEigenvalues_add_vecMulVec_succ_le {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜} (hA : A.IsHermitian) (v : Fin (n + 1) → 𝕜)
    (hB : (A + vecMulVec v (star v)).IsHermitian) (k : Fin n) :
    sortedEigenvalues _ hB k.succ ≤ sortedEigenvalues A hA k.castSucc := by
  obtain ⟨W, hW, hWB⟩ := (courant_fischer 𝕜 _ hB k.succ).1
  let f : (Fin (n + 1) → 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun x => star v ⬝ᵥ x
      map_add' := dotProduct_add _
      map_smul' := fun c x => dotProduct_smul c _ x }
  have hker : n ≤ Module.finrank 𝕜 (LinearMap.ker f) := by
    have := LinearMap.finrank_range_add_finrank_ker f
    have := (LinearMap.range f).finrank_le
    simp_all
    lia
  have hdim : (k : ℕ) + 1 ≤ Module.finrank 𝕜 ↥(W ⊓ LinearMap.ker f) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
    have := (W ⊔ LinearMap.ker f).finrank_le
    simp_all
    lia
  obtain ⟨T, hTle, hT⟩ := exists_submodule_le_finrank_eq _ _ hdim
  obtain ⟨x, hxT, hx0, hxA⟩ := (courant_fischer 𝕜 A hA k.castSucc).2 T (by simpa using hT)
  have hx := hTle hxT
  calc sortedEigenvalues _ hB k.succ ≤ rayleigh (A + vecMulVec v (star v)) x := hWB x hx.1 hx0
    _ = rayleigh A x := rayleigh_add_vecMulVec_of_dotProduct_eq_zero A hx.2
    _ ≤ _ := hxA

/-- **Weyl interlacing** in characteristic-polynomial form: for a real symmetric `A` and a
vector `v`, the characteristic polynomials of `A` and `A + v vᵀ` interlace, with the roots of
`A + v vᵀ` on the right. -/
theorem charpoly_strictInterl_add_vecMulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (v : Fin N → ℝ) :
    StrictInterl A.charpoly (A + vecMulVec v v).charpoly := by
  have hv : vecMulVec v v = vecMulVec v (star v) := by rw [star_trivial]
  have hB : (A + vecMulVec v (star v)).IsHermitian := hA.add (isHermitian_vecMulVec_star v)
  rw [hv]
  set B := A + vecMulVec v (star v)
  refine ⟨⟨A.charpoly_monic.ne_zero, hA.splits_charpoly⟩,
    ⟨B.charpoly_monic.ne_zero, hB.splits_charpoly⟩,
    List.ofFn fun k : Fin N => sortedEigenvalues A hA k.rev,
    List.ofFn fun k : Fin N => sortedEigenvalues B hB k.rev,
    pairwise_ofFn_sortedEigenvalues_rev A hA, pairwise_ofFn_sortedEigenvalues_rev B hB,
    coe_ofFn_sortedEigenvalues_rev A hA, coe_ofFn_sortedEigenvalues_rev B hB,
    Or.inr ⟨by simp, listAlternates_of_interleaves_of_length (by simp)
      (List.interleaves_ofFn.2 ⟨fun k => sortedEigenvalues_le_add_vecMulVec hA v hB _,
        fun i hi => ?_⟩)⟩⟩
  obtain _ | n := N
  · lia
  have := sortedEigenvalues_add_vecMulVec_succ_le hA v hB ⟨n - 1 - i, by lia⟩
  convert this using 2 <;> ext <;> simp <;> lia

end RealRooted
