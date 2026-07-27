import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Cauchy interlacing theorem: statement and supporting API

This module sets up the **Cauchy interlacing theorem** for Hermitian matrices,
together with the reusable, unconditional API surrounding it.

Given a Hermitian matrix `A` of size `n + 1` and a deleted index `i`, the
principal submatrix `B = A.submatrix i.succAbove i.succAbove` of size `n` has
eigenvalues that interlace those of `A`. Writing the eigenvalues in decreasing
order as `λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ` for `A` and `μ₀ ≥ ⋯ ≥ μₙ₋₁` for `B`,
interlacing means `λ_{k+1} ≤ μ_k ≤ λ_k` for every `k`.

## Main definitions

* `RealRooted.sortedEigenvalues` — the eigenvalues of a Hermitian `Fin N`-matrix
  reindexed by `Fin N` (rather than by `Fin (Fintype.card (Fin N))`), still in
  decreasing order.
* `RealRooted.Interlace` — the interlacing relation between a length-`n` and a
  length-`n+1` decreasing family of reals.
* `RealRooted.CauchyInterlacingStatement` — the interlacing statement for the
  one-index deletion `i.succAbove`.

## Main results

* `RealRooted.sortedEigenvalues_antitone` — the sorted eigenvalues are
  decreasing.
* `RealRooted.sortedEigenvalues_charpoly_roots` — the sorted eigenvalues are
  exactly the roots of the characteristic polynomial, with multiplicity.
* `RealRooted.Interlace.le`, `RealRooted.Interlace.ge` — the two-sided
  classical restatement.
* `RealRooted.cauchy_interlacing` — the Cauchy interlacing theorem itself,
  proved via the Courant-Fischer variational principle formalized below.

## References

* S. Fisk, *A very short proof of Cauchy's interlace theorem for eigenvalues of
  Hermitian matrices*.
-/

open Matrix Polynomial

namespace RealRooted

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The eigenvalues of a Hermitian `Fin N`-matrix, reindexed by `Fin N`
(rather than by `Fin (Fintype.card (Fin N))`) and listed in decreasing order.

This is just `Matrix.IsHermitian.eigenvalues₀` transported along the canonical
identification `Fintype.card (Fin N) = N`, which removes the `Fintype.card`
bookkeeping from downstream statements. -/
noncomputable def sortedEigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) : Fin N → ℝ :=
  fun k => hA.eigenvalues₀ (finCongr (Fintype.card_fin N).symm k)

/-- The sorted eigenvalues are listed in decreasing order. -/
theorem sortedEigenvalues_antitone {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) :
    Antitone (sortedEigenvalues A hA) :=
  fun _ _ hab => hA.eigenvalues₀_antitone (by simp_all)

/-- The sorted eigenvalues of a Hermitian matrix are exactly the roots of its
characteristic polynomial, counted with multiplicity. -/
theorem sortedEigenvalues_charpoly_roots {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) :
    A.charpoly.roots =
      (Finset.univ : Finset (Fin N)).val.map
        (fun k => (RCLike.ofReal (sortedEigenvalues A hA k) : 𝕜)) := by
  simpa [sortedEigenvalues] using hA.roots_charpoly_eq_eigenvalues₀

/-- The coordinate embedding `Fin n → Fin (n+1)` skipping index `i`, extended
by zero: a vector on the `n` retained coordinates is placed into the big space,
with `0` in the deleted slot `i`. -/
noncomputable def embedCompl {n : ℕ} (i : Fin (n + 1)) (x : Fin n → 𝕜) :
    Fin (n + 1) → 𝕜 :=
  Function.extend i.succAbove x 0

@[simp] theorem embedCompl_succAbove {n : ℕ} (i : Fin (n + 1)) (x : Fin n → 𝕜)
    (a : Fin n) : embedCompl i x (i.succAbove a) = x a := by
  rw [embedCompl, i.succAbove_right_injective.extend_apply]

@[simp] theorem embedCompl_self {n : ℕ} (i : Fin (n + 1)) (x : Fin n → 𝕜) :
    embedCompl i x i = 0 := by
  rw [embedCompl, Function.extend_apply'] <;> simp

/-- **Rayleigh restriction identity.** The quadratic form of the principal
submatrix `A.submatrix i.succAbove i.succAbove` at `x` coincides with the form of
the full matrix `A` at the zero-extended vector `embedCompl i x`. -/
theorem submatrix_dotProduct_mulVec {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1))
    (x : Fin n → 𝕜) :
    star x ⬝ᵥ (A.submatrix i.succAbove i.succAbove).mulVec x =
      star (embedCompl i x) ⬝ᵥ A.mulVec (embedCompl i x) := by
  have h_split : ∀ f : Fin (n + 1) → 𝕜,
      ∑ j, f j = f i + ∑ a, f (i.succAbove a) := fun f => Fin.sum_univ_succAbove f i
  simp only [dotProduct, Matrix.mulVec, dotProduct, Pi.star_apply, Matrix.submatrix_apply]
  simp [embedCompl, h_split, Function.extend]

/-- **Denominator restriction identity.** The Hermitian squared norm of the
zero-extended vector `embedCompl i x` equals that of `x`: the deleted slot only
adds a zero coordinate. -/
theorem embedCompl_dotProduct_self {n : ℕ} (i : Fin (n + 1)) (x : Fin n → 𝕜) :
    star (embedCompl i x) ⬝ᵥ embedCompl i x = star x ⬝ᵥ x := by
  have h_split : ∀ f : Fin (n + 1) → 𝕜,
      ∑ j, f j = f i + ∑ a, f (i.succAbove a) := fun f => Fin.sum_univ_succAbove f i
  simp only [dotProduct, Pi.star_apply]
  simp [embedCompl, h_split, Function.extend]

/-- The Rayleigh quotient of a matrix at a vector, using the standard Hermitian
dot product `star x ⬝ᵥ A.mulVec x` as numerator and `star x ⬝ᵥ x` as
denominator, both taken as real parts. -/
noncomputable def rayleigh {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (x : Fin N → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ A.mulVec x) / RCLike.re (star x ⬝ᵥ x)

/-- The Rayleigh quotient of the principal submatrix at `x` equals the Rayleigh
quotient of the full matrix at the zero-extended vector `embedCompl i x`. -/
theorem rayleigh_submatrix_embedCompl {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1))
    (x : Fin n → 𝕜) :
    rayleigh (A.submatrix i.succAbove i.succAbove) x =
      rayleigh A (embedCompl i x) := by
  rw [rayleigh, rayleigh, submatrix_dotProduct_mulVec, embedCompl_dotProduct_self]

/-- The zero-extension embedding `embedCompl i` packaged as a `𝕜`-linear map
`(Fin n → 𝕜) →ₗ[𝕜] (Fin (n+1) → 𝕜)`. -/
noncomputable def embedComplₗ {n : ℕ} (i : Fin (n + 1)) :
    (Fin n → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜) where
  toFun := embedCompl i
  map_add' x y := by
    funext j
    refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp
  map_smul' c x := by
    funext j
    refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp

@[simp] theorem embedComplₗ_apply {n : ℕ} (i : Fin (n + 1)) (x : Fin n → 𝕜) :
    embedComplₗ i x = embedCompl i x := rfl

/-- The linear zero-extension embedding is injective. -/
theorem embedComplₗ_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (embedComplₗ (𝕜 := 𝕜) i) := fun x y hxy => by
  ext a
  have := congr_fun hxy (i.succAbove a)
  simpa using this

/-- Pushing a subspace forward along `embedComplₗ` preserves its dimension. -/
theorem finrank_map_embedComplₗ {n : ℕ} (i : Fin (n + 1))
    (W : Submodule 𝕜 (Fin n → 𝕜)) :
    Module.finrank 𝕜 (W.map (embedComplₗ i)) = Module.finrank 𝕜 W :=
  LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (embedComplₗ_injective i) _).symm

/-- The range of `embedComplₗ i` is a hyperplane: it has dimension `n` inside
the `(n+1)`-dimensional ambient space. -/
theorem finrank_range_embedComplₗ {n : ℕ} (i : Fin (n + 1)) :
    Module.finrank 𝕜 (LinearMap.range (embedComplₗ (𝕜 := 𝕜) i)) = n := by
  rw [LinearMap.range_eq_map]
  simpa using finrank_map_embedComplₗ i (⊤ : Submodule 𝕜 (Fin n → 𝕜))

/-- Any finite-dimensional subspace contains a subspace of every dimension up to
its own. -/
theorem exists_submodule_le_finrank_eq {N : ℕ}
    (S : Submodule 𝕜 (Fin N → 𝕜)) (m : ℕ) (hm : m ≤ Module.finrank 𝕜 S) :
    ∃ T : Submodule 𝕜 (Fin N → 𝕜), T ≤ S ∧ Module.finrank 𝕜 T = m := by
  by_contra h_contra
  obtain ⟨T, hT⟩ : ∃ T : Submodule 𝕜 S, Module.finrank 𝕜 T = m := by
    have := Module.finBasis 𝕜 S
    refine
      ⟨Submodule.span 𝕜 (Set.range fun i : Fin m => this (Fin.castLE hm i)), ?_⟩
    rw [@finrank_span_eq_card]
    · simp
    · exact this.linearIndependent.comp _ (Fin.castLE_injective _)
  refine h_contra ⟨Submodule.map (Submodule.subtype S) T, Submodule.map_subtype_le _ _, ?_⟩
  simp_all

/-- Interlacing relation: a decreasing length-`n` family `μ` interlaces a
decreasing length-`n+1` family `lam` when `lam_{k+1} ≤ μ_k ≤ lam_k` for every
`k`. -/
def Interlace {n : ℕ} (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin n, lam k.succ ≤ μ k ∧ μ k ≤ lam k.castSucc

/-- Upper interlacing inequality `μ_k ≤ lam_k`. -/
theorem Interlace.le {n : ℕ} {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (h : Interlace μ lam) (k : Fin n) : μ k ≤ lam k.castSucc :=
  (h k).2

/-- Lower interlacing inequality `lam_{k+1} ≤ μ_k`. -/
theorem Interlace.ge {n : ℕ} {μ : Fin n → ℝ} {lam : Fin (n + 1) → ℝ}
    (h : Interlace μ lam) (k : Fin n) : lam k.succ ≤ μ k :=
  (h k).1

/-- **Cauchy interlacing statement.** For every Hermitian matrix `A` of size
`n + 1` and every deleted index `i`, the eigenvalues of the principal submatrix
obtained by deleting row and column `i` interlace the eigenvalues of `A`. -/
def CauchyInterlacingStatement (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (hA : A.IsHermitian)
    (i : Fin (n + 1)),
    Interlace
      (sortedEigenvalues (A.submatrix i.succAbove i.succAbove)
        (hA.submatrix i.succAbove))
      (sortedEigenvalues A hA)

/-- **Courant-Fischer min-max characterization** (witnessed form). For a
Hermitian matrix `A` and index `k`, the `k`-th sorted eigenvalue `λ_k` is the
max-min of the Rayleigh quotient over `(k+1)`-dimensional subspaces. -/
def CourantFischerStatement (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) (k : Fin N),
    (∃ W : Submodule 𝕜 (Fin N → 𝕜), Module.finrank 𝕜 W = (k : ℕ) + 1 ∧
        ∀ x ∈ W, x ≠ 0 → sortedEigenvalues A hA k ≤ rayleigh A x) ∧
    (∀ W : Submodule 𝕜 (Fin N → 𝕜), Module.finrank 𝕜 W = (k : ℕ) + 1 →
        ∃ x ∈ W, x ≠ 0 ∧ rayleigh A x ≤ sortedEigenvalues A hA k)

/-- Assuming the witnessed min-max characterization of sorted eigenvalues, the
Cauchy interlacing theorem follows from the linear-algebra API above. -/
theorem cauchyInterlacing_of_courantFischer
    (hCF : CourantFischerStatement 𝕜) : CauchyInterlacingStatement 𝕜 := by
  intro n A hA i k
  constructor
  · obtain ⟨W_A, hW_A₁, hW_A₂⟩ := (hCF A hA k.succ).1
    generalize_proofs at *
    obtain ⟨T, hT₁, hT₂⟩ :=
      exists_submodule_le_finrank_eq (W_A ⊓ LinearMap.range (embedComplₗ i)) (k + 1)
        (by
          have := Submodule.finrank_sup_add_finrank_inf_eq W_A
            (LinearMap.range (embedComplₗ i))
          simp_all [finrank_range_embedComplₗ]
          linarith [show Module.finrank 𝕜 (↥(W_A ⊔ (embedComplₗ i).range)) ≤ n + 1 from
            le_trans (Submodule.finrank_le _) (by simp)])
    generalize_proofs at *
    obtain ⟨y, hy₁, hy₂⟩ :=
      hCF (A.submatrix i.succAbove i.succAbove) ‹_› k |>.2
        (Submodule.comap (embedComplₗ i) T)
        (by
          have hT₃ : Module.finrank 𝕜
              (Submodule.map (embedComplₗ i) (Submodule.comap (embedComplₗ i) T)) =
                Module.finrank 𝕜 T := by
            rw [Submodule.map_comap_eq_self]
            simp_all
          generalize_proofs at *
          rw [← hT₂, ← hT₃, finrank_map_embedComplₗ])
    generalize_proofs at *
    have := hW_A₂ (embedCompl i y) ?_ ?_
    · exact this.trans (by simpa only [rayleigh_submatrix_embedCompl] using hy₂.2)
    · exact (hT₁ hy₁).1
    · exact fun h => hy₂.1 (by ext a; simpa using congr_fun h (i.succAbove a))
  · obtain ⟨W, hW₁, hW₂⟩ :=
      hCF (A.submatrix i.succAbove i.succAbove) (hA.submatrix i.succAbove) k |>.1
    generalize_proofs at *
    obtain ⟨x, hx₁, hx₂, hx₃⟩ :=
      hCF A hA (Fin.castSucc k) |>.2 (Submodule.map (embedComplₗ (𝕜 := 𝕜) i) W)
        (by
          convert finrank_map_embedComplₗ i W using 1
          simp_all)
    generalize_proofs at *
    obtain ⟨y, hy₁, rfl⟩ := Submodule.mem_map.mp hx₁
    generalize_proofs at *
    refine (hW₂ y hy₁ ?_).trans ?_
    · grind
    · simpa only [embedComplₗ_apply, rayleigh_submatrix_embedCompl] using hx₃

/-!
### The Courant-Fischer min-max principle from an orthonormal eigenbasis

The remaining classical input is the min-max characterization of the sorted
eigenvalues.  We prove it from the spectral theorem via a reusable statement
`courantFischer_of_eigenbasis`, which takes an arbitrary orthonormal basis of
eigenvectors (with real, antitone eigenvalues) and produces the two-sided
variational bounds.  It is then specialised to `Matrix.IsHermitian.eigenvectorBasis`
to discharge `CourantFischerStatement`.
-/

private theorem star_ofLp_dotProduct_self {N : ℕ} (x : EuclideanSpace 𝕜 (Fin N)) :
    star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x = (inner 𝕜 x x : 𝕜) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/--
Expansion of the Rayleigh **denominator** in an orthonormal basis: the
Hermitian square norm of `x` is the sum of the squared moduli of its Fourier
coefficients `⟪b i, x⟫`.
-/
theorem denom_eq_sum_sq {N : ℕ}
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (x : EuclideanSpace 𝕜 (Fin N)) :
    RCLike.re (star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x)
      = ∑ i, ‖(inner 𝕜 (b i) x : 𝕜)‖ ^ 2 := by
  rw [star_ofLp_dotProduct_self x, inner_self_eq_norm_sq, ← b.sum_sq_norm_inner_right x]

/--
Expansion of the Rayleigh **numerator** in an orthonormal eigenbasis: if
`A *ᵥ (b j) = μ j • (b j)` for each `j`, then the Hermitian form of `A` at `x`
is the `μ`-weighted sum of the squared moduli of the Fourier coefficients.
-/
theorem num_eq_sum_sq {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (μ : Fin N → ℝ)
    (hb : ∀ j, A *ᵥ WithLp.ofLp (b j) = μ j • WithLp.ofLp (b j))
    (x : EuclideanSpace 𝕜 (Fin N)) :
    RCLike.re (star (WithLp.ofLp x) ⬝ᵥ A.mulVec (WithLp.ofLp x))
      = ∑ i, μ i * ‖(inner 𝕜 (b i) x : 𝕜)‖ ^ 2 := by
  have hAx : A.mulVec (WithLp.ofLp x)
      = WithLp.ofLp (∑ i, ((μ i : 𝕜) * inner 𝕜 (b i) x) • b i) := by
    have hx : WithLp.ofLp x
        = ∑ i, (inner 𝕜 (b i) x : 𝕜) • WithLp.ofLp (b i) := by
      conv_lhs => rw [← b.sum_repr' x]
      simp
    rw [hx, Matrix.mulVec_sum, WithLp.ofLp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.mulVec_smul, hb i, WithLp.ofLp_smul,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul, mul_comm]
  have hnum : star (WithLp.ofLp x) ⬝ᵥ A.mulVec (WithLp.ofLp x)
      = inner 𝕜 x (∑ i, ((μ i : 𝕜) * inner 𝕜 (b i) x) • b i) := by
    rw [hAx, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hnum, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hconj : (inner 𝕜 x (b i) : 𝕜) = starRingEnd 𝕜 (inner 𝕜 (b i) x) :=
    (inner_conj_symm x (b i)).symm
  rw [inner_smul_right, hconj, mul_assoc, RCLike.mul_conj,
    ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/--
The Rayleigh denominator is strictly positive for a nonzero vector.
-/
theorem denom_pos {N : ℕ} (x : EuclideanSpace 𝕜 (Fin N)) (hx : x ≠ 0) :
    0 < RCLike.re (star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x) := by
  simpa [star_ofLp_dotProduct_self x, inner_self_eq_norm_sq] using
    pow_pos (norm_pos_iff.mpr hx) 2

/--
Fourier coefficients supported on `Set.range g`: if `x` lies in the span of
`b (g j)`, then `⟪b i, x⟫ = 0` whenever `i` is not of the form `g j`.
-/
theorem inner_eq_zero_of_mem_span_range {N m : ℕ}
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (g : Fin m → Fin N) (x : EuclideanSpace 𝕜 (Fin N))
    (hx : x ∈ Submodule.span 𝕜
      (Set.range (fun j => (b (g j) : EuclideanSpace 𝕜 (Fin N)))))
    (i : Fin N) (hi : i ∉ Set.range g) :
    (inner 𝕜 (b i) x : 𝕜) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact b.orthonormal.2 fun e ↦ hi ⟨j, e.symm⟩
  | zero => simp
  | add y z _ _ ihy ihz => rw [inner_add_right, ihy, ihz, add_zero]
  | smul a y _ ihy => rw [inner_smul_right, ihy, mul_zero]

/--
The span of an injective reindexing `b ∘ g` of the eigenbasis has dimension
equal to the number of indices.
-/
theorem finrank_span_range_eigen {N m : ℕ}
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (g : Fin m → Fin N) (hg : Function.Injective g) :
    Module.finrank 𝕜 (Submodule.span 𝕜
      (Set.range (fun j ↦ (b (g j) : EuclideanSpace 𝕜 (Fin N))))) = m := by
  rw [finrank_span_eq_card]
  · simp
  · exact b.toBasis.linearIndependent.comp g hg

/--
Lower Rayleigh bound from the support of the Fourier coefficients: if every
index `i` contributing to `x` satisfies `t ≤ μ i`, then `t ≤` Rayleigh quotient.
-/
theorem rayleigh_ge_of_support {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (μ : Fin N → ℝ)
    (hb : ∀ j, A *ᵥ WithLp.ofLp (b j) = μ j • WithLp.ofLp (b j))
    (x : EuclideanSpace 𝕜 (Fin N)) (hx : x ≠ 0) (t : ℝ)
    (h : ∀ i, (inner 𝕜 (b i) x : 𝕜) ≠ 0 → t ≤ μ i) :
    t ≤ rayleigh A (WithLp.ofLp x) := by
  rw [rayleigh, le_div_iff₀ (denom_pos x hx), num_eq_sum_sq A b μ hb x,
    denom_eq_sum_sq b x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases eq_or_ne (inner 𝕜 (b i) x : 𝕜) 0 with hi | hi
  · simp [hi]
  · simp_all

/--
Upper Rayleigh bound from the support of the Fourier coefficients: if every
index `i` contributing to `x` satisfies `μ i ≤ t`, then Rayleigh quotient `≤ t`.
-/
theorem rayleigh_le_of_support {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (μ : Fin N → ℝ)
    (hb : ∀ j, A *ᵥ WithLp.ofLp (b j) = μ j • WithLp.ofLp (b j))
    (x : EuclideanSpace 𝕜 (Fin N)) (hx : x ≠ 0) (t : ℝ)
    (h : ∀ i, (inner 𝕜 (b i) x : 𝕜) ≠ 0 → μ i ≤ t) :
    rayleigh A (WithLp.ofLp x) ≤ t := by
  rw [rayleigh, div_le_iff₀ (denom_pos x hx), num_eq_sum_sq A b μ hb x,
    denom_eq_sum_sq b x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases eq_or_ne (inner 𝕜 (b i) x : 𝕜) 0 with hi | hi
  · simp [hi]
  · simp_all

/--
**Courant-Fischer min-max principle from an orthonormal eigenbasis.**

Given a Hermitian action encoded by an orthonormal eigenbasis `b` with real
eigenvalues `μ` listed in decreasing (antitone) order, the `k`-th eigenvalue
`μ k` is the max-min of the Rayleigh quotient over `(k+1)`-dimensional
subspaces.  This is the reusable spectral input; the matrix Courant-Fischer
statement follows by specialising to `Matrix.IsHermitian.eigenvectorBasis`.
-/
theorem courantFischer_of_eigenbasis {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)))
    (μ : Fin N → ℝ) (hμ : Antitone μ)
    (hb : ∀ j, A *ᵥ WithLp.ofLp (b j) = μ j • WithLp.ofLp (b j)) (k : Fin N) :
    (∃ W : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)),
        Module.finrank 𝕜 W = (k : ℕ) + 1 ∧
        ∀ x ∈ W, x ≠ 0 → μ k ≤ rayleigh A (WithLp.ofLp x)) ∧
    (∀ W : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)),
        Module.finrank 𝕜 W = (k : ℕ) + 1 →
        ∃ x ∈ W, x ≠ 0 ∧ rayleigh A (WithLp.ofLp x) ≤ μ k) := by
  refine ⟨?_, ?_⟩
  · have hk : (k : ℕ) + 1 ≤ N := k.isLt
    refine ⟨Submodule.span 𝕜 (Set.range fun j : Fin ((k : ℕ) + 1) =>
        (b (Fin.castLE hk j) : EuclideanSpace 𝕜 (Fin N))), ?_, ?_⟩
    · exact finrank_span_range_eigen b (Fin.castLE hk) (Fin.castLE_injective hk)
    · intro x hx hx0
      refine rayleigh_ge_of_support A b μ hb x hx0 (μ k) fun i hi => ?_
      have hmem : i ∈ Set.range (Fin.castLE hk) := by
        by_contra hcon
        exact hi (inner_eq_zero_of_mem_span_range b (Fin.castLE hk) x hx i hcon)
      obtain ⟨j, rfl⟩ := hmem
      refine hμ ?_
      grind
  · intro W hW
    have hkN : (k : ℕ) < N := k.isLt
    set g : Fin (N - (k : ℕ)) → Fin N :=
      fun j ↦ ⟨(k : ℕ) + (j : ℕ), by grind⟩ with hg
    have hgval : ∀ j, ((g j : Fin N) : ℕ) = (k : ℕ) + (j : ℕ) := fun _ ↦ rfl
    have hg_inj : Function.Injective g :=
      fun _ _ hac ↦ Fin.ext <| by
        simpa [hgval, Nat.add_left_cancel_iff] using congrArg Fin.val hac
    set U : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin N)) :=
      Submodule.span 𝕜 (Set.range fun j => (b (g j) : EuclideanSpace 𝕜 (Fin N)))
      with hU
    have hU_dim : Module.finrank 𝕜 U = N - (k : ℕ) :=
      finrank_span_range_eigen b g hg_inj
    have hU_zero : ∀ x ∈ U, ∀ i : Fin N, (i : ℕ) < (k : ℕ) →
        (inner 𝕜 (b i) x : 𝕜) = 0 := by
      intro x hx i hi
      refine inner_eq_zero_of_mem_span_range b g x hx i ?_
      rintro ⟨j, rfl⟩
      rw [hgval] at hi
      lia
    obtain ⟨x, hxW, hxU, hx0⟩ : ∃ x ∈ W, x ∈ U ∧ x ≠ 0 := by
      have hpos : 0 < Module.finrank 𝕜 (W ⊓ U : Submodule 𝕜 _) := by
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq W U
        have hsum : Module.finrank 𝕜 (W ⊔ U : Submodule 𝕜 _) ≤ N :=
          le_trans (Submodule.finrank_le _) (le_of_eq finrank_euclideanSpace_fin)
        rw [hW, hU_dim] at hadd
        have hk_le : (k : ℕ) ≤ N := Nat.le_of_lt k.isLt
        have hk_sum : (k : ℕ) + 1 + (N - (k : ℕ)) = N + 1 := by
          rw [Nat.add_comm (k : ℕ) 1, Nat.add_assoc, Nat.add_sub_of_le hk_le,
            Nat.add_comm 1 N]
        have htotal : Module.finrank 𝕜 (W ⊔ U : Submodule 𝕜 _) +
            Module.finrank 𝕜 (W ⊓ U : Submodule 𝕜 _) = N + 1 := by
          rw [hadd, hk_sum]
        by_contra hnonpos
        have hinf_zero : Module.finrank 𝕜 (W ⊓ U : Submodule 𝕜 _) = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hnonpos)
        have hle : Module.finrank 𝕜 (W ⊔ U : Submodule 𝕜 _) +
            Module.finrank 𝕜 (W ⊓ U : Submodule 𝕜 _) ≤ N := by
          simpa [hinf_zero] using hsum
        have hbad : N + 1 ≤ N := htotal ▸ hle
        exact (Nat.not_succ_le_self N) hbad
      have hne : (W ⊓ U : Submodule 𝕜 _) ≠ ⊥ := fun h => by
        rw [h] at hpos; simp at hpos
      obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact ⟨x, (Submodule.mem_inf.mp hxmem).1, (Submodule.mem_inf.mp hxmem).2, hx0⟩
    refine ⟨x, hxW, hx0,
      rayleigh_le_of_support A b μ hb x hx0 (μ k) fun i hi => ?_⟩
    refine hμ ?_
    by_contra hcon
    rw [not_le, Fin.lt_def] at hcon
    exact hi (hU_zero x hxU i hcon)

/--
The Courant-Fischer min-max characterization of the sorted eigenvalues of a
Hermitian matrix, obtained by specialising `courantFischer_of_eigenbasis` to the
spectral eigenbasis `Matrix.IsHermitian.eigenvectorBasis` and transporting the
witnessing subspaces along the (identity) linear equivalence between
`EuclideanSpace 𝕜 (Fin N)` and `Fin N → 𝕜`.
-/
theorem courant_fischer (𝕜 : Type*) [RCLike 𝕜] :
    CourantFischerStatement 𝕜 := by
  intro N A hA k
  set e : Fin (Fintype.card (Fin N)) ≃ Fin N :=
    Fintype.equivOfCardEq (by simp) with he
  set σ : Fin N ≃ Fin N := (finCongr (Fintype.card_fin N).symm).trans e with hσ
  set b : OrthonormalBasis (Fin N) 𝕜 (EuclideanSpace 𝕜 (Fin N)) :=
    hA.eigenvectorBasis.reindex σ.symm with hb_def
  have hev : ∀ j, hA.eigenvalues (σ j) = sortedEigenvalues A hA j :=
    fun j => by simp [hσ, he, sortedEigenvalues, Matrix.IsHermitian.eigenvalues]
  have hbrel : ∀ j, A *ᵥ WithLp.ofLp (b j)
      = sortedEigenvalues A hA j • WithLp.ofLp (b j) :=
    fun j => by
      simpa [hb_def, OrthonormalBasis.reindex_apply, hev j] using
        hA.mulVec_eigenvectorBasis (σ j)
  obtain ⟨⟨W₀, hW₀card, hW₀⟩, huniv⟩ :=
    courantFischer_of_eigenbasis A b (sortedEigenvalues A hA)
      (sortedEigenvalues_antitone A hA) hbrel k
  set L := WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜) with hL
  refine ⟨⟨W₀.map L.toLinearMap, ?_, ?_⟩, ?_⟩
  · simpa [LinearEquiv.finrank_map_eq] using hW₀card
  · simp_all
  · intro W hW
    have hcard : Module.finrank 𝕜 (W.comap L.toLinearMap) = (k : ℕ) + 1 := by
      rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
      simp_all
    obtain ⟨y, hy, hy0, hyr⟩ := huniv _ hcard
    exact ⟨L y, Submodule.mem_comap.mp hy, fun h ↦ hy0 (by simpa using h), hyr⟩

/-- **Cauchy interlacing theorem.** The eigenvalues of a principal submatrix of
a Hermitian matrix, obtained by deleting one row and the corresponding column,
interlace the eigenvalues of the full matrix.

The classical proof uses the Courant-Fischer min-max variational principle
(`courant_fischer`); the reduction to it (`cauchyInterlacing_of_courantFischer`)
is proved unconditionally from the linear-algebra API in this file. -/
theorem cauchy_interlacing (𝕜 : Type*) [RCLike 𝕜] :
    CauchyInterlacingStatement 𝕜 :=
  cauchyInterlacing_of_courantFischer (courant_fischer 𝕜)

end RealRooted
