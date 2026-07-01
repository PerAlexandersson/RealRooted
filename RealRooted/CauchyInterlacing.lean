import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Cauchy interlacing theorem: statement and supporting API

This module sets up the **Cauchy interlacing theorem** for Hermitian matrices,
together with the reusable, unconditional API surrounding it.

Given a Hermitian matrix `A` of size `n + 1` and a deleted index `i`, the
principal submatrix `B = A.submatrix i.succAbove i.succAbove` of size `n` has
eigenvalues that interlace those of `A`. Writing the eigenvalues in
decreasing order as `λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ` for `A` and `μ₀ ≥ ⋯ ≥ μₙ₋₁` for `B`,
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
  reduced to the single classical boundary `RealRooted.courant_fischer`.

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
    Antitone (sortedEigenvalues A hA) := by
  intro a b hab
  exact hA.eigenvalues₀_antitone (by simpa [finCongr] using hab)

/-- The sorted eigenvalues of a Hermitian matrix are exactly the roots of its
characteristic polynomial, counted with multiplicity. -/
theorem sortedEigenvalues_charpoly_roots {N : ℕ}
    (A : Matrix (Fin N) (Fin N) 𝕜) (hA : A.IsHermitian) :
    A.charpoly.roots =
      (Finset.univ : Finset (Fin N)).val.map
        (fun k => (RCLike.ofReal (sortedEigenvalues A hA k) : 𝕜)) := by
  have := hA.roots_charpoly_eq_eigenvalues₀
  simp +decide [this, sortedEigenvalues]

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
  rw [embedCompl, Function.extend_apply']
  · rfl
  · rintro ⟨a, ha⟩
    exact (Fin.succAbove_ne i a) ha

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
    Function.Injective (embedComplₗ (𝕜 := 𝕜) i) := by
  intro x y hxy
  ext a
  have := congr_fun hxy (i.succAbove a)
  simpa using this

/-- Pushing a subspace forward along `embedComplₗ` preserves its dimension. -/
theorem finrank_map_embedComplₗ {n : ℕ} (i : Fin (n + 1))
    (W : Submodule 𝕜 (Fin n → 𝕜)) :
    Module.finrank 𝕜 (W.map (embedComplₗ i)) = Module.finrank 𝕜 W := by
  exact LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (embedComplₗ_injective i) _).symm

/-- The range of `embedComplₗ i` is a hyperplane: it has dimension `n` inside
the `(n+1)`-dimensional ambient space. -/
theorem finrank_range_embedComplₗ {n : ℕ} (i : Fin (n + 1)) :
    Module.finrank 𝕜 (LinearMap.range (embedComplₗ (𝕜 := 𝕜) i)) = n := by
  convert finrank_map_embedComplₗ i (⊤ : Submodule 𝕜 (Fin n → 𝕜)) using 1
  · rw [LinearMap.range_eq_map]
  · simp +decide

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
    · simp +decide
    · exact this.linearIndependent.comp _ (Fin.castLE_injective _)
  refine h_contra ⟨Submodule.map (Submodule.subtype S) T, Submodule.map_subtype_le _ _, ?_⟩
  convert hT using 1
  convert Submodule.finrank_map_subtype_eq _ _

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

set_option linter.flexible false in
/-- Assuming the witnessed min-max characterization of sorted eigenvalues, the
Cauchy interlacing theorem follows from the linear-algebra API above. -/
theorem cauchyInterlacing_of_courantFischer
    (hCF : CourantFischerStatement 𝕜) : CauchyInterlacingStatement 𝕜 := by
  intro n A hA i
  have := hCF A hA
  simp_all +decide [CourantFischerStatement]
  intro k
  constructor
  · obtain ⟨W_A, hW_A₁, hW_A₂⟩ := (hCF A hA k.succ).1
    generalize_proofs at *
    obtain ⟨T, hT₁, hT₂⟩ :=
      exists_submodule_le_finrank_eq (W_A ⊓ LinearMap.range (embedComplₗ i)) (k + 1)
        (by
          have := Submodule.finrank_sup_add_finrank_inf_eq W_A
            (LinearMap.range (embedComplₗ i))
          simp_all +decide [finrank_range_embedComplₗ]
          linarith [show Module.finrank 𝕜 (↥(W_A ⊔ (embedComplₗ i).range)) ≤ n + 1 from
            le_trans (Submodule.finrank_le _) (by simp +decide)])
    generalize_proofs at *
    obtain ⟨y, hy₁, hy₂⟩ :=
      hCF (A.submatrix i.succAbove i.succAbove) ‹_› k |>.2
        (Submodule.comap (embedComplₗ i) T)
        (by
          have hT₃ : Module.finrank 𝕜
              (Submodule.map (embedComplₗ i) (Submodule.comap (embedComplₗ i) T)) =
                Module.finrank 𝕜 T := by
            rw [Submodule.map_comap_eq_self]
            aesop
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
          aesop)
    generalize_proofs at *
    obtain ⟨y, hy₁, rfl⟩ := Submodule.mem_map.mp hx₁
    generalize_proofs at *
    refine (hW₂ y hy₁ ?_).trans ?_
    · intro hy
      exact hx₂ (by simpa [hy] using (map_zero (embedComplₗ (𝕜 := 𝕜) i)))
    · simpa only [embedComplₗ_apply, rayleigh_submatrix_embedCompl] using hx₃

/-- The Courant-Fischer min-max characterization of the sorted eigenvalues of a
Hermitian matrix. This is the remaining classical input; its proof needs the
spectral theorem together with the variational principle, which is not yet in
Mathlib. -/
theorem courant_fischer (𝕜 : Type*) [RCLike 𝕜] :
    CourantFischerStatement 𝕜 := by
  sorry

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
