/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Eigenspace.Zero
import RealRooted.Mathlib.LinearAlgebra.Matrix.CompoundSpectrum
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Nonneg
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
public import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Auxiliary
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Compound

/-!
# Gantmacher-Krein for matrices with primitive compounds

If every compound matrix `compound q A` of a real matrix `A` is primitive
(in particular entrywise nonnegative), then the spectrum of `A` is real,
positive, algebraically simple, and the characteristic polynomial splits over
`ℝ`.

This covers the oscillatory case of the Gantmacher-Krein theorem: for an
oscillatory (totally nonnegative and suitably irreducible) matrix all
compounds are primitive.  The general totally nonnegative case requires
Whitney density and root continuity and is not treated here.

Sort an eigenvalue enumeration `μ` from `exists_charpoly_compound_eq_prod` by
descending modulus.  For each `q` the
Perron root `ρ_q` of `compound q A` is an eigenvalue, and by strict spectral
dominance (`spectral_dominance_of_primitive'`) every other eigenvalue of
`compound q A` has strictly smaller modulus.  The top product
`μ 0 * ⋯ * μ (q-1)` is an eigenvalue of maximal modulus, so it must *equal*
`ρ_q` — otherwise its modulus would be strictly below `ρ_q ≤ ‖μ 0 ⋯ μ (q-1)‖`.
Hence every partial product is real and positive, and
`μ q = ρ_{q+1} / ρ_q > 0` is real.  Finally, equal eigenvalues would give two
different selections with the same Perron-root product in a compound.  This
contradicts algebraic simplicity of that compound's Perron root.
-/

@[expose] public section

open Polynomial Finset

namespace Matrix

open CollatzWielandt

variable {n : ℕ}

/-- Compound matrices commute with entrywise ring homomorphisms. -/
theorem compound_map {m l : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : ℕ) (A : Matrix (Fin m) (Fin l) R) :
    compound q (A.map f) = (compound q A).map (f : R → S) := by
  ext s t
  simp only [compound_apply, map_apply]
  have h1 : (A.map ⇑f).submatrix (powersetEnum s) (powersetEnum t)
      = f.mapMatrix (A.submatrix (powersetEnum s) (powersetEnum t)) := rfl
  rw [h1, ← RingHom.map_det]

/-- The product of the values of `f` over an increasing selection equals the
product over the underlying finite set. -/
theorem prod_powersetEnum {q : ℕ} {R : Type*} [CommMonoid R]
    (s : Set.powersetCard (Fin n) q) (f : Fin n → R) :
    ∏ k, f (powersetEnum s k) = ∏ i ∈ (s : Finset (Fin n)), f i := by
  have himg : Finset.univ.image (powersetEnum s) = (s : Finset (Fin n)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨k, hk⟩ =>
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).1 ⟨k, hk⟩,
      fun hi => (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).2 hi⟩
  calc ∏ k, f (powersetEnum s k)
      = ∏ i ∈ Finset.univ.image (powersetEnum s), f i :=
        (Finset.prod_image fun x _ y _ h =>
          (strictMono_powersetEnum s).injective h).symm
    _ = ∏ i ∈ (s : Finset (Fin n)), f i := by rw [himg]

/-- The compound charpoly factorization is invariant under permuting the
eigenvalue enumeration. -/
theorem prod_powersetCard_comp_perm {q : ℕ} (π : Equiv.Perm (Fin n)) (μ : Fin n → ℂ) :
    ∏ s : Set.powersetCard (Fin n) q,
        ((X : ℂ[X]) - C (∏ k, (μ ∘ π) (powersetEnum s k)))
      = ∏ s : Set.powersetCard (Fin n) q,
        ((X : ℂ[X]) - C (∏ k, μ (powersetEnum s k))) := by
  -- the permutation acts on selections by taking images
  have himg : ∀ (ρ : Equiv.Perm (Fin n)) (s : Set.powersetCard (Fin n) q),
      ((s : Finset (Fin n)).image ρ) ∈ Set.powersetCard (Fin n) q := by
    intro ρ s
    rw [Set.powersetCard.mem_iff, Finset.card_image_of_injective _ ρ.injective]
    exact Set.powersetCard.mem_iff.mp s.prop
  refine Finset.prod_nbij'
    (fun s => ⟨(s : Finset (Fin n)).image π, himg π s⟩)
    (fun t => ⟨(t : Finset (Fin n)).image π.symm, himg π.symm t⟩)
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro s _
    apply Subtype.ext
    simp [Finset.image_image, Function.comp_def]
  · intro t _
    apply Subtype.ext
    simp [Finset.image_image, Function.comp_def]
  · intro s _
    congr 2
    rw [prod_powersetEnum, prod_powersetEnum]
    change ∏ i ∈ (s : Finset (Fin n)), μ (π i)
      = ∏ i ∈ (s : Finset (Fin n)).image π, μ i
    exact (Finset.prod_image fun x _ y _ h => π.injective h).symm

/-! ### Algebraic simplicity of the Perron root -/

private lemma exists_pos_add_smul {ι : Type*} [Finite ι] [Nonempty ι]
    {v x : ι → ℝ} (hv : ∀ i, 0 < v i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, 0 < (x + c • v) i := by
  let _ := Fintype.ofFinite ι
  let b := Finset.univ.sup' Finset.univ_nonempty (fun i => -x i / v i)
  refine ⟨max 0 b + 1, by positivity, ?_⟩
  intro i
  have hi : -x i / v i ≤ b :=
    Finset.le_sup' (fun j => -x j / v j) (Finset.mem_univ i)
  have hi' : -x i / v i < max 0 b + 1 :=
    lt_of_le_of_lt (hi.trans (le_max_right 0 b)) (lt_add_one _)
  have hmul : -x i < (max 0 b + 1) * v i :=
    (div_lt_iff₀ (hv i)).mp hi'
  change 0 < x i + (max 0 b + 1) * v i
  linarith

private lemma maxGenEigenspace_eq_span_of_eigenspace_eq_span
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f : Module.End ℝ V} {r : ℝ} {v : V} {L : V →ₗ[ℝ] ℝ}
    (heig : f.eigenspace r = ℝ ∙ v) (hLv : L v ≠ 0)
    (hL : ∀ x, L (f x - r • x) = 0) :
    f.maxGenEigenspace r = ℝ ∙ v := by
  apply le_antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f r x).mp hx
    clear hx
    induction k generalizing x with
    | zero =>
        have hx_zero : x = 0 := by simpa using hk
        simp [hx_zero]
    | succ k ih =>
        let T := f - r • (1 : Module.End ℝ V)
        let y := T x
        have hy_pow : (T ^ k) y = 0 := by
          change (T ^ k) (T x) = 0
          rw [← Module.End.mul_apply, ← pow_succ]
          exact hk
        have hy_span : y ∈ ℝ ∙ v := ih hy_pow
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_span
        have hLy : L y = 0 := by
          simpa [y, T, LinearMap.sub_apply] using hL x
        have hc_mul : c * L v = 0 := by
          calc
            c * L v = L (c • v) := by simp
            _ = L y := by rw [hc]
            _ = 0 := hLy
        have hc_zero : c = 0 := (mul_eq_zero.mp hc_mul).resolve_right hLv
        have hy_zero : y = 0 := by rw [← hc, hc_zero, zero_smul]
        have hx_eig : x ∈ f.eigenspace r := by
          rw [Module.End.mem_eigenspace_iff]
          apply sub_eq_zero.mp
          simpa [y, T, LinearMap.sub_apply] using hy_zero
        exact heig ▸ hx_eig
  · rw [← heig]
    exact Module.End.eigenspace_le_maxGenEigenspace

/-- The Perron root of an irreducible nonnegative real matrix is algebraically simple. -/
theorem perronRoot_rootMultiplicity_eq_one_of_irreducible
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA_irred : A.IsIrreducible) :
    A.charpoly.rootMultiplicity (perronRoot A) = 1 := by
  obtain ⟨r, v, hr_pos, hv_pos, hv_eig⟩ :=
    exists_positive_eigenvector_of_irreducible hA_irred
  have hr_eq : r = perronRoot A :=
    eigenvalue_is_perron_root_of_positive_eigenvector
      hA_irred hA_irred.nonneg hr_pos hv_pos hv_eig
  subst r
  have hv_ne_zero : v ≠ 0 := Pi.ne_zero_of_pos hv_pos
  have heig : Module.End.eigenspace A.toLin' (perronRoot A) = ℝ ∙ v := by
    apply le_antisymm
    · intro x hx
      have hx_eig : A *ᵥ x = perronRoot A • x := by
        simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hx
      obtain ⟨c, hc_pos, hx_add_pos⟩ := exists_pos_add_smul hv_pos (x := x)
      have hx_add_eig : A *ᵥ (x + c • v) = perronRoot A • (x + c • v) := by
        calc
          A *ᵥ (x + c • v) = A *ᵥ x + c • (A *ᵥ v) := by
            rw [mulVec_add, mulVec_smul]
          _ = perronRoot A • x + c • (perronRoot A • v) := by
            rw [hx_eig, hv_eig]
          _ = perronRoot A • (x + c • v) := by
            rw [smul_add, smul_smul, smul_smul, mul_comm c]
      obtain ⟨d, _, h_add_eq⟩ := uniqueness_of_positive_eigenvector_gen
        hA_irred (perronRoot_pos_of_irreducible hA_irred hA_irred.nonneg)
        hx_add_pos hv_pos hx_add_eig hv_eig
      apply Submodule.mem_span_singleton.mpr
      refine ⟨d - c, ?_⟩
      simpa [sub_smul] using (eq_sub_of_add_eq h_add_eq).symm
    · rw [Submodule.span_singleton_le_iff_mem]
      apply Module.End.mem_eigenspace_iff.mpr
      simpa [Matrix.toLin'_apply] using hv_eig
  obtain ⟨u, hu_pos, hu_left_eig⟩ :=
    exists_positive_left_perron_eigenvector hA_irred hA_irred.nonneg
  let L : (ι → ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ) u
  have hLv : L v ≠ 0 :=
    (dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos
      (fun i => (hv_pos i).le) hv_ne_zero).ne'
  have hL : ∀ x, L (A.toLin' x - perronRoot A • x) = 0 := by
    intro x
    simpa [L, Matrix.toLin'_apply] using
      dotProduct_left_perron_sub_eq_zero (y := x) hu_left_eig
  have hmax : Module.End.maxGenEigenspace A.toLin' (perronRoot A) = ℝ ∙ v :=
    maxGenEigenspace_eq_span_of_eigenspace_eq_span heig hLv hL
  calc
    A.charpoly.rootMultiplicity (perronRoot A) =
        Module.finrank ℝ (Module.End.maxGenEigenspace A.toLin' (perronRoot A)) := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      simp
    _ = Module.finrank ℝ (ℝ ∙ v) := by rw [hmax]
    _ = 1 := finrank_span_singleton hv_ne_zero

/-- The Perron root of a primitive nonnegative real matrix is algebraically simple. -/
theorem perronRoot_rootMultiplicity_eq_one_of_primitive
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA_prim : A.IsPrimitive) :
    A.charpoly.rootMultiplicity (perronRoot A) = 1 :=
  perronRoot_rootMultiplicity_eq_one_of_irreducible hA_prim.isIrreducible

/-! ### The main theorem -/

/-- Values of a strictly monotone map out of `Fin q` dominate the index. -/
lemma _root_.Fin.le_val_of_strictMono {q : ℕ} {f : Fin q → Fin n} (hf : StrictMono f)
    (k : Fin q) : (k : ℕ) ≤ (f k : ℕ) := by
  have H : ∀ m : ℕ, ∀ k : Fin q, (k : ℕ) = m → m ≤ (f k : ℕ) := by
    intro m
    induction m with
    | zero => exact fun k _ => Nat.zero_le _
    | succ m ih =>
      intro k hk
      have hm : m < q := by have := k.isLt; lia
      have h1 := ih ⟨m, hm⟩ rfl
      have h2 : f ⟨m, hm⟩ < f k := hf (by simp [Fin.lt_def, hk])
      have h3 : (f ⟨m, hm⟩ : ℕ) < (f k : ℕ) := h2
      lia
  exact H (k : ℕ) k rfl

/-- The first `q` indices of `Fin n`, as a finite set. -/
private def topFinset (n q : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i : ℕ) < q)

private lemma topFinset_zero : topFinset n 0 = ∅ := by
  simp [topFinset]

private lemma topFinset_succ {q : ℕ} (hq : q < n) :
    topFinset n (q + 1) = insert ⟨q, hq⟩ (topFinset n q)
      ∧ (⟨q, hq⟩ : Fin n) ∉ topFinset n q := by
  constructor
  · ext i
    simp only [topFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hi)
      · exact Nat.lt_succ_self q
      · exact Nat.lt_succ_of_lt hi
  · simp [topFinset]

private lemma topFinset_card {q : ℕ} (hq : q ≤ n) : (topFinset n q).card = q := by
  induction q with
  | zero => simp [topFinset_zero]
  | succ q ih =>
    have hqn : q < n := Nat.lt_of_succ_le hq
    obtain ⟨hins, hnot⟩ := topFinset_succ hqn
    rw [hins, Finset.card_insert_of_notMem hnot, ih (le_of_lt hqn)]

private lemma topFinset_eq_image {q : ℕ} (hq : q ≤ n) :
    topFinset n q = Finset.univ.image (Fin.castLE hq) := by
  ext i
  simp only [topFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hi
    exact ⟨⟨(i : ℕ), hi⟩, Fin.ext rfl⟩
  · rintro ⟨k, rfl⟩
    exact k.isLt

private lemma two_le_count_map_univ_of_eq
    {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) {a b : α} (hab : a ≠ b) (hfab : f a = f b) :
    2 ≤ (Finset.univ.val.map f).count (f a) := by
  classical
  rw [Multiset.count_map]
  have hsub :
      ({a, b} : Finset α) ⊆ Finset.univ.filter (fun x => f a = f x) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp
    · simp [hfab]
  calc
    2 = ({a, b} : Finset α).card := by simp [hab]
    _ ≤ (Finset.univ.filter (fun x => f a = f x)).card :=
      Finset.card_le_card hsub
    _ = (Finset.univ.val.filter fun x => f a = f x).card := by
      rw [← Finset.filter_val]
      rfl

private lemma card_prod_insert_erase_eq_of_eq
    {α M : Type*} [DecidableEq α] [CommMonoid M]
    (f : α → M) {S : Finset α} {a b : α}
    (ha : a ∈ S) (hb : b ∉ S) (hfab : f a = f b) :
    (insert b (S.erase a)).card = S.card ∧
      (∏ x ∈ insert b (S.erase a), f x) = ∏ x ∈ S, f x ∧
      insert b (S.erase a) ≠ S := by
  have hb_erase : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  have hcard : (insert b (S.erase a)).card = S.card := by
    rw [Finset.card_insert_of_notMem hb_erase, Finset.card_erase_of_mem ha]
    exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨a, ha⟩)
  have hprod : (∏ x ∈ insert b (S.erase a), f x) = ∏ x ∈ S, f x := by
    rw [Finset.prod_insert hb_erase, ← hfab]
    exact Finset.mul_prod_erase S f ha
  have hne : insert b (S.erase a) ≠ S := by
    intro h
    have : b ∈ insert b (S.erase a) := by simp
    exact hb (h ▸ this)
  exact ⟨hcard, hprod, hne⟩

/-- The complex eigenvalues can be ordered by decreasing norm, compatibly with all compounds. -/
private theorem exists_sorted_complex_eigenvalues
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ μ : Fin n → ℂ,
      (∀ i j, i ≤ j → ‖μ j‖ ≤ ‖μ i‖) ∧
      (A.map (algebraMap ℝ ℂ)).charpoly = ∏ i, (X - C (μ i)) ∧
      ∀ q, (compound q A).charpoly.map (algebraMap ℝ ℂ) =
        ∏ s : Set.powersetCard (Fin n) q,
          ((X : ℂ[X]) - C (∏ k, μ (powersetEnum s k))) := by
  obtain ⟨ν, hν_char, hν_comp⟩ :=
    exists_charpoly_compound_eq_prod (A.map (algebraMap ℝ ℂ))
  set σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => ‖ν i‖) with hσ
  set τ : Equiv.Perm (Fin n) := Fin.revPerm.trans σ with hτ
  set μ : Fin n → ℂ := ν ∘ τ with hμ
  have hanti : ∀ i j : Fin n, i ≤ j → ‖μ j‖ ≤ ‖μ i‖ := by
    intro i j hij
    have hm := Tuple.monotone_sort (fun i => ‖ν i‖)
    have hrev : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    simpa [hμ, hτ, Function.comp] using hm hrev
  have hchar : (A.map (algebraMap ℝ ℂ)).charpoly = ∏ i, (X - C (μ i)) := by
    rw [hν_char]
    exact (Equiv.prod_comp τ fun i => (X : ℂ[X]) - C (ν i)).symm
  refine ⟨μ, hanti, hchar, fun q => ?_⟩
  calc
    (compound q A).charpoly.map (algebraMap ℝ ℂ) =
        ((compound q A).map (algebraMap ℝ ℂ)).charpoly :=
      (charpoly_map (compound q A) (algebraMap ℝ ℂ)).symm
    _ = (compound q (A.map (algebraMap ℝ ℂ))).charpoly := by rw [compound_map]
    _ = ∏ s : Set.powersetCard (Fin n) q,
          ((X : ℂ[X]) - C (∏ k, μ (powersetEnum s k))) := by
      rw [hν_comp q]
      exact (prod_powersetCard_comp_perm τ ν).symm

/-- A primitive compound has a selection product equal to its Perron root, which dominates all
other selection products. -/
private theorem exists_selection_eq_perronRoot_and_dominance
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive)
    (μ : Fin n → ℂ)
    (hcomp : ∀ q, (compound q A).charpoly.map (algebraMap ℝ ℂ) =
      ∏ s : Set.powersetCard (Fin n) q,
        ((X : ℂ[X]) - C (∏ k, μ (powersetEnum s k))))
    {q : ℕ} (hq1 : 1 ≤ q) (hqn : q ≤ n) :
    ∃ s₀ : Set.powersetCard (Fin n) q,
      (∏ k, μ (powersetEnum s₀ k)) =
        ((perronRoot (compound q A) : ℝ) : ℂ) ∧
      ∀ s : Set.powersetCard (Fin n) q,
        (∏ k, μ (powersetEnum s k)) ≠
          ((perronRoot (compound q A) : ℝ) : ℂ) →
        ‖∏ k, μ (powersetEnum s k)‖ < perronRoot (compound q A) := by
  let B := compound q A
  have hBprim := hprim q hq1 hqn
  have hBnn : ∀ s t, 0 ≤ B s t := hBprim.nonneg
  let _ : Nonempty (Set.powersetCard (Fin n) q) :=
    ⟨⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩⟩
  obtain ⟨v, -, hv_ne, hv_eig⟩ := exists_nonneg_mulVec_eq_perronRoot_smul hBnn
  have hroot : B.charpoly.IsRoot (perronRoot B) :=
    mem_spectrum_iff_isRoot_charpoly.mp (mem_spectrum_of_eigenvalue hv_ne hv_eig)
  have hrootC : (B.charpoly.map (algebraMap ℝ ℂ)).eval
      ((perronRoot B : ℝ) : ℂ) = 0 := by
    have hmap : (B.charpoly.map (algebraMap ℝ ℂ)).eval
        ((algebraMap ℝ ℂ) (perronRoot B)) =
        (algebraMap ℝ ℂ) (B.charpoly.eval (perronRoot B)) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    simpa [hroot.eq_zero] using hmap
  obtain ⟨s₀, hs₀⟩ : ∃ s : Set.powersetCard (Fin n) q,
      ∏ k, μ (powersetEnum s k) = ((perronRoot B : ℝ) : ℂ) := by
    rw [show B = compound q A by rfl, hcomp q, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at hrootC
    obtain ⟨s, -, hs⟩ := hrootC
    refine ⟨s, ?_⟩
    have h := hs
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h
    simpa only [B] using h.symm
  refine ⟨s₀, by simpa only [B] using hs₀, fun s hne => ?_⟩
  have heig : (∏ k, μ (powersetEnum s k)) ∈
      spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
    rw [mem_spectrum_iff_isRoot_charpoly, charpoly_map, IsRoot.def,
      show B = compound q A by rfl, hcomp q, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ s)
      (by simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
  apply spectral_dominance_of_primitive' hBprim hBnn _ heig
  simpa only [B] using hne

/-- The product over any selection is bounded by the product over the first indices. -/
private theorem norm_selection_le_norm_top
    {μ : Fin n → ℂ} (hanti : ∀ i j, i ≤ j → ‖μ j‖ ≤ ‖μ i‖)
    {q : ℕ} (hqn : q ≤ n) (s : Set.powersetCard (Fin n) q) :
    ‖∏ k, μ (powersetEnum s k)‖ ≤ ‖∏ i ∈ topFinset n q, μ i‖ := by
  have htop : ∏ i ∈ topFinset n q, μ i = ∏ k : Fin q, μ (Fin.castLE hqn k) := by
    rw [topFinset_eq_image hqn]
    exact Finset.prod_image fun x _ y _ h => Fin.castLE_injective hqn h
  rw [htop, norm_prod, norm_prod]
  apply Finset.prod_le_prod₀ (fun k _ => norm_nonneg _)
  intro k _
  apply hanti
  exact Fin.le_def.mpr (by
    simpa using Fin.le_val_of_strictMono (strictMono_powersetEnum s) k)

/-- The product over the first `q` ordered eigenvalues is the Perron root of the compound. -/
private theorem top_product_eq_perronRoot
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive)
    (μ : Fin n → ℂ) (hanti : ∀ i j, i ≤ j → ‖μ j‖ ≤ ‖μ i‖)
    (hcomp : ∀ q, (compound q A).charpoly.map (algebraMap ℝ ℂ) =
      ∏ s : Set.powersetCard (Fin n) q,
        ((X : ℂ[X]) - C (∏ k, μ (powersetEnum s k))))
    {q : ℕ} (hq1 : 1 ≤ q) (hqn : q ≤ n) :
    ∏ i ∈ topFinset n q, μ i = ((perronRoot (compound q A) : ℝ) : ℂ) := by
  obtain ⟨s₀, hs₀, hdom⟩ :=
    exists_selection_eq_perronRoot_and_dominance hprim μ hcomp hq1 hqn
  let sTop : Set.powersetCard (Fin n) q :=
    ⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩
  have htop : ∏ k, μ (powersetEnum sTop k) = ∏ i ∈ topFinset n q, μ i :=
    prod_powersetEnum sTop μ
  by_contra hne
  have hlt : ‖∏ i ∈ topFinset n q, μ i‖ < perronRoot (compound q A) := by
    have h := hdom sTop (by rw [htop]; exact hne)
    rwa [htop] at h
  have hge : perronRoot (compound q A) ≤ ‖∏ i ∈ topFinset n q, μ i‖ := by
    have h := norm_selection_le_norm_top hanti hqn s₀
    rw [hs₀] at h
    have hnonneg : 0 ≤ perronRoot (compound q A) :=
      perronRoot_nonneg (hprim q hq1 hqn).nonneg
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at h
    exact h
  exact absurd hge (not_le.mpr hlt)

/-- Ratios of consecutive Perron roots give positive, antitone real eigenvalues. -/
private theorem exists_positive_antitone_real_eigenvalues
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive)
    (μ : Fin n → ℂ) (hanti : ∀ i j, i ≤ j → ‖μ j‖ ≤ ‖μ i‖)
    (hkey : ∀ q, 1 ≤ q → ∀ _hq : q ≤ n,
      ∏ i ∈ topFinset n q, μ i = ((perronRoot (compound q A) : ℝ) : ℂ)) :
    ∃ μr : Fin n → ℝ, (∀ i, 0 < μr i) ∧
      (∀ i, μ i = ((μr i : ℝ) : ℂ)) ∧ Antitone μr := by
  let R : ℕ → ℝ := fun q => if q = 0 then 1 else perronRoot (compound q A)
  have hRpos : ∀ q, q ≤ n → 0 < R q := by
    intro q hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [R]
    · let _ : Nonempty (Set.powersetCard (Fin n) q) :=
        ⟨⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩⟩
      simp only [R, ite_eq_right hq1.ne']
      exact perronRoot_pos_of_irreducible
        (hprim q hq1 hqn).isIrreducible (hprim q hq1 hqn).nonneg
  have hprodR : ∀ q, q ≤ n → ∏ i ∈ topFinset n q, μ i = ((R q : ℝ) : ℂ) := by
    intro q hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [topFinset_zero, R]
    · rw [hkey q hq1 hqn]
      simp only [R, ite_eq_right hq1.ne']
  set μr : Fin n → ℝ := fun i => R ((i : ℕ) + 1) / R (i : ℕ) with hμr
  have hμr_pos : ∀ i, 0 < μr i := fun i =>
    div_pos (hRpos _ (Nat.succ_le_of_lt i.isLt)) (hRpos _ (le_of_lt i.isLt))
  have hreal : ∀ i : Fin n, μ i = ((μr i : ℝ) : ℂ) := by
    intro i
    obtain ⟨hins, hnot⟩ := topFinset_succ i.isLt
    have h1 := hprodR ((i : ℕ) + 1) (Nat.succ_le_of_lt i.isLt)
    have h2 := hprodR (i : ℕ) (le_of_lt i.isLt)
    rw [hins, Finset.prod_insert hnot, h2] at h1
    have hR_ne : ((R (i : ℕ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hRpos _ (le_of_lt i.isLt)).ne'
    rw [show (⟨(i : ℕ), i.isLt⟩ : Fin n) = i by rfl] at h1
    rw [hμr]
    push_cast
    exact (eq_div_iff hR_ne).mpr h1
  refine ⟨μr, hμr_pos, hreal, fun i j hij => ?_⟩
  have hj : ‖μ j‖ = μr j := by
    rw [hreal j, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hμr_pos j)]
  have hi : ‖μ i‖ = μr i := by
    rw [hreal i, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hμr_pos i)]
  simpa only [hj, hi] using hanti i j hij

/-- Simplicity of every compound Perron root makes the ordered real eigenvalues injective. -/
private theorem injective_real_eigenvalues_of_simple_perron
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive)
    (μ : Fin n → ℂ) (μr : Fin n → ℝ)
    (hreal : ∀ i, μ i = ((μr i : ℝ) : ℂ))
    (hkey : ∀ q, 1 ≤ q → ∀ _hq : q ≤ n,
      ∏ i ∈ topFinset n q, μ i = ((perronRoot (compound q A) : ℝ) : ℂ))
    (hcomp : ∀ q, (compound q A).charpoly.map (algebraMap ℝ ℂ) =
      ∏ s : Set.powersetCard (Fin n) q,
        ((X : ℂ[X]) - C (∏ k, μ (powersetEnum s k)))) :
    Function.Injective μr := by
  have hne_of_lt : ∀ {i j : Fin n}, i < j → μr i ≠ μr j := by
    intro i j hij hμij
    let q := (i : ℕ) + 1
    have hq1 : 1 ≤ q := by simp only [q, le_add_iff_nonneg_left, zero_le]
    have hqn : q ≤ n := Nat.succ_le_of_lt i.isLt
    have hi_top : i ∈ topFinset n q := by simp only [topFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, q, Nat.lt_add_one]
    have hj_not : j ∉ topFinset n q := by
      simp only [topFinset, Finset.mem_filter, Finset.mem_univ, true_and, q]
      exact Nat.not_lt.mpr (Nat.succ_le_of_lt hij)
    have hμijC : μ i = μ j := by rw [hreal i, hreal j, hμij]
    have hswap := card_prod_insert_erase_eq_of_eq μ hi_top hj_not hμijC
    let sTop : Set.powersetCard (Fin n) q :=
      ⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩
    let sAlt : Set.powersetCard (Fin n) q :=
      ⟨insert j ((topFinset n q).erase i),
        Set.powersetCard.mem_iff.mpr (hswap.1.trans (topFinset_card hqn))⟩
    have hs_ne : sTop ≠ sAlt := by
      intro h
      exact hswap.2.2 ((congrArg Subtype.val h).symm)
    let g : Set.powersetCard (Fin n) q → ℂ :=
      fun s => ∏ k, μ (powersetEnum s k)
    have hg_eq : g sTop = g sAlt := by
      dsimp only [g]
      rw [prod_powersetEnum, prod_powersetEnum]
      exact hswap.2.1.symm
    have hg_top : g sTop = ((perronRoot (compound q A) : ℝ) : ℂ) := by
      dsimp only [g]
      rw [prod_powersetEnum]
      exact hkey q hq1 hqn
    have hroots : ((compound q A).charpoly.map (algebraMap ℝ ℂ)).roots =
        Finset.univ.val.map g := by
      rw [hcomp q, Finset.prod]
      rw [show (fun s => (X : ℂ[X]) - C (∏ k, μ (powersetEnum s k))) =
          (fun y => (X : ℂ[X]) - C y) ∘ g by rfl]
      rw [← Multiset.map_map]
      exact Polynomial.roots_multiset_prod_X_sub_C _
    have htwo : 2 ≤ ((compound q A).charpoly.map (algebraMap ℝ ℂ)).roots.count
        (((perronRoot (compound q A) : ℝ) : ℂ)) := by
      rw [hroots, ← hg_top]
      exact two_le_count_map_univ_of_eq g hs_ne hg_eq
    let _ : Nonempty (Set.powersetCard (Fin n) q) := ⟨sTop⟩
    have hsimpleC :
        ((compound q A).charpoly.map (algebraMap ℝ ℂ)).rootMultiplicity
          (((perronRoot (compound q A) : ℝ) : ℂ)) = 1 := by
      change ((compound q A).charpoly.map (algebraMap ℝ ℂ)).rootMultiplicity
        ((algebraMap ℝ ℂ) (perronRoot (compound q A))) = 1
      rw [← Polynomial.eq_rootMultiplicity_map (p := (compound q A).charpoly)
        (f := algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
          (perronRoot (compound q A))]
      exact perronRoot_rootMultiplicity_eq_one_of_primitive (hprim q hq1 hqn)
    rw [Polynomial.count_roots, hsimpleC] at htwo
    lia
  intro i j hμij
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hne_of_lt hij hμij
  · exact hne_of_lt hji hμij.symm

/-- **Gantmacher-Krein for matrices with primitive compounds.**  If every
compound of `A` is primitive, the characteristic polynomial of `A` splits over
`ℝ` with positive roots in strictly decreasing order. -/
theorem exists_charpoly_eq_prod_strictAnti_of_forall_compound_primitive
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive) :
    ∃ μ : Fin n → ℝ, StrictAnti μ ∧ (∀ i, 0 < μ i) ∧
      A.charpoly = ∏ i, (X - C (μ i)) := by
  classical
  obtain ⟨μc, hanti, hchar, hcomp⟩ := exists_sorted_complex_eigenvalues A
  have hkey : ∀ q, 1 ≤ q → ∀ hq : q ≤ n,
      ∏ i ∈ topFinset n q, μc i = ((perronRoot (compound q A) : ℝ) : ℂ) :=
    fun _ hq1 hqn => top_product_eq_perronRoot hprim μc hanti hcomp hq1 hqn
  obtain ⟨μr, hμr_pos, hμc_real, hμr_anti⟩ :=
    exists_positive_antitone_real_eigenvalues hprim μc hanti hkey
  have hμr_inj :=
    injective_real_eigenvalues_of_simple_perron hprim μc μr hμc_real hkey hcomp
  have hμr_strict : StrictAnti μr := hμr_anti.strictAnti_of_injective hμr_inj
  -- transport the complex factorization back to `ℝ`
  have hmapped : A.charpoly.map (algebraMap ℝ ℂ)
      = (∏ i, ((X : ℝ[X]) - C (μr i))).map (algebraMap ℝ ℂ) := by
    rw [← charpoly_map, hchar, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hμc_real i]
    rfl
  exact ⟨μr, hμr_strict, hμr_pos,
    Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective hmapped⟩

/-- If every compound of `A` is primitive, the positive roots of its
characteristic polynomial can be enumerated in nonincreasing order. -/
theorem exists_charpoly_eq_prod_antitone_of_forall_compound_primitive
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive) :
    ∃ μ : Fin n → ℝ, Antitone μ ∧ (∀ i, 0 < μ i) ∧
      A.charpoly = ∏ i, (X - C (μ i)) := by
  obtain ⟨μ, hμ_strict, hμ_pos, hchar⟩ :=
    exists_charpoly_eq_prod_strictAnti_of_forall_compound_primitive hprim
  exact ⟨μ, hμ_strict.antitone, hμ_pos, hchar⟩

/-- If every compound of `A` is primitive, the characteristic polynomial of
`A` splits over `ℝ` with strictly positive roots. -/
theorem exists_charpoly_eq_prod_of_forall_compound_primitive
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 < μ i) ∧ A.charpoly = ∏ i, (X - C (μ i)) := by
  obtain ⟨μ, -, hμ_pos, hchar⟩ :=
    exists_charpoly_eq_prod_antitone_of_forall_compound_primitive hprim
  exact ⟨μ, hμ_pos, hchar⟩

/-! ### Strict interlacing closure -/

/-- Weak interlacing of two factored characteristic polynomials is strict when
the polynomials have no common root.  The weak interlacing hypothesis remains
essential; real-rootedness and disjoint spectra alone do not imply it. -/
theorem strictInterlace_charpoly_of_interlace_of_noCommonRoot
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {B : Matrix (Fin n) (Fin n) ℝ}
    {lam : Fin (n + 1) → ℝ} {μ : Fin n → ℝ}
    (hA : A.charpoly = ∏ i, (X - C (lam i)))
    (hB : B.charpoly = ∏ i, (X - C (μ i)))
    (hinter : ∀ k : Fin n, lam k.succ ≤ μ k ∧ μ k ≤ lam k.castSucc)
    (hno : ∀ r : ℝ, A.charpoly.IsRoot r → ¬ B.charpoly.IsRoot r) :
    ∀ k : Fin n, lam k.succ < μ k ∧ μ k < lam k.castSucc := by
  have hrootA : ∀ i, A.charpoly.IsRoot (lam i) := by
    intro i
    rw [hA, Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hrootB : ∀ j, B.charpoly.IsRoot (μ j) := by
    intro j
    rw [hB, Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  have hne : ∀ i j, lam i ≠ μ j :=
    fun i j hij => hno (lam i) (hrootA i) (by simpa [hij] using hrootB j)
  intro k
  exact ⟨lt_of_le_of_ne (hinter k).1 (hne k.succ k),
    lt_of_le_of_ne (hinter k).2 (hne k.castSucc k).symm⟩

/-! ### The oscillatory bridge -/

/-- Compounds commute with matrix powers. -/
theorem compound_pow {m : ℕ} {R : Type*} [CommRing R] (q k : ℕ)
    (A : Matrix (Fin m) (Fin m) R) :
    compound q (A ^ k) = compound q A ^ k := by
  induction k with
  | zero => simpa using compound_one
  | succ k ih => rw [pow_succ, compound_mul, ih, pow_succ]

/-- If some positive power of a totally nonnegative matrix has strictly
positive compound entries — the oscillatory situation — then every compound is
primitive. -/
theorem isPrimitive_compound_of_pow {A : Matrix (Fin n) (Fin n) ℝ}
    (hTN : A.IsTotallyNonneg) {k : ℕ} (hk : 0 < k)
    (hpos : ∀ q, 1 ≤ q → q ≤ n → ∀ s t, 0 < compound q (A ^ k) s t) :
    ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive := by
  intro q hq1 hqn
  refine ⟨fun s t => compound_nonneg q hTN.toRect s t, ⟨k, hk, fun s t => ?_⟩⟩
  have h := hpos q hq1 hqn s t
  rwa [compound_pow] at h

/-- **Oscillatory matrices have real positive spectrum.**  A totally
nonnegative matrix, some power of which has strictly positive compound
entries, has characteristic polynomial splitting over `ℝ` with strictly
positive roots. -/
theorem exists_charpoly_eq_prod_of_pow_compound_pos
    {A : Matrix (Fin n) (Fin n) ℝ} (hTN : A.IsTotallyNonneg) {k : ℕ} (hk : 0 < k)
    (hpos : ∀ q, 1 ≤ q → q ≤ n → ∀ s t, 0 < compound q (A ^ k) s t) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 < μ i) ∧ A.charpoly = ∏ i, (X - C (μ i)) :=
  exists_charpoly_eq_prod_of_forall_compound_primitive
    (isPrimitive_compound_of_pow hTN hk hpos)

/-- The splitting form of the conclusion: the characteristic polynomial is
real-rooted with strictly positive roots. -/
theorem charpoly_splits_of_forall_compound_primitive
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive) :
    A.charpoly.Splits ∧ ∀ t ∈ A.charpoly.roots, 0 < t := by
  obtain ⟨μ, hμ_pos, hfact⟩ := exists_charpoly_eq_prod_of_forall_compound_primitive hprim
  have hmulti : A.charpoly
      = ((Finset.univ.val.map μ).map fun a => (X : ℝ[X]) - C a).prod := by
    rw [hfact, Finset.prod, Multiset.map_map]
    rfl
  have hroots : A.charpoly.roots = Finset.univ.val.map μ := by
    rw [hmulti, Polynomial.roots_multiset_prod_X_sub_C]
  constructor
  · rw [Polynomial.splits_iff_card_roots, hroots]
    have hdeg : A.charpoly.natDegree = n := by
      simp
    simp [hdeg]
  · intro t ht
    rw [hroots] at ht
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ht
    exact hμ_pos i

end Matrix
