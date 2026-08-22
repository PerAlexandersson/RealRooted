import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.CompoundSpectrum
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Nonneg

/-!
# Gantmacher-Krein for matrices with primitive compounds

If every compound matrix `compound q A` of a real matrix `A` is primitive
(in particular entrywise nonnegative), then the spectrum of `A` is real,
positive, and the characteristic polynomial splits over `ℝ`.

This covers the oscillatory case of the Gantmacher-Krein theorem: for an
oscillatory (totally nonnegative and suitably irreducible) matrix all
compounds are primitive.  The general totally nonnegative case requires
Whitney density and root continuity and is not treated here.

The argument needs no tie analysis.  Sort an eigenvalue enumeration `μ` from
`exists_charpoly_compound_eq_prod` by descending modulus.  For each `q` the
Perron root `ρ_q` of `compound q A` is an eigenvalue, and by strict spectral
dominance (`spectral_dominance_of_primitive'`) every other eigenvalue of
`compound q A` has strictly smaller modulus.  The top product
`μ 0 * ⋯ * μ (q-1)` is an eigenvalue of maximal modulus, so it must *equal*
`ρ_q` — otherwise its modulus would be strictly below `ρ_q ≤ ‖μ 0 ⋯ μ (q-1)‖`.
Hence every partial product is real and positive, and
`μ q = ρ_{q+1} / ρ_q > 0` is real.
-/

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
    show ∏ i ∈ (s : Finset (Fin n)), μ (π i)
      = ∏ i ∈ (s : Finset (Fin n)).image π, μ i
    exact (Finset.prod_image fun x _ y _ h => π.injective h).symm

/-! ### The main theorem -/

/-- Values of a strictly monotone map out of `Fin q` dominate the index. -/
private lemma le_val_of_strictMono {q : ℕ} {f : Fin q → Fin n} (hf : StrictMono f)
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

/-- **Gantmacher-Krein for matrices with primitive compounds.**  If every
compound of `A` is primitive, the characteristic polynomial of `A` splits over
`ℝ` with strictly positive roots.  This covers the oscillatory case; the
general totally nonnegative case needs Whitney density and root continuity. -/
theorem exists_charpoly_eq_prod_of_forall_compound_primitive
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hprim : ∀ q, 1 ≤ q → q ≤ n → (compound q A).IsPrimitive) :
    ∃ μ : Fin n → ℝ, (∀ i, 0 < μ i) ∧ A.charpoly = ∏ i, (X - C (μ i)) := by
  classical
  -- the complex eigenvalue enumeration, sorted by descending modulus
  obtain ⟨ν, hν_char, hν_comp⟩ :=
    exists_charpoly_compound_eq_prod (A.map (algebraMap ℝ ℂ))
  set σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => ‖ν i‖) with hσ
  set τ : Equiv.Perm (Fin n) := Fin.revPerm.trans σ with hτ
  set μc : Fin n → ℂ := ν ∘ τ with hμc
  have hanti : ∀ i j : Fin n, i ≤ j → ‖μc j‖ ≤ ‖μc i‖ := by
    intro i j hij
    have hm := Tuple.monotone_sort (fun i => ‖ν i‖)
    have hrev : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    simpa [hμc, hτ, Function.comp] using hm hrev
  have hchar : (A.map (algebraMap ℝ ℂ)).charpoly = ∏ i, (X - C (μc i)) := by
    rw [hν_char]
    exact (Equiv.prod_comp τ fun i => (X : ℂ[X]) - C (ν i)).symm
  have hcomp : ∀ q, ((compound q A).charpoly.map (algebraMap ℝ ℂ))
      = ∏ s : Set.powersetCard (Fin n) q,
          ((X : ℂ[X]) - C (∏ k, μc (powersetEnum s k))) := by
    intro q
    calc (compound q A).charpoly.map (algebraMap ℝ ℂ)
        = ((compound q A).map (algebraMap ℝ ℂ)).charpoly :=
          (charpoly_map (compound q A) (algebraMap ℝ ℂ)).symm
      _ = (compound q (A.map (algebraMap ℝ ℂ))).charpoly := by
          rw [compound_map]
      _ = ∏ s : Set.powersetCard (Fin n) q,
            ((X : ℂ[X]) - C (∏ k, μc (powersetEnum s k))) := by
          rw [hν_comp q]
          exact (prod_powersetCard_comp_perm τ ν).symm
  -- the key identity: the top product equals the Perron root of the compound
  have hkey : ∀ q, 1 ≤ q → ∀ hq : q ≤ n,
      ∏ i ∈ topFinset n q, μc i = ((perronRoot (compound q A) : ℝ) : ℂ) := by
    intro q hq1 hqn
    set B : Matrix (Set.powersetCard (Fin n) q) (Set.powersetCard (Fin n) q) ℝ :=
      compound q A with hB
    have hBprim := hprim q hq1 hqn
    have hBnn : ∀ s t, 0 ≤ B s t := hBprim.nonneg
    haveI : Nonempty (Set.powersetCard (Fin n) q) :=
      ⟨⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩⟩
    have hρ_nonneg : 0 ≤ perronRoot B := perronRoot_nonneg hBnn
    -- the Perron root is a complex root of the factored charpoly
    obtain ⟨v, hv_nn, hv_ne, hv_eig⟩ := exists_nonneg_mulVec_eq_perronRoot_smul hBnn
    have hroot : B.charpoly.IsRoot (perronRoot B) :=
      mem_spectrum_iff_isRoot_charpoly.mp (mem_spectrum_of_eigenvalue hv_ne hv_eig)
    have hrootC : (B.charpoly.map (algebraMap ℝ ℂ)).eval ((perronRoot B : ℝ) : ℂ) = 0 := by
      have h1 : (B.charpoly.map (algebraMap ℝ ℂ)).eval ((algebraMap ℝ ℂ) (perronRoot B))
          = (algebraMap ℝ ℂ) (B.charpoly.eval (perronRoot B)) := by
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simpa [hroot.eq_zero] using h1
    -- hence some selection product equals the Perron root
    obtain ⟨s₀, hs₀⟩ : ∃ s : Set.powersetCard (Fin n) q,
        ∏ k, μc (powersetEnum s k) = ((perronRoot B : ℝ) : ℂ) := by
      rw [hcomp q, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hrootC
      obtain ⟨s, -, hs⟩ := hrootC
      refine ⟨s, ?_⟩
      have := hs
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at this
      exact this.symm
    -- every selection product is an eigenvalue, and dominance is strict
    have hdom : ∀ s : Set.powersetCard (Fin n) q,
        (∏ k, μc (powersetEnum s k)) ≠ ((perronRoot B : ℝ) : ℂ) →
        ‖∏ k, μc (powersetEnum s k)‖ < perronRoot B := by
      intro s hne
      have heig : (∏ k, μc (powersetEnum s k))
          ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
        rw [mem_spectrum_iff_isRoot_charpoly, charpoly_map, IsRoot.def, hcomp q,
          Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ s)
          (by simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
      exact spectral_dominance_of_primitive' hBprim hBnn _ heig hne
    -- the top selection dominates every selection in modulus
    set sTop : Set.powersetCard (Fin n) q :=
      ⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩ with hsTop
    have htop_prod : ∏ k, μc (powersetEnum sTop k) = ∏ i ∈ topFinset n q, μc i :=
      prod_powersetEnum sTop μc
    have htop_norm : ∏ i ∈ topFinset n q, μc i = ∏ k : Fin q, μc (Fin.castLE hqn k) := by
      rw [topFinset_eq_image hqn]
      exact Finset.prod_image fun x _ y _ h => Fin.castLE_injective hqn h
    have hmax : ∀ s : Set.powersetCard (Fin n) q,
        ‖∏ k, μc (powersetEnum s k)‖ ≤ ‖∏ i ∈ topFinset n q, μc i‖ := by
      intro s
      rw [htop_norm, norm_prod, norm_prod]
      apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
      intro k _
      apply hanti
      have h1 := le_val_of_strictMono (strictMono_powersetEnum s) k
      exact Fin.le_def.mpr (by simpa using h1)
    -- if the top product were not the Perron root, its modulus would be both
    -- strictly below and at least the Perron root
    by_contra hne
    have hlt : ‖∏ i ∈ topFinset n q, μc i‖ < perronRoot B := by
      have h := hdom sTop (by rw [htop_prod]; exact hne)
      rwa [htop_prod] at h
    have hge : perronRoot B ≤ ‖∏ i ∈ topFinset n q, μc i‖ := by
      have h := hmax s₀
      rw [hs₀] at h
      have hnorm : ‖((perronRoot B : ℝ) : ℂ)‖ = perronRoot B := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ_nonneg]
      rwa [hnorm] at h
    exact absurd hge (not_le.mpr hlt)
  -- the chain of Perron roots and the real eigenvalues
  set R : ℕ → ℝ := fun q => if q = 0 then 1 else perronRoot (compound q A) with hR
  have hRpos : ∀ q, q ≤ n → 0 < R q := by
    intro q hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [hR]
    · haveI : Nonempty (Set.powersetCard (Fin n) q) :=
        ⟨⟨topFinset n q, Set.powersetCard.mem_iff.mpr (topFinset_card hqn)⟩⟩
      have hBprim := hprim q hq1 hqn
      simp only [hR, if_neg hq1.ne']
      exact perronRoot_pos_of_irreducible hBprim.isIrreducible hBprim.nonneg
  have hprodR : ∀ q, q ≤ n → ∏ i ∈ topFinset n q, μc i = ((R q : ℝ) : ℂ) := by
    intro q hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq1
    · simp [topFinset_zero, hR]
    · rw [hkey q hq1 hqn]
      simp [hR, if_neg hq1.ne']
  set μr : Fin n → ℝ := fun i => R ((i : ℕ) + 1) / R (i : ℕ) with hμr
  have hμr_pos : ∀ i, 0 < μr i := fun i =>
    div_pos (hRpos _ (Nat.succ_le_of_lt i.isLt)) (hRpos _ (le_of_lt i.isLt))
  have hμc_real : ∀ i : Fin n, μc i = ((μr i : ℝ) : ℂ) := by
    intro i
    obtain ⟨hins, hnot⟩ := topFinset_succ i.isLt
    have h1 := hprodR ((i : ℕ) + 1) (Nat.succ_le_of_lt i.isLt)
    have h2 := hprodR (i : ℕ) (le_of_lt i.isLt)
    rw [hins, Finset.prod_insert hnot, h2] at h1
    have hR_ne : ((R (i : ℕ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hRpos _ (le_of_lt i.isLt)).ne'
    have hii : (⟨(i : ℕ), i.isLt⟩ : Fin n) = i := rfl
    rw [hii] at h1
    rw [hμr]
    push_cast
    exact (eq_div_iff hR_ne).mpr h1
  -- transport the complex factorization back to `ℝ`
  have hmapped : A.charpoly.map (algebraMap ℝ ℂ)
      = (∏ i, ((X : ℝ[X]) - C (μr i))).map (algebraMap ℝ ℂ) := by
    rw [← charpoly_map, hchar, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hμc_real i]
    rfl
  exact ⟨μr, hμr_pos,
    Polynomial.map_injective (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective hmapped⟩

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
      simpa using A.charpoly_natDegree_eq_dim
    simp [hdeg]
  · intro t ht
    rw [hroots] at ht
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ht
    exact hμ_pos i

end Matrix
