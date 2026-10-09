import RealRooted.HosterStump.PosetBasic

/-!
# Counting chains of subsets of a finite set

`card_boolChains` identifies `gapMultinomial r U` with the number of chains of subsets of an
`r`-set having sizes `U + 1`.  The recursion on the top element is proved for an arbitrary finite
poset with a rank function (`chainCount_succ`); it is reused for graded simplicial posets.
-/

open Finset

noncomputable section

namespace RealRooted.HosterStump

section Chains

variable {Q : Type*} [PartialOrder Q] [Fintype Q]

open scoped Classical in
/-- The number of strict chains `c 0 < c 1 < …` in `Q` with `rk (c j) = s j + 1`. -/
def chainCount (rk : Q → ℕ) {k : ℕ} (s : Fin k → ℕ) : ℕ :=
  (univ.filter fun c : Fin k → Q => StrictMono c ∧ ∀ j, rk (c j) = s j + 1).card

open scoped Classical in
/-- The number of chains as in `chainCount` all of whose elements lie below `x`. -/
def chainCountBelow (rk : Q → ℕ) {k : ℕ} (s : Fin k → ℕ) (x : Q) : ℕ :=
  (univ.filter fun c : Fin k → Q =>
    StrictMono c ∧ (∀ j, rk (c j) = s j + 1) ∧ ∀ j, c j ≤ x).card

/-- The empty chain is unique. -/
theorem chainCount_zero (rk : Q → ℕ) (s : Fin 0 → ℕ) : chainCount rk s = 1 := by
  classical
  have h : ∀ c : Fin 0 → Q, StrictMono c ∧ ∀ j, rk (c j) = s j + 1 :=
    fun c => ⟨fun a => a.elim0, fun j => j.elim0⟩
  unfold chainCount
  rw [Finset.filter_true_of_mem (fun c _ => h c)]
  simp

omit [Fintype Q] in
private theorem strictMono_snoc {k : ℕ} {c : Fin k → Q} {x : Q} (h : StrictMono c)
    (hx : ∀ j, c j < x) : StrictMono (Fin.snoc (α := fun _ => Q) c x) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (lt_irrefl _)
    | cast i => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hx i
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last _))
    | cast i =>
      simpa only [Fin.snoc_castSucc] using h (Fin.castSucc_lt_castSucc_iff.1 hij)

/-- Splitting a chain by its top element. -/
theorem chainCount_succ (rk : Q → ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ) (hs : StrictMono s) :
    chainCount rk s = ∑ x ∈ (univ.filter fun x : Q => rk x = s (Fin.last k) + 1),
      chainCountBelow rk (fun j : Fin k => s j.castSucc) x := by
  classical
  unfold chainCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun c : Fin (k + 1) → Q => c (Fin.last k))
    (t := univ.filter fun x : Q => rk x = s (Fin.last k) + 1)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    unfold chainCountBelow
    have hx' : rk x = s (Fin.last k) + 1 := (Finset.mem_filter.1 hx).2
    refine Finset.card_nbij' (fun c => Fin.init c) (fun c => Fin.snoc (α := fun _ => Q) c x)
      ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      obtain ⟨⟨hm, hr⟩, hl⟩ := hc
      refine ⟨fun a b hab => hm (Fin.castSucc_lt_castSucc_iff.2 hab),
        fun j => hr j.castSucc, fun j => ?_⟩
      have := hm (Fin.castSucc_lt_last j)
      rw [hl] at this
      exact this.le
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      obtain ⟨hm, hr, hle⟩ := hc
      have hlt : ∀ j, c j < x := by
        intro j
        refine lt_of_le_of_ne (hle j) fun hjx => ?_
        have h1 := hr j
        have h2 := hs (Fin.castSucc_lt_last j)
        rw [hjx] at h1
        lia
      refine ⟨⟨strictMono_snoc hm hlt, fun j => ?_⟩, by simp⟩
      induction j using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using hx'
      | cast j => simpa only [Fin.snoc_castSucc] using hr j
    · intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rw [← hc.2]
      exact Fin.snoc_init_self c
    · intro c _
      simp
  · intro c hc
    have hc' := Finset.mem_filter.1 hc
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hc'.2.2 (Fin.last k)⟩

/-- Chains below `x` correspond to chains in a Boolean lattice when the lower interval of `x`
is order isomorphic to a Boolean lattice compatibly with ranks. -/
theorem chainCountBelow_eq_of_orderIso (rk : Q → ℕ) {k m : ℕ} (s : Fin k → ℕ) (x : Q)
    (e : Set.Iic x ≃o Finset (Fin m)) (he : ∀ y : Set.Iic x, (e y).card = rk y) :
    chainCountBelow rk s x = chainCount (Finset.card : Finset (Fin m) → ℕ) s := by
  classical
  unfold chainCountBelow chainCount
  refine Finset.card_bij (fun c hc => fun j => e ⟨c j, ?_⟩) ?_ ?_ ?_
  · exact (Finset.mem_filter.1 hc).2.2.2 j
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    obtain ⟨hm, hr, hle⟩ := hc
    refine ⟨fun a b hab => ?_, fun j => ?_⟩
    · have hab' : (⟨c a, hle a⟩ : Set.Iic x) < ⟨c b, hle b⟩ := hm hab
      exact e.strictMono hab'
    · rw [he]
      exact hr j
  · intro c₁ hc₁ c₂ hc₂ h
    funext j
    have := congrFun h j
    exact congrArg Subtype.val (e.injective this)
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    obtain ⟨hm, hr⟩ := hd
    refine ⟨fun j => (e.symm (d j)).1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun a b hab => ?_, fun j => ?_, fun j => (e.symm (d j)).2⟩
      · exact e.symm.strictMono (hm hab)
      · have := he (e.symm (d j))
        rw [OrderIso.apply_symm_apply] at this
        rw [← this, hr j]
    · funext j
      exact e.apply_symm_apply (d j)

end Chains

section Bool

variable {r : ℕ}

/-- The largest value of a strictly monotone sequence is its last value. -/
theorem image_max'_eq_last {k : ℕ} {s : Fin (k + 1) → ℕ} (hs : StrictMono s)
    (hne : (univ.image s).Nonempty) : (univ.image s).max' hne = s (Fin.last k) := by
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  intro y hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
  exact hs.monotone (Fin.le_last i)

/-- Removing the last value of a strictly monotone sequence from its image. -/
theorem image_erase_last {k : ℕ} {s : Fin (k + 1) → ℕ} (hs : StrictMono s) :
    (univ.image s).erase (s (Fin.last k)) = univ.image (fun j : Fin k => s j.castSucc) := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hy, a, rfl⟩
    induction a using Fin.lastCases with
    | last => exact absurd rfl hy
    | cast b => exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨hs.injective.ne (Fin.castSucc_lt_last b).ne, _, rfl⟩

private theorem map_preimage_orderEmb {A y : Finset (Fin r)} (hy : y ⊆ A) :
    (y.preimage (A.orderEmbOfFin rfl) (A.orderEmbOfFin rfl).injective.injOn).map
      (A.orderEmbOfFin rfl).toEmbedding = y := by
  ext a
  simp only [Finset.mem_map, Finset.mem_preimage, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    have : a ∈ Set.range (A.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hy ha
    obtain ⟨b, rfl⟩ := this
    exact ⟨b, ha, rfl⟩

/-- The lower interval of a subset `A` of `Fin r` is the Boolean lattice on `A.card` points. -/
def boolIic (A : Finset (Fin r)) : Set.Iic A ≃o Finset (Fin A.card) where
  toFun y := y.1.preimage (A.orderEmbOfFin rfl) (A.orderEmbOfFin rfl).injective.injOn
  invFun d := ⟨d.map (A.orderEmbOfFin rfl).toEmbedding, by
    intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_map.1 ha
    exact Finset.orderEmbOfFin_mem A rfl b⟩
  left_inv y := by
    apply Subtype.ext
    exact map_preimage_orderEmb y.2
  right_inv d := by
    exact Finset.preimage_map _ d
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have h' := (Finset.map_subset_map (f := (A.orderEmbOfFin rfl).toEmbedding)).2 h
      have h1 := map_preimage_orderEmb a.2
      have h2 := map_preimage_orderEmb b.2
      have h3 : a.1 ⊆ b.1 := by
        rw [← h1, ← h2]
        exact h'
      exact h3
    · intro h c hc
      change c ∈ a.1.preimage (A.orderEmbOfFin rfl)
        (A.orderEmbOfFin rfl).injective.injOn at hc
      change c ∈ b.1.preimage (A.orderEmbOfFin rfl) (A.orderEmbOfFin rfl).injective.injOn
      rw [Finset.mem_preimage] at hc ⊢
      exact h hc

private theorem card_boolIic (A : Finset (Fin r)) (y : Set.Iic A) :
    (boolIic A y).card = y.1.card := by
  have h := map_preimage_orderEmb y.2
  conv_rhs => rw [← h]
  rw [Finset.card_map]
  rfl

/-- `gapMultinomial` counts chains of subsets, in the form with an index function `s`. -/
theorem chainCount_finset_eq_gapMultinomial :
    ∀ {k : ℕ} (r : ℕ) (s : Fin k → ℕ), StrictMono s →
      chainCount (Finset.card : Finset (Fin r) → ℕ) s = gapMultinomial r (univ.image s) := by
  intro k
  induction k with
  | zero =>
    intro r s _
    rw [chainCount_zero, Finset.univ_eq_empty, Finset.image_empty]
    simp [gapMultinomial]
  | succ k ih =>
    intro r s hs
    have hne : (univ.image s).Nonempty := ⟨s 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hmax := image_max'_eq_last hs hne
    have herase := image_erase_last hs
    rw [chainCount_succ _ s hs, gapMultinomial]
    simp only [hne, ↓reduceDIte]
    rw [hmax, herase]
    have hstep : ∀ x ∈ (univ.filter fun x : Finset (Fin r) => x.card = s (Fin.last k) + 1),
        chainCountBelow (Finset.card : Finset (Fin r) → ℕ) (fun j : Fin k => s j.castSucc) x =
          gapMultinomial (s (Fin.last k) + 1) (univ.image (fun j : Fin k => s j.castSucc)) := by
      intro x hx
      have hx' : x.card = s (Fin.last k) + 1 := (Finset.mem_filter.1 hx).2
      rw [chainCountBelow_eq_of_orderIso _ _ x (boolIic x) (card_boolIic x),
        ih x.card (fun j : Fin k => s j.castSucc) (hs.comp Fin.strictMono_castSucc), hx']
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, smul_eq_mul]
    congr 1
    have : (univ.filter fun x : Finset (Fin r) => x.card = s (Fin.last k) + 1) =
        Finset.powersetCard (s (Fin.last k) + 1) univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
    rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end Bool

/-- Chains of subsets of an `r`-set with sizes `U + 1` are counted by `gapMultinomial r U`. -/
theorem card_boolChains (r : ℕ) (U : Finset ℕ) :
    (boolChains r U).card = gapMultinomial r U := by
  have h := chainCount_finset_eq_gapMultinomial r (U.orderEmbOfFin rfl)
    (U.orderEmbOfFin rfl).strictMono
  rw [Finset.image_orderEmbOfFin_univ] at h
  rw [← h]
  classical
  unfold boolChains chainCount
  congr

end RealRooted.HosterStump

end
