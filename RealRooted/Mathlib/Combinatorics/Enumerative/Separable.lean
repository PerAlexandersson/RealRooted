import RealRooted.Mathlib.Combinatorics.Enumerative.GenPoly
import RealRooted.Mathlib.Combinatorics.Enumerative.Pattern
import RealRooted.Mathlib.Combinatorics.Enumerative.PermStatistics
import RealRooted.Mathlib.Combinatorics.Enumerative.PermSum
import RealRooted.Mathlib.Combinatorics.Enumerative.PermSumDescent
import RealRooted.Mathlib.Combinatorics.Enumerative.PermSumPattern
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Separable permutations: sum decompositions and the descent recurrence

A permutation is separable when it avoids `2413` and `3142`.  A separable permutation of length
at least two is a direct or a skew sum of two shorter separable permutations.  We prove that a
permutation `σ` of `Fin (m + k)` whose prefix of length `m` carries exactly the smallest `m`
values is the direct sum of its two restricted blocks (the skew case is analogous), and that
separable permutations with a prescribed first direct (resp. skew) cut at `m` correspond
bijectively to pairs of a separable sum- (resp. skew-) indecomposable permutation of length `m`
and an arbitrary separable permutation of length `k`.  From the classical split lemma, taken as
an explicit hypothesis, we deduce the recurrence
`S_n = ∑_{k=1}^{n-1} P_k S_{n-k} + X ∑_{k=1}^{n-1} Q_k S_{n-k}`
for the descent enumerators of separable permutations (`S_n`), of separable
sum-indecomposable permutations (`P_n`) and of separable skew-indecomposable permutations
(`Q_n`).

The split lemma (a separable permutation of length at least two has a proper direct- or skew-sum
cut) was proved by Aristotle (Harmonic); `exists_hasSumCut_of_isSeparable` is its port, together
with the bridge between canonical pattern avoidance and the positional definition of avoidance.
The recurrence `separableDescentEnumerator_recurrence` is therefore unconditional.
-/

open scoped BigOperators Polynomial
open Polynomial

noncomputable section

namespace Equiv.Perm

/-- A proper direct-sum cut: the first `m` positions carry the smallest values. -/
def HasDirectSumCut {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) : Prop :=
  0 < m ∧ m < n ∧ ∀ i j : Fin n, i.val < m → m ≤ j.val → σ i < σ j

/-- A proper skew-sum cut: the first `m` positions carry the largest values. -/
def HasSkewSumCut {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) : Prop :=
  0 < m ∧ m < n ∧ ∀ i j : Fin n, i.val < m → m ≤ j.val → σ j < σ i

instance {n : ℕ} (σ : Perm (Fin n)) : DecidablePred (HasDirectSumCut σ) := fun m => by
  unfold HasDirectSumCut
  infer_instance

instance {n : ℕ} (σ : Perm (Fin n)) : DecidablePred (HasSkewSumCut σ) := fun m => by
  unfold HasSkewSumCut
  infer_instance

/-- Separable permutations are exactly the `2413`- and `3142`-avoiders. -/
def IsSeparable {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  σ.Avoids pattern2413 ∧ σ.Avoids pattern3142

instance {n : ℕ} : DecidablePred (IsSeparable (n := n)) := fun σ => by
  unfold IsSeparable
  infer_instance

/-- A permutation is sum-indecomposable when it has no proper direct-sum cut. -/
def IsSumIndecomposable {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  ∀ m < n, ¬HasDirectSumCut σ m

/-- A permutation is skew-indecomposable when it has no proper skew-sum cut. -/
def IsSkewIndecomposable {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  ∀ m < n, ¬HasSkewSumCut σ m

instance {n : ℕ} : DecidablePred (IsSumIndecomposable (n := n)) := fun σ => by
  unfold IsSumIndecomposable
  infer_instance

instance {n : ℕ} : DecidablePred (IsSkewIndecomposable (n := n)) := fun σ => by
  unfold IsSkewIndecomposable
  infer_instance

/-- A cut `m` is the first direct-sum cut when it is the smallest one. -/
def IsFirstSumCut {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) : Prop :=
  HasDirectSumCut σ m ∧ ∀ c, HasDirectSumCut σ c → m ≤ c

/-- A cut `m` is the first skew-sum cut when it is the smallest one. -/
def IsFirstSkewCut {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) : Prop :=
  HasSkewSumCut σ m ∧ ∀ c, HasSkewSumCut σ c → m ≤ c

/-- The first direct-sum cut is unique. -/
theorem IsFirstSumCut.unique {n : ℕ} {σ : Perm (Fin n)} {m k : ℕ}
    (hm : IsFirstSumCut σ m) (hk : IsFirstSumCut σ k) : m = k :=
  Nat.le_antisymm (hm.2 k hk.1) (hk.2 m hm.1)

/-- The first skew-sum cut is unique. -/
theorem IsFirstSkewCut.unique {n : ℕ} {σ : Perm (Fin n)} {m k : ℕ}
    (hm : IsFirstSkewCut σ m) (hk : IsFirstSkewCut σ k) : m = k :=
  Nat.le_antisymm (hm.2 k hk.1) (hk.2 m hm.1)

/-- A permutation of length at least two cannot have both a direct and a skew proper cut. -/
theorem not_hasSkewSumCut_of_hasDirectSumCut {n m m' : ℕ} {σ : Perm (Fin n)}
    (hd : HasDirectSumCut σ m) (hs : HasSkewSumCut σ m') : False := by
  have hj : max m m' < n := max_lt hd.2.1 hs.2.1
  have h1 := hd.2.2 ⟨0, by lia⟩ ⟨max m m', hj⟩ (by simpa using hd.1) (le_max_left _ _)
  have h2 := hs.2.2 ⟨0, by lia⟩ ⟨max m m', hj⟩ (by simpa using hs.1) (le_max_right _ _)
  exact lt_asymm h1 h2

/-- Complement exchanges direct-sum and skew-sum cuts. -/
theorem hasDirectSumCut_complement_iff {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :
    HasDirectSumCut (complement σ) m ↔ HasSkewSumCut σ m := by
  constructor
  · rintro ⟨hm, hn, h⟩
    refine ⟨hm, hn, fun i j hi hj => ?_⟩
    simpa only [complement, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev] using
      h i j hi hj
  · rintro ⟨hm, hn, h⟩
    refine ⟨hm, hn, fun i j hi hj => ?_⟩
    simpa only [complement, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_lt_rev] using
      h i j hi hj

/-- Complement exchanges skew-sum and direct-sum cuts. -/
theorem hasSkewSumCut_complement_iff {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :
    HasSkewSumCut (complement σ) m ↔ HasDirectSumCut σ m := by
  rw [← hasDirectSumCut_complement_iff (complement σ) m, complement_complement]

/-- Complement exchanges the two forbidden patterns. -/
theorem complement_pattern2413 : complement pattern2413 = pattern3142 := by
  decide

/-- Complement exchanges the two forbidden patterns. -/
theorem complement_pattern3142 : complement pattern3142 = pattern2413 := by
  decide

/-- Complement preserves separability. -/
theorem isSeparable_complement_iff {n : ℕ} (σ : Perm (Fin n)) :
    IsSeparable (complement σ) ↔ IsSeparable σ := by
  constructor
  · intro h
    refine ⟨fun hc => h.2 ?_, fun hc => h.1 ?_⟩
    · rw [← complement_pattern2413]
      exact (containsPattern_complement_iff σ pattern2413).mp hc
    · rw [← complement_pattern3142]
      exact (containsPattern_complement_iff σ pattern3142).mp hc
  · intro h
    refine ⟨fun hc => h.2 ?_, fun hc => h.1 ?_⟩
    · rw [← complement_pattern3142] at hc
      exact (containsPattern_complement_iff σ pattern3142).mpr hc
    · rw [← complement_pattern2413] at hc
      exact (containsPattern_complement_iff σ pattern2413).mpr hc

/-- Complement exchanges sum- and skew-indecomposability. -/
theorem isSumIndecomposable_complement_iff {n : ℕ} (σ : Perm (Fin n)) :
    IsSumIndecomposable (complement σ) ↔ IsSkewIndecomposable σ :=
  forall₂_congr fun m _ => not_congr (hasDirectSumCut_complement_iff σ m)

/-- Complement exchanges skew- and sum-indecomposability. -/
theorem isSkewIndecomposable_complement_iff {n : ℕ} (σ : Perm (Fin n)) :
    IsSkewIndecomposable (complement σ) ↔ IsSumIndecomposable σ :=
  forall₂_congr fun m _ => not_congr (hasSkewSumCut_complement_iff σ m)

/-- Complement exchanges first direct-sum and first skew-sum cuts. -/
theorem isFirstSumCut_complement_iff {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) :
    IsFirstSumCut (complement σ) m ↔ IsFirstSkewCut σ m := by
  unfold IsFirstSumCut IsFirstSkewCut
  simp only [hasDirectSumCut_complement_iff]

/-- Complement reverses the descent number. -/
theorem descentCount_complement {n : ℕ} (σ : Perm (Fin n)) :
    (complement σ).descentCount = n - 1 - σ.descentCount := by
  have h := descentCount_add_ascentCount σ
  rw [descentCount, descentSet_complement]
  change σ.descentCount + σ.ascentSet.card = n - 1 at h
  lia

/-! ### Realization of cuts -/

/-- The first block of a permutation with a direct-sum cut stays below the cut. -/
private theorem val_lt_of_hasDirectSumCut {n m : ℕ} {σ : Perm (Fin n)}
    (h : HasDirectSumCut σ m) {i : Fin n} (hi : i.val < m) : (σ i).val < m := by
  by_contra hcon
  push Not at hcon
  let a : Fin n := ⟨m, h.2.1⟩
  have hsub : (insert i (Finset.Ici a)).image σ ⊆ Finset.Ici a := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_Ici.mpr (Fin.le_def.mpr hcon)
    · have hj' : m ≤ j.val := Fin.le_def.mp (Finset.mem_Ici.mp hj)
      have := h.2.2 i j hi hj'
      exact Finset.mem_Ici.mpr (Fin.le_def.mpr (by rw [Fin.lt_def] at this; lia))
  have hi' : i ∉ Finset.Ici a := fun hmem => by
    have := Fin.le_def.mp (Finset.mem_Ici.mp hmem)
    lia
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ σ.injective, Finset.card_insert_of_notMem hi',
    Fin.card_Ici] at hcard
  lia

/-- A permutation of `Fin (m + k)` with a direct-sum cut at `m` is a direct sum of its blocks. -/
theorem exists_eq_directSum_of_hasDirectSumCut {m k : ℕ} {σ : Perm (Fin (m + k))}
    (h : HasDirectSumCut σ m) :
    ∃ (a : Perm (Fin m)) (b : Perm (Fin k)), σ = directSum a b := by
  have hlt : ∀ i : Fin m, (σ (Fin.castAdd k i)).val < m := fun i =>
    val_lt_of_hasDirectSumCut h (by simp)
  let f : Fin m → Fin m := fun i => ⟨(σ (Fin.castAdd k i)).val, hlt i⟩
  have hf : Function.Injective f := by
    intro i i' hii
    have hv : (f i).val = (f i').val := congrArg Fin.val hii
    have : σ (Fin.castAdd k i) = σ (Fin.castAdd k i') := Fin.ext hv
    exact Fin.castAdd_injective m k (σ.injective this)
  let a : Perm (Fin m) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hge : ∀ j : Fin k, m ≤ (σ (Fin.natAdd m j)).val := by
    intro j
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := a.surjective ⟨(σ (Fin.natAdd m j)).val, hcon⟩
    have hv : (a i).val = (σ (Fin.natAdd m j)).val := congrArg Fin.val hi
    have hi' : σ (Fin.castAdd k i) = σ (Fin.natAdd m j) := Fin.ext hv
    have := congrArg Fin.val (σ.injective hi')
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    have := i.isLt
    lia
  have hlt' : ∀ j : Fin k, (σ (Fin.natAdd m j)).val - m < k := fun j => by
    have := (σ (Fin.natAdd m j)).isLt
    have := hge j
    have := j.isLt
    lia
  let g : Fin k → Fin k := fun j => ⟨(σ (Fin.natAdd m j)).val - m, hlt' j⟩
  have hg : Function.Injective g := by
    intro j j' hjj
    have h1 := hge j
    have h2 := hge j'
    have hv : (σ (Fin.natAdd m j)).val = (σ (Fin.natAdd m j')).val := by
      have := congrArg Fin.val hjj
      change (σ (Fin.natAdd m j)).val - m = (σ (Fin.natAdd m j')).val - m at this
      lia
    exact Fin.natAdd_injective k m (σ.injective (Fin.ext hv))
  let b : Perm (Fin k) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  refine ⟨a, b, Equiv.ext fun x => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · rw [directSum_apply_left]
    exact Fin.ext (by simp [a, f])
  · rw [directSum_apply_right]
    have := hge j
    refine Fin.ext ?_
    simp only [Fin.val_natAdd, b, g, Equiv.ofBijective_apply]
    lia

/-- A permutation of `Fin (m + k)` with a skew-sum cut at `m` is a skew sum of its blocks. -/
theorem exists_eq_skewSum_of_hasSkewSumCut {m k : ℕ} {σ : Perm (Fin (m + k))}
    (h : HasSkewSumCut σ m) :
    ∃ (a : Perm (Fin m)) (b : Perm (Fin k)), σ = skewSum a b := by
  obtain ⟨a, b, hab⟩ := exists_eq_directSum_of_hasDirectSumCut
    ((hasDirectSumCut_complement_iff σ m).mpr h)
  refine ⟨complement a, complement b, ?_⟩
  rw [skewSum, complement_complement, complement_complement, ← hab, complement_complement]

/-! ### Separable permutations have a cut -/

section Occurrence

variable {n k : ℕ}

private def HasOccurrence (σ : Perm (Fin n)) (τ : Perm (Fin k)) : Prop :=
  ∃ e : Fin k ↪o Fin n, ∀ i j, σ (e i) < σ (e j) ↔ τ i < τ j

private theorem containsPattern_iff_hasOccurrence (σ : Perm (Fin n)) (τ : Perm (Fin k)) :
    σ.ContainsPattern τ ↔ HasOccurrence σ τ := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := (Equiv.Perm.containsPattern_iff σ τ).mp h
    obtain ⟨e₀, he₀⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
    have hlen : s.length = (List.ofFn τ).length := List.sameOrderType_length hst
    have hlenSk : s.length = k := hlen.trans List.length_ofFn
    let e₁ : Fin k ↪o Fin s.length := (Fin.castOrderIso hlenSk.symm).toOrderEmbedding
    let e₂ : Fin (List.ofFn σ).length ↪o Fin n :=
      (Fin.castOrderIso List.length_ofFn).toOrderEmbedding
    let e : Fin k ↪o Fin n := e₁.trans (e₀.trans e₂)
    refine ⟨e, ?_⟩
    have hst' : ∀ a b : Fin s.length,
        s.get a < s.get b ↔ (List.ofFn τ).get (Fin.cast hlen a) <
          (List.ofFn τ).get (Fin.cast hlen b) := by
      unfold List.SameOrderType List.sameOrderTypeBool at hst
      simp only [dite_eq_left hlen] at hst
      exact of_decide_eq_true hst
    intro i j
    have hrel := hst' (e₁ i) (e₁ j)
    have hei := he₀ (e₁ i)
    have hej := he₀ (e₁ j)
    have hcastσ (a : Fin (List.ofFn σ).length) :
        (Fin.castOrderIso List.length_ofFn).toOrderEmbedding a =
          Fin.cast List.length_ofFn a := by
      rfl
    calc
      σ (e i) < σ (e j) ↔
          (List.ofFn σ).get (e₀ (e₁ i)) < (List.ofFn σ).get (e₀ (e₁ j)) := by
        simp only [e, e₂, RelEmbedding.trans_apply, List.get_ofFn]
        rw [hcastσ, hcastσ]
      _ ↔ s.get (e₁ i) < s.get (e₁ j) := by rw [hei, hej]
      _ ↔ (List.ofFn τ).get (Fin.cast hlen (e₁ i)) <
          (List.ofFn τ).get (Fin.cast hlen (e₁ j)) := hrel
      _ ↔ τ i < τ j := by
        simp only [List.get_ofFn]
        rfl
  · rintro ⟨e, he⟩
    let s : List (Fin n) := List.ofFn (fun i => σ (e i))
    have hlenSk : s.length = k := by simp only [s, List.length_ofFn]
    let e₁ : Fin s.length ↪o Fin k := (Fin.castOrderIso hlenSk).toOrderEmbedding
    let e₀ : Fin s.length ↪o Fin (List.ofFn σ).length :=
      e₁.trans (e.trans (Fin.castOrderIso List.length_ofFn.symm).toOrderEmbedding)
    have hs : List.Sublist s (List.ofFn σ) := by
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨e₀, ?_⟩
      intro i
      change (List.ofFn (fun j => σ (e j))).get i = (List.ofFn σ).get (e₀ i)
      simp only [List.get_ofFn]
      rfl
    have hst : s.SameOrderType (List.ofFn τ) := by
      unfold List.SameOrderType List.sameOrderTypeBool
      simp only [s, List.length_ofFn, ↓reduceDIte]
      apply decide_eq_true
      intro i j
      simp only [List.get_ofFn]
      convert he (Fin.cast hlenSk i) (Fin.cast hlenSk j) using 1; rfl
    exact (Equiv.Perm.containsPattern_iff σ τ).mpr ⟨s, hs, hst⟩

end Occurrence

/-- `σ` avoids `2413` in terms of positions: there are no positions `i < j < k < l` with
`σ k < σ i < σ l < σ j`. -/
private def Avoids2413Pos {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  ∀ i j k l : Fin n, i < j → j < k → k < l → ¬(σ k < σ i ∧ σ i < σ l ∧ σ l < σ j)

/-- `σ` avoids `3142` in terms of positions: there are no positions `i < j < k < l` with
`σ j < σ l < σ i < σ k`. -/
private def Avoids3142Pos {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  ∀ i j k l : Fin n, i < j → j < k → k < l → ¬(σ j < σ l ∧ σ l < σ i ∧ σ i < σ k)

/-- A split of a permutation after its first `m` positions, direct or skew. -/
private def SplitsAtPos {n : ℕ} (σ : Perm (Fin n)) (m : ℕ) : Prop :=
  (∀ i j : Fin n, i.val < m → m ≤ j.val → σ i < σ j) ∨
    (∀ i j : Fin n, i.val < m → m ≤ j.val → σ j < σ i)

private theorem avoids_pattern2413_iff {n : ℕ} (σ : Perm (Fin n)) :
    σ.Avoids pattern2413 ↔ Avoids2413Pos σ := by
  unfold Avoids Avoids2413Pos
  rw [containsPattern_iff_hasOccurrence]
  constructor
  · intro hav i j k l hij hjk hkl hrel
    apply hav
    let f : Fin 4 → Fin n := ![i, j, k, l]
    have hf : StrictMono f := by
      rw [Fin.strictMono_iff_lt_succ]
      intro a
      fin_cases a
      · exact hij
      · exact hjk
      · exact hkl
    refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hrel
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.isValue, OrderEmbedding.coe_ofStrictMono, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      pattern2413, coe_fn_mk, Fin.reduceLT, iff_true, iff_false, not_lt, not_lt_zero,
      lt_self_iff_false, f] <;> grind
  · rintro hav ⟨e, he⟩
    have h1 := (he 2 0).mpr (by decide)
    have h2 := (he 0 3).mpr (by decide)
    have h3 := (he 3 1).mpr (by decide)
    exact hav (e 0) (e 1) (e 2) (e 3) (e.lt_iff_lt.mpr (by decide)) (e.lt_iff_lt.mpr (by decide))
      (e.lt_iff_lt.mpr (by decide)) ⟨h1, h2, h3⟩


private theorem avoids_pattern3142_iff {n : ℕ} (σ : Perm (Fin n)) :
    σ.Avoids pattern3142 ↔ Avoids3142Pos σ := by
  unfold Avoids Avoids3142Pos
  rw [containsPattern_iff_hasOccurrence]
  constructor
  · intro hav i j k l hij hjk hkl hrel
    apply hav
    let f : Fin 4 → Fin n := ![i, j, k, l]
    have hf : StrictMono f := by
      rw [Fin.strictMono_iff_lt_succ]
      intro a
      fin_cases a
      · exact hij
      · exact hjk
      · exact hkl
    refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
    obtain ⟨h1, h2, h3⟩ := hrel
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.isValue, OrderEmbedding.coe_ofStrictMono, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      pattern3142, coe_fn_mk, Fin.reduceLT, iff_true, iff_false, not_lt, not_lt_zero,
      lt_self_iff_false, f] <;> grind
  · rintro hav ⟨e, he⟩
    have h1 := (he 1 3).mpr (by decide)
    have h2 := (he 3 0).mpr (by decide)
    have h3 := (he 0 2).mpr (by decide)
    exact hav (e 0) (e 1) (e 2) (e 3) (e.lt_iff_lt.mpr (by decide)) (e.lt_iff_lt.mpr (by decide))
      (e.lt_iff_lt.mpr (by decide)) ⟨h1, h2, h3⟩


/-- A split of the prefix `[0, N)` of a sequence `f`. -/
private def SplitP {α : Type*} [LinearOrder α] (f : ℕ → α) (N m : ℕ) : Prop :=
  (∀ i j, i < m → m ≤ j → j < N → f i < f j) ∨
    (∀ i j, i < m → m ≤ j → j < N → f j < f i)

private theorem step_sum {α : Type*} [LinearOrder α] (f : ℕ → α) (n : ℕ)
    (hinj : ∀ i j, i < n + 1 → j < n + 1 → f i = f j → i = j)
    (h3142 : ∀ i j k l, i < j → j < k → k < l → l < n + 1 →
      ¬ (f j < f l ∧ f l < f i ∧ f i < f k))
    (m : ℕ) (hm : 0 < m) (hmn : m < n)
    (hsum : ∀ i j, i < m → m ≤ j → j < n → f i < f j) :
    ∃ m', 0 < m' ∧ m' < n + 1 ∧ SplitP f (n + 1) m' := by
  have hne : ∀ i, i < n → f i ≠ f n := fun i hi h => by
    have := hinj i n (by lia) (by lia) h; lia
  by_cases hA : ∀ i, i < m → f i < f n
  · refine ⟨m, hm, by lia, Or.inl fun i j hi hj hjn => ?_⟩
    rcases Nat.lt_or_ge j n with h | h
    · exact hsum i j hi hj h
    · obtain rfl : j = n := by lia
      exact hA i hi
  push Not at hA
  obtain ⟨a, ha, hax⟩ := hA
  have hax' : f n < f a := lt_of_le_of_ne hax (fun h => hne a (by lia) h.symm)
  by_cases hH : ∀ i, i < m → f n < f i
  · refine ⟨n, by lia, by lia, Or.inr fun i j hi hj hjn => ?_⟩
    obtain rfl : j = n := by lia
    rcases Nat.lt_or_ge i m with h | h
    · exact hH i h
    · exact lt_trans hax' (hsum a i ha h hi)
  push Not at hH
  obtain ⟨b, hb, hbx⟩ := hH
  have hbx' : f b < f n := lt_of_le_of_ne hbx (hne b (by lia))
  by_cases hP : ∃ i j, i < j ∧ j < m ∧ f n < f i ∧ f j < f n
  · obtain ⟨i, j, hij, hjm, hi, hj⟩ := hP
    exact absurd ⟨hj, hi, hsum i m (by lia) le_rfl hmn⟩
      (h3142 i j m n hij (by lia) hmn (by lia))
  push Not at hP
  have hex : ∃ i, f n < f i ∧ i < m := ⟨a, hax', ha⟩
  classical
  let m' := Nat.find hex
  have hm'1 : f n < f m' ∧ m' < m := Nat.find_spec hex
  have hm'2 : ∀ i, i < m' → ¬ (f n < f i ∧ i < m) := fun i hi => Nat.find_min hex hi
  have hlow : ∀ i, i < m' → f i < f n := by
    intro i hi
    have h1 : ¬ f n < f i := fun h => hm'2 i hi ⟨h, by lia⟩
    exact lt_of_le_of_ne (not_lt.mp h1) (hne i (by lia))
  have hbm : b < m' := by
    by_contra hc
    rcases Nat.lt_or_ge m' b with h | h
    · exact absurd hbx' (not_lt.mpr (hP m' b h hb hm'1.1))
    · obtain rfl : b = m' := by lia
      exact absurd hm'1.1 (not_lt.mpr hbx'.le)
  refine ⟨m', by lia, by lia, Or.inl fun i j hi hj hjn => ?_⟩
  rcases Nat.lt_or_ge j m with h | h
  · rcases Nat.lt_or_ge m' j with h' | h'
    · have : f n ≤ f j := hP m' j h' h hm'1.1
      exact lt_of_lt_of_le (hlow i hi) this
    · obtain rfl : j = m' := by lia
      exact lt_trans (hlow i hi) hm'1.1
  · rcases Nat.lt_or_ge j n with h' | h'
    · exact hsum i j (by lia) h h'
    · obtain rfl : j = n := by lia
      exact hlow i hi

private theorem main_aux {α : Type*} [LinearOrder α] (f : ℕ → α) (N : ℕ) (hN : 2 ≤ N)
    (hinj : ∀ i j, i < N → j < N → f i = f j → i = j)
    (h2413 : ∀ i j k l, i < j → j < k → k < l → l < N →
      ¬ (f k < f i ∧ f i < f l ∧ f l < f j))
    (h3142 : ∀ i j k l, i < j → j < k → k < l → l < N →
      ¬ (f j < f l ∧ f l < f i ∧ f i < f k)) :
    ∃ m, 0 < m ∧ m < N ∧ SplitP f N m := by
  induction N, hN using Nat.le_induction generalizing α with
  | base =>
    refine ⟨1, by lia, by lia, ?_⟩
    have h01 : f 0 ≠ f 1 := fun h => by have := hinj 0 1 (by lia) (by lia) h; lia
    rcases lt_or_gt_of_ne h01 with h | h
    · left; intro i j hi hj hjn
      obtain rfl : i = 0 := by lia
      obtain rfl : j = 1 := by lia
      exact h
    · right; intro i j hi hj hjn
      obtain rfl : i = 0 := by lia
      obtain rfl : j = 1 := by lia
      exact h
  | succ n hn ih =>
    obtain ⟨m, hm, hmn, hs⟩ := ih f (fun i j hi hj => hinj i j (by lia) (by lia))
      (fun i j k l a b c d => h2413 i j k l a b c (by lia))
      (fun i j k l a b c d => h3142 i j k l a b c (by lia))
    rcases hs with hs | hs
    · exact step_sum f n hinj h3142 m hm hmn hs
    · obtain ⟨m', h1, h2, h3⟩ := step_sum (fun i => OrderDual.toDual (f i)) n
        (fun i j hi hj h => hinj i j hi hj (by simpa using h))
        (fun i j k l a b c d => by
          simpa [and_comm, and_left_comm, and_assoc] using h2413 i j k l a b c d)
        m hm hmn (fun i j a b c => by simpa using hs i j a b c)
      refine ⟨m', h1, h2, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inr fun i j a b c => by simpa using h3 i j a b c
      · exact Or.inl fun i j a b c => by simpa using h3 i j a b c

/-- Every separable permutation (avoiding 2413 and 3142) of length at least two is a direct sum or
a skew sum of two nonempty blocks.  Classical: a permutation of length ≥ 2 that is both sum- and
skew-indecomposable contains 2413 or 3142. -/
private theorem exists_splitsAt (n : ℕ) (hn : 2 ≤ n) (σ : Perm (Fin n))
    (h1 : Avoids2413Pos σ) (h2 : Avoids3142Pos σ) :
    ∃ m, 0 < m ∧ m < n ∧ SplitsAtPos σ m := by
  let f : ℕ → ℕ := fun i => if h : i < n then (σ ⟨i, h⟩).val else 0
  have hf : ∀ i : Fin n, f i.val = (σ i).val := fun i => by simp [f, i.isLt]
  obtain ⟨m, hm, hmn, hs⟩ := main_aux f n hn
    (fun i j hi hj h => by
      have e1 : f i = (σ ⟨i, hi⟩).val := hf ⟨i, hi⟩
      have e2 : f j = (σ ⟨j, hj⟩).val := hf ⟨j, hj⟩
      have : σ ⟨i, hi⟩ = σ ⟨j, hj⟩ := Fin.ext (by lia)
      simpa using σ.injective this)
    (fun i j k l a b c d => by
      have := h1 ⟨i, by lia⟩ ⟨j, by lia⟩ ⟨k, by lia⟩ ⟨l, d⟩ a b c
      simpa [Fin.lt_def, ← hf] using this)
    (fun i j k l a b c d => by
      have := h2 ⟨i, by lia⟩ ⟨j, by lia⟩ ⟨k, by lia⟩ ⟨l, d⟩ a b c
      simpa [Fin.lt_def, ← hf] using this)
  refine ⟨m, hm, hmn, ?_⟩
  rcases hs with hs | hs
  · exact Or.inl fun i j hi hj => by
      have := hs i j hi hj j.isLt; rw [hf, hf] at this; exact this
  · exact Or.inr fun i j hi hj => by
      have := hs i j hi hj j.isLt; rw [hf, hf] at this; exact this


/-- A separable permutation of length at least two has a proper direct-sum or skew-sum cut.

This is the classical fact that a permutation of length at least two avoiding `2413` and `3142`
is a direct or skew sum of two nonempty blocks.  The proof, by induction on the length, was
found by Aristotle (Harmonic). -/
theorem exists_hasSumCut_of_isSeparable {n : ℕ} (hn : 2 ≤ n) {σ : Perm (Fin n)}
    (h : IsSeparable σ) :
    ∃ m, 0 < m ∧ m < n ∧ (HasDirectSumCut σ m ∨ HasSkewSumCut σ m) := by
  obtain ⟨m, hm, hmn, hs⟩ := exists_splitsAt n hn σ ((avoids_pattern2413_iff σ).mp h.1)
    ((avoids_pattern3142_iff σ).mp h.2)
  exact ⟨m, hm, hmn, hs.imp (fun h => ⟨hm, hmn, h⟩) (fun h => ⟨hm, hmn, h⟩)⟩


/-! ### Finite sets and enumerators -/

/-- The finite set of separable permutations of `Fin n`. -/
def separablePermutations (n : ℕ) : Finset (Perm (Fin n)) :=
  Finset.univ.filter IsSeparable

/-- The finite set of separable sum-indecomposable permutations of `Fin n`. -/
def separableSumIndecomposables (n : ℕ) : Finset (Perm (Fin n)) :=
  (separablePermutations n).filter IsSumIndecomposable

/-- The finite set of separable skew-indecomposable permutations of `Fin n`. -/
def separableSkewIndecomposables (n : ℕ) : Finset (Perm (Fin n)) :=
  (separablePermutations n).filter IsSkewIndecomposable

/-- Membership in the set of separable permutations. -/
@[simp]
theorem mem_separablePermutations {n : ℕ} {σ : Perm (Fin n)} :
    σ ∈ separablePermutations n ↔ IsSeparable σ := by
  simp only [separablePermutations, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Membership in the set of separable sum-indecomposable permutations. -/
@[simp]
theorem mem_separableSumIndecomposables {n : ℕ} {σ : Perm (Fin n)} :
    σ ∈ separableSumIndecomposables n ↔ IsSeparable σ ∧ IsSumIndecomposable σ := by
  simp only [separableSumIndecomposables, Finset.mem_filter, mem_separablePermutations]

/-- Membership in the set of separable skew-indecomposable permutations. -/
@[simp]
theorem mem_separableSkewIndecomposables {n : ℕ} {σ : Perm (Fin n)} :
    σ ∈ separableSkewIndecomposables n ↔ IsSeparable σ ∧ IsSkewIndecomposable σ := by
  simp only [separableSkewIndecomposables, Finset.mem_filter, mem_separablePermutations]

/-- The descent enumerator of the separable permutations of `Fin n`. -/
def separableDescentEnumerator (R : Type*) [CommSemiring R] (n : ℕ) : R[X] :=
  Finset.genPoly (separablePermutations n) descentCount

/-- The descent enumerator of the separable sum-indecomposable permutations of `Fin n`. -/
def separableSumIndecomposableEnumerator (R : Type*) [CommSemiring R] (n : ℕ) : R[X] :=
  Finset.genPoly (separableSumIndecomposables n) descentCount

/-- The descent enumerator of the separable skew-indecomposable permutations of `Fin n`. -/
def separableSkewIndecomposableEnumerator (R : Type*) [CommSemiring R] (n : ℕ) : R[X] :=
  Finset.genPoly (separableSkewIndecomposables n) descentCount

/-! ### Direct and skew sums: injectivity, cuts, separability -/

private theorem directSum_inj {m k : ℕ} {a a' : Perm (Fin m)} {b b' : Perm (Fin k)}
    (h : directSum a b = directSum a' b') : a = a' ∧ b = b' := by
  refine ⟨Equiv.ext fun i => ?_, Equiv.ext fun j => ?_⟩
  · have := congrArg (fun f => f (Fin.castAdd k i)) h
    simp only [directSum_apply_left] at this
    exact Fin.castAdd_injective m k this
  · have := congrArg (fun f => f (Fin.natAdd m j)) h
    simp only [directSum_apply_right] at this
    exact Fin.natAdd_injective k m this

private theorem skewSum_inj {m k : ℕ} {a a' : Perm (Fin m)} {b b' : Perm (Fin k)}
    (h : skewSum a b = skewSum a' b') : a = a' ∧ b = b' := by
  have h' := congrArg complement h
  rw [skewSum, skewSum, complement_complement, complement_complement] at h'
  obtain ⟨h1, h2⟩ := directSum_inj h'
  have h1' := congrArg complement h1
  have h2' := congrArg complement h2
  rw [complement_complement, complement_complement] at h1' h2'
  exact ⟨h1', h2'⟩

private theorem isSeparable_directSum_iff {m k : ℕ} (a : Perm (Fin m)) (b : Perm (Fin k)) :
    IsSeparable (directSum a b) ↔ IsSeparable a ∧ IsSeparable b := by
  unfold IsSeparable
  rw [directSum_avoids_pattern2413_iff, directSum_avoids_pattern3142_iff]
  tauto

private theorem hasDirectSumCut_directSum {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : Perm (Fin m)) (b : Perm (Fin k)) : HasDirectSumCut (directSum a b) m := by
  refine ⟨hm, by lia, fun i j hi hj => ?_⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.castAdd k i' := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = Fin.natAdd m j' :=
    ⟨⟨j.val - m, by have := j.isLt; lia⟩, Fin.ext (by rw [Fin.val_natAdd]; lia)⟩
  rw [directSum_apply_left, directSum_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  have := (a i').isLt
  lia

private theorem hasDirectSumCut_directSum_left {m k c : ℕ} {a : Perm (Fin m)}
    (b : Perm (Fin k)) (h : HasDirectSumCut a c) : HasDirectSumCut (directSum a b) c := by
  have hcm := h.2.1
  refine ⟨h.1, by lia, fun i j hi hj => ?_⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = Fin.castAdd k i' := ⟨⟨i.val, by lia⟩, Fin.ext rfl⟩
  rw [directSum_apply_left]
  rcases lt_or_ge j.val m with hjm | hjm
  · obtain ⟨j', rfl⟩ : ∃ j', j = Fin.castAdd k j' := ⟨⟨j.val, hjm⟩, Fin.ext rfl⟩
    rw [directSum_apply_left, Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd]
    exact Fin.lt_def.mp (h.2.2 i' j' hi hj)
  · obtain ⟨j', rfl⟩ : ∃ j', j = Fin.natAdd m j' :=
      ⟨⟨j.val - m, by have := j.isLt; lia⟩, Fin.ext (by rw [Fin.val_natAdd]; lia)⟩
    rw [directSum_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    have := (a i').isLt
    lia

private theorem isSeparable_and_isFirstSumCut_iff {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (σ : Perm (Fin (m + k))) :
    (IsSeparable σ ∧ IsFirstSumCut σ m) ↔
      ∃ (a : Perm (Fin m)) (b : Perm (Fin k)),
        ((IsSeparable a ∧ IsSumIndecomposable a) ∧ IsSeparable b) ∧ directSum a b = σ := by
  constructor
  · rintro ⟨hsep, hcut, hmin⟩
    obtain ⟨a, b, rfl⟩ := exists_eq_directSum_of_hasDirectSumCut hcut
    obtain ⟨ha, hb⟩ := (isSeparable_directSum_iff a b).mp hsep
    refine ⟨a, b, ⟨⟨ha, fun c hc hcut' => ?_⟩, hb⟩, rfl⟩
    have := hmin c (hasDirectSumCut_directSum_left b hcut')
    lia
  · rintro ⟨a, b, ⟨⟨ha, hai⟩, hb⟩, rfl⟩
    refine ⟨(isSeparable_directSum_iff a b).mpr ⟨ha, hb⟩,
      hasDirectSumCut_directSum hm hk a b, fun c hc => ?_⟩
    by_contra hlt
    push Not at hlt
    refine hai c hlt ⟨hc.1, hlt, fun i j hi hj => ?_⟩
    have := hc.2.2 (Fin.castAdd k i) (Fin.castAdd k j) hi hj
    rw [directSum_apply_left, directSum_apply_left, Fin.lt_def, Fin.val_castAdd,
      Fin.val_castAdd] at this
    exact Fin.lt_def.mpr this

private theorem isSeparable_and_isFirstSkewCut_iff {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (σ : Perm (Fin (m + k))) :
    (IsSeparable σ ∧ IsFirstSkewCut σ m) ↔
      ∃ (a : Perm (Fin m)) (b : Perm (Fin k)),
        ((IsSeparable a ∧ IsSkewIndecomposable a) ∧ IsSeparable b) ∧ skewSum a b = σ := by
  rw [← isSeparable_complement_iff σ, ← isFirstSumCut_complement_iff σ m,
    isSeparable_and_isFirstSumCut_iff hm hk]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hai⟩, hb⟩, hab⟩
    refine ⟨complement a, complement b, ⟨⟨(isSeparable_complement_iff a).mpr ha,
      (isSkewIndecomposable_complement_iff a).mpr hai⟩, (isSeparable_complement_iff b).mpr hb⟩,
      ?_⟩
    rw [skewSum, complement_complement, complement_complement, hab, complement_complement]
  · rintro ⟨a, b, ⟨⟨ha, hai⟩, hb⟩, rfl⟩
    refine ⟨complement a, complement b, ⟨⟨(isSeparable_complement_iff a).mpr ha,
      (isSumIndecomposable_complement_iff a).mpr hai⟩, (isSeparable_complement_iff b).mpr hb⟩,
      ?_⟩
    rw [skewSum, complement_complement]

/-! ### Generating polynomials of sums -/

private theorem genPoly_image_directSum {R : Type*} [CommSemiring R] {m k : ℕ} (hk : 0 < k)
    (A : Finset (Perm (Fin m))) (B : Finset (Perm (Fin k))) :
    Finset.genPoly (R := R) ((A ×ˢ B).image fun p => directSum p.1 p.2) descentCount =
      Finset.genPoly (R := R) A descentCount * Finset.genPoly (R := R) B descentCount := by
  rw [← Finset.genPoly_product]
  unfold Finset.genPoly
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [descentCount_directSum _ _ hk]
  · intro p _ q _ h
    obtain ⟨h1, h2⟩ := directSum_inj h
    exact Prod.ext h1 h2

private theorem genPoly_image_skewSum {R : Type*} [CommSemiring R] {m k : ℕ} (hm : 0 < m)
    (hk : 0 < k) (A : Finset (Perm (Fin m))) (B : Finset (Perm (Fin k))) :
    Finset.genPoly (R := R) ((A ×ˢ B).image fun p => skewSum p.1 p.2) descentCount =
      X * (Finset.genPoly (R := R) A descentCount * Finset.genPoly (R := R) B descentCount) := by
  rw [← Finset.genPoly_product]
  unfold Finset.genPoly
  rw [Finset.sum_image, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [descentCount_skewSum _ _ hm hk]
    ring
  · intro p _ q _ h
    obtain ⟨h1, h2⟩ := skewSum_inj h
    exact Prod.ext h1 h2

open scoped Classical in
/-- Separable permutations whose first direct-sum cut is at `m`. -/
private def directFirst (n m : ℕ) : Finset (Perm (Fin n)) :=
  (separablePermutations n).filter fun σ => IsFirstSumCut σ m

open scoped Classical in
/-- Separable permutations whose first skew-sum cut is at `m`. -/
private def skewFirst (n m : ℕ) : Finset (Perm (Fin n)) :=
  (separablePermutations n).filter fun σ => IsFirstSkewCut σ m

private theorem mem_directFirst {n m : ℕ} {σ : Perm (Fin n)} :
    σ ∈ directFirst n m ↔ IsSeparable σ ∧ IsFirstSumCut σ m := by
  simp only [directFirst, Finset.mem_filter, mem_separablePermutations]

private theorem mem_skewFirst {n m : ℕ} {σ : Perm (Fin n)} :
    σ ∈ skewFirst n m ↔ IsSeparable σ ∧ IsFirstSkewCut σ m := by
  simp only [skewFirst, Finset.mem_filter, mem_separablePermutations]

private theorem genPoly_directFirst_add {R : Type*} [CommSemiring R] {m k : ℕ} (hm : 0 < m)
    (hk : 0 < k) :
    Finset.genPoly (R := R) (directFirst (m + k) m) descentCount =
      separableSumIndecomposableEnumerator R m * separableDescentEnumerator R k := by
  have : directFirst (m + k) m =
      (separableSumIndecomposables m ×ˢ separablePermutations k).image
        fun p => directSum p.1 p.2 := by
    ext σ
    rw [mem_directFirst, isSeparable_and_isFirstSumCut_iff hm hk, Finset.mem_image]
    simp only [Finset.mem_product, mem_separableSumIndecomposables, mem_separablePermutations,
      Prod.exists]
  rw [this, genPoly_image_directSum hk]
  rfl

private theorem genPoly_skewFirst_add {R : Type*} [CommSemiring R] {m k : ℕ} (hm : 0 < m)
    (hk : 0 < k) :
    Finset.genPoly (R := R) (skewFirst (m + k) m) descentCount =
      X * (separableSkewIndecomposableEnumerator R m * separableDescentEnumerator R k) := by
  have : skewFirst (m + k) m =
      (separableSkewIndecomposables m ×ˢ separablePermutations k).image
        fun p => skewSum p.1 p.2 := by
    ext σ
    rw [mem_skewFirst, isSeparable_and_isFirstSkewCut_iff hm hk, Finset.mem_image]
    simp only [Finset.mem_product, mem_separableSkewIndecomposables, mem_separablePermutations,
      Prod.exists]
  rw [this, genPoly_image_skewSum hm hk]
  rfl

private theorem genPoly_directFirst {R : Type*} [CommSemiring R] {n m : ℕ} (hm : 0 < m)
    (hmn : m < n) :
    Finset.genPoly (R := R) (directFirst n m) descentCount =
      separableSumIndecomposableEnumerator R m * separableDescentEnumerator R (n - m) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by lia⟩
  rw [genPoly_directFirst_add hm (by lia), Nat.add_sub_cancel_left]

private theorem genPoly_skewFirst {R : Type*} [CommSemiring R] {n m : ℕ} (hm : 0 < m)
    (hmn : m < n) :
    Finset.genPoly (R := R) (skewFirst n m) descentCount =
      X * (separableSkewIndecomposableEnumerator R m * separableDescentEnumerator R (n - m)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by lia⟩
  rw [genPoly_skewFirst_add hm (by lia), Nat.add_sub_cancel_left]

/-! ### The recurrence -/

private theorem genPoly_biUnion {R : Type*} [CommSemiring R] {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : ι → Finset κ) (stat : κ → ℕ)
    (h : (s : Set ι).PairwiseDisjoint t) :
    Finset.genPoly (R := R) (s.biUnion t) stat =
      ∑ i ∈ s, Finset.genPoly (R := R) (t i) stat := by
  unfold Finset.genPoly
  rw [Finset.sum_biUnion h]

private theorem exists_isFirstSumCut {n : ℕ} {σ : Perm (Fin n)}
    (h : ∃ c, HasDirectSumCut σ c) : ∃ m, IsFirstSumCut σ m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun c hc => Nat.find_min' h hc⟩

private theorem exists_isFirstSkewCut {n : ℕ} {σ : Perm (Fin n)}
    (h : ∃ c, HasSkewSumCut σ c) : ∃ m, IsFirstSkewCut σ m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun c hc => Nat.find_min' h hc⟩

private theorem separablePermutations_eq_biUnion {n : ℕ} (hn : 2 ≤ n) :
    separablePermutations n =
      (Finset.Ico 1 n).biUnion (directFirst n) ∪ (Finset.Ico 1 n).biUnion (skewFirst n) := by
  ext σ
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · intro hσ
    have hsep := mem_separablePermutations.mp hσ
    obtain ⟨m, hm, hmn, hcut | hcut⟩ := exists_hasSumCut_of_isSeparable hn hsep
    · obtain ⟨m0, hm0⟩ := exists_isFirstSumCut ⟨m, hcut⟩
      exact Or.inl ⟨m0, Finset.mem_Ico.mpr ⟨hm0.1.1, hm0.1.2.1⟩,
        mem_directFirst.mpr ⟨hsep, hm0⟩⟩
    · obtain ⟨m0, hm0⟩ := exists_isFirstSkewCut ⟨m, hcut⟩
      exact Or.inr ⟨m0, Finset.mem_Ico.mpr ⟨hm0.1.1, hm0.1.2.1⟩,
        mem_skewFirst.mpr ⟨hsep, hm0⟩⟩
  · rintro (⟨m, -, hσ⟩ | ⟨m, -, hσ⟩)
    · exact mem_separablePermutations.mpr (mem_directFirst.mp hσ).1
    · exact mem_separablePermutations.mpr (mem_skewFirst.mp hσ).1

/-- **Recurrence for the descent enumerator of separable permutations.**

With `S_n`, `P_n`, `Q_n` the descent enumerators of the separable, separable sum-indecomposable
and separable skew-indecomposable permutations of `Fin n`, for `n ≥ 2` we have
`S_n = ∑_{k=1}^{n-1} P_k S_{n-k} + X ∑_{k=1}^{n-1} Q_k S_{n-k}`.
The first sum collects the permutations with a direct-sum cut, split at the first such cut; the
second sum collects those with a skew-sum cut, whose junction contributes one descent. -/
theorem separableDescentEnumerator_recurrence (R : Type*) [CommSemiring R] {n : ℕ}
    (hn : 2 ≤ n) :
    separableDescentEnumerator R n =
      (∑ k ∈ Finset.Ico 1 n,
        separableSumIndecomposableEnumerator R k * separableDescentEnumerator R (n - k)) +
      X * ∑ k ∈ Finset.Ico 1 n,
        separableSkewIndecomposableEnumerator R k * separableDescentEnumerator R (n - k) := by
  classical
  have hd1 : ((Finset.Ico 1 n : Finset ℕ) : Set ℕ).PairwiseDisjoint (directFirst n) := by
    intro m _ m' _ hne
    refine Finset.disjoint_left.mpr fun σ h1 h2 => hne ?_
    exact IsFirstSumCut.unique (mem_directFirst.mp h1).2 (mem_directFirst.mp h2).2
  have hd2 : ((Finset.Ico 1 n : Finset ℕ) : Set ℕ).PairwiseDisjoint (skewFirst n) := by
    intro m _ m' _ hne
    refine Finset.disjoint_left.mpr fun σ h1 h2 => hne ?_
    exact IsFirstSkewCut.unique (mem_skewFirst.mp h1).2 (mem_skewFirst.mp h2).2
  have hdisj : _root_.Disjoint ((Finset.Ico 1 n).biUnion (directFirst n))
      ((Finset.Ico 1 n).biUnion (skewFirst n)) := by
    refine Finset.disjoint_left.mpr fun σ h1 h2 => ?_
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.mp h1
    obtain ⟨m', -, hm'⟩ := Finset.mem_biUnion.mp h2
    exact not_hasSkewSumCut_of_hasDirectSumCut (mem_directFirst.mp hm).2.1
      (mem_skewFirst.mp hm').2.1
  unfold separableDescentEnumerator
  rw [separablePermutations_eq_biUnion hn, Finset.genPoly_union _ _ hdisj,
    genPoly_biUnion _ _ _ hd1, genPoly_biUnion _ _ _ hd2, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    have := Finset.mem_Ico.mp hm
    exact genPoly_directFirst (by lia) this.2
  · refine Finset.sum_congr rfl fun m hm => ?_
    have := Finset.mem_Ico.mp hm
    exact genPoly_skewFirst (by lia) this.2

/-! ### Reflection and small cases -/

private theorem descentCount_le {n : ℕ} (σ : Perm (Fin n)) : σ.descentCount ≤ n - 1 := by
  have := descentCount_add_ascentCount σ
  lia

private theorem card_skew_fibre_eq {n k : ℕ} (hk : k ≤ n - 1) :
    ((separableSkewIndecomposables n).filter fun σ => σ.descentCount = k).card =
      ((separableSumIndecomposables n).filter fun σ => σ.descentCount = n - 1 - k).card := by
  refine Finset.card_nbij' complement complement ?_ ?_ ?_ ?_
  · intro σ hσ
    obtain ⟨hmem, hdes⟩ := Finset.mem_filter.mp hσ
    obtain ⟨hs, hi⟩ := mem_separableSkewIndecomposables.mp hmem
    refine Finset.mem_filter.mpr ⟨mem_separableSumIndecomposables.mpr
      ⟨(isSeparable_complement_iff σ).mpr hs,
        (isSumIndecomposable_complement_iff σ).mpr hi⟩, ?_⟩
    rw [descentCount_complement, hdes]
  · intro σ hσ
    obtain ⟨hmem, hdes⟩ := Finset.mem_filter.mp hσ
    obtain ⟨hs, hi⟩ := mem_separableSumIndecomposables.mp hmem
    refine Finset.mem_filter.mpr ⟨mem_separableSkewIndecomposables.mpr
      ⟨(isSeparable_complement_iff σ).mpr hs,
        (isSkewIndecomposable_complement_iff σ).mpr hi⟩, ?_⟩
    have := descentCount_le σ
    rw [descentCount_complement, hdes]
    lia
  · intro σ _
    exact complement_complement σ
  · intro σ _
    exact complement_complement σ

/-- The skew-indecomposable enumerator is the coefficient reversal, by complementation, of the
sum-indecomposable enumerator, of degree `n - 1`. -/
theorem separableSkewIndecomposableEnumerator_eq_reflect (R : Type*) [CommSemiring R]
    (n : ℕ) :
    separableSkewIndecomposableEnumerator R n =
      (separableSumIndecomposableEnumerator R n).reflect (n - 1) := by
  ext k
  rw [coeff_reflect]
  unfold separableSkewIndecomposableEnumerator separableSumIndecomposableEnumerator
  rw [Finset.coeff_genPoly, Finset.coeff_genPoly]
  by_cases hk : k ≤ n - 1
  · rw [revAt_le hk, card_skew_fibre_eq hk]
  · have h0 : ∀ s : Finset (Perm (Fin n)),
        (s.filter fun σ => σ.descentCount = k).card = 0 := fun s => by
      rw [Finset.card_eq_zero]
      refine Finset.filter_eq_empty_iff.mpr fun σ _ hσ => ?_
      have := descentCount_le σ
      lia
    rw [revAt_eq_self_of_lt (by lia), h0, h0]

/-- The enumerator of separable permutations of length one is `1`. -/
theorem separableDescentEnumerator_one (R : Type*) [CommSemiring R] :
    separableDescentEnumerator R 1 = 1 := by
  have h : separablePermutations 1 = {1} := by
    ext σ
    rw [Finset.mem_singleton, mem_separablePermutations]
    have hσ : σ = 1 := Subsingleton.elim _ _
    simp only [hσ, iff_true]
    decide
  rw [separableDescentEnumerator, h]
  unfold Finset.genPoly
  rw [Finset.sum_singleton]
  have : (1 : Perm (Fin 1)).descentCount = 0 := by decide
  rw [this, pow_zero]

/-! ### Small kernel checks -/

private def descentFibre (n k : ℕ) : Finset (Perm (Fin n)) :=
  (separablePermutations n).filter fun σ => σ.descentCount = k

example : (separablePermutations 1).card = 1 := by decide

example : (descentFibre 2 0).card = 1 ∧ (descentFibre 2 1).card = 1 := by decide

example :
    (descentFibre 3 0).card = 1 ∧ (descentFibre 3 1).card = 4 ∧
      (descentFibre 3 2).card = 1 := by
  decide

example :
    (descentFibre 4 0).card = 1 ∧ (descentFibre 4 1).card = 10 ∧
      (descentFibre 4 2).card = 10 ∧ (descentFibre 4 3).card = 1 := by
  decide +kernel

/-- The recurrence at `n = 2` gives `1 + X`. -/
example : separableDescentEnumerator ℕ 2 = 1 + X := by
  rw [separableDescentEnumerator_recurrence ℕ le_rfl]
  have hP : separableSumIndecomposableEnumerator ℕ 1 = 1 := by
    have h : separableSumIndecomposables 1 = separablePermutations 1 := by
      ext σ
      rw [mem_separableSumIndecomposables, mem_separablePermutations]
      exact ⟨fun h => h.1, fun h => ⟨h, fun m hm hc => by have := hc.1; lia⟩⟩
    rw [separableSumIndecomposableEnumerator, h]
    exact separableDescentEnumerator_one ℕ
  have hQ : separableSkewIndecomposableEnumerator ℕ 1 = 1 := by
    have h : separableSkewIndecomposables 1 = separablePermutations 1 := by
      ext σ
      rw [mem_separableSkewIndecomposables, mem_separablePermutations]
      exact ⟨fun h => h.1, fun h => ⟨h, fun m hm hc => by have := hc.1; lia⟩⟩
    rw [separableSkewIndecomposableEnumerator, h]
    exact separableDescentEnumerator_one ℕ
  rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton, Finset.sum_singleton, hP, hQ,
    show 2 - 1 = 1 from rfl, separableDescentEnumerator_one]
  ring

end Equiv.Perm
