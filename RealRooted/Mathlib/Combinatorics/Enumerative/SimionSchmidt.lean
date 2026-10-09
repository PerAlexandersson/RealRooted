import RealRooted.Mathlib.Combinatorics.Enumerative.InverseStatistics
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Simion--Schmidt symmetries

Reversal, complementation, and inversion give bijections between permutation
classes defined by a single avoided pattern.  We use these bijections to
reduce the six patterns of length three to two cardinality classes.
-/

namespace RealRooted
namespace SimionSchmidt

open Equiv.Perm

private theorem mem_avoiders_singleton_iff {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (τ : Equiv.Perm (Fin k)) :
    σ ∈ avoiders n [⟨k, τ⟩] ↔ σ.Avoids τ := by
  simp only [avoiders, Finset.mem_filter, Finset.mem_univ, true_and,
    List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq, and_true]

/-! ### Symmetry bijections -/

/-- Reversal preserves the cardinality of a single-pattern avoidance class. -/
theorem card_avoiders_reverse {n k : ℕ} (τ : Equiv.Perm (Fin k)) :
    (avoiders n [⟨k, τ⟩]).card =
      (avoiders n [⟨k, reverse τ⟩]).card := by
  apply Finset.card_bij (fun σ _ ↦ reverse σ)
  · intro σ hσ
    rw [mem_avoiders_singleton_iff] at hσ ⊢
    intro h
    exact hσ ((containsPattern_reverse_iff σ τ).mpr h)
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    have hh := congrArg (fun σ : Equiv.Perm (Fin n) ↦ reverse σ) h
    simpa only [reverse_reverse] using hh
  · intro σ hσ
    refine ⟨reverse σ, ?_, ?_⟩
    · rw [mem_avoiders_singleton_iff] at hσ ⊢
      intro h
      have hh := (containsPattern_reverse_iff (reverse σ) τ).mp h
      exact hσ (by simpa only [reverse_reverse] using hh)
    · exact reverse_reverse σ

/-- Complementation preserves the cardinality of a single-pattern avoidance class. -/
theorem card_avoiders_complement {n k : ℕ} (τ : Equiv.Perm (Fin k)) :
    (avoiders n [⟨k, τ⟩]).card =
      (avoiders n [⟨k, complement τ⟩]).card := by
  apply Finset.card_bij (fun σ _ ↦ complement σ)
  · intro σ hσ
    rw [mem_avoiders_singleton_iff] at hσ ⊢
    intro h
    exact hσ ((containsPattern_complement_iff σ τ).mpr h)
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    have hh := congrArg (fun σ : Equiv.Perm (Fin n) ↦ complement σ) h
    simpa only [complement_complement] using hh
  · intro σ hσ
    refine ⟨complement σ, ?_, ?_⟩
    · rw [mem_avoiders_singleton_iff] at hσ ⊢
      intro h
      have hh := (containsPattern_complement_iff (complement σ) τ).mp h
      exact hσ (by simpa only [complement_complement] using hh)
    · exact complement_complement σ

/-- Inversion preserves the cardinality of a single-pattern avoidance class. -/
theorem card_avoiders_inv {n k : ℕ} (τ : Equiv.Perm (Fin k)) :
    (avoiders n [⟨k, τ⟩]).card =
      (avoiders n [⟨k, τ⁻¹⟩]).card := by
  apply Finset.card_bij (fun σ _ ↦ σ⁻¹)
  · intro σ hσ
    rw [mem_avoiders_singleton_iff] at hσ ⊢
    intro h
    exact hσ ((containsPattern_inv_iff σ τ).mpr h)
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    have hh := congrArg (fun σ : Equiv.Perm (Fin n) ↦ σ⁻¹) h
    simpa only [inv_inv] using hh
  · intro σ hσ
    refine ⟨σ⁻¹, ?_, ?_⟩
    · rw [mem_avoiders_singleton_iff] at hσ ⊢
      intro h
      have hh := (containsPattern_inv_iff σ⁻¹ τ).mp h
      exact hσ (by simpa only [inv_inv] using hh)
    · exact inv_inv σ

/-! ### The six patterns of length three -/

/-- The increasing pattern `123`, in zero-based one-line notation. -/
def p123 : Equiv.Perm (Fin 3) :=
  { toFun := ![0, 1, 2]
    invFun := ![0, 1, 2]
    left_inv := by decide
    right_inv := by decide }

/-- The pattern `132`, in zero-based one-line notation. -/
def p132 : Equiv.Perm (Fin 3) :=
  { toFun := ![0, 2, 1]
    invFun := ![0, 2, 1]
    left_inv := by decide
    right_inv := by decide }

/-- The pattern `213`, in zero-based one-line notation. -/
def p213 : Equiv.Perm (Fin 3) :=
  { toFun := ![1, 0, 2]
    invFun := ![1, 0, 2]
    left_inv := by decide
    right_inv := by decide }

/-- The pattern `231`, in zero-based one-line notation. -/
def p231 : Equiv.Perm (Fin 3) :=
  { toFun := ![1, 2, 0]
    invFun := ![2, 0, 1]
    left_inv := by decide
    right_inv := by decide }

/-- The pattern `312`, in zero-based one-line notation. -/
def p312 : Equiv.Perm (Fin 3) :=
  { toFun := ![2, 0, 1]
    invFun := ![1, 2, 0]
    left_inv := by decide
    right_inv := by decide }

/-- The decreasing pattern `321`, in zero-based one-line notation. -/
def p321 : Equiv.Perm (Fin 3) :=
  { toFun := ![2, 1, 0]
    invFun := ![2, 1, 0]
    left_inv := by decide
    right_inv := by decide }

/-- Reversal sends `132` to `231`. -/
theorem reverse_p132 : reverse p132 = p231 := by decide

/-- Complementation sends `132` to `312`. -/
theorem complement_p132 : complement p132 = p312 := by decide

/-- Inversion fixes `132`. -/
theorem inv_p132 : p132⁻¹ = p132 := by decide

/-- Reversal sends `213` to `312`. -/
theorem reverse_p213 : reverse p213 = p312 := by decide

/-- Complementation sends `213` to `231`. -/
theorem complement_p213 : complement p213 = p231 := by decide

/-- Inversion fixes `213`. -/
theorem inv_p213 : p213⁻¹ = p213 := by decide

/-- Reversal sends `123` to `321`. -/
theorem reverse_p123 : reverse p123 = p321 := by decide

/-- Complementation sends `123` to `321`. -/
theorem complement_p123 : complement p123 = p321 := by decide

/-- Inversion fixes `123`. -/
theorem inv_p123 : p123⁻¹ = p123 := by decide

/-- The four non-monotone length-three patterns have equal avoidance counts. -/
theorem card_avoiders_p132_eq_p231_eq_p213_eq_p312 (n : ℕ) :
    (avoiders n [⟨3, p132⟩]).card = (avoiders n [⟨3, p231⟩]).card ∧
    (avoiders n [⟨3, p231⟩]).card = (avoiders n [⟨3, p213⟩]).card ∧
    (avoiders n [⟨3, p213⟩]).card = (avoiders n [⟨3, p312⟩]).card := by
  have h132_231 := card_avoiders_reverse (n := n) p132
  have h132_312 := card_avoiders_complement (n := n) p132
  have h213_312 := card_avoiders_reverse (n := n) p213
  rw [reverse_p132] at h132_231
  rw [complement_p132] at h132_312
  rw [reverse_p213] at h213_312
  constructor
  · exact h132_231
  constructor
  · exact h132_231.symm.trans (h132_312.trans h213_312.symm)
  · exact h213_312

open Finset
open scoped List

/-- `σ` avoids the pattern 132: no positions `i < j < k` with `σ i < σ k < σ j`. -/
def Avoids132 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → ¬ (σ i < σ k ∧ σ k < σ j)

/-- `σ` avoids the pattern 123: no positions `i < j < k` with `σ i < σ j < σ k`. -/
def Avoids123 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → ¬ (σ i < σ j ∧ σ j < σ k)

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids132 σ) := by
  unfold Avoids132; infer_instance

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids123 σ) := by
  unfold Avoids123; infer_instance

private lemma sameOrderType_132 {n : ℕ} {a b c : Fin n} :
    ([a, b, c] : List (Fin n)).SameOrderType (List.ofFn p132) ↔
      a < c ∧ c < b := by
  change ([a, b, c] : List (Fin n)).SameOrderType ([0, 2, 1] : List (Fin 3)) ↔ _
  unfold List.SameOrderType List.sameOrderTypeBool
  simp only [List.length_cons, List.length_nil, ↓reduceDIte]
  constructor
  · intro h
    have h' := of_decide_eq_true h
    have h02 := h' ⟨0, by simp⟩ ⟨2, by simp⟩
    have h21 := h' ⟨2, by simp⟩ ⟨1, by simp⟩
    simpa using And.intro h02 h21
  · rintro ⟨hac, hcb⟩
    apply decide_eq_true
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> lia

private lemma sameOrderType_123 {n : ℕ} {a b c : Fin n} :
    ([a, b, c] : List (Fin n)).SameOrderType (List.ofFn p123) ↔
      a < b ∧ b < c := by
  change ([a, b, c] : List (Fin n)).SameOrderType ([0, 1, 2] : List (Fin 3)) ↔ _
  unfold List.SameOrderType List.sameOrderTypeBool
  simp only [List.length_cons, List.length_nil, ↓reduceDIte]
  constructor
  · intro h
    have h' := of_decide_eq_true h
    have h01 := h' ⟨0, by simp⟩ ⟨1, by simp⟩
    have h12 := h' ⟨1, by simp⟩ ⟨2, by simp⟩
    simpa using And.intro h01 h12
  · rintro ⟨hab, hbc⟩
    apply decide_eq_true
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> lia

private lemma contains_p132_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.ContainsPattern p132 ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧ σ i < σ k ∧ σ k < σ j := by
  rw [Equiv.Perm.containsPattern_iff]
  constructor
  · rintro ⟨s, hs, hst⟩
    have hlen : s.length = 3 := by
      rw [List.sameOrderType_length hst, List.length_ofFn]
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
    obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
    let i : Fin n := Fin.cast List.length_ofFn (e ⟨0, by simp⟩)
    let j : Fin n := Fin.cast List.length_ofFn (e ⟨1, by simp⟩)
    let k : Fin n := Fin.cast List.length_ofFn (e ⟨2, by simp⟩)
    have hij : i < j := by
      have h := e.lt_iff_lt.mpr (by decide : (0 : Fin 3) < 1)
      exact_mod_cast h
    have hjk : j < k := by
      have h := e.lt_iff_lt.mpr (by decide : (1 : Fin 3) < 2)
      exact_mod_cast h
    have ha : a = σ i := by
      calc
        a = (List.ofFn σ).get (e ⟨0, by simp⟩) := he ⟨0, by simp⟩
        _ = σ i := by
          simp only [List.get_ofFn]
          congr 1
    have hb : b = σ j := by
      calc
        b = (List.ofFn σ).get (e ⟨1, by simp⟩) := he ⟨1, by simp⟩
        _ = σ j := by
          simp only [List.get_ofFn]
          congr 1
    have hc : c = σ k := by
      calc
        c = (List.ofFn σ).get (e ⟨2, by simp⟩) := he ⟨2, by simp⟩
        _ = σ k := by
          simp only [List.get_ofFn]
          congr 1
    have hst' := (sameOrderType_132 (a := a) (b := b) (c := c)).mp hst
    refine ⟨i, j, k, hij, hjk, ?_⟩
    simpa [ha, hb, hc] using hst'
  · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
    refine ⟨[σ i, σ j, σ k], ?_, ?_⟩
    · let e₀ : Fin 3 → Fin (List.ofFn σ).length := fun x =>
          Fin.cast List.length_ofFn.symm (![i, j, k] x)
      let e₀' : Fin 3 ↪o Fin (List.ofFn σ).length :=
        OrderEmbedding.ofStrictMono e₀ (by
          rw [Fin.strictMono_iff_lt_succ]
          intro x
          fin_cases x
          · exact hij
          · exact hjk)
      have hsub : List.Sublist ([σ i, σ j, σ k] : List (Fin n)) (List.ofFn σ) := by
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨e₀', by
          intro x
          simp only [List.length_cons, List.length_nil] at x ⊢
          fin_cases x <;> simp [e₀, e₀']⟩
      exact hsub
    · exact (sameOrderType_132 (a := σ i) (b := σ j) (c := σ k)).mpr ⟨hik, hkj⟩

private lemma contains_p123_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.ContainsPattern p123 ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧ σ i < σ j ∧ σ j < σ k := by
  rw [Equiv.Perm.containsPattern_iff]
  constructor
  · rintro ⟨s, hs, hst⟩
    have hlen : s.length = 3 := by
      rw [List.sameOrderType_length hst, List.length_ofFn]
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
    obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hs
    let i : Fin n := Fin.cast List.length_ofFn (e ⟨0, by simp⟩)
    let j : Fin n := Fin.cast List.length_ofFn (e ⟨1, by simp⟩)
    let k : Fin n := Fin.cast List.length_ofFn (e ⟨2, by simp⟩)
    have hij : i < j := by
      have h := e.lt_iff_lt.mpr (by decide : (0 : Fin 3) < 1)
      exact_mod_cast h
    have hjk : j < k := by
      have h := e.lt_iff_lt.mpr (by decide : (1 : Fin 3) < 2)
      exact_mod_cast h
    have ha : a = σ i := by
      calc
        a = (List.ofFn σ).get (e ⟨0, by simp⟩) := he ⟨0, by simp⟩
        _ = σ i := by simp only [List.get_ofFn]; congr 1
    have hb : b = σ j := by
      calc
        b = (List.ofFn σ).get (e ⟨1, by simp⟩) := he ⟨1, by simp⟩
        _ = σ j := by simp only [List.get_ofFn]; congr 1
    have hc : c = σ k := by
      calc
        c = (List.ofFn σ).get (e ⟨2, by simp⟩) := he ⟨2, by simp⟩
        _ = σ k := by simp only [List.get_ofFn]; congr 1
    have hst' := (sameOrderType_123 (a := a) (b := b) (c := c)).mp hst
    refine ⟨i, j, k, hij, hjk, ?_⟩
    simpa [ha, hb, hc] using hst'
  · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
    refine ⟨[σ i, σ j, σ k], ?_, ?_⟩
    · let e₀ : Fin 3 → Fin (List.ofFn σ).length := fun x =>
          Fin.cast List.length_ofFn.symm (![i, j, k] x)
      let e₀' : Fin 3 ↪o Fin (List.ofFn σ).length :=
        OrderEmbedding.ofStrictMono e₀ (by
          rw [Fin.strictMono_iff_lt_succ]
          intro x
          fin_cases x
          · exact hij
          · exact hjk)
      have hsub : List.Sublist ([σ i, σ j, σ k] : List (Fin n)) (List.ofFn σ) := by
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨e₀', by
          intro x
          simp only [List.length_cons, List.length_nil] at x ⊢
          fin_cases x <;> simp [e₀, e₀']⟩
      exact hsub
    · exact (sameOrderType_123 (a := σ i) (b := σ j) (c := σ k)).mpr ⟨hik, hkj⟩

/-- Canonical pattern containment and the direct 132 avoidance predicate agree. -/
theorem avoids_p132_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.Avoids p132 ↔ Avoids132 σ := by
  unfold Equiv.Perm.Avoids Avoids132
  rw [contains_p132_iff]
  constructor
  · intro h i j k hij hjk hrel
    exact h ⟨i, j, k, hij, hjk, hrel.1, hrel.2⟩
  · intro h hex
    rcases hex with ⟨i, j, k, hij, hjk, hik, hkj⟩
    exact h i j k hij hjk ⟨hik, hkj⟩

/-- Canonical pattern containment and the direct 123 avoidance predicate agree. -/
theorem avoids_p123_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    σ.Avoids p123 ↔ Avoids123 σ := by
  unfold Equiv.Perm.Avoids Avoids123
  rw [contains_p123_iff]
  constructor
  · intro h i j k hij hjk hrel
    exact h ⟨i, j, k, hij, hjk, hrel.1, hrel.2⟩
  · intro h hex
    rcases hex with ⟨i, j, k, hij, hjk, hik, hkj⟩
    exact h i j k hij hjk ⟨hik, hkj⟩

example : (univ.filter fun σ : Equiv.Perm (Fin 4) => Avoids132 σ).card = 14 := by decide
example : (univ.filter fun σ : Equiv.Perm (Fin 4) => Avoids123 σ).card = 14 := by decide

/-! ### Auxiliary material: pattern avoidance for lists of distinct naturals -/

section Aux

open scoped List

/-- A list avoids the 3-letter "pattern" `R` if no length-3 sublist `[a, b, c]` satisfies `R`. -/
private def LAvoids (R : ℕ → ℕ → ℕ → Prop) (l : List ℕ) : Prop :=
  ∀ a b c, [a, b, c] <+ l → ¬ R a b c

/-- The pattern 132. -/
private def R132 : ℕ → ℕ → ℕ → Prop := fun a b c => a < c ∧ c < b

/-- The pattern 123. -/
private def R123 : ℕ → ℕ → ℕ → Prop := fun a b c => a < b ∧ b < c

private lemma LAvoids.mono {R} {l₁ l₂ : List ℕ} (h : l₁ <+ l₂)
    (H : LAvoids R l₂) : LAvoids R l₁ :=
  fun a b c h' => H a b c (h'.trans h)

/-! #### From permutations of `Fin n` to lists -/

/-- The one-line notation of a permutation, as a list of naturals. -/
private def toL {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (fun i => (σ i : ℕ))

private theorem triple_sublist_ofFn {n : ℕ} (f : Fin n → ℕ) (a b c : ℕ) :
    [a, b, c] <+ List.ofFn f ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧ f i = a ∧ f j = b ∧ f k = c := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  constructor
  · rintro ⟨g, hg⟩
    have h0 := hg ⟨0, by simp⟩
    have h1 := hg ⟨1, by simp⟩
    have h2 := hg ⟨2, by simp⟩
    simp only [List.get_ofFn] at h0 h1 h2
    refine ⟨Fin.cast (by simp) (g ⟨0, by simp⟩), Fin.cast (by simp) (g ⟨1, by simp⟩),
      Fin.cast (by simp) (g ⟨2, by simp⟩), ?_, ?_, ?_, ?_, ?_⟩
    · simp [Fin.lt_def]
    · simp [Fin.lt_def]
    · simpa using h0.symm
    · simpa using h1.symm
    · simpa using h2.symm
  · rintro ⟨i, j, k, hij, hjk, rfl, rfl, rfl⟩
    have hm : StrictMono (fun x : Fin 3 => Fin.cast (by simp) (![i, j, k] x) :
        Fin 3 → Fin (List.ofFn f).length) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro x
      fin_cases x
      · exact hij
      · exact hjk
    refine ⟨OrderEmbedding.ofStrictMono _ hm, ?_⟩
    intro x
    fin_cases x <;> simp

private theorem avoids132_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids132 σ ↔ LAvoids R132 (toL σ) := by
  constructor
  · intro h a b c hs
    obtain ⟨i, j, k, hij, hjk, rfl, rfl, rfl⟩ := (triple_sublist_ofFn _ a b c).mp hs
    exact h i j k hij hjk
  · intro h i j k hij hjk
    exact h _ _ _ ((triple_sublist_ofFn _ _ _ _).mpr ⟨i, j, k, hij, hjk, rfl, rfl, rfl⟩)

private theorem avoids123_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids123 σ ↔ LAvoids R123 (toL σ) := by
  constructor
  · intro h a b c hs
    obtain ⟨i, j, k, hij, hjk, rfl, rfl, rfl⟩ := (triple_sublist_ofFn _ a b c).mp hs
    exact h i j k hij hjk
  · intro h i j k hij hjk
    exact h _ _ _ ((triple_sublist_ofFn _ _ _ _).mpr ⟨i, j, k, hij, hjk, rfl, rfl, rfl⟩)

private lemma toL_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) : toL σ ~ List.range n := by
  rw [List.perm_ext_iff_of_nodup]
  · intro a
    simp only [toL, List.mem_ofFn, List.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact (σ i).isLt
    · intro h; exact ⟨σ.symm ⟨a, h⟩, by simp⟩
  · rw [toL, List.nodup_ofFn]
    intro i j h
    exact σ.injective (Fin.ext h)
  · exact List.nodup_range

open Classical in
/-- The set of rearrangements of `L` satisfying `P`. -/
private noncomputable def perms (P : List ℕ → Prop) (L : List ℕ) : Finset (List ℕ) :=
  L.permutations.toFinset.filter P

private lemma mem_perms {P : List ℕ → Prop} {L l : List ℕ} :
    l ∈ perms P L ↔ l ~ L ∧ P l := by
  classical
  simp [perms]

private lemma perms_congr {P : List ℕ → Prop} {L L' : List ℕ} (h : L ~ L') :
    perms P L = perms P L' := by
  ext l
  simp only [mem_perms]
  exact ⟨fun ⟨a, b⟩ => ⟨a.trans h, b⟩, fun ⟨a, b⟩ => ⟨a.trans h.symm, b⟩⟩

private lemma card_perm_filter {n : ℕ} (P : List ℕ → Prop)
    (Q : Equiv.Perm (Fin n) → Prop) [DecidablePred Q] (hPQ : ∀ σ, Q σ ↔ P (toL σ)) :
    (univ.filter Q).card = (perms P (List.range n)).card := by
  apply Finset.card_bij (fun σ _ => toL σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact mem_perms.mpr ⟨toL_perm σ, (hPQ σ).1 hσ⟩
  · intro σ _ τ _ h
    have h' := List.ofFn_injective h
    ext i
    exact congrArg (fun g => g i) h'
  · intro l hl
    obtain ⟨hp, hP⟩ := mem_perms.mp hl
    have hlen : l.length = n := by simpa using hp.length_eq
    have hlt : ∀ x ∈ l, x < n := fun x hx => List.mem_range.mp (hp.subset hx)
    have hnd : l.Nodup := hp.nodup_iff.mpr List.nodup_range
    let g : Fin n → Fin n := fun i => ⟨l[i.1]'(by lia), hlt _ (List.getElem_mem _)⟩
    have hg : Function.Injective g := by
      intro i j h
      simp only [g, Fin.mk.injEq] at h
      exact Fin.ext ((hnd.getElem_inj_iff).mp h)
    let σ := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
    have hσ : toL σ = l := by
      apply List.ext_getElem
      · simp [toL, hlen]
      · intro i h1 h2
        simp [toL, σ, g]
    refine ⟨σ, ?_, hσ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hPQ, hσ]; exact hP

/-! #### 132-avoiders: decomposition at the largest value -/

private lemma second_mem_of_sublist_cons {b c m : ℕ} {B : List ℕ}
    (h : [b, c] <+ m :: B) : c ∈ B := by
  rw [List.sublist_cons_iff] at h
  rcases h with h | ⟨r, hr, h⟩
  · exact h.subset (by simp)
  · simp only [List.cons.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    exact h.subset (by simp)

private lemma av132_append (A B : List ℕ) (m : ℕ) (hA : LAvoids R132 A) (hB : LAvoids R132 B)
    (hAm : ∀ a ∈ A, a < m) (hBm : ∀ b ∈ B, b < m) (hBA : ∀ a ∈ A, ∀ b ∈ B, b < a) :
    LAvoids R132 (A ++ m :: B) := by
  intro a b c h
  rw [List.sublist_append_iff] at h
  obtain ⟨r1, r2, he, h1, h2⟩ := h
  rcases r1 with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, r1⟩⟩⟩⟩
  · simp only [List.nil_append] at he
    subst he
    rw [List.sublist_cons_iff] at h2
    rcases h2 with h2 | ⟨r, hr, h2⟩
    · exact hB a b c h2
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have := hBm c (h2.subset (by simp))
      simp only [R132]; lia
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hc := second_mem_of_sublist_cons h2
    have := hBA a (h1.subset (by simp : a ∈ [a])) c hc
    simp only [R132]; lia
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hc : c ∈ m :: B := h2.subset (by simp)
    have hb := hAm b (h1.subset (by simp : b ∈ [a, b]))
    have ha := h1.subset (by simp : a ∈ [a, b])
    simp only [R132]
    rcases List.mem_cons.mp hc with rfl | hc
    · lia
    · have := hBA a ha c hc; lia
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact hA a b c (by simpa using h1)
  · simp at he

private lemma split_sorted (s A B : List ℕ) (hs : s.Pairwise (· < ·)) (hp : B ++ A ~ s)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, b < a) : s.take B.length ~ B ∧ s.drop B.length ~ A := by
  set sB := B.mergeSort (fun a b => decide (a ≤ b))
  set sA := A.mergeSort (fun a b => decide (a ≤ b))
  have pB : sB ~ B := List.mergeSort_perm _ _
  have pA : sA ~ A := List.mergeSort_perm _ _
  have hsB : sB.Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (by intro a b c; simpa using le_trans) (by intro a b; simpa using le_total a b) B
    simpa using this
  have hsA : sA.Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (by intro a b c; simpa using le_trans) (by intro a b; simpa using le_total a b) A
    simpa using this
  have hsorted : (sB ++ sA).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨hsB, hsA, fun x hx y hy => le_of_lt (hBA x (pB.subset hx) y (pA.subset hy))⟩
  have heq : sB ++ sA = s := by
    refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2) hsorted
      (hs.imp le_of_lt) ?_
    exact (pB.append pA).trans hp
  have hlen : sB.length = B.length := pB.length_eq
  subst heq
  rw [← hlen, List.take_left, List.drop_left]
  exact ⟨pB, pA⟩

private lemma key132 (m : ℕ) (s : List ℕ) (hs : s.Pairwise (· < ·)) (hm : ∀ x ∈ s, x < m)
    (l : List ℕ) :
    (l ~ m :: s ∧ LAvoids R132 l) ↔ ∃ j ∈ Finset.range (s.length + 1), ∃ A B : List ℕ,
      (A ~ s.drop j ∧ LAvoids R132 A) ∧ (B ~ s.take j ∧ LAvoids R132 B) ∧
      A ++ m :: B = l := by
  constructor
  · rintro ⟨hp, hav⟩
    obtain ⟨A, B, rfl⟩ := List.append_of_mem (hp.symm.subset (List.mem_cons_self))
    have hnd : (A ++ m :: B).Nodup :=
      hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun h => lt_irrefl _ (hm m h), hs.imp ne_of_lt⟩)
    have hAB : A ++ B ~ s := (List.perm_cons m).mp (List.perm_middle.symm.trans hp)
    have hBA : ∀ b ∈ B, ∀ a ∈ A, b < a := by
      intro b hb a ha
      by_contra hlt
      push Not at hlt
      have hne : a ≠ b := by
        rintro rfl
        rw [List.nodup_append] at hnd
        exact hnd.2.2 a ha a (List.mem_cons_of_mem _ hb) rfl
      have hbm : b < m := hm b (hAB.subset (List.mem_append_right _ hb))
      have hsub : [a, m, b] <+ A ++ m :: B := by
        have := (List.singleton_sublist.mpr ha).append
          ((List.singleton_sublist.mpr hb).cons_cons m)
        simpa using this
      exact hav a m b hsub ⟨lt_of_le_of_ne hlt hne, hbm⟩
    obtain ⟨h1, h2⟩ := split_sorted s A B hs (List.perm_append_comm.trans hAB) hBA
    refine ⟨B.length, ?_, A, B, ⟨h2.symm, hav.mono (List.sublist_append_left _ _)⟩,
      ⟨h1.symm, hav.mono ((List.sublist_cons_self m B).trans (List.sublist_append_right A _))⟩,
      rfl⟩
    have := hAB.length_eq
    simp only [List.length_append] at this
    simp only [Finset.mem_range]; lia
  · rintro ⟨j, -, A, B, ⟨hA, avA⟩, ⟨hB, avB⟩, rfl⟩
    have hs' : s = s.take j ++ s.drop j := (List.take_append_drop j s).symm
    have hBA : ∀ x ∈ s.take j, ∀ y ∈ s.drop j, x < y := by
      have := hs; rw [hs', List.pairwise_append] at this; exact this.2.2
    refine ⟨?_, av132_append A B m avA avB
      (fun a ha => hm a (List.mem_of_mem_drop (hA.subset ha)))
      (fun b hb => hm b (List.mem_of_mem_take (hB.subset hb)))
      (fun a ha b hb => hBA b (hB.subset hb) a (hA.subset ha))⟩
    refine List.perm_middle.trans ((List.perm_cons m).mpr ?_)
    rw [hs']
    exact List.perm_append_comm.trans (hB.append hA)

private theorem count132 : ∀ n (L : List ℕ), L.Nodup → L.length = n →
    (perms (LAvoids R132) L).card = catalan n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hL hlen
  rcases n with _ | n
  · rw [List.length_eq_zero_iff] at hlen
    subst hlen
    have : perms (LAvoids R132) [] = {[]} := by
      ext l
      simp only [mem_perms, Finset.mem_singleton]
      constructor
      · exact fun h => List.perm_nil.mp h.1
      · rintro rfl
        exact ⟨List.Perm.refl _, fun a b c h => by simp at h⟩
    rw [this]; simp
  · have hne : L.toFinset.Nonempty := by
      rw [List.toFinset_nonempty_iff]; rintro rfl; simp at hlen
    set m := L.toFinset.max' hne
    set s := (L.toFinset.erase m).sort (· ≤ ·)
    have hmL : m ∈ L := List.mem_toFinset.mp (Finset.max'_mem _ _)
    have hsnd : s.Nodup := Finset.sort_nodup _ _
    have hs : s.Pairwise (· < ·) :=
      ((Finset.pairwise_sort _ (· ≤ ·)).and hsnd).imp (fun h => lt_of_le_of_ne h.1 h.2)
    have hmem : ∀ x, x ∈ s ↔ x ≠ m ∧ x ∈ L := by intro x; simp [s]
    have hm : ∀ x ∈ s, x < m := by
      intro x hx; rw [hmem] at hx
      exact lt_of_le_of_ne (Finset.le_max' _ _ (List.mem_toFinset.mpr hx.2)) hx.1
    have hslen : s.length = n := by
      rw [Finset.length_sort, Finset.card_erase_of_mem (Finset.max'_mem _ _),
        List.toFinset_card_of_nodup hL, hlen]; rfl
    have hLs : L ~ m :: s := by
      rw [List.perm_ext_iff_of_nodup hL
        (List.nodup_cons.mpr ⟨fun h => lt_irrefl _ (hm m h), hsnd⟩)]
      intro a; rw [List.mem_cons, hmem]; constructor
      · intro ha; by_cases h : a = m
        · exact Or.inl h
        · exact Or.inr ⟨h, ha⟩
      · rintro (rfl | ⟨_, ha⟩)
        · exact hmL
        · exact ha
    rw [perms_congr hLs]
    have hset : perms (LAvoids R132) (m :: s) = (Finset.range (s.length + 1)).biUnion (fun j =>
        (perms (LAvoids R132) (s.drop j) ×ˢ perms (LAvoids R132) (s.take j)).image
          (fun p => p.1 ++ m :: p.2)) := by
      ext l
      rw [mem_perms, key132 m s hs hm l]
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, mem_perms, Prod.exists,
        and_assoc]
    have hmA : ∀ j, ∀ A ∈ perms (LAvoids R132) (s.drop j), m ∉ A := fun j A hA h =>
      lt_irrefl _ (hm m (List.mem_of_mem_drop ((mem_perms.mp hA).1.subset h)))
    have hmB : ∀ j, ∀ B ∈ perms (LAvoids R132) (s.take j), m ∉ B := fun j B hB h =>
      lt_irrefl _ (hm m (List.mem_of_mem_take ((mem_perms.mp hB).1.subset h)))
    have hlenA : ∀ j, ∀ A ∈ perms (LAvoids R132) (s.drop j), A.length = n - j := by
      intro j A hA
      rw [(mem_perms.mp hA).1.length_eq, List.length_drop, hslen]
    rw [hset, Finset.card_biUnion]
    · rw [catalan_succ, ← Finset.sum_range (fun i => catalan i * catalan (n - i)), hslen]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.card_image_of_injOn, Finset.card_product,
        ih (n - j) (by lia) _ (hsnd.sublist (List.drop_sublist _ _))
          (by rw [List.length_drop, hslen]),
        ih j (by lia) _ (hsnd.sublist (List.take_sublist _ _))
          (by rw [List.length_take, hslen]; lia)]
      · ring
      · rintro ⟨A, B⟩ hp ⟨A', B'⟩ hp' he
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
        have he' : A ++ m :: B = A' ++ m :: B' := he
        have := (List.append_cons_inj_of_notMem (hmA j A hp.1) (hmB j B hp.2)).mp he'
        simp only [Prod.mk.injEq]
        exact ⟨this.1, this.2.2⟩
    · intro j hj j' hj' hjj'
      rw [Function.onFun, Finset.disjoint_left]
      intro l hl hl'
      simp only [Finset.mem_image, Finset.mem_product, Prod.exists] at hl hl'
      obtain ⟨A, B, ⟨hA, hB⟩, rfl⟩ := hl
      obtain ⟨A', B', ⟨hA', hB'⟩, he⟩ := hl'
      have := (List.append_cons_inj_of_notMem (hmA j A hA) (hmB j B hB)).mp he.symm
      have h1 := hlenA j A hA
      have h2 := hlenA j' A' hA'
      rw [← this.1] at h2
      simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
      rw [hslen] at hj hj'
      lia

/-! #### A common refined recursion for 123- and 132-avoiders -/

private lemma perms_congr_pred {P Q : List ℕ → Prop} {L : List ℕ}
    (h : ∀ l, l ~ L → (P l ↔ Q l)) :
    perms P L = perms Q L := by
  ext l
  simp only [mem_perms]
  exact ⟨fun ⟨a, b⟩ => ⟨a, (h l a).1 b⟩, fun ⟨a, b⟩ => ⟨a, (h l a).2 b⟩⟩

private lemma card_perms_cons (P : List ℕ → Prop) (L : List ℕ) (hL0 : L ≠ []) :
    (perms P L).card = ∑ x ∈ L.toFinset, (perms (fun l => P (x :: l)) (L.erase x)).card := by
  have hset : perms P L = L.toFinset.biUnion
      (fun x => (perms (fun l => P (x :: l)) (L.erase x)).image (x :: ·)) := by
    ext l
    simp only [mem_perms, Finset.mem_biUnion, Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨hp, hP⟩
      cases l with
      | nil => exact absurd (List.perm_nil.mp hp.symm) hL0
      | cons x l' =>
        have hx : x ∈ L := hp.subset List.mem_cons_self
        exact ⟨x, hx, l', ⟨(hp.trans (List.perm_cons_erase hx)).cons_inv, hP⟩, rfl⟩
    · rintro ⟨x, hx, l', ⟨hp', hP⟩, rfl⟩
      exact ⟨((List.perm_cons x).mpr hp').trans (List.perm_cons_erase hx).symm, hP⟩
  rw [hset, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun x _ => Finset.card_image_of_injective _ List.cons_injective
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro l hl hl'
    simp only [Finset.mem_image] at hl hl'
    obtain ⟨a, -, rfl⟩ := hl
    obtain ⟨b, -, hb⟩ := hl'
    exact hxy (List.cons.inj hb).1.symm

/-- The refined count: `G n c` counts the rearrangements of `n` distinct numbers avoiding the
pattern, in which the `c` largest entries appear in monotone order. -/
private def G : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, c => (if c = 0 then 0 else G n (c - 1)) + ∑ r ∈ Finset.Ico c (n + 1), G n r

/-- Number of entries of `L` that are `≥ t`. -/
private noncomputable def cnt (L : List ℕ) (t : ℕ) : ℕ :=
  (L.toFinset.filter (fun y => t ≤ y)).card

private lemma rank_sum (S : Finset ℕ) (t : ℕ) (φ : ℕ → ℕ) :
    ∑ x ∈ S.filter (· < t), φ (S.filter (x < ·)).card =
      ∑ r ∈ Finset.Ico (S.filter (t ≤ ·)).card S.card, φ r := by
  have hinj : Set.InjOn (fun x => (S.filter (x < ·)).card) (S.filter (· < t) : Set ℕ) := by
    have key : ∀ x ∈ S, ∀ y ∈ S, x < y →
        (S.filter (y < ·)).card < (S.filter (x < ·)).card := by
      intro x hx y hy hxy
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨y, by simp [hy, hxy], by simp⟩
      · intro z; simp only [Finset.mem_filter]; exact fun ⟨h1, h2⟩ => ⟨h1, by lia⟩
    intro x hx y hy he
    simp only [Finset.coe_filter] at hx hy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd he (ne_of_gt (key x hx.1 y hy.1 h))
    · exact h
    · exact absurd he (ne_of_lt (key y hy.1 x hx.1 h))
  rw [← Finset.sum_image hinj]
  congr 1
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    simp only [Finset.mem_image, Finset.mem_filter] at hr
    obtain ⟨x, ⟨hxS, hxt⟩, rfl⟩ := hr
    rw [Finset.mem_Ico]
    constructor
    · apply Finset.card_le_card
      intro z; simp only [Finset.mem_filter]; exact fun ⟨h1, h2⟩ => ⟨h1, by lia⟩
    · apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨x, hxS, by simp⟩
  · rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]
    have := Finset.card_filter_add_card_filter_not (s := S) (fun x => x < t)
    have h2 : S.filter (fun x => ¬ x < t) = S.filter (t ≤ ·) := by
      apply Finset.filter_congr; intro x _; lia
    rw [h2] at this
    lia

private lemma toFinset_erase_of_nodup {L : List ℕ} (hL : L.Nodup) (x : ℕ) :
    (L.erase x).toFinset = L.toFinset.erase x := by
  ext y
  simp [hL.mem_erase_iff]

open Classical in
private theorem count_G (P : ℕ → List ℕ → Prop) (Ext : List ℕ → ℕ → ℕ → Prop)
    (hnil : ∀ t, P t [])
    (hlt : ∀ (L : List ℕ) (t x : ℕ), L.Nodup → x ∈ L → ∀ l',
      l' ~ L.erase x → x < t →
      (P t (x :: l') ↔ P (x + 1) l'))
    (hge : ∀ (L : List ℕ) (t x : ℕ), L.Nodup → x ∈ L → ∀ l',
      l' ~ L.erase x → t ≤ x →
      (P t (x :: l') ↔ Ext L t x ∧ P t l'))
    (hExt : ∀ (L : List ℕ) (t : ℕ), L.Nodup →
      (L.toFinset.filter (fun x => t ≤ x ∧ Ext L t x)).card = if cnt L t = 0 then 0 else 1) :
    ∀ n (L : List ℕ) t, L.Nodup → L.length = n → (perms (P t) L).card = G n (cnt L t) := by
  classical
  intro n
  induction n with
  | zero =>
    intro L t hL hlen
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    have : perms (P t) [] = {[]} := by
      ext l
      simp only [mem_perms, Finset.mem_singleton]
      constructor
      · exact fun h => List.perm_nil.mp h.1
      · rintro rfl
        exact ⟨List.Perm.refl _, hnil t⟩
    rw [this]; simp [G]
  | succ n ih =>
    intro L t hL hlen
    have hL0 : L ≠ [] := by rintro rfl; simp at hlen
    set S := L.toFinset
    have hScard : S.card = n + 1 := by rw [List.toFinset_card_of_nodup hL, hlen]
    have hlen' : ∀ x ∈ L, (L.erase x).length = n := fun x hx => by
      rw [List.length_erase_of_mem hx, hlen]; rfl
    have inner : ∀ x ∈ S, (perms (fun l => P t (x :: l)) (L.erase x)).card =
        if x < t then G n (S.filter (x < ·)).card
        else if Ext L t x then G n (cnt L t - 1) else 0 := by
      classical
      intro x hxS
      have hx : x ∈ L := List.mem_toFinset.mp hxS
      by_cases hxt : x < t
      · rw [ite_eq_left hxt, perms_congr_pred (fun l hl => hlt L t x hL hx l hl hxt),
          ih _ _ (List.Nodup.erase x hL) (hlen' x hx)]
        congr 1
        rw [cnt, toFinset_erase_of_nodup hL]
        congr 1
        ext y; simp only [Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, by lia⟩,
          fun ⟨h1, h2⟩ => ⟨⟨by lia, h1⟩, by lia⟩⟩
      · rw [ite_eq_right hxt]
        push Not at hxt
        by_cases hE : Ext L t x
        · rw [ite_eq_left hE, perms_congr_pred (fun l hl => (hge L t x hL hx l hl hxt).trans
            (and_iff_right hE)), ih _ _ (List.Nodup.erase x hL) (hlen' x hx)]
          congr 1
          rw [cnt, cnt, toFinset_erase_of_nodup hL, Finset.filter_erase,
            Finset.card_erase_of_mem (by simp [hx, hxt])]
        · rw [ite_eq_right hE, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro l hl
          have hl' := mem_perms.mp hl
          rw [hge L t x hL hx l hl'.1 hxt] at hl'
          exact hE hl'.2.1
    rw [card_perms_cons _ _ hL0, Finset.sum_congr rfl inner, Finset.sum_ite, Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, rank_sum, hScard,
      Finset.filter_filter]
    have hf : S.filter (fun x => ¬ x < t ∧ Ext L t x) =
        S.filter (fun x => t ≤ x ∧ Ext L t x) := by
      apply Finset.filter_congr; intro x _; simp only [not_lt]
    rw [hf, hExt L t hL, G]
    change _ = (if cnt L t = 0 then 0 else G n (cnt L t - 1)) + _
    rw [add_comm]
    congr 1
    split_ifs <;> simp

private lemma pairs_cons (Q : ℕ → ℕ → Prop) (x : ℕ) (l : List ℕ) :
    (∀ b c, [b, c] <+ x :: l → Q b c) ↔
      (∀ c ∈ l, Q x c) ∧ ∀ b c, [b, c] <+ l → Q b c := by
  constructor
  · intro h
    exact ⟨fun c hc => h x c ((List.singleton_sublist.mpr hc).cons_cons x),
      fun b c hs => h b c (hs.trans (List.sublist_cons_self x l))⟩
  · rintro ⟨h1, h2⟩ b c hs
    rw [List.sublist_cons_iff] at hs
    rcases hs with hs | ⟨r, hr, hs⟩
    · exact h2 b c hs
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact h1 c (List.singleton_sublist.mp hs)

private lemma LAvoids_cons (R : ℕ → ℕ → ℕ → Prop) (x : ℕ) (l : List ℕ) :
    LAvoids R (x :: l) ↔ LAvoids R l ∧ ∀ b c, [b, c] <+ l → ¬ R x b c := by
  constructor
  · intro H
    exact ⟨H.mono (List.sublist_cons_self x l), fun b c h => H x b c (h.cons_cons x)⟩
  · rintro ⟨H1, H2⟩ a b c h
    rw [List.sublist_cons_iff] at h
    rcases h with h | ⟨r, hr, h⟩
    · exact H1 a b c h
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact H2 b c h

private lemma LAvoids_nil (R : ℕ → ℕ → ℕ → Prop) : LAvoids R [] :=
  fun a b c h => by simp at h

/-- 123-avoiding, and the entries `≥ t` appear in decreasing order. -/
private def P123 (t : ℕ) (l : List ℕ) : Prop :=
  LAvoids R123 l ∧ ∀ b c, [b, c] <+ l → t ≤ b → t ≤ c → c ≤ b

/-- 132-avoiding, and the entries `≥ t` appear in increasing order. -/
private def P132 (t : ℕ) (l : List ℕ) : Prop :=
  LAvoids R132 l ∧ ∀ b c, [b, c] <+ l → t ≤ b → t ≤ c → b ≤ c

private lemma mem_L_of_perm_erase {L l' : List ℕ} {x y : ℕ}
    (hl : l' ~ L.erase x) (hy : y ∈ l') :
    y ∈ L := List.mem_of_mem_erase (hl.subset hy)

private lemma mem_perm_erase {L l' : List ℕ} {x y : ℕ} (hL : L.Nodup) (hl : l' ~ L.erase x)
    (hy : y ∈ L) (hyx : y ≠ x) : y ∈ l' :=
  hl.symm.subset ((hL.mem_erase_iff).mpr ⟨hyx, hy⟩)

private lemma P123_lt (t x : ℕ) (l' : List ℕ) (hxt : x < t) :
    P123 t (x :: l') ↔ P123 (x + 1) l' := by
  unfold P123
  rw [LAvoids_cons, pairs_cons]
  constructor
  · rintro ⟨⟨hA, h1⟩, -, -⟩
    refine ⟨hA, fun b c hs hb hc => ?_⟩
    by_contra hcb
    exact h1 b c hs ⟨by lia, by lia⟩
  · rintro ⟨hA, h⟩
    refine ⟨⟨hA, fun b c hs hbc => ?_⟩, fun c _ h1 _ => absurd h1 (by lia),
      fun b c hs hb hc => h b c hs (by lia) (by lia)⟩
    obtain ⟨h1, h2⟩ := hbc
    have := h b c hs (by lia) (by lia)
    lia

private lemma P123_ge (L : List ℕ) (t x : ℕ) (hL : L.Nodup) (l' : List ℕ)
    (hl : l' ~ L.erase x)
    (hxt : t ≤ x) :
    P123 t (x :: l') ↔ (∀ y ∈ L, t ≤ y → y ≤ x) ∧ P123 t l' := by
  unfold P123
  rw [LAvoids_cons, pairs_cons]
  constructor
  · rintro ⟨⟨hA, -⟩, h2, h3⟩
    refine ⟨fun y hy hty => ?_, hA, h3⟩
    by_cases hyx : y = x
    · lia
    · exact h2 y (mem_perm_erase hL hl hy hyx) hxt hty
  · rintro ⟨hE, hA, h3⟩
    refine ⟨⟨hA, fun b c hs hbc => ?_⟩,
      fun c hc _ htc => hE c (mem_L_of_perm_erase hl hc) htc, h3⟩
    obtain ⟨h1, -⟩ := hbc
    have := hE b (mem_L_of_perm_erase hl (hs.subset (by simp))) (by lia)
    lia

private lemma P132_lt (t x : ℕ) (l' : List ℕ) (hxt : x < t) :
    P132 t (x :: l') ↔ P132 (x + 1) l' := by
  unfold P132
  rw [LAvoids_cons, pairs_cons]
  constructor
  · rintro ⟨⟨hA, h1⟩, -, -⟩
    refine ⟨hA, fun b c hs hb hc => ?_⟩
    by_contra hcb
    exact h1 b c hs ⟨by lia, by lia⟩
  · rintro ⟨hA, h⟩
    refine ⟨⟨hA, fun b c hs hbc => ?_⟩, fun c _ h1 _ => absurd h1 (by lia),
      fun b c hs hb hc => h b c hs (by lia) (by lia)⟩
    obtain ⟨h1, h2⟩ := hbc
    have := h b c hs (by lia) (by lia)
    lia

private lemma P132_ge (L : List ℕ) (t x : ℕ) (hL : L.Nodup) (l' : List ℕ)
    (hl : l' ~ L.erase x)
    (hxt : t ≤ x) :
    P132 t (x :: l') ↔ (∀ y ∈ L, t ≤ y → x ≤ y) ∧ P132 t l' := by
  unfold P132
  rw [LAvoids_cons, pairs_cons]
  constructor
  · rintro ⟨⟨hA, -⟩, h2, h3⟩
    refine ⟨fun y hy hty => ?_, hA, h3⟩
    by_cases hyx : y = x
    · lia
    · exact h2 y (mem_perm_erase hL hl hy hyx) hxt hty
  · rintro ⟨hE, hA, h3⟩
    refine ⟨⟨hA, fun b c hs hbc => ?_⟩,
      fun c hc _ htc => hE c (mem_L_of_perm_erase hl hc) htc, h3⟩
    obtain ⟨h1, h2⟩ := hbc
    have := h3 b c hs (by lia) (by lia)
    lia

private lemma card_max_filter (L : List ℕ) (t : ℕ) :
    (L.toFinset.filter (fun x => t ≤ x ∧ ∀ y ∈ L, t ≤ y → y ≤ x)).card =
      if cnt L t = 0 then 0 else 1 := by
  unfold cnt
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h ⊢
    exact fun x hx hx' => h hx hx'.1
  · have hne : (L.toFinset.filter (fun y => t ≤ y)).Nonempty := by
      rw [← Finset.card_pos]; lia
    set m := (L.toFinset.filter (fun y => t ≤ y)).max' hne
    have hm := Finset.max'_mem _ hne
    rw [Finset.mem_filter] at hm
    rw [Finset.card_eq_one]
    refine ⟨m, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, htx, hE⟩
      have h1 := hE m (List.mem_toFinset.mp hm.1) hm.2
      have h2 : x ≤ m := Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hx, htx⟩)
      lia
    · rintro rfl
      exact ⟨hm.1, hm.2, fun y hy hty =>
        Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hy, hty⟩)⟩

private lemma card_min_filter (L : List ℕ) (t : ℕ) :
    (L.toFinset.filter (fun x => t ≤ x ∧ ∀ y ∈ L, t ≤ y → x ≤ y)).card =
      if cnt L t = 0 then 0 else 1 := by
  unfold cnt
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h ⊢
    exact fun x hx hx' => h hx hx'.1
  · have hne : (L.toFinset.filter (fun y => t ≤ y)).Nonempty := by
      rw [← Finset.card_pos]; lia
    set m := (L.toFinset.filter (fun y => t ≤ y)).min' hne
    have hm := Finset.min'_mem _ hne
    rw [Finset.mem_filter] at hm
    rw [Finset.card_eq_one]
    refine ⟨m, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, htx, hE⟩
      have h1 := hE m (List.mem_toFinset.mp hm.1) hm.2
      have h2 : m ≤ x := Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, htx⟩)
      lia
    · rintro rfl
      exact ⟨hm.1, hm.2, fun y hy hty =>
        Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hy, hty⟩)⟩

open Classical in
private theorem count123_G (n : ℕ) (L : List ℕ) (t : ℕ) (hL : L.Nodup) (hlen : L.length = n) :
    (perms (P123 t) L).card = G n (cnt L t) :=
  count_G P123 (fun L t x => ∀ y ∈ L, t ≤ y → y ≤ x)
    (fun t => ⟨LAvoids_nil _, fun b c h => by simp at h⟩)
    (fun L t x _ _ l' _ hxt => P123_lt t x l' hxt)
    (fun L t x hL _ l' hl hxt => P123_ge L t x hL l' hl hxt)
    (fun L t _ => by convert card_max_filter L t) n L t hL hlen

open Classical in
private theorem count132_G (n : ℕ) (L : List ℕ) (t : ℕ) (hL : L.Nodup) (hlen : L.length = n) :
    (perms (P132 t) L).card = G n (cnt L t) :=
  count_G P132 (fun L t x => ∀ y ∈ L, t ≤ y → x ≤ y)
    (fun t => ⟨LAvoids_nil _, fun b c h => by simp at h⟩)
    (fun L t x _ _ l' _ hxt => P132_lt t x l' hxt)
    (fun L t x hL _ l' hl hxt => P132_ge L t x hL l' hl hxt)
    (fun L t _ => by convert card_min_filter L t) n L t hL hlen

private lemma cnt_range (n : ℕ) : cnt (List.range n) n = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  simp only [List.mem_toFinset, List.mem_range] at hx
  lia

private lemma perms_range_123 (n : ℕ) :
    perms (LAvoids R123) (List.range n) = perms (P123 n) (List.range n) :=
  perms_congr_pred fun l hl => ⟨fun h => ⟨h, fun b c hs hb _ =>
    absurd (List.mem_range.mp (hl.subset (hs.subset (by simp : b ∈ [b, c]))))
      (by lia)⟩, fun h => h.1⟩

private lemma perms_range_132 (n : ℕ) :
    perms (LAvoids R132) (List.range n) = perms (P132 n) (List.range n) :=
  perms_congr_pred fun l hl => ⟨fun h => ⟨h, fun b c hs hb _ =>
    absurd (List.mem_range.mp (hl.subset (hs.subset (by simp : b ∈ [b, c]))))
      (by lia)⟩, fun h => h.1⟩

private theorem count123_range (n : ℕ) :
    (perms (LAvoids R123) (List.range n)).card = catalan n := by
  rw [perms_range_123, count123_G n _ n List.nodup_range List.length_range, cnt_range,
    ← cnt_range n, ← count132_G n _ n List.nodup_range List.length_range, ← perms_range_132,
    count132 n _ List.nodup_range List.length_range]

end Aux

/-- Simion–Schmidt: 132-avoiding permutations are counted by the Catalan numbers.
(Hint: the position of the largest value splits σ into a left block whose values all exceed those
of the right block, both 132-avoiding, giving Mathlib's `catalan_succ`.) -/
theorem card_avoids132 (n : ℕ) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => Avoids132 σ).card = catalan n := by
  rw [card_perm_filter (LAvoids R132) _ avoids132_iff]
  exact count132 n _ List.nodup_range List.length_range

/-- Simion–Schmidt: 123-avoiding permutations are counted by the Catalan numbers.
(Hint: Simion–Schmidt's bijection with 132-avoiders fixing the left-to-right minima, or a direct
decomposition; any correct proof is fine.) -/
theorem card_avoids123 (n : ℕ) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => Avoids123 σ).card = catalan n := by
  rw [card_perm_filter (LAvoids R123) _ avoids123_iff]
  exact count123_range n

private lemma avoiders_p132_eq_filter (n : ℕ) :
    avoiders n [⟨3, p132⟩] = univ.filter (fun σ : Equiv.Perm (Fin n) => Avoids132 σ) := by
  ext σ
  rw [mem_avoiders_singleton_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact avoids_p132_iff σ

private lemma avoiders_p123_eq_filter (n : ℕ) :
    avoiders n [⟨3, p123⟩] = univ.filter (fun σ : Equiv.Perm (Fin n) => Avoids123 σ) := by
  ext σ
  rw [mem_avoiders_singleton_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact avoids_p123_iff σ

/-- The canonical 132-avoiders have Catalan cardinality. -/
theorem card_avoiders_p132_catalan (n : ℕ) :
    (avoiders n [⟨3, p132⟩]).card = catalan n := by
  rw [avoiders_p132_eq_filter, card_avoids132]

/-- The canonical 231-avoiders have Catalan cardinality. -/
theorem card_avoiders_p231_catalan (n : ℕ) :
    (avoiders n [⟨3, p231⟩]).card = catalan n := by
  calc
    (avoiders n [⟨3, p231⟩]).card = (avoiders n [⟨3, p132⟩]).card :=
      (card_avoiders_p132_eq_p231_eq_p213_eq_p312 n).1.symm
    _ = catalan n := card_avoiders_p132_catalan n

/-- The canonical 213-avoiders have Catalan cardinality. -/
theorem card_avoiders_p213_catalan (n : ℕ) :
    (avoiders n [⟨3, p213⟩]).card = catalan n := by
  calc
    (avoiders n [⟨3, p213⟩]).card = (avoiders n [⟨3, p132⟩]).card :=
      ((card_avoiders_p132_eq_p231_eq_p213_eq_p312 n).1.trans
        (card_avoiders_p132_eq_p231_eq_p213_eq_p312 n).2.1).symm
    _ = catalan n := card_avoiders_p132_catalan n

/-- The canonical 312-avoiders have Catalan cardinality. -/
theorem card_avoiders_p312_catalan (n : ℕ) :
    (avoiders n [⟨3, p312⟩]).card = catalan n := by
  calc
    (avoiders n [⟨3, p312⟩]).card = (avoiders n [⟨3, p132⟩]).card :=
      ((card_avoiders_p132_eq_p231_eq_p213_eq_p312 n).1.trans
        ((card_avoiders_p132_eq_p231_eq_p213_eq_p312 n).2.1.trans
          (card_avoiders_p132_eq_p231_eq_p213_eq_p312 n).2.2)).symm
    _ = catalan n := card_avoiders_p132_catalan n

/-- The canonical 123-avoiders have Catalan cardinality. -/
theorem card_avoiders_p123_catalan (n : ℕ) :
    (avoiders n [⟨3, p123⟩]).card = catalan n := by
  rw [avoiders_p123_eq_filter, card_avoids123]

/-- The canonical 321-avoiders have Catalan cardinality. -/
theorem card_avoiders_p321_catalan (n : ℕ) :
    (avoiders n [⟨3, p321⟩]).card = catalan n := by
  calc
    (avoiders n [⟨3, p321⟩]).card = (avoiders n [⟨3, p123⟩]).card :=
      by
        have h := card_avoiders_reverse (n := n) p123
        rw [reverse_p123] at h
        exact h.symm
    _ = catalan n := card_avoiders_p123_catalan n

/-- The two monotone length-three patterns have equal avoidance counts. -/
theorem card_avoiders_p123_eq_p321 (n : ℕ) :
    (avoiders n [⟨3, p123⟩]).card = (avoiders n [⟨3, p321⟩]).card := by
  simpa only [reverse_p123] using card_avoiders_reverse (n := n) p123

example : ∀ n ≤ 4,
    (avoiders n [⟨3, p132⟩]).card = (avoiders n [⟨3, p231⟩]).card := by
  decide

example : ∀ n ≤ 4,
    (avoiders n [⟨3, p132⟩]).card = (avoiders n [⟨3, p213⟩]).card := by
  decide

example : ∀ n ≤ 4,
    (avoiders n [⟨3, p132⟩]).card = (avoiders n [⟨3, p312⟩]).card := by
  decide

example : ∀ n ≤ 4,
    (avoiders n [⟨3, p123⟩]).card = (avoiders n [⟨3, p321⟩]).card := by
  decide

end SimionSchmidt
end RealRooted
