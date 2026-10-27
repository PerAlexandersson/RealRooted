module

import RealRooted.AffineFamily.PF
import RealRooted.ChudnovskySeymour.PF
public import RealRooted.PFPolynomial

/-!
# Local-to-global preservation for operator matrices

An operator matrix preserves ordered vectors of PF polynomials exactly when all of its ordered
two-by-two blocks preserve ordered pairs.  Empty and singleton dimensions are treated by separate
interfaces below.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- A vector has PF coordinates in directed interlacing order. -/
def IsOrderedPF {n : ℕ} (f : Fin n → ℝ[X]) : Prop :=
  (∀ i, IsPFPolynomial (f i)) ∧ ∀ i k, i < k → Interl (f i) (f k)

/-- Apply a matrix of real-linear polynomial operators to a polynomial vector. -/
def apply {m n : ℕ} (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X])
    (f : Fin n → ℝ[X]) : Fin m → ℝ[X] :=
  fun i => ∑ j, M i j (f j)

/-- An operator matrix preserves ordered PF vectors. -/
def PreservesOrderedPF {m n : ℕ} (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ f, IsOrderedPF f → IsOrderedPF (apply M f)

/-- Four operators preserve ordered PF pairs when used as a two-by-two block. -/
def PreservesOrderedPFPair
    (a b c d : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ f g, IsPFPolynomial f → IsPFPolynomial g → Interl f g →
    IsPFPolynomial (a f + b g) ∧ IsPFPolynomial (c f + d g) ∧
      Interl (a f + b g) (c f + d g)

/-- The block on rows `i < k` and columns `j < l` preserves ordered PF pairs. -/
def PreservesBlock {m n : ℕ} (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X])
    (i k : Fin m) (j l : Fin n) : Prop :=
  PreservesOrderedPFPair (M i j) (M i l) (M k j) (M k l)

private def pairInput {n : ℕ} (j l : Fin n) (f g : ℝ[X]) : Fin n → ℝ[X] :=
  fun q => if q = j then f else if q = l then g else 0

private def singleInput {n : ℕ} (j : Fin n) (f : ℝ[X]) : Fin n → ℝ[X] :=
  fun q => if q = j then f else 0

private lemma apply_pairInput {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X])
    {j l : Fin n} (hjl : j ≠ l) (f g : ℝ[X]) (i : Fin m) :
    apply M (pairInput j l f g) i = M i j f + M i l g := by
  classical
  simp only [apply, pairInput]
  calc
    (∑ q, M i q (if q = j then f else if q = l then g else 0)) =
        ∑ q, if q = j then M i q f else if q = l then M i q g else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split
      · rfl
      · split
        · rfl
        · exact (M i q).map_zero
    _ = M i j f + M i l g := by
      have hsplit : ∀ q : Fin n,
          (if q = j then M i q f else if q = l then M i q g else 0) =
            (if q = j then M i q f else 0) + (if q = l then M i q g else 0) := by
        intro q
        by_cases hqj : q = j
        · simp [hqj, hjl]
        · simp [hqj]
      rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma apply_singleInput {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X])
    (j : Fin n) (f : ℝ[X]) (i : Fin m) :
    apply M (singleInput j f) i = M i j f := by
  classical
  simp only [apply, singleInput]
  calc
    (∑ q, M i q (if q = j then f else 0)) =
        ∑ q, if q = j then M i q f else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split
      · rfl
      · exact (M i q).map_zero
    _ = M i j f := by
      rw [Finset.sum_ite_eq']
      simp

private lemma pairInput_isOrderedPF {n : ℕ} {j l : Fin n} (hjl : j < l)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hfg : Interl f g) :
    IsOrderedPF (pairInput j l f g) := by
  constructor
  · intro q
    by_cases hqj : q = j
    · simpa [pairInput, hqj] using hf
    by_cases hql : q = l
    · simpa [pairInput, hqj, hql, hjl.ne'] using hg
    · simp [pairInput, hqj, hql, IsPFPolynomial.zero]
  · intro q r hqr
    have hqr_ne : q ≠ r := ne_of_lt hqr
    by_cases hqj : q = j
    · by_cases hrl : r = l
      · simpa [pairInput, hqj, hrl, hjl.ne'] using hfg
      · have hrj : r ≠ j := fun hrj => hqr_ne (hqj.trans hrj.symm)
        simp [pairInput, hqj, hrl, hrj, interl_zero_right]
    · by_cases hql : q = l
      · have hrl : r ≠ l := fun hrl => hqr_ne (hql.trans hrl.symm)
        have hrj : r ≠ j := by
          intro hrj
          subst q
          subst r
          exact (lt_asymm hjl hqr)
        simp [pairInput, hql, hrl, hrj, hjl.ne', interl_zero_right]
      · simp [pairInput, hqj, hql, interl_zero_left]

private lemma singleInput_isOrderedPF {n : ℕ} (j : Fin n) {f : ℝ[X]}
    (hf : IsPFPolynomial f) : IsOrderedPF (singleInput j f) := by
  constructor
  · intro q
    by_cases hqj : q = j
    · simpa [singleInput, hqj] using hf
    · simp [singleInput, hqj, IsPFPolynomial.zero]
  · intro q r hqr
    have hqr_ne : q ≠ r := ne_of_lt hqr
    by_cases hqj : q = j
    · have hrj : r ≠ j := fun hrj => hqr_ne (hqj.trans hrj.symm)
      simp [singleInput, hqj, hrj, interl_zero_right]
    · simp [singleInput, hqj, interl_zero_left]

private lemma exists_fin_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : ∃ k : Fin n, k ≠ i :=
  haveI := Fin.nontrivial_iff_two_le.mpr hn
  exists_ne i

private lemma map_C_mul (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (a : ℝ) (p : ℝ[X]) :
    L (C a * p) = C a * L p := by
  rw [← smul_eq_C_mul, L.map_smul, smul_eq_C_mul]

private lemma isPFPolynomial_C_mul {a : ℝ} (ha : 0 ≤ a) {f : ℝ[X]}
    (hf : IsPFPolynomial f) : IsPFPolynomial (C a * f) :=
  (IsPFPolynomial.of_C_nonneg ha).mul hf

private lemma scaled_pair_isOrderedPF {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hfg : Interl f g) :
    IsPFPolynomial (C a * f) ∧ IsPFPolynomial (C b * g) ∧
      Interl (C a * f) (C b * g) := by
  exact ⟨isPFPolynomial_C_mul ha hf, isPFPolynomial_C_mul hb hg,
    (hfg.C_mul_left_of_nonneg ha).C_mul_right_of_nonneg hb⟩

private lemma compatible_of_forall_nonneg_combo_isPF {f g : ℝ[X]}
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IsPFPolynomial (C a * f + C b * g)) :
    Compatible f g := by
  intro a b ha hb
  by_cases hz : C a * f + C b * g = 0
  · exact Or.inl hz
  · exact Or.inr ⟨hz, (h a b ha hb).ne_zero_and_splits hz |>.2⟩

private lemma isPFPolynomial_fin_sum {n : ℕ} (p : Fin n → ℝ[X])
    (hpf : ∀ j, IsPFPolynomial (p j))
    (hpair : ∀ j l, j < l → Compatible (p j) (p l)) :
    IsPFPolynomial (∑ j, p j) := by
  let fs := List.ofFn p
  have hpf_list : ∀ q ∈ fs, IsPFPolynomial q := by
    intro q hq
    rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩
    exact hpf j
  have hpair_list : PairwiseCompatible fs := by
    exact List.pairwise_iff_get.mp (by
      simpa [fs] using List.pairwise_ofFn.mpr hpair)
  have hsum := hpair_list.isPFPolynomial_weightedSum hpf_list
    (ws := List.ofFn fun j => ((1 : ℝ), p j))
    (fun ap hap => by
      rcases List.mem_ofFn.mp hap with ⟨j, rfl⟩
      simp [fs])
    (by simp)
  simpa [weightedSum_ofFn] using hsum

private lemma isPFPolynomial_entry_of_blocks {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hblock : ∀ i k j l, i < k → j < l → PreservesBlock M i k j l)
    (i : Fin m) (j : Fin n) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (M i j p) := by
  obtain ⟨k, hki⟩ := exists_fin_ne hm i
  obtain ⟨l, hlj⟩ := exists_fin_ne hn j
  rcases lt_or_gt_of_ne hki with hki | hik
  · rcases lt_or_gt_of_ne hlj with hlj | hjl
    · simpa using
        (hblock k i l j hki hlj 0 p IsPFPolynomial.zero hp (interl_zero_left p)).2.1
    · simpa using
        (hblock k i j l hki hjl p 0 hp IsPFPolynomial.zero (interl_zero_right p)).2.1
  · rcases lt_or_gt_of_ne hlj with hlj | hjl
    · simpa using
        (hblock i k l j hik hlj 0 p IsPFPolynomial.zero hp (interl_zero_left p)).1
    · simpa using
        (hblock i k j l hik hjl p 0 hp IsPFPolynomial.zero (interl_zero_right p)).1

private lemma interl_entries_of_blocks {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hn : 2 ≤ n)
    (hblock : ∀ i k j l, i < k → j < l → PreservesBlock M i k j l)
    {i k : Fin m} (hik : i < k) (j : Fin n) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl (M i j p) (M k j p) := by
  obtain ⟨l, hlj⟩ := exists_fin_ne hn j
  rcases lt_or_gt_of_ne hlj with hlj | hjl
  · simpa using
      (hblock i k l j hik hlj 0 p IsPFPolynomial.zero hp (interl_zero_left p)).2.2
  · simpa using
      (hblock i k j l hik hjl p 0 hp IsPFPolynomial.zero (interl_zero_right p)).2.2

private lemma compatible_row_entries_of_blocks {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m)
    (hblock : ∀ i k j l, i < k → j < l → PreservesBlock M i k j l)
    (i : Fin m) {j l : Fin n} (hjl : j < l) {f g : ℝ[X]}
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hfg : Interl f g) :
    Compatible (M i j f) (M i l g) := by
  apply compatible_of_forall_nonneg_combo_isPF
  intro a b ha hb
  obtain ⟨k, hki⟩ := exists_fin_ne hm i
  have hscaled := scaled_pair_isOrderedPF ha hb hf hg hfg
  have hlinear (r : Fin m) :
      M r j (C a * f) + M r l (C b * g) =
        C a * M r j f + C b * M r l g := by
    simp only [map_C_mul]
  rcases lt_or_gt_of_ne hki with hki | hik
  · rw [← hlinear i]
    exact (hblock k i j l hki hjl _ _ hscaled.1 hscaled.2.1 hscaled.2.2).2.1
  · rw [← hlinear i]
    exact (hblock i k j l hik hjl _ _ hscaled.1 hscaled.2.1 hscaled.2.2).1

private lemma row_isPFPolynomial_of_blocks {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hblock : ∀ i k j l, i < k → j < l → PreservesBlock M i k j l)
    {f : Fin n → ℝ[X]} (hf : IsOrderedPF f) (i : Fin m) :
    IsPFPolynomial (apply M f i) := by
  apply isPFPolynomial_fin_sum
  · intro j
    exact isPFPolynomial_entry_of_blocks M hm hn hblock i j (hf.1 j)
  · intro j l hjl
    exact compatible_row_entries_of_blocks M hm hblock i hjl
      (hf.1 j) (hf.1 l) (hf.2 j l hjl)

private lemma affine_column_isPFPolynomial_of_blocks {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hn : 2 ≤ n)
    (hblock : ∀ i k j l, i < k → j < l → PreservesBlock M i k j l)
    {i k : Fin m} (hik : i < k) (j : Fin n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IsPFPolynomial ((C s * X + C t) * M i j p + M k j p) := by
  have hi := isPFPolynomial_entry_of_blocks M (by lia) hn hblock i j hp
  have hk := isPFPolynomial_entry_of_blocks M (by lia) hn hblock k j hp
  exact (interl_entries_of_blocks M hn hblock hik j hp).isPFPolynomial_affine hi hk hs ht

private lemma compatible_affine_columns_of_blocks {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X])
    (hblock : ∀ i k j l, i < k → j < l → PreservesBlock M i k j l)
    {i k : Fin m} (hik : i < k) {j l : Fin n} (hjl : j < l)
    {f g : ℝ[X]} (hf : IsPFPolynomial f) (hg : IsPFPolynomial g) (hfg : Interl f g)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Compatible ((C s * X + C t) * M i j f + M k j f)
      ((C s * X + C t) * M i l g + M k l g) := by
  apply compatible_of_forall_nonneg_combo_isPF
  intro a b ha hb
  have hscaled := scaled_pair_isOrderedPF ha hb hf hg hfg
  have hout := hblock i k j l hik hjl _ _ hscaled.1 hscaled.2.1 hscaled.2.2
  have hpencil := hout.2.2.isPFPolynomial_affine hout.1 hout.2.1 hs ht
  have heq :
      C a * ((C s * X + C t) * M i j f + M k j f) +
          C b * ((C s * X + C t) * M i l g + M k l g) =
        (C s * X + C t) * (M i j (C a * f) + M i l (C b * g)) +
          (M k j (C a * f) + M k l (C b * g)) := by
    simp only [map_C_mul]
    ring
  rwa [heq]

/-- For at least two rows and columns, ordered-PF preservation is equivalent to preservation by
every ordered two-by-two block, including nonadjacent blocks. -/
theorem preservesOrderedPF_iff_preservesBlock_of_two_le {m n : ℕ}
    (M : Fin m → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    PreservesOrderedPF M ↔
      ∀ i k j l, i < k → j < l → PreservesBlock M i k j l := by
  constructor
  · intro hpres i k j l hik hjl f g hf hg hfg
    have hout := hpres (pairInput j l f g) (pairInput_isOrderedPF hjl hf hg hfg)
    have hi := hout.1 i
    have hk := hout.1 k
    have hik_out := hout.2 i k hik
    rw [apply_pairInput M hjl.ne f g i] at hi
    rw [apply_pairInput M hjl.ne f g i] at hik_out
    rw [apply_pairInput M hjl.ne f g k] at hk hik_out
    exact ⟨hi, hk, hik_out⟩
  · intro hblock f hf
    constructor
    · intro i
      exact row_isPFPolynomial_of_blocks M hm hn hblock hf i
    · intro i k hik
      have hi := row_isPFPolynomial_of_blocks M hm hn hblock hf i
      have hk := row_isPFPolynomial_of_blocks M hm hn hblock hf k
      apply (interl_iff_isPFPolynomial_affine hi hk).mpr
      intro s t hs ht
      let H : Fin n → ℝ[X] := fun j =>
        (C s * X + C t) * M i j (f j) + M k j (f j)
      have hH : IsPFPolynomial (∑ j, H j) := by
        apply isPFPolynomial_fin_sum
        · intro j
          exact affine_column_isPFPolynomial_of_blocks M hn hblock hik j (hf.1 j) hs ht
        · intro j l hjl
          exact compatible_affine_columns_of_blocks M hblock hik hjl
            (hf.1 j) (hf.1 l) (hf.2 j l hjl) hs ht
      have heq : ∑ j, H j = (C s * X + C t) * apply M f i + apply M f k := by
        simp only [H, apply, Finset.sum_add_distrib, Finset.mul_sum]
      rwa [← heq]

/-- A matrix with no output rows preserves ordered PF vectors. -/
theorem preservesOrderedPF_of_rows_zero {n : ℕ}
    (M : Fin 0 → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPF M :=
  fun _ _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- A matrix with no input columns has zero output and preserves ordered PF vectors. -/
theorem preservesOrderedPF_of_columns_zero {m : ℕ}
    (M : Fin m → Fin 0 → ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPF M := by
  intro f _
  constructor
  · intro i
    simpa [apply] using IsPFPolynomial.zero
  · intro i k _
    simpa [apply] using interl_zero_zero

/-- A one-by-one operator matrix preserves ordered PF vectors exactly when its sole entry
preserves PF polynomials. -/
theorem preservesOrderedPF_one_one_iff
    (M : Fin 1 → Fin 1 → ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPF M ↔ ∀ p, IsPFPolynomial p → IsPFPolynomial (M 0 0 p) := by
  constructor
  · intro hpres p hp
    let f : Fin 1 → ℝ[X] := fun _ => p
    have hf : IsOrderedPF f := by
      constructor
      · intro
        exact hp
      · intro i k hik
        exact False.elim ((ne_of_lt hik) (Subsingleton.elim i k))
    simpa [apply, f] using (hpres f hf).1 0
  · intro hentry f hf
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [apply] using hentry (f 0) (hf.1 0)
    · intro i k hik
      exact False.elim ((ne_of_lt hik) (Subsingleton.elim i k))

/-- For one output row, preservation is equivalent to scalar
preservation by every entry together with PF preservation of every ordered two-input row sum. -/
theorem preservesOrderedPF_one_row_iff {n : ℕ}
    (M : Fin 1 → Fin n → ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPF M ↔
      (∀ j p, IsPFPolynomial p → IsPFPolynomial (M 0 j p)) ∧
      ∀ j l, j < l → ∀ f g, IsPFPolynomial f → IsPFPolynomial g → Interl f g →
        IsPFPolynomial (M 0 j f + M 0 l g) := by
  constructor
  · intro hpres
    constructor
    · intro j p hp
      have hout := hpres (singleInput j p) (singleInput_isOrderedPF j hp)
      simpa [apply_singleInput M j p 0] using hout.1 0
    · intro j l hjl f g hf hg hfg
      have hout := hpres (pairInput j l f g) (pairInput_isOrderedPF hjl hf hg hfg)
      simpa [apply_pairInput M hjl.ne f g 0] using hout.1 0
  · rintro ⟨hentry, hpair⟩ f hf
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      apply isPFPolynomial_fin_sum
      · intro j
        exact hentry j (f j) (hf.1 j)
      · intro j l hjl
        apply compatible_of_forall_nonneg_combo_isPF
        intro a b ha hb
        have hscaled := scaled_pair_isOrderedPF ha hb (hf.1 j) (hf.1 l) (hf.2 j l hjl)
        have hrow := hpair j l hjl _ _ hscaled.1 hscaled.2.1 hscaled.2.2
        have heq :
            M 0 j (C a * f j) + M 0 l (C b * f l) =
              C a * M 0 j (f j) + C b * M 0 l (f l) := by
          simp only [map_C_mul]
        rwa [heq] at hrow
    · intro i k hik
      exact False.elim ((ne_of_lt hik) (Subsingleton.elim i k))

/-- For one input column, preservation is equivalent to scalar
preservation by every entry and the same-input comparison for every ordered row pair. -/
theorem preservesOrderedPF_one_column_iff {m : ℕ}
    (M : Fin m → Fin 1 → ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesOrderedPF M ↔
      (∀ i p, IsPFPolynomial p → IsPFPolynomial (M i 0 p)) ∧
      ∀ i k, i < k → ∀ p, IsPFPolynomial p → Interl (M i 0 p) (M k 0 p) := by
  constructor
  · intro hpres
    constructor
    · intro i p hp
      let f : Fin 1 → ℝ[X] := fun _ => p
      have hf : IsOrderedPF f := by
        constructor
        · intro
          exact hp
        · intro j l hjl
          exact False.elim ((ne_of_lt hjl) (Subsingleton.elim j l))
      simpa [apply, f] using (hpres f hf).1 i
    · intro i k hik p hp
      let f : Fin 1 → ℝ[X] := fun _ => p
      have hf : IsOrderedPF f := by
        constructor
        · intro
          exact hp
        · intro j l hjl
          exact False.elim ((ne_of_lt hjl) (Subsingleton.elim j l))
      simpa [apply, f] using (hpres f hf).2 i k hik
  · rintro ⟨hentry, hcompare⟩ f hf
    have hf0 : IsPFPolynomial (f 0) := hf.1 0
    constructor
    · intro i
      simpa [apply] using hentry i (f 0) hf0
    · intro i k hik
      simpa [apply] using hcompare i k hik (f 0) hf0

/-- The derivative, which kills constants, is accepted by the one-by-one interface. -/
example : PreservesOrderedPF (fun _ : Fin 1 => fun _ : Fin 1 => Polynomial.derivative) := by
  rw [preservesOrderedPF_one_one_iff]
  intro p hp
  exact hp.derivative

/-- Repeated roots are allowed in ordered PF inputs. -/
example : IsOrderedPF (fun _ : Fin 2 => (X + 1) ^ 2) := by
  have hp : IsPFPolynomial ((X + 1) ^ 2) :=
    (isPFPolynomial_X_add_C zero_le_one).pow 2
  exact ⟨fun _ => hp, fun _ _ _ => Interl.refl fun hne => (hp.ne_zero_and_splits hne).2⟩

/-- The zero operator matrix preserves ordered PF vectors in every dimension. -/
theorem preservesOrderedPF_zero {m n : ℕ} :
    PreservesOrderedPF (fun _ : Fin m => fun _ : Fin n => (0 : ℝ[X] →ₗ[ℝ] ℝ[X])) := by
  intro f _
  constructor
  · intro i
    simpa [apply] using IsPFPolynomial.zero
  · intro i k _
    simpa [apply] using interl_zero_zero

end RealRooted.OperatorMatrix

