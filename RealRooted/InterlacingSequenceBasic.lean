import RealRooted.Basic
import RealRooted.Linear
import RealRooted.WagnerX

/-!
# Interlacing sequences and matrices preserving them

Primary source for this file:

- Petter Brändén, "Unimodality, log-concavity, real-rootedness and beyond",
  in Miklós Bóna (ed.), Handbook of Enumerative Combinatorics, CRC Press, 2015,
  §7.8 "Common interleavers" (book p. 460; PDF p. 485).

Relevant source landmarks in that section:

- after Theorem 7.8.1: definitions of `g` being an interleaver or proper
  interleaver of a family;
- Lemma 7.8.4: affine-family criterion for common interleaving;
- Theorem 7.8.5: matrix characterization via the `2 × 2` affine test.

## Definitions

A sequence `{f₁, f₂, ..., fₙ}` of polynomials with positive leading coefficients
is an **interlacing sequence** if `fᵢ ⊳ fⱼ` for all `i < j`.

`𝓕ₙ⁺` denotes the family of interlacing sequences of length `n` with
non-negative coefficients.

## Main theorem

An `m × n` matrix `G` of polynomials maps `𝓕ₙ⁺ → 𝓕ₘ⁺` if and only if:

1. All entries of `G` have non-negative coefficients.
2. For every `2 × 2` submatrix `[[a, b], [c, d]]` of `G` and reals
   `λ, μ > 0`, we have
   `(λt + μ) b(t) + d(t) ⊳ (λt + μ) a(t) + c(t)`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Interlacing sequences -/

/-- A list of polynomials is an **interlacing sequence** if every earlier
    polynomial interlaces every later one (with positive leading coefficients).

    This is the list-level packaging used here for Brändén's "common interleaver"
    language from Handbook of Enumerative Combinatorics, §7.8, after Theorem 7.8.1. -/
def IsInterlacingSeq : List ℝ[X] → Prop
  | [] => True
  | [_] => True
  | fs => ∀ (i j : Fin fs.length), i < j → Prec (fs.get i) (fs.get j)

/-- An interlacing sequence in Brändén's `𝓕ₙ⁺`: each member is real-rooted with
non-negative coefficients, and the list is pairwise interlacing. The
elementwise clause is needed so singleton lists are treated correctly. -/
def IsInterlacingSeqNonneg (fs : List ℝ[X]) : Prop :=
  (∀ f ∈ fs, (f ≠ 0 ∧ f.Splits) ∧ HasNonnegCoeffs f) ∧
  IsInterlacingSeq fs

/-- Weak zero-aware version of `IsInterlacingSeq`, using `Prec0` instead of the
strict nonzero relation `Prec`. This matches the handbook converse setup where
sparse test families may contain zero polynomials. -/
def IsInterlacingSeq0 : List ℝ[X] → Prop
  | [] => True
  | [_] => True
  | fs => ∀ (i j : Fin fs.length), i < j → Prec0 (fs.get i) (fs.get j)

/-- Weak zero-aware interlacing sequence with non-negative coefficients. -/
def IsInterlacingSeq0Nonneg (fs : List ℝ[X]) : Prop :=
  IsInterlacingSeq0 fs ∧ ∀ f ∈ fs, HasNonnegCoeffs f

/-- `𝓕ₙ⁺`: the type of interlacing sequences of length `n` with
    non-negative coefficients. -/
def InterlacingSeqNonneg (n : ℕ) :=
  { fs : List ℝ[X] // fs.length = n ∧ IsInterlacingSeqNonneg fs }

/-- Weak zero-aware counterpart of `InterlacingSeqNonneg`. -/
def InterlacingSeq0Nonneg (n : ℕ) :=
  { fs : List ℝ[X] // fs.length = n ∧ IsInterlacingSeq0Nonneg fs }

/-! ## Basic properties -/

/-- `IsInterlacingSeq` is exactly the pairwise `Prec` relation on a list. -/
lemma isInterlacingSeq_iff_pairwise {fs : List ℝ[X]} :
    IsInterlacingSeq fs ↔ fs.Pairwise Prec := by
  constructor
  · intro h
    cases fs with
    | nil =>
        simp
    | cons f fs =>
        cases fs with
        | nil =>
            simp
        | cons g gs =>
            exact List.pairwise_iff_get.2 (by simpa [IsInterlacingSeq] using h)
  · intro h
    cases fs with
    | nil =>
        trivial
    | cons f fs =>
        cases fs with
        | nil =>
            trivial
        | cons g gs =>
            simpa [IsInterlacingSeq] using (List.pairwise_iff_get.1 h)

/-- `IsInterlacingSeq0` is exactly pairwise `Prec0`. -/
lemma isInterlacingSeq0_iff_pairwise {fs : List ℝ[X]} :
    IsInterlacingSeq0 fs ↔ fs.Pairwise Prec0 := by
  constructor
  · intro h
    cases fs with
    | nil =>
        simp
    | cons f fs =>
        cases fs with
        | nil =>
            simp
        | cons g gs =>
            exact List.pairwise_iff_get.2 (by simpa [IsInterlacingSeq0] using h)
  · intro h
    cases fs with
    | nil =>
        trivial
    | cons f fs =>
        cases fs with
        | nil =>
            trivial
        | cons g gs =>
            simpa [IsInterlacingSeq0] using (List.pairwise_iff_get.1 h)

/-- A strict interlacing sequence is also interlacing in the weak `Prec0`
sense. -/
lemma IsInterlacingSeq.toIsInterlacingSeq0 {fs : List ℝ[X]} (h : IsInterlacingSeq fs) :
    IsInterlacingSeq0 fs := by
  rw [isInterlacingSeq_iff_pairwise] at h
  rw [isInterlacingSeq0_iff_pairwise]
  exact h.imp Prec.toPrec0

/-- Any pair in an interlacing sequence interlaces. -/
lemma IsInterlacingSeq.prec {fs : List ℝ[X]} (h : IsInterlacingSeq fs)
    {i j : Fin fs.length} (hij : i < j) :
    Prec (fs.get i) (fs.get j) := by
  cases fs with
  | nil =>
      grind
  | cons f fs =>
      cases fs with
      | nil =>
          grind
      | cons g gs =>
          simpa [IsInterlacingSeq] using h i j hij

/-- Any pair in a weak zero-aware interlacing sequence satisfies `Prec0`. -/
lemma IsInterlacingSeq0.prec0 {fs : List ℝ[X]} (h : IsInterlacingSeq0 fs)
    {i j : Fin fs.length} (hij : i < j) :
    Prec0 (fs.get i) (fs.get j) := by
  cases fs with
  | nil =>
      grind
  | cons f fs =>
      cases fs with
      | nil =>
          grind
      | cons g gs =>
          simpa [IsInterlacingSeq0] using h i j hij

/-- A subsequence of an interlacing sequence is interlacing. -/
lemma IsInterlacingSeq.sublist {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq fs) (hgs : gs.Sublist fs) :
    IsInterlacingSeq gs := by
  rw [isInterlacingSeq_iff_pairwise] at hfs ⊢
  grind

lemma IsInterlacingSeqNonneg.sublist {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) (hgs : gs.Sublist fs) :
    IsInterlacingSeqNonneg gs := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact hfs.1 p (hgs.subset hp)
  · exact hfs.2.sublist hgs

lemma IsInterlacingSeq0.sublist {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq0 fs) (hgs : gs.Sublist fs) :
    IsInterlacingSeq0 gs := by
  rw [isInterlacingSeq0_iff_pairwise] at hfs ⊢
  grind

lemma IsInterlacingSeq0Nonneg.sublist_of_realRooted_of_ne
    {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs) (hgs : gs.Sublist fs)
    (hreal : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hne : ∀ f ∈ gs, f ≠ 0) :
    IsInterlacingSeqNonneg gs := by
  refine ⟨?_, ?_⟩
  · intro p hp
    exact ⟨hreal p (hgs.subset hp) (hne p hp), hfs.2 p (hgs.subset hp)⟩
  · have hgs0 : IsInterlacingSeq0 gs := hfs.1.sublist hgs
    rw [isInterlacingSeq_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    have hprec0 := hgs0.prec0 (i := i) (j := j) hij
    exact hprec0.toPrec_of_ne
      (hne _ (List.get_mem _ _)) (hne _ (List.get_mem _ _))

/-- Concatenating two interlacing sequences that are compatible
    (every element of the first interlaces every element of the second). -/
lemma IsInterlacingSeq.append {fs gs : List ℝ[X]}
    (hfs : IsInterlacingSeq fs) (hgs : IsInterlacingSeq gs)
    (hfg : ∀ f ∈ fs, ∀ g ∈ gs, Prec f g) :
    IsInterlacingSeq (fs ++ gs) := by
  rw [isInterlacingSeq_iff_pairwise] at hfs hgs ⊢
  grind

/-- Reversing an interlacing sequence preserves pairwise interlacing. -/
lemma IsInterlacingSeq.reverse {fs : List ℝ[X]} (hfs : IsInterlacingSeq fs) :
    fs.reverse.Pairwise (fun f g => Prec g f) := by
  rw [isInterlacingSeq_iff_pairwise] at hfs
  grind

/-- Reversing a weak zero-aware interlacing sequence preserves pairwise
interlacing. -/
lemma IsInterlacingSeq0.reverse {fs : List ℝ[X]} (hfs : IsInterlacingSeq0 fs) :
    fs.reverse.Pairwise (fun f g => Prec0 g f) := by
  rw [isInterlacingSeq0_iff_pairwise] at hfs
  grind

/-- Reversing an interlacing sequence with nonnegative coefficients preserves
the same structure. -/
lemma IsInterlacingSeqNonneg.reverse {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) : (∀ f ∈ fs.reverse, (f ≠ 0 ∧ f.Splits) ∧ HasNonnegCoeffs f) ∧
    fs.reverse.Pairwise (fun f g => Prec g f) := by
  rcases hfs with ⟨hmem, hint⟩
  refine ⟨?_, hint.reverse⟩
  simp_all

lemma IsInterlacingSeqNonneg.realRooted {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits) := by
  intro f hf
  exact (hfs.1 f hf).1

lemma IsInterlacingSeqNonneg.splits {fs : List ℝ[X]} (hfs : IsInterlacingSeqNonneg fs) {f : ℝ[X]}
    (hf : f ∈ fs) : f.Splits := (hfs.1 f hf).1.2

lemma IsInterlacingSeqNonneg.posLeadingCoeff {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ fs, HasPosLeadingCoeff f := by
  intro f hf
  exact ((hfs.1 f hf).2).pos_leadingCoeff (hfs.realRooted f hf).1

lemma IsInterlacingSeqNonneg.nonnegCoeffs {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ fs, HasNonnegCoeffs f := by
  intro f hf
  exact (hfs.1 f hf).2

lemma IsInterlacingSeq0Nonneg.filter_ne_zero_of_realRooted
    {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hreal : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg (fs.filter (· ≠ 0)) := by
  rcases hfs with ⟨hint0, hnonneg⟩
  have hpair0 : fs.Pairwise Prec0 := isInterlacingSeq0_iff_pairwise.mp hint0
  refine ⟨?_, ?_⟩
  · simp_all
  · rw [isInterlacingSeq_iff_pairwise]
    have hpair_filter0 : (fs.filter (· ≠ 0)).Pairwise Prec0 := hpair0.filter _
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    have hfg0 := List.pairwise_iff_get.1 hpair_filter0 i j hij
    have hfi_mem : (fs.filter (· ≠ 0)).get i ∈ fs.filter (· ≠ 0) :=
      List.get_mem _ _
    have hgj_mem : (fs.filter (· ≠ 0)).get j ∈ fs.filter (· ≠ 0) :=
      List.get_mem _ _
    have hfi_ne : (fs.filter (· ≠ 0)).get i ≠ 0 :=
      of_decide_eq_true (List.mem_filter.mp hfi_mem).2
    have hgj_ne : (fs.filter (· ≠ 0)).get j ≠ 0 :=
      of_decide_eq_true (List.mem_filter.mp hgj_mem).2
    exact hfg0.toPrec_of_ne hfi_ne hgj_ne

end RealRooted
