module

public import RealRooted.Mesh.DiscreteMultiplier
public import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Discrete multiplier sequences

Brändén, Krasikov, and Shapiro, *Elements of Pólya--Schur theory in finite difference setting*,
Proc. AMS 144 (2016), Corollary 2 (polynomial case): if `φ` is a nonzero real-rooted polynomial
with only nonpositive roots, then `i ↦ φ(i)` is a discrete multiplier sequence.

The falling factorials `[x]_i = descPochhammer ℝ i` are eigenvectors of the discrete Euler
operator `xΔ p = X * (p - p(X - 1))`, with `xΔ [x]_i = i [x]_i`.  Hence `φ(xΔ)` acts on `[x]_i`
by `φ(i)`, and `φ(xΔ) = c ∏ (c_k + xΔ)` is a composition of the operators of Theorem 5
(`RealRooted.meshGE_one_add_X_mul_meshDifference`).

The linear map sending `[x]_i` to `a i • [x]_i` exists and is unique, because the falling
factorials form a basis of `ℝ[X]` (`Polynomial.descPochhammerBasis`).  We phrase
`IsDiscreteMultiplierSequence` by quantifying over all linear maps with this action.  Proposition 12
of the paper (`IsDiscreteMultiplierSequence.le_succ`) shows that a discrete multiplier sequence is
weakly increasing wherever it is positive.  See RealRooted issue #2070.
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-! ### The discrete Euler operator -/

/-- The discrete Euler operator `xΔ p = X * (p - p(X - 1))` as a linear map. -/
def discreteEuler : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := X * meshDifference 1 1 p
  map_add' p q := by
    simp only [meshDifference, add_comp]
    ring
  map_smul' c p := by
    simp only [meshDifference, smul_comp, RingHom.id_apply, map_one, one_mul]
    simp only [smul_eq_C_mul]
    ring

@[simp]
theorem discreteEuler_apply (p : ℝ[X]) :
    discreteEuler p = X * meshDifference 1 1 p := rfl

/-- The falling factorials are eigenvectors of the discrete Euler operator:
`xΔ [x]_i = i [x]_i`. -/
theorem discreteEuler_descPochhammer (i : ℕ) :
    discreteEuler (descPochhammer ℝ i) = (i : ℝ) • descPochhammer ℝ i := by
  cases i with
  | zero => simp [meshDifference]
  | succ n =>
    have h := descPochhammer_succ_comp_X_sub_one (R := ℝ) n
    simp only [discreteEuler_apply, meshDifference, map_one, one_mul, h]
    rw [descPochhammer_succ_left (R := ℝ) n]
    simp only [smul_eq_C_mul, sub_sub_cancel, Nat.cast_add, Nat.cast_one, map_add, map_natCast,
      map_one]
    ring

/-- `φ(xΔ)` acts on the falling factorial `[x]_i` by multiplication with `φ(i)`. -/
theorem aeval_discreteEuler_descPochhammer (φ : ℝ[X]) (i : ℕ) :
    aeval discreteEuler φ (descPochhammer ℝ i) = φ.eval (i : ℝ) • descPochhammer ℝ i := by
  have hev : Module.End.HasEigenvector discreteEuler (i : ℝ) (descPochhammer ℝ i) :=
    ⟨Module.End.mem_eigenspace_iff.mpr (discreteEuler_descPochhammer i),
      (monic_descPochhammer ℝ i).ne_zero⟩
  exact Module.End.aeval_apply_of_hasEigenvector hev

/-! ### Preservation of the mesh class -/

/-- The class of polynomials with mesh at least one and only nonnegative roots. -/
private def MeshClass (p : ℝ[X]) : Prop := p.MeshGE 1 ∧ HasOnlyNonnegRoots p

private theorem MeshClass.aeval_X_sub_C {r : ℝ} (hr : r ≤ 0) {p : ℝ[X]} (hp : MeshClass p) :
    MeshClass (aeval discreteEuler (X - C r) p) := by
  have h := meshGE_one_add_X_mul_meshDifference (a := -r) (b := 1) (neg_nonneg.mpr hr)
    zero_le_one hp.1 hp.2
  have e : aeval discreteEuler (X - C r) p =
      C (-r) * p + C 1 * (X * meshDifference 1 1 p) := by
    simp [sub_eq_add_neg, smul_eq_C_mul]
    ring
  rw [e]
  exact h

private theorem MeshClass.aeval_prod {s : Multiset ℝ} (hs : ∀ r ∈ s, r ≤ 0) {p : ℝ[X]}
    (hp : MeshClass p) :
    MeshClass (aeval discreteEuler (s.map fun r => X - C r).prod p) := by
  induction s using Multiset.induction_on generalizing p with
  | empty => simpa using hp
  | cons r s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply]
    exact MeshClass.aeval_X_sub_C (hs r (Multiset.mem_cons_self r s))
      (ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)) hp)

/-- BKS 2016, Corollary 2 (operator form): if `φ ≠ 0` is real-rooted with only nonpositive roots,
then `φ(xΔ)` preserves real-rooted polynomials with nonnegative roots and mesh at least one. -/
theorem meshGE_one_aeval_discreteEuler {φ : ℝ[X]} (hφ : φ ≠ 0) (hs : φ.Splits)
    (hroots : ∀ r ∈ φ.roots, r ≤ 0) {p : ℝ[X]} (hp : p.MeshGE 1) (hpnn : HasOnlyNonnegRoots p) :
    (aeval discreteEuler φ p).MeshGE 1 ∧ HasOnlyNonnegRoots (aeval discreteEuler φ p) := by
  have hφeq : φ = C φ.leadingCoeff * (φ.roots.map fun r => X - C r).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C (splits_iff_card_roots.mp hs)).symm
  have hc : φ.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hφ
  obtain ⟨h1, h2⟩ := MeshClass.aeval_prod hroots (show MeshClass p from ⟨hp, hpnn⟩)
  have e : aeval discreteEuler φ p =
      C φ.leadingCoeff * aeval discreteEuler (φ.roots.map fun r => X - C r).prod p := by
    conv_lhs => rw [hφeq]
    simp [smul_eq_C_mul]
  rw [e]
  exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 hc).2 h1, (HasOnlyNonnegRoots.C_mul_iff hc _).2 h2⟩

/-! ### Discrete multiplier sequences -/

/-- A sequence `a` is a *discrete multiplier sequence* if the linear operator `T` with
`T [x]_i = a i • [x]_i` on the falling factorials `[x]_i = descPochhammer ℝ i` preserves the class
of polynomials with mesh at least one and only nonnegative roots.  The falling factorials span
`ℝ[X]` (`Polynomial.descPochhammerBasis`), so such a `T` is unique
(`Polynomial.linearMap_ext_descPochhammer`) and exists for every `a`
(`RealRooted.exists_linearMap_descPochhammer`), so the predicate is not vacuous.  We quantify over
all of them instead of fixing a choice. -/
def IsDiscreteMultiplierSequence (a : ℕ → ℝ) : Prop :=
  ∀ T : ℝ[X] →ₗ[ℝ] ℝ[X], (∀ i, T (descPochhammer ℝ i) = a i • descPochhammer ℝ i) →
    ∀ p : ℝ[X], p.MeshGE 1 → HasOnlyNonnegRoots p → (T p).MeshGE 1 ∧ HasOnlyNonnegRoots (T p)

/-- BKS 2016, Corollary 2 (polynomial case): if `φ ≠ 0` is real-rooted with only nonpositive
roots, then `i ↦ φ(i)` is a discrete multiplier sequence. -/
theorem isDiscreteMultiplierSequence_eval {φ : ℝ[X]} (hφ : φ ≠ 0) (hs : φ.Splits)
    (hroots : ∀ r ∈ φ.roots, r ≤ 0) :
    IsDiscreteMultiplierSequence fun i : ℕ => φ.eval (i : ℝ) := by
  intro T hT p hp hpnn
  have hTeq : T = aeval discreteEuler φ := by
    apply Polynomial.linearMap_ext_descPochhammer
    intro i
    rw [hT i]
    exact (aeval_discreteEuler_descPochhammer φ i).symm
  rw [hTeq]
  exact meshGE_one_aeval_discreteEuler hφ hs hroots hp hpnn

/-- Discrete multiplier sequences exist for every sequence of values on the falling factorials:
there is a linear operator `T` with `T [x]_i = a i • [x]_i`.  (This does not claim that `T`
preserves the mesh class; that is `IsDiscreteMultiplierSequence a`.) -/
theorem exists_linearMap_descPochhammer (a : ℕ → ℝ) :
    ∃ T : ℝ[X] →ₗ[ℝ] ℝ[X], ∀ i, T (descPochhammer ℝ i) = a i • descPochhammer ℝ i :=
  Polynomial.exists_linearMap_descPochhammer fun i => a i • descPochhammer ℝ i

/-! ### Monotonicity of positive multiplier sequences -/

private theorem descPochhammer_eq_prod (m : ℕ) :
    descPochhammer ℝ m = ((Multiset.range m).map fun j : ℕ => X - C (j : ℝ)).prod := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_right, ih, Multiset.range_succ, Multiset.map_cons,
      Multiset.prod_cons, mul_comm]
    simp

/-- The roots `0, 1, …, m - 1, m + t, m + 1 + t` of the test polynomial. -/
private def testRoots (m : ℕ) (t : ℝ) : Multiset ℝ :=
  (Multiset.range m).map (fun j : ℕ => (j : ℝ)) + {(m : ℝ) + t, (m : ℝ) + 1 + t}

private theorem testRoots_prod (m : ℕ) (t : ℝ) :
    ((testRoots m t).map fun r => X - C r).prod =
      descPochhammer ℝ m * ((X - C ((m : ℝ) + t)) * (X - C ((m : ℝ) + 1 + t))) := by
  rw [descPochhammer_eq_prod]
  simp [testRoots, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
  ring

private theorem mem_testRoots {m : ℕ} {t r : ℝ} :
    r ∈ testRoots m t ↔ (∃ j : ℕ, j < m ∧ (j : ℝ) = r) ∨ r = (m : ℝ) + t ∨
      r = (m : ℝ) + 1 + t := by
  simp only [testRoots, Multiset.mem_add, Multiset.mem_map, Multiset.mem_range,
    Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]

private theorem testRoots_gap {m : ℕ} {t : ℝ} (ht : 0 < t) {r s : ℝ}
    (hr : r ∈ testRoots m t) (hs : s ∈ testRoots m t) (hrs : r < s) : r + 1 ≤ s := by
  rw [mem_testRoots] at hr hs
  rcases hr with ⟨j, hj, rfl⟩ | rfl | rfl <;> rcases hs with ⟨k, hk, rfl⟩ | rfl | rfl
  · have : j < k := by exact_mod_cast hrs
    have : j + 1 ≤ k := this
    exact_mod_cast this
  · have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    linarith
  · have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    linarith
  · have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
    linarith
  · exact absurd hrs (lt_irrefl _)
  · linarith
  · have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
    linarith
  · linarith
  · exact absurd hrs (lt_irrefl _)

private theorem testRoots_nodup (m : ℕ) {t : ℝ} (ht : 0 < t) : (testRoots m t).Nodup := by
  unfold testRoots
  rw [Multiset.nodup_add]
  refine ⟨(Multiset.nodup_range m).map Nat.cast_injective, ?_, ?_⟩
  · simp
  · rw [Multiset.disjoint_left]
    intro r hr
    simp only [Multiset.mem_map, Multiset.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    constructor <;> intro h <;> linarith

private theorem meshClass_testRoots (m : ℕ) {t : ℝ} (ht : 0 < t) :
    MeshClass ((testRoots m t).map fun r => X - C r).prod := by
  have hsplit : ((testRoots m t).map fun r => X - C r).prod.Splits := by
    apply Splits.multisetProd
    intro f hf
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hf
    exact Splits.X_sub_C r
  have hroots := roots_multiset_prod_X_sub_C (testRoots m t)
  refine ⟨?_, Or.inr ⟨hsplit, fun r hr => ?_⟩⟩
  · rw [Polynomial.MeshGE.iff_roots_nodup_pairwise_gap one_pos]
    refine ⟨hsplit, by rw [hroots]; exact testRoots_nodup m ht, fun r hr s hs hrs => ?_⟩
    rw [hroots] at hr hs
    rw [le_abs]
    rcases lt_or_gt_of_ne hrs with h | h
    · right
      linarith [testRoots_gap ht hr hs h]
    · left
      linarith [testRoots_gap ht hs hr h]
  · rw [hroots, mem_testRoots] at hr
    rcases hr with ⟨j, -, rfl⟩ | rfl | rfl
    · exact Nat.cast_nonneg j
    · positivity
    · positivity

/-- The quadratic `A (x - m)(x - m - 1) - 2 t B (x - m) + t (t + 1) C`, expanded. -/
private def quadFactor (A B C : ℝ) (m : ℕ) (t : ℝ) : ℝ[X] :=
  Polynomial.C A * X ^ 2 + Polynomial.C (-(A * (2 * m + 1)) - 2 * t * B) * X +
    Polynomial.C (A * m * (m + 1) + 2 * t * B * m + t * (t + 1) * C)

private theorem eval_quadFactor (A B C : ℝ) (m : ℕ) (t z : ℝ) :
    (quadFactor A B C m t).eval z =
      A * z ^ 2 + (-(A * (2 * m + 1)) - 2 * t * B) * z +
        (A * m * (m + 1) + 2 * t * B * m + t * (t + 1) * C) := by
  simp [quadFactor]

private theorem natDegree_quadFactor {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (m : ℕ) (t : ℝ) :
    (quadFactor A B C m t).natDegree = 2 :=
  natDegree_quadratic hA

private theorem testRoots_prod_eq (m : ℕ) (t : ℝ) :
    ((testRoots m t).map fun r => X - C r).prod =
      descPochhammer ℝ (m + 2) - (2 * t) • descPochhammer ℝ (m + 1) +
        (t * (t + 1)) • descPochhammer ℝ m := by
  rw [testRoots_prod, descPochhammer_succ_right, descPochhammer_succ_right]
  simp only [smul_eq_C_mul, map_mul, map_add, map_natCast, map_ofNat, map_one, Nat.cast_add,
    Nat.cast_one]
  ring

/-- BKS 2016, Proposition 12: for a discrete multiplier sequence `a`, positivity of `a (m + 2)`
forces `a m ≤ a (m + 1)`. -/
theorem IsDiscreteMultiplierSequence.le_succ {a : ℕ → ℝ} (ha : IsDiscreteMultiplierSequence a)
    (m : ℕ) (hpos : 0 < a (m + 2)) : a m ≤ a (m + 1) := by
  obtain ⟨T, hT⟩ := exists_linearMap_descPochhammer a
  have key : ∀ t : ℝ, 0 < t →
      0 ≤ a (m + 2) * (a (m + 1) - a m) + t * (a (m + 1) ^ 2 - a (m + 2) * a m) := by
    intro t ht
    have hp := meshClass_testRoots m ht
    obtain ⟨hmesh, -⟩ := ha T hT _ hp.1 hp.2
    have hTp : T ((testRoots m t).map fun r => X - C r).prod =
        descPochhammer ℝ m * quadFactor (a (m + 2)) (a (m + 1)) (a m) m t := by
      rw [testRoots_prod_eq, map_add, map_sub, map_smul, map_smul, hT, hT, hT]
      rw [descPochhammer_succ_right, descPochhammer_succ_right]
      simp only [quadFactor, smul_eq_C_mul, map_mul, map_add, map_sub, map_neg, map_natCast,
        map_ofNat, map_one, Nat.cast_add, Nat.cast_one]
      ring
    rw [hTp] at hmesh
    have hA : a (m + 2) ≠ 0 := hpos.ne'
    have hQdeg := natDegree_quadFactor hA (a (m + 1)) (a m) m t
    have hQne : quadFactor (a (m + 2)) (a (m + 1)) (a m) m t ≠ 0 := by
      intro h
      simp [h] at hQdeg
    have hPne := (monic_descPochhammer ℝ m).ne_zero
    have hne := mul_ne_zero hPne hQne
    have hQsplit := hmesh.1.of_dvd hne (dvd_mul_left _ _)
    have hcard : (quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots.card = 2 := by
      rw [splits_iff_card_roots.mp hQsplit, hQdeg]
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hcard
    have hle : (quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots ≤
        (descPochhammer ℝ m * quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots := by
      rw [roots_mul hne]
      exact Multiset.le_add_left _ _
    have hnodup := (hmesh.roots_nodup one_pos)
    have hxy_nodup : ({x, y} : Multiset ℝ).Nodup := by
      rw [← hxy]
      exact Multiset.nodup_of_le hle hnodup
    have hxy_ne : x ≠ y := by simpa using hxy_nodup
    have hxmem : x ∈ (descPochhammer ℝ m *
        quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots :=
      Multiset.subset_of_le hle (by rw [hxy]; simp)
    have hymem : y ∈ (descPochhammer ℝ m *
        quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots :=
      Multiset.subset_of_le hle (by rw [hxy]; simp)
    have hgap := ((Polynomial.MeshGE.iff_roots_nodup_pairwise_gap one_pos).1 hmesh).2.2 x hxmem
      y hymem hxy_ne
    have hxroot : (quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).eval x = 0 := by
      have : x ∈ (quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots := by rw [hxy]; simp
      exact (mem_roots hQne).1 this
    have hyroot : (quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).eval y = 0 := by
      have : y ∈ (quadFactor (a (m + 2)) (a (m + 1)) (a m) m t).roots := by rw [hxy]; simp
      exact (mem_roots hQne).1 this
    rw [eval_quadFactor] at hxroot hyroot
    have hsq : 1 ≤ (x - y) ^ 2 := by
      have h1 : 1 ≤ |x - y| := by simpa using hgap
      nlinarith [sq_abs (x - y)]
    generalize a (m + 2) = A at *
    generalize a (m + 1) = B at *
    generalize a m = Cc at *
    have hsum : A * (x + y) = A * (2 * m + 1) + 2 * t * B := by
      have h0 : (x - y) * (A * (x + y) + (-(A * (2 * m + 1)) - 2 * t * B)) = 0 := by
        linear_combination hxroot - hyroot
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd (sub_eq_zero.mp h) hxy_ne
      · linarith
    have hprod : A * (x * y) = A * m * (m + 1) + 2 * t * B * m + t * (t + 1) * Cc := by
      linear_combination (-1 : ℝ) * hxroot + x * hsum
    have hmain : A ^ 2 * 1 ≤ A ^ 2 * (x - y) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg A)
    have hid : A ^ 2 * (x - y) ^ 2 = (A * (x + y)) ^ 2 - 4 * A * (A * (x * y)) := by ring
    rw [hid, hsum, hprod] at hmain
    have h4 : 0 ≤ 4 * t * (A * (B - Cc) + t * (B ^ 2 - A * Cc)) := by nlinarith
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * t)).1 h4
    exact this
  by_contra hlt
  push Not at hlt
  have hδ : 0 < a (m + 2) * (a m - a (m + 1)) := mul_pos hpos (sub_pos.2 hlt)
  by_cases hK : a (m + 1) ^ 2 - a (m + 2) * a m ≤ 0
  · have := key 1 one_pos
    nlinarith
  · push Not at hK
    have := key (a (m + 2) * (a m - a (m + 1)) / (2 * (a (m + 1) ^ 2 - a (m + 2) * a m)))
      (by positivity)
    have e : a (m + 2) * (a m - a (m + 1)) / (2 * (a (m + 1) ^ 2 - a (m + 2) * a m)) *
        (a (m + 1) ^ 2 - a (m + 2) * a m) = a (m + 2) * (a m - a (m + 1)) / 2 := by
      field_simp
    nlinarith

end

end RealRooted
