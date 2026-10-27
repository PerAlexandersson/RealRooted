module

public import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer
public import RealRooted.Mesh.Basic
public import RealRooted.Mesh.FiniteDifference
public import RealRooted.NarayanaTransformation.RootGeometry
import RealRooted.Linear
import RealRooted.Mesh.DiscreteMultiplier
import RealRooted.Mesh.FallingFactorial

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

open Polynomial Module

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

/-! ### Falling-factorial coordinates and Corollary 3 -/

/-- A linear operator that is diagonal on the falling factorials multiplies the `k`-th
falling-factorial coordinate by `a k`. -/
theorem descPochhammerBasis_repr_apply_eq_mul_repr {a : ℕ → ℝ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : ∀ i, T (descPochhammer ℝ i) = a i • descPochhammer ℝ i) (p : ℝ[X]) (k : ℕ) :
    (descPochhammerBasis ℝ).repr (T p) k = a k * (descPochhammerBasis ℝ).repr p k := by
  have e : ∀ i, descPochhammerBasis ℝ i = descPochhammer ℝ i := fun i =>
    descPochhammerBasis_apply i
  have h : (descPochhammerBasis ℝ).coord k ∘ₗ T = a k • (descPochhammerBasis ℝ).coord k := by
    refine (descPochhammerBasis ℝ).ext fun i => ?_
    rw [LinearMap.comp_apply, e i, hT i, ← e i, map_smul, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]
  have := LinearMap.congr_fun h p
  simpa using this

private theorem roots_descPochhammer (n : ℕ) :
    (descPochhammer ℝ n).roots = (Multiset.range n).map fun j : ℕ => (j : ℝ) := by
  have := roots_multiset_prod_X_sub_C ((Multiset.range n).map fun j : ℕ => (j : ℝ))
  rw [Multiset.map_map] at this
  rw [descPochhammer_eq_prod]
  exact this

private theorem meshGE_descPochhammer (n : ℕ) : (descPochhammer ℝ n).MeshGE 1 := by
  have hs : (descPochhammer ℝ n).Splits := by
    rw [splits_iff_card_roots, roots_descPochhammer, descPochhammer_natDegree]
    simp
  rw [Polynomial.MeshGE.iff_roots_nodup_pairwise_gap one_pos]
  refine ⟨hs, ?_, fun r hr s hs' hrs => ?_⟩
  · rw [roots_descPochhammer]
    exact (Multiset.nodup_range n).map Nat.cast_injective
  · rw [roots_descPochhammer, Multiset.mem_map] at hr hs'
    obtain ⟨j, -, rfl⟩ := hr
    obtain ⟨k, -, rfl⟩ := hs'
    have hjk : j ≠ k := fun h => hrs (by rw [h])
    rw [le_abs]
    rcases lt_or_gt_of_ne hjk with h | h
    · right
      have : j + 1 ≤ k := h
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast this
      linarith
    · left
      have : k + 1 ≤ j := h
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast this
      linarith

/-- The shifted falling factorial `[x - t]_n`. -/
private def shiftedFalling (n : ℕ) (t : ℝ) : ℝ[X] := (descPochhammer ℝ n).comp (X - C t)

private theorem shiftedFalling_meshClass (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasPosLeadingCoeff (shiftedFalling n t) ∧ (shiftedFalling n t).MeshGE 1 ∧
      HasOnlyNonnegRoots (shiftedFalling n t) := by
  have hform : shiftedFalling n t = (descPochhammer ℝ n).comp (X + C (-t)) := by
    simp [shiftedFalling, sub_eq_add_neg]
  have hmesh : (shiftedFalling n t).MeshGE 1 := by
    rw [hform]
    exact (Polynomial.MeshGE.comp_X_add_C_iff _ 1 (-t)).2 (meshGE_descPochhammer n)
  have hmonic : (shiftedFalling n t).Monic := by
    rw [hform]
    exact (monic_descPochhammer ℝ n).comp (monic_X_add_C _)
      (by rw [natDegree_X_add_C]; exact one_ne_zero)
  refine ⟨by simp [HasPosLeadingCoeff, hmonic.leadingCoeff], hmesh,
    Or.inr ⟨hmesh.1, fun r hr => ?_⟩⟩
  rw [hform, roots_comp_X_add_C, roots_descPochhammer, Multiset.map_map,
    Multiset.mem_map] at hr
  obtain ⟨j, -, rfl⟩ := hr
  simp only [Function.comp_apply, sub_neg_eq_add]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

private theorem shiftedFalling_natDegree (n : ℕ) (t : ℝ) :
    (shiftedFalling n t).natDegree = n := by
  simp [shiftedFalling, natDegree_comp]

private theorem eval_zero_shiftedFalling_ne_zero {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (shiftedFalling n t).eval 0 ≠ 0 := by
  have h : (shiftedFalling n t).eval 0 = (descPochhammer ℝ n).eval (-t) := by
    simp [shiftedFalling]
  rw [h]
  clear h
  induction n with
  | zero => simp
  | succ m ih =>
    rw [descPochhammer_succ_eval]
    refine mul_ne_zero ih ?_
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    intro h0
    linarith

private theorem forwardDifference_shiftedFalling (n : ℕ) (t : ℝ) :
    forwardDifference (shiftedFalling (n + 1) t) = ((n : ℝ) + 1) • shiftedFalling n t := by
  have h1 : forwardDifference (shiftedFalling (n + 1) t) =
      (forwardDifference (descPochhammer ℝ (n + 1))).comp (X - C t) := by
    simp only [forwardDifference_apply, shiftedFalling, sub_comp, comp_assoc]
    congr 2
    simp only [add_comp, X_comp, C_comp]
    ring
  rw [h1, forwardDifference_descPochhammer]
  simp [shiftedFalling, smul_comp]

private theorem repr_shiftedFalling_ne_zero {t : ℝ} (ht : 0 < t) :
    ∀ k n : ℕ, k ≤ n → (descPochhammerBasis ℝ).repr (shiftedFalling n t) k ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro n _
    rw [descPochhammerBasis_repr_zero]
    exact eval_zero_shiftedFalling_ne_zero ht n
  | succ k ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by lia⟩
    have h := descPochhammerBasis_repr_forwardDifference (shiftedFalling (n' + 1) t) k
    rw [forwardDifference_shiftedFalling, map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have hk := ih n' (by lia)
    intro h0
    rw [h0, mul_zero] at h
    exact mul_ne_zero (by positivity) hk h

/-- The coordinates of `[x - 1]_n` are nonzero, and alternate in sign. -/
private theorem shiftedFalling_sign {n : ℕ} :
    ∀ k ≤ n, 0 < (-1 : ℝ) ^ (n - k) * (descPochhammerBasis ℝ).repr (shiftedFalling n 1) k := by
  obtain ⟨hpos, hmesh, hnn⟩ := shiftedFalling_meshClass n (t := 1) zero_le_one
  intro k hk
  have h := neg_one_pow_mul_descPochhammerBasis_repr_nonneg hpos hmesh hnn (i := k)
    (by rw [shiftedFalling_natDegree]; exact hk)
  rw [shiftedFalling_natDegree] at h
  refine lt_of_le_of_ne h fun h0 => repr_shiftedFalling_ne_zero one_pos k n hk ?_
  rcases mul_eq_zero.mp h0.symm with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact h

/-- The image of `[x - 1]_n` under a diagonal operator with `a n ≠ 0` has degree `n`, and lies in
the mesh class when `a` is a discrete multiplier sequence. -/
private theorem IsDiscreteMultiplierSequence.shifted {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : ∀ i, T (descPochhammer ℝ i) = a i • descPochhammer ℝ i) {n : ℕ} (hn : a n ≠ 0) :
    T (shiftedFalling n 1) ≠ 0 ∧ (T (shiftedFalling n 1)).natDegree = n ∧
      (T (shiftedFalling n 1)).MeshGE 1 ∧ HasOnlyNonnegRoots (T (shiftedFalling n 1)) := by
  obtain ⟨-, hmesh, hnn⟩ := shiftedFalling_meshClass n (t := 1) zero_le_one
  obtain ⟨hU1, hU2⟩ := ha T hT _ hmesh hnn
  have hrepr := descPochhammerBasis_repr_apply_eq_mul_repr hT (shiftedFalling n 1)
  have hcn := repr_shiftedFalling_ne_zero one_pos n n le_rfl
  refine ⟨?_, ?_, hU1, hU2⟩
  · intro h0
    have := hrepr n
    rw [h0, map_zero] at this
    exact mul_ne_zero hn hcn this.symm
  · apply le_antisymm
    · rw [natDegree_le_iff_repr_descPochhammerBasis]
      intro k hk
      have h0 := natDegree_le_iff_repr_descPochhammerBasis.mp
        (shiftedFalling_natDegree n 1).le k hk
      rw [hrepr, h0, mul_zero]
    · by_contra hlt
      push Not at hlt
      have := natDegree_le_iff_repr_descPochhammerBasis.mp le_rfl n hlt
      rw [hrepr] at this
      exact mul_ne_zero hn hcn this

/-- Along `[x - 1]_n`, the sign of a discrete multiplier sequence is constant on `0, …, n`. -/
private theorem IsDiscreteMultiplierSequence.sign_le {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) {n : ℕ} (hn : a n ≠ 0) :
    (∀ k ≤ n, 0 ≤ a k) ∨ (∀ k ≤ n, a k ≤ 0) := by
  obtain ⟨T, hT⟩ := exists_linearMap_descPochhammer a
  obtain ⟨hU0, hdeg, hU1, hU2⟩ := ha.shifted hT hn
  have hrepr := descPochhammerBasis_repr_apply_eq_mul_repr hT (shiftedFalling n 1)
  set U := T (shiftedFalling n 1) with hU
  have hc := shiftedFalling_sign (n := n)
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hU0) with hneg | hposU
  · right
    have hV : HasPosLeadingCoeff (C (-1) * U) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C]
      linarith
    have hVdeg : (C (-1 : ℝ) * U).natDegree = n := by
      rw [natDegree_C_mul (by norm_num), hdeg]
    intro k hk
    have h' := neg_one_pow_mul_descPochhammerBasis_repr_nonneg hV
      ((Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).2 hU1)
      ((HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).2 hU2) (i := k) (by rw [hVdeg]; exact hk)
    rw [hVdeg, ← smul_eq_C_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, hrepr] at h'
    have := hc k hk
    by_contra hak
    push Not at hak
    have e : (-1 : ℝ) ^ (n - k) * (-1 * (a k * (descPochhammerBasis ℝ).repr
        (shiftedFalling n 1) k)) = -(a k * ((-1 : ℝ) ^ (n - k) *
        (descPochhammerBasis ℝ).repr (shiftedFalling n 1) k)) := by ring
    rw [e] at h'
    nlinarith [mul_pos hak this]
  · left
    intro k hk
    have h' := neg_one_pow_mul_descPochhammerBasis_repr_nonneg hposU hU1 hU2 (i := k)
      (by rw [hdeg]; exact hk)
    rw [hdeg, hrepr] at h'
    have := hc k hk
    by_contra hak
    push Not at hak
    have e : (-1 : ℝ) ^ (n - k) * (a k * (descPochhammerBasis ℝ).repr
        (shiftedFalling n 1) k) = a k * ((-1 : ℝ) ^ (n - k) *
        (descPochhammerBasis ℝ).repr (shiftedFalling n 1) k) := by ring
    rw [e] at h'
    nlinarith [mul_pos (neg_pos.mpr hak) this]

/-- BKS 2016, Corollary 3: all nonzero entries of a discrete multiplier sequence have the same
sign. -/
theorem IsDiscreteMultiplierSequence.nonneg_or_nonpos {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) : (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
  rcases le_total i j with hij | hji
  · rcases ha.sign_le hj.ne' with h | h
    · exact absurd (h i hij) (not_le.mpr hi)
    · exact absurd (h j le_rfl) (not_le.mpr hj)
  · rcases ha.sign_le hi.ne with h | h
    · exact absurd (h i le_rfl) (not_le.mpr hi)
    · exact absurd (h j hji) (not_le.mpr hj)

/-! ### Proposition 7: sequences with two nonzero entries -/

private theorem sum_ge_of_pairwise_gap : ∀ (rs : List ℝ) (r : ℝ),
    rs.Pairwise (fun a b : ℝ => a + 1 ≤ b) → (∀ x ∈ rs, r ≤ x) →
      (rs.length : ℝ) * r + (rs.length : ℝ) * ((rs.length : ℝ) - 1) / 2 ≤ rs.sum
  | [], r, _, _ => by simp
  | x :: rs, r, hp, hr => by
      rw [List.pairwise_cons] at hp
      have ih := sum_ge_of_pairwise_gap rs (x + 1) hp.2 hp.1
      have hx := hr x (by simp)
      simp only [List.length_cons, List.sum_cons]
      push_cast
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (rs.length : ℝ) + 1) (sub_nonneg.2 hx)]

private theorem sum_range_cast (d : ℕ) :
    ∑ i ∈ Finset.range d, (i : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `A + B [x]_d` with `A, B ≠ 0` and `d ≥ 2` does not have mesh at least one with only
nonnegative roots: its roots would have the same sum as those of `[x]_d`, forcing the roots
`0, 1, …, d - 1`. -/
private theorem not_meshClass_const_add_descPochhammer {A B : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hA : A ≠ 0) (hB : B ≠ 0) (h1 : (C A + C B * descPochhammer ℝ d).MeshGE 1)
    (h2 : HasOnlyNonnegRoots (C A + C B * descPochhammer ℝ d)) : False := by
  have hPd := monic_descPochhammer ℝ d
  have hdegP := descPochhammer_natDegree (R := ℝ) d
  have hVW : C A + C B * descPochhammer ℝ d = C B * (descPochhammer ℝ d + C (A / B)) := by
    rw [mul_add, ← C_mul, mul_div_cancel₀ _ hB]
    ring
  rw [hVW] at h1 h2
  have hW1 := (Polynomial.MeshGE.C_mul_iff _ 1 hB).1 h1
  have hW2 := (HasOnlyNonnegRoots.C_mul_iff hB _).1 h2
  set W := descPochhammer ℝ d + C (A / B) with hW
  have hWdeg : W.natDegree = d := by
    rw [hW, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_C, hdegP]; lia), hdegP]
  have hWmonic : W.Monic := hPd.add_of_left (by
    rw [degree_eq_natDegree hPd.ne_zero, hdegP]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (by lia : 0 < d)))
  have hW0 := hWmonic.ne_zero
  have hWroots : ∀ r ∈ W.roots, 0 ≤ r := (hW2.resolve_left hW0).2
  have hPs : (descPochhammer ℝ d).Splits := by
    rw [splits_iff_card_roots, roots_descPochhammer, hdegP]
    simp
  have hnext : W.nextCoeff = (descPochhammer ℝ d).nextCoeff := by
    simp only [nextCoeff, hdegP, hW, coeff_add, coeff_C]
    have : d - 1 ≠ 0 := by lia
    simp [this, show d ≠ 0 by lia]
  have hsum : W.roots.sum = ∑ i ∈ Finset.range d, (i : ℝ) := by
    have e1 := hW1.1.nextCoeff_eq_neg_sum_roots_of_monic hWmonic
    have e2 := hPs.nextCoeff_eq_neg_sum_roots_of_monic hPd
    rw [hnext, e2, neg_inj] at e1
    rw [← e1, roots_descPochhammer]
    rfl
  -- the sorted roots
  have hgap := hW1.pairwise_sort_roots
  have hsort := Multiset.pairwise_sort W.roots (· ≤ ·)
  have hlen : (W.roots.sort (· ≤ ·)).length = d := by
    rw [Multiset.length_sort, splits_iff_card_roots.mp hW1.1, hWdeg]
  obtain ⟨r₀, rs, hrs⟩ : ∃ r₀ rs, W.roots.sort (· ≤ ·) = r₀ :: rs := by
    cases h : W.roots.sort (· ≤ ·) with
    | nil => rw [h] at hlen; simp at hlen; lia
    | cons r₀ rs => exact ⟨r₀, rs, rfl⟩
  rw [hrs] at hgap hsort hlen
  have hmin : ∀ x ∈ r₀ :: rs, r₀ ≤ x := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact (List.pairwise_cons.mp hsort).1 x hx
  have hbound := sum_ge_of_pairwise_gap (r₀ :: rs) r₀ hgap hmin
  have hsumlist : (r₀ :: rs).sum = W.roots.sum := by
    rw [← hrs, ← Multiset.sum_coe, Multiset.sort_eq]
  rw [hsumlist, hsum, sum_range_cast, hlen] at hbound
  have hr₀mem : r₀ ∈ W.roots := by
    rw [← Multiset.mem_sort (· ≤ ·), hrs]
    simp
  have hr₀ : 0 ≤ r₀ := hWroots r₀ hr₀mem
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by lia : 0 < d)
  have hr₀0 : r₀ = 0 := by nlinarith
  have hroot : W.eval 0 = 0 := by
    have := (mem_roots hW0).1 hr₀mem
    rwa [hr₀0, IsRoot.def] at this
  have h0 : (descPochhammer ℝ d).eval 0 = 0 := descPochhammer_ne_zero_eval_zero ℝ (by lia)
  rw [hW, eval_add, eval_C, h0, zero_add] at hroot
  exact hA ((div_eq_zero_iff.mp hroot).resolve_right hB)

/-- If `a` is a discrete multiplier sequence with `a i ≠ 0` and `a j ≠ 0` and no other nonzero
entries, then `j ≤ i + 1` for `i < j`. -/
private theorem IsDiscreteMultiplierSequence.not_two_apart {a : ℕ → ℝ}
    (ha : IsDiscreteMultiplierSequence a) {i j : ℕ} (hij : i + 2 ≤ j) (hi : a i ≠ 0)
    (hj : a j ≠ 0) (hz : ∀ k, k ≠ i → k ≠ j → a k = 0) : False := by
  obtain ⟨T, hT⟩ := exists_linearMap_descPochhammer a
  obtain ⟨hU0, hdeg, hU1, hU2⟩ := ha.shifted hT hj
  have hrepr := descPochhammerBasis_repr_apply_eq_mul_repr hT (shiftedFalling j 1)
  set U := T (shiftedFalling j 1) with hU
  obtain ⟨g0, g1, g2, g3⟩ := hU1.iterate_forwardDifference hU0 hU2 i (by lia)
  choose f hf hfrepr using descPochhammerBasis_repr_iterate_forwardDifference i
  have hc : ∀ k ≤ j, (descPochhammerBasis ℝ).repr (shiftedFalling j 1) k ≠ 0 := fun k hk =>
    repr_shiftedFalling_ne_zero one_pos k j hk
  obtain ⟨d, hd⟩ : ∃ d, j = i + d := ⟨j - i, by lia⟩
  have hd2 : 2 ≤ d := by lia
  have hVeq : (⇑forwardDifference)^[i] U =
      C (f U 0 * (a i * (descPochhammerBasis ℝ).repr (shiftedFalling j 1) i)) +
        C (f U d * (a j * (descPochhammerBasis ℝ).repr (shiftedFalling j 1) j)) *
          descPochhammer ℝ d := by
    apply (descPochhammerBasis ℝ).repr.injective
    ext k
    have e : ∀ x y : ℝ, C x + C y * descPochhammer ℝ d =
        x • descPochhammerBasis ℝ 0 + y • descPochhammerBasis ℝ d := fun x y => by
      simp [smul_eq_C_mul]
    rw [e, hfrepr U k, hrepr (k + i)]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hk0 : k = 0
    · subst hk0
      simp [show d ≠ 0 by lia]
    · by_cases hkd : k = d
      · subst hkd
        simp [← hd, add_comm, Ne.symm hk0]
      · have : a (k + i) = 0 := hz _ (by lia) (by lia)
        simp [this, Ne.symm hk0, Ne.symm hkd]
  rw [hVeq] at g2 g3
  refine not_meshClass_const_add_descPochhammer hd2 ?_ ?_ g2 g3
  · exact mul_ne_zero (hf U 0).ne' (mul_ne_zero hi (hc i (by lia)))
  · exact mul_ne_zero (hf U d).ne' (mul_ne_zero hj (hc j le_rfl))

private theorem good_zero : (0 : ℝ[X]).MeshGE 1 ∧ HasOnlyNonnegRoots (0 : ℝ[X]) :=
  ⟨Polynomial.MeshGE.of_natDegree_le_one (by simp) (by simp) zero_le_one, Or.inl rfl⟩

private theorem good_descPochhammer (m : ℕ) :
    (descPochhammer ℝ m).MeshGE 1 ∧ HasOnlyNonnegRoots (descPochhammer ℝ m) := by
  refine ⟨meshGE_descPochhammer m, Or.inr ⟨(meshGE_descPochhammer m).1, fun r hr => ?_⟩⟩
  rw [roots_descPochhammer, Multiset.mem_map] at hr
  obtain ⟨j, -, rfl⟩ := hr
  exact Nat.cast_nonneg j

/-- `[x]_m (x - r)` with `r ≥ m` has mesh at least one and nonnegative roots. -/
private theorem good_descPochhammer_mul {m : ℕ} {r : ℝ} (hr : (m : ℝ) ≤ r) :
    (descPochhammer ℝ m * (X - C r)).MeshGE 1 ∧
      HasOnlyNonnegRoots (descPochhammer ℝ m * (X - C r)) := by
  have hne : descPochhammer ℝ m * (X - C r) ≠ 0 :=
    mul_ne_zero (monic_descPochhammer ℝ m).ne_zero (X_sub_C_ne_zero r)
  have hroots : (descPochhammer ℝ m * (X - C r)).roots =
      (Multiset.range m).map (fun j : ℕ => (j : ℝ)) + {r} := by
    rw [roots_mul hne, roots_descPochhammer, roots_X_sub_C]
  have hs : (descPochhammer ℝ m * (X - C r)).Splits :=
    (meshGE_descPochhammer m).1.mul (Polynomial.Splits.X_sub_C r)
  have hmem : ∀ x, x ∈ (descPochhammer ℝ m * (X - C r)).roots ↔
      (∃ j : ℕ, j < m ∧ (j : ℝ) = x) ∨ x = r := by
    intro x
    simp [hroots, Multiset.mem_add]
  refine ⟨?_, Or.inr ⟨hs, fun x hx => ?_⟩⟩
  · rw [Polynomial.MeshGE.iff_roots_nodup_pairwise_gap one_pos]
    refine ⟨hs, ?_, fun x hx y hy hxy => ?_⟩
    · rw [hroots, Multiset.nodup_add]
      refine ⟨(Multiset.nodup_range m).map Nat.cast_injective, Multiset.nodup_singleton r, ?_⟩
      rw [Multiset.disjoint_left]
      intro x hx
      simp only [Multiset.mem_map, Multiset.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
      simp only [Multiset.mem_singleton]
      intro h
      linarith
    · rw [hmem] at hx hy
      rw [le_abs]
      rcases hx with ⟨j, hj, rfl⟩ | rfl <;> rcases hy with ⟨k, hk, rfl⟩ | rfl
      · have hjk : j ≠ k := fun h => hxy (by rw [h])
        rcases lt_or_gt_of_ne hjk with h | h
        · right
          have : j + 1 ≤ k := h
          have : (j : ℝ) + 1 ≤ k := by exact_mod_cast this
          linarith
        · left
          have : k + 1 ≤ j := h
          have : (k : ℝ) + 1 ≤ j := by exact_mod_cast this
          linarith
      · have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
        right
        linarith
      · have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
        left
        linarith
      · exact absurd rfl hxy
  · rw [hmem] at hx
    rcases hx with ⟨j, -, rfl⟩ | rfl
    · exact Nat.cast_nonneg j
    · exact (Nat.cast_nonneg m).trans hr

/-- The product of the falling-factorial coordinates `c_m c_{m+1}` of a polynomial with mesh at
least one and nonnegative roots is nonpositive (BKS 2016, Lemma 11). -/
private theorem repr_mul_repr_succ_nonpos {p : ℝ[X]} (hmesh : p.MeshGE 1)
    (hnn : HasOnlyNonnegRoots p) (m : ℕ) :
    (descPochhammerBasis ℝ).repr p m * (descPochhammerBasis ℝ).repr p (m + 1) ≤ 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have key : ∀ q : ℝ[X], HasPosLeadingCoeff q → q.MeshGE 1 → HasOnlyNonnegRoots q →
      (descPochhammerBasis ℝ).repr q m * (descPochhammerBasis ℝ).repr q (m + 1) ≤ 0 := by
    intro q hq hq1 hq2
    by_cases hmn : m + 1 ≤ q.natDegree
    · have h1 := neg_one_pow_mul_descPochhammerBasis_repr_nonneg hq hq1 hq2 (i := m) (by lia)
      have h2 := neg_one_pow_mul_descPochhammerBasis_repr_nonneg hq hq1 hq2 (i := m + 1) hmn
      have hpow : (-1 : ℝ) ^ (q.natDegree - m) = -(-1) ^ (q.natDegree - (m + 1)) := by
        rw [show q.natDegree - m = (q.natDegree - (m + 1)) + 1 by lia, pow_succ]
        ring
      have he : ((-1 : ℝ) ^ (q.natDegree - (m + 1))) * (-1) ^ (q.natDegree - (m + 1)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        simp
      rw [hpow] at h1
      nlinarith [mul_nonneg h1 h2]
    · have : (descPochhammerBasis ℝ).repr q (m + 1) = 0 :=
        natDegree_le_iff_repr_descPochhammerBasis.mp le_rfl (m + 1) (by lia)
      rw [this, mul_zero]
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp0) with hneg | hpos
  · have hq : HasPosLeadingCoeff (C (-1) * p) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C]
      linarith
    have h := key _ hq ((Polynomial.MeshGE.C_mul_iff _ 1 (by norm_num)).2 hmesh)
      ((HasOnlyNonnegRoots.C_mul_iff (by norm_num) _).2 hnn)
    rw [← smul_eq_C_mul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul] at h
    nlinarith
  · exact key p hpos hmesh hnn

/-- BKS 2016, Proposition 7 ("if"): a sequence with `a m a (m + 1) ≥ 0` and all other entries
zero is a discrete multiplier sequence. -/
theorem isDiscreteMultiplierSequence_of_adjacent {a : ℕ → ℝ} {m : ℕ}
    (hm : 0 ≤ a m * a (m + 1)) (hz : ∀ i, i ≠ m → i ≠ m + 1 → a i = 0) :
    IsDiscreteMultiplierSequence a := by
  intro T hT p hp hpnn
  have e : ∀ k, descPochhammerBasis ℝ k = descPochhammer ℝ k := fun k =>
    descPochhammerBasis_apply k
  set A := a m * (descPochhammerBasis ℝ).repr p m with hA
  set B := a (m + 1) * (descPochhammerBasis ℝ).repr p (m + 1) with hB
  have hTp : T p = A • descPochhammer ℝ m + B • descPochhammer ℝ (m + 1) := by
    apply (descPochhammerBasis ℝ).repr.injective
    ext k
    rw [descPochhammerBasis_repr_apply_eq_mul_repr hT, ← e m, ← e (m + 1)]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hkm : k = m
    · subst hkm
      simp [hA]
    · by_cases hkm1 : k = m + 1
      · subst hkm1
        simp [hB]
      · simp [hz k hkm hkm1, Ne.symm hkm, Ne.symm hkm1]
  have hAB : A * B ≤ 0 := by
    have h := repr_mul_repr_succ_nonpos hp hpnn m
    have : A * B = (a m * a (m + 1)) * ((descPochhammerBasis ℝ).repr p m *
        (descPochhammerBasis ℝ).repr p (m + 1)) := by rw [hA, hB]; ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hm h
  rw [hTp]
  by_cases hB0 : B = 0
  · rw [hB0, zero_smul, add_zero]
    by_cases hA0 : A = 0
    · rw [hA0, zero_smul]
      exact good_zero
    · rw [smul_eq_C_mul]
      exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 hA0).2 (good_descPochhammer m).1,
        (HasOnlyNonnegRoots.C_mul_iff hA0 _).2 (good_descPochhammer m).2⟩
  · have hAB' : A / B ≤ 0 := by
      by_contra h
      push Not at h
      have : A * B = (A / B) * (B * B) := by field_simp
      nlinarith [mul_pos h (mul_self_pos.2 hB0)]
    have hCA : C A = C B * C (A / B) := by rw [← C_mul, mul_div_cancel₀ _ hB0]
    have hform : A • descPochhammer ℝ m + B • descPochhammer ℝ (m + 1) =
        C B * (descPochhammer ℝ m * (X - C ((m : ℝ) - A / B))) := by
      rw [descPochhammer_succ_right]
      simp only [smul_eq_C_mul, map_sub, map_natCast, hCA]
      ring
    rw [hform]
    obtain ⟨h1, h2⟩ := good_descPochhammer_mul (m := m) (r := (m : ℝ) - A / B) (by linarith)
    exact ⟨(Polynomial.MeshGE.C_mul_iff _ 1 hB0).2 h1, (HasOnlyNonnegRoots.C_mul_iff hB0 _).2 h2⟩

/-- BKS 2016, Proposition 7: a sequence with at most two nonzero entries is a discrete
multiplier sequence if and only if its nonzero entries are adjacent and have the same sign.  The
"if" direction holds without the assumption on the number of nonzero entries, see
`isDiscreteMultiplierSequence_of_adjacent`. -/
theorem isDiscreteMultiplierSequence_iff_adjacent_of_two_nonzero {a : ℕ → ℝ}
    (h2 : ∃ i j, ∀ k, k ≠ i → k ≠ j → a k = 0) :
    IsDiscreteMultiplierSequence a ↔
      ∃ m, 0 ≤ a m * a (m + 1) ∧ ∀ i, i ≠ m → i ≠ m + 1 → a i = 0 := by
  constructor
  · intro ha
    obtain ⟨i, j, hz⟩ := h2
    wlog hij : i ≤ j generalizing i j
    · exact this j i (fun k h1 h2' => hz k h2' h1) (le_of_not_ge hij)
    by_cases hai : a i = 0
    · refine ⟨j, ?_, fun k hk hk1 => ?_⟩
      · rw [hz (j + 1) (by lia) (by lia), mul_zero]
      · by_cases hki : k = i
        · rw [hki, hai]
        · exact hz k hki hk
    by_cases haj : a j = 0
    · refine ⟨i, ?_, fun k hk hk1 => ?_⟩
      · by_cases h : i + 1 = j
        · rw [h, haj, mul_zero]
        · rw [hz (i + 1) (by lia) h, mul_zero]
      · by_cases hkj : k = j
        · rw [hkj, haj]
        · exact hz k hk hkj
    rcases hij.eq_or_lt with rfl | hlt
    · exact ⟨i, by rw [hz (i + 1) (by lia) (by lia), mul_zero], fun k hk _ => hz k hk hk⟩
    · by_cases hadj : j = i + 1
      · subst hadj
        refine ⟨i, ?_, fun k hk hk1 => hz k hk hk1⟩
        rcases ha.nonneg_or_nonpos with h | h
        · exact mul_nonneg (h i) (h _)
        · exact mul_nonneg_of_nonpos_of_nonpos (h i) (h _)
      · exact (ha.not_two_apart (by lia) hai haj hz).elim
  · rintro ⟨m, hm, hz⟩
    exact isDiscreteMultiplierSequence_of_adjacent hm hz

end

end RealRooted
