module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
public import RealRooted.Apolarity
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# Real-rootedness with roots in a prescribed set

`RealRooted.IsRealRootedIn S p` says that `p` is a nonzero real polynomial which splits over `ℝ`
and all of whose roots lie in `S`.  This is the common vocabulary for statements of the form
"the map `T` sends polynomials rooted in `I` to polynomials rooted in `J`".

We provide the closure API (monotonicity, products, powers, linear factors), the bridge to
`Polynomial.RootsIn`, the transport along affine substitutions and reversal, and the predicate
`MapsRealRootedIn T n I J` for a linear map `T` on polynomials with its composition, monotonicity
and restriction lemmas.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted

/-- A nonzero real polynomial which splits and whose roots all belong to `S`. -/
def IsRealRootedIn (S : Set ℝ) (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits ∧ ∀ r ∈ p.roots, r ∈ S

namespace IsRealRootedIn

variable {S T : Set ℝ} {p q : ℝ[X]}

/-- A polynomial rooted in a set is nonzero. -/
protected theorem ne_zero (h : IsRealRootedIn S p) : p ≠ 0 := h.1

/-- A polynomial rooted in a set splits over `ℝ`. -/
protected theorem splits (h : IsRealRootedIn S p) : p.Splits := h.2.1

/-- Every multiset root of a polynomial rooted in `S` lies in `S`. -/
protected theorem mem_of_mem_roots (h : IsRealRootedIn S p) {r : ℝ} (hr : r ∈ p.roots) :
    r ∈ S := h.2.2 r hr

/-- Every root of a polynomial rooted in `S` lies in `S`. -/
protected theorem mem_of_isRoot (h : IsRealRootedIn S p) {r : ℝ} (hr : p.IsRoot r) : r ∈ S :=
  h.2.2 r ((mem_roots h.1).2 hr)

/-- Rooted-in-`S` unfolded: nonzero, splitting, and every root lies in `S`. -/
theorem iff_isRoot : IsRealRootedIn S p ↔ p ≠ 0 ∧ p.Splits ∧ ∀ r, p.IsRoot r → r ∈ S := by
  refine ⟨fun h => ⟨h.1, h.2.1, fun r hr => h.mem_of_isRoot hr⟩, fun h => ⟨h.1, h.2.1, ?_⟩⟩
  intro r hr
  exact h.2.2 r ((mem_roots h.1).1 hr)

/-- Rooted-in-`S` unfolded with the root set: nonzero, splitting, and `p.rootSet ℝ ⊆ S`. -/
theorem iff_rootSet_subset : IsRealRootedIn S p ↔ p ≠ 0 ∧ p.Splits ∧ p.rootSet ℝ ⊆ S := by
  simp only [IsRealRootedIn, Set.subset_def, mem_rootSet]
  refine and_congr_right fun hp => and_congr_right fun _ => forall_congr' fun r => ?_
  simp [mem_roots hp, IsRoot.def, hp, aeval_def, eval₂_eq_eval_map]

/-- Rooted-in-`S` as `Polynomial.RootsIn` together with nonvanishing and splitting. -/
theorem iff_rootsIn : IsRealRootedIn S p ↔ p ≠ 0 ∧ p.Splits ∧ p.RootsIn S := iff_isRoot

/-- A polynomial rooted in `S` has all its roots in `S` in the sense of `Polynomial.RootsIn`. -/
protected theorem rootsIn (h : IsRealRootedIn S p) : p.RootsIn S := fun _ hr =>
  h.mem_of_isRoot hr

/-- A nonzero splitting polynomial with all roots in `S` is rooted in `S`. -/
protected theorem of_rootsIn (hp : p ≠ 0) (hs : p.Splits) (h : p.RootsIn S) :
    IsRealRootedIn S p := iff_rootsIn.2 ⟨hp, hs, h⟩

/-- Rooted-in-`S` is monotone in `S`. -/
protected theorem mono (h : IsRealRootedIn S p) (hST : S ⊆ T) : IsRealRootedIn T p :=
  ⟨h.1, h.2.1, fun r hr => hST (h.2.2 r hr)⟩

/-- Rooted in `S` and in `T` gives rooted in `S ∩ T`. -/
protected theorem inter (hS : IsRealRootedIn S p) (hT : IsRealRootedIn T p) :
    IsRealRootedIn (S ∩ T) p :=
  ⟨hS.1, hS.2.1, fun r hr => ⟨hS.2.2 r hr, hT.2.2 r hr⟩⟩

/-- A polynomial is rooted in `univ` iff it is nonzero and splits. -/
@[simp] theorem univ_iff : IsRealRootedIn Set.univ p ↔ p ≠ 0 ∧ p.Splits := by
  simp [IsRealRootedIn]

/-- The constant `1` is rooted in every set. -/
protected theorem one : IsRealRootedIn S 1 := by
  simp [IsRealRootedIn, Splits.one]

/-- A nonzero constant is rooted in every set. -/
protected theorem C {c : ℝ} (hc : c ≠ 0) : IsRealRootedIn S (C c) := by
  simp [IsRealRootedIn, hc, Splits.C]

/-- A linear factor with root in `S` is rooted in `S`. -/
protected theorem X_sub_C {r : ℝ} (hr : r ∈ S) : IsRealRootedIn S (X - C r) := by
  simp [IsRealRootedIn, X_sub_C_ne_zero, Splits.X_sub_C, roots_X_sub_C, hr]

/-- The monomial `X` is rooted in any set containing `0`. -/
protected theorem X (h0 : (0 : ℝ) ∈ S) : IsRealRootedIn S (X : ℝ[X]) := by
  simpa using IsRealRootedIn.X_sub_C h0

/-- A product is rooted in `S` iff both factors are. -/
theorem mul_iff : IsRealRootedIn S (p * q) ↔ IsRealRootedIn S p ∧ IsRealRootedIn S q := by
  constructor
  · rintro ⟨hpq, hs, hr⟩
    have hp : p ≠ 0 := left_ne_zero_of_mul hpq
    have hq : q ≠ 0 := right_ne_zero_of_mul hpq
    have hs' := (splits_mul hp hq).1 hs
    rw [roots_mul hpq] at hr
    exact ⟨⟨hp, hs'.1, fun r h => hr r (Multiset.mem_add.2 (Or.inl h))⟩,
      ⟨hq, hs'.2, fun r h => hr r (Multiset.mem_add.2 (Or.inr h))⟩⟩
  · rintro ⟨⟨hp, hps, hpr⟩, ⟨hq, hqs, hqr⟩⟩
    refine ⟨mul_ne_zero hp hq, hps.mul hqs, fun r hr => ?_⟩
    rw [roots_mul (mul_ne_zero hp hq)] at hr
    rcases Multiset.mem_add.1 hr with h | h
    exacts [hpr r h, hqr r h]

/-- A product of polynomials rooted in `S` is rooted in `S`. -/
protected theorem mul (hp : IsRealRootedIn S p) (hq : IsRealRootedIn S q) :
    IsRealRootedIn S (p * q) := mul_iff.2 ⟨hp, hq⟩

/-- A nonzero scalar multiple is rooted in `S` iff the polynomial is. -/
theorem C_mul_iff {c : ℝ} (hc : c ≠ 0) : IsRealRootedIn S (C c * p) ↔ IsRealRootedIn S p := by
  rw [mul_iff]
  exact ⟨fun h => h.2, fun h => ⟨IsRealRootedIn.C hc, h⟩⟩

/-- A nonzero scalar multiple of a polynomial rooted in `S` is rooted in `S`. -/
protected theorem C_mul {c : ℝ} (hc : c ≠ 0) (h : IsRealRootedIn S p) :
    IsRealRootedIn S (C c * p) := (C_mul_iff hc).2 h

/-- Powers of a polynomial rooted in `S` are rooted in `S`. -/
protected theorem pow (h : IsRealRootedIn S p) (n : ℕ) : IsRealRootedIn S (p ^ n) := by
  induction n with
  | zero => simpa using IsRealRootedIn.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

/-- A finite product of polynomials rooted in `S` is rooted in `S`. -/
protected theorem prod {ι : Type*} (s : Finset ι) {f : ι → ℝ[X]}
    (h : ∀ i ∈ s, IsRealRootedIn S (f i)) : IsRealRootedIn S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IsRealRootedIn S) (fun _ _ => IsRealRootedIn.mul)
    IsRealRootedIn.one h

/-- A product of a multiset of polynomials rooted in `S` is rooted in `S`. -/
protected theorem multiset_prod {m : Multiset ℝ[X]} (h : ∀ f ∈ m, IsRealRootedIn S f) :
    IsRealRootedIn S m.prod :=
  Multiset.prod_induction (IsRealRootedIn S) m (fun _ _ => IsRealRootedIn.mul)
    IsRealRootedIn.one h

/-- The monic polynomial with roots a multiset `m ⊆ S` is rooted in `S`. -/
protected theorem multiset_prod_X_sub_C {m : Multiset ℝ} (h : ∀ r ∈ m, r ∈ S) :
    IsRealRootedIn S (m.map fun r => X - C r).prod :=
  IsRealRootedIn.multiset_prod fun f hf => by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hf
    exact IsRealRootedIn.X_sub_C (h r hr)

end IsRealRootedIn

/-! ### Affine transport -/

namespace IsRealRootedIn

variable {S : Set ℝ} {p : ℝ[X]}

/-- Substituting an affine map `a X + b` with `a ≠ 0` into a polynomial rooted in `S` gives a
polynomial rooted in the preimage of `S` under `x ↦ a x + b`. -/
protected theorem comp_C_mul_X_add_C {a : ℝ} (b : ℝ) (ha : a ≠ 0) (h : IsRealRootedIn S p) :
    IsRealRootedIn ((fun x => a * x + b) ⁻¹' S) (p.comp (C a * X + C b)) := by
  have hlin : (C a * X + C b).natDegree ≤ 1 := by
    compute_degree
  have hne : p.comp (C a * X + C b) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_comp, natDegree_linear ha] at this
    simp only [mul_one, natDegree_zero] at this
    obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨_, eq_C_of_natDegree_eq_zero this⟩
    have hc : c ≠ 0 := by simpa using h.1
    simp [hc] at h0
  refine ⟨hne, h.2.1.comp_of_natDegree_le_one_of_invertible hlin ?_, fun z hz => ?_⟩
  · rw [leadingCoeff_linear ha]
    exact invertibleOfNonzero ha
  · have := (Multiset.mem_map_of_mem (fun x => a * x + b) hz)
    rw [map_roots_comp_C_mul_X_add_C p a b (IsUnit.mk0 a ha)] at this
    exact h.mem_of_mem_roots this


/-- Substituting `-X` into a polynomial rooted in `S` gives a polynomial rooted in the preimage
of `S` under negation. -/
protected theorem comp_neg_X (h : IsRealRootedIn S p) :
    IsRealRootedIn ((fun x => -x) ⁻¹' S) (p.comp (-X)) := by
  simpa using h.comp_C_mul_X_add_C 0 (neg_ne_zero.2 one_ne_zero)

/-- Substituting `a X + b` with `a ≠ 0` has the same root location: the composite is rooted in
the preimage of `S` iff `p` is rooted in `S`. -/
theorem comp_C_mul_X_add_C_iff {a : ℝ} (b : ℝ) (ha : a ≠ 0) :
    IsRealRootedIn ((fun x => a * x + b) ⁻¹' S) (p.comp (C a * X + C b)) ↔
      IsRealRootedIn S p := by
  refine ⟨fun h => ?_, fun h => h.comp_C_mul_X_add_C b ha⟩
  have hmap := map_roots_comp_C_mul_X_add_C p a b (IsUnit.mk0 a ha)
  have hp : p ≠ 0 := by
    rintro rfl
    exact h.1 (by simp)
  refine ⟨hp, splits_iff_card_roots.2 ?_, fun r hr => ?_⟩
  · rw [← hmap, Multiset.card_map, ← h.splits.natDegree_eq_card_roots, natDegree_comp,
      natDegree_linear ha, mul_one]
  · rw [← hmap] at hr
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hr
    exact h.mem_of_mem_roots hz

/-- Affine substitution `a X + b` with `a > 0` sends polynomials rooted in `[L, U]` to polynomials
rooted in `[(L - b) / a, (U - b) / a]`. -/
theorem comp_C_mul_X_add_C_Icc_of_pos {a L U : ℝ} (b : ℝ) (ha : 0 < a)
    (h : IsRealRootedIn (Icc L U) p) :
    IsRealRootedIn (Icc ((L - b) / a) ((U - b) / a)) (p.comp (C a * X + C b)) := by
  refine (h.comp_C_mul_X_add_C b ha.ne').mono fun x hx => ?_
  simp only [mem_preimage, mem_Icc] at hx ⊢
  constructor
  · rw [div_le_iff₀ ha]; linarith [hx.1]
  · rw [le_div_iff₀ ha]; linarith [hx.2]

/-- Affine substitution `a X + b` with `a < 0` sends polynomials rooted in `[L, U]` to polynomials
rooted in `[(U - b) / a, (L - b) / a]`. -/
theorem comp_C_mul_X_add_C_Icc_of_neg {a L U : ℝ} (b : ℝ) (ha : a < 0)
    (h : IsRealRootedIn (Icc L U) p) :
    IsRealRootedIn (Icc ((U - b) / a) ((L - b) / a)) (p.comp (C a * X + C b)) := by
  refine (h.comp_C_mul_X_add_C b ha.ne).mono fun x hx => ?_
  simp only [mem_preimage, mem_Icc] at hx ⊢
  constructor
  · rw [div_le_iff_of_neg ha]; linarith [hx.2]
  · rw [le_div_iff_of_neg ha]; linarith [hx.1]

/-! ### Reversal -/

/-- The reverse of a polynomial rooted in `S` is rooted in the inverses of the nonzero points
of `S`: the zero roots of `p` disappear and the others are inverted. -/
protected theorem reverse (h : IsRealRootedIn S p) :
    IsRealRootedIn ((fun x => x⁻¹) '' (S \ {0})) p.reverse := by
  classical
  refine ⟨reverse_eq_zero.not.2 h.1, h.splits.reverse, fun r hr => ?_⟩
  rw [roots_reverse_eq_filter_map_inv h.1 h.splits] at hr
  obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hr
  rw [Multiset.mem_filter] at hs
  exact ⟨s, ⟨h.mem_of_mem_roots hs.1, hs.2⟩, rfl⟩

/-- The reverse of a polynomial rooted in `S` is rooted in `(·⁻¹) '' S`. -/
protected theorem reverse_image (h : IsRealRootedIn S p) :
    IsRealRootedIn ((fun x => x⁻¹) '' S) p.reverse :=
  h.reverse.mono (image_mono sdiff_subset)

/-- Reversing a polynomial rooted in `[L, U]` with `0 < L` gives one rooted in `[U⁻¹, L⁻¹]`. -/
theorem reverse_Icc {L U : ℝ} (hL : 0 < L) (h : IsRealRootedIn (Icc L U) p) :
    IsRealRootedIn (Icc U⁻¹ L⁻¹) p.reverse := by
  refine h.reverse_image.mono ?_
  rintro - ⟨s, hs, rfl⟩
  have hs0 : 0 < s := hL.trans_le hs.1
  exact ⟨inv_anti₀ hs0 hs.2, inv_anti₀ hL hs.1⟩

end IsRealRootedIn

/-! ### Maps between root locations -/

/-- `MapsRealRootedIn T n I J` says that the linear map `T` sends every polynomial of degree at
most `n` which is rooted in `I` to `0` or to a polynomial rooted in `J`.  The zero output is
allowed (a non-injective `T` may kill a rooted polynomial), so the statement is about the
nonzero outputs only. -/
def MapsRealRootedIn (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) (I J : Set ℝ) : Prop :=
  ∀ p : ℝ[X], p.natDegree ≤ n → IsRealRootedIn I p → T p = 0 ∨ IsRealRootedIn J (T p)

namespace MapsRealRootedIn

variable {T S : ℝ[X] →ₗ[ℝ] ℝ[X]} {n m : ℕ} {I I' J J' K : Set ℝ}

/-- The identity map sends `I`-rooted polynomials to `I`-rooted polynomials. -/
theorem id : MapsRealRootedIn LinearMap.id n I I := fun _ _ h => Or.inr h

/-- The zero map maps anything anywhere. -/
theorem zero : MapsRealRootedIn 0 n I J := fun _ _ _ => Or.inl rfl

/-- Shrinking the source set preserves `MapsRealRootedIn`. -/
theorem mono_left (h : MapsRealRootedIn T n I J) (hI : I' ⊆ I) : MapsRealRootedIn T n I' J :=
  fun p hp hr => h p hp (hr.mono hI)

/-- Enlarging the target set preserves `MapsRealRootedIn`. -/
theorem mono_right (h : MapsRealRootedIn T n I J) (hJ : J ⊆ J') : MapsRealRootedIn T n I J' :=
  fun p hp hr => (h p hp hr).imp_right fun h' => h'.mono hJ

/-- Restricting to smaller degrees preserves `MapsRealRootedIn`. -/
theorem of_le (h : MapsRealRootedIn T n I J) (hmn : m ≤ n) : MapsRealRootedIn T m I J :=
  fun p hp hr => h p (hp.trans hmn) hr

/-- Composition: if `T` maps `I`-rooted polynomials of degree at most `n` to `J`-rooted ones,
raising the degree to at most `m`, and `S` maps `J`-rooted polynomials of degree at most `m` to
`K`-rooted ones, then `S ∘ₗ T` maps `I`-rooted polynomials of degree at most `n` to `K`-rooted
ones. -/
theorem comp (hS : MapsRealRootedIn S m J K) (hT : MapsRealRootedIn T n I J)
    (hdeg : ∀ p : ℝ[X], p.natDegree ≤ n → (T p).natDegree ≤ m) :
    MapsRealRootedIn (S ∘ₗ T) n I K := by
  intro p hp hr
  rcases hT p hp hr with h0 | hJ
  · simp [h0]
  · exact hS (T p) (hdeg p hp) hJ

end MapsRealRootedIn

end RealRooted
