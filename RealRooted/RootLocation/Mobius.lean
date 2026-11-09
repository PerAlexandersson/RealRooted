module

public import RealRooted.RootLocation.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform

/-!
# Möbius transport of root locations

For real `a b c d` with `a d - b c ≠ 0`, the degree-`n` Möbius transform
`mobiusTransform n a b c d p = (c X + d)^n p ((a X + b) / (c X + d))` sends a polynomial of
degree at most `n` which is rooted in `S` to a polynomial rooted in the preimage of `S` under
`x ↦ (a x + b) / (c x + d)`, together with the pole `c x + d = 0` when the degree of `p` drops
below `n` (the roots of `p` at infinity).

The headline instance is the Bernstein/Cayley change of variable (issue #2361):
`cayleyTransform D = (1 - X)^D p (X / (1 - X))` and `K_D := mobiusTransform D 1 0 1 1` are
mutually inverse on polynomials of degree at most `D`, and for `p` of degree exactly `D`
`p` is rooted in `[-1, 0]` iff `cayleyTransform D p` is rooted in `(-∞, 0]`.  Hence a map `T`
preserving `(-∞, 0]`-rootedness gives a map `K_D ∘ T ∘ cayleyTransform D` preserving
`[-1, 0]`-rootedness.
-/

@[expose] public section

open Polynomial Set

noncomputable section

namespace RealRooted

namespace IsRealRootedIn

variable {S : Set ℝ} {p : ℝ[X]} {n : ℕ} {a b c d : ℝ}

/-- A common zero of `a X + b` and `c X + d` forces `a d - b c = 0`. -/
private theorem det_eq_zero_of_eval_eq_zero {x : ℝ} (h1 : a * x + b = 0) (h2 : c * x + d = 0) :
    a * d - b * c = 0 := by
  linear_combination a * h2 - c * h1

/-- Möbius transport of root locations.  If `p` has degree at most `n` and is rooted in `S`, and
`a d - b c ≠ 0`, then `mobiusTransform n a b c d p` is rooted in the preimage of `S` under
`x ↦ (a x + b) / (c x + d)`, together with the pole `c x + d = 0` when `natDegree p < n`. -/
theorem mobiusTransform (hdet : a * d - b * c ≠ 0) (hdeg : p.natDegree ≤ n)
    (h : IsRealRootedIn S p) :
    IsRealRootedIn ({x | c * x + d ≠ 0 ∧ (a * x + b) / (c * x + d) ∈ S} ∪
        {x | c * x + d = 0 ∧ p.natDegree < n}) (Polynomial.mobiusTransform n a b c d p) := by
  have hne := Polynomial.mobiusTransform_ne_zero n a b c d h.ne_zero hdeg (Ne.isUnit hdet)
  refine ⟨hne, Polynomial.Splits.mobiusTransform a b c d h.splits hdeg, fun x hx => ?_⟩
  have hx' := (mem_roots hne).1 hx
  rw [Polynomial.mobiusTransform_eq_rootFactorProduct_mul n a b c d h.splits hdeg] at hx'
  simp only [IsRoot.def, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, eval_pow,
    eval_add, eval_X] at hx'
  rcases mul_eq_zero.1 hx' with h1 | h2
  · rcases mul_eq_zero.1 h1 with h3 | h4
    · exact absurd (leadingCoeff_eq_zero.1 h3) h.ne_zero
    · obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h4)
      have hr1 : (a - r * c) * x + (b - r * d) = 0 := by simpa using hr0
      have hcx : c * x + d ≠ 0 := fun hcx =>
        hdet (det_eq_zero_of_eval_eq_zero (by linear_combination hr1 + r * hcx) hcx)
      have hrx : (a * x + b) / (c * x + d) = r := by
        rw [div_eq_iff hcx]
        linear_combination hr1
      exact Or.inl ⟨hcx, hrx ▸ h.mem_of_mem_roots hr⟩
  · have hpow := pow_eq_zero_iff'.1 h2
    refine Or.inr ⟨hpow.1, ?_⟩
    have := hpow.2
    lia

/-- If `p` has degree exactly `n` there is no pole: `mobiusTransform n a b c d p` is rooted in
the preimage of `S` under `x ↦ (a x + b) / (c x + d)`. -/
theorem mobiusTransform_of_natDegree_eq (hdet : a * d - b * c ≠ 0) (hdeg : p.natDegree = n)
    (h : IsRealRootedIn S p) :
    IsRealRootedIn {x | c * x + d ≠ 0 ∧ (a * x + b) / (c * x + d) ∈ S}
      (Polynomial.mobiusTransform n a b c d p) :=
  (h.mobiusTransform hdet hdeg.le).mono
    (union_subset subset_rfl fun _ hx => absurd hx.2 (by lia))

/-- The affine case `c = 0`: `mobiusTransform n a b 0 d p = d ^ n p ((a X + b) / d)` is rooted in
the preimage of `S` under `x ↦ (a x + b) / d`, whatever the degree of `p` is. -/
theorem mobiusTransform_of_c_eq_zero (hdet : a * d - b * 0 ≠ 0) (hdeg : p.natDegree ≤ n)
    (h : IsRealRootedIn S p) :
    IsRealRootedIn {x | (a * x + b) / d ∈ S} (Polynomial.mobiusTransform n a b 0 d p) := by
  have hd : d ≠ 0 := by rintro rfl; simp at hdet
  refine (h.mobiusTransform hdet hdeg).mono (union_subset (fun x hx => ?_) fun x hx => ?_)
  · simpa using hx.2
  · exact absurd (by simpa using hx.1) hd

end IsRealRootedIn

/-! ### The Bernstein/Cayley change of variable -/

section Bernstein

/-- A point whose Cayley image `x / (1 - x)` lies in `[-1, 0]` is nonpositive. -/
private theorem nonpos_of_div_mem_Icc {x : ℝ} (hx : (-1) * x + 1 ≠ 0)
    (h : (1 * x + 0) / ((-1) * x + 1) ∈ Icc (-1 : ℝ) 0) : x ≤ 0 := by
  obtain ⟨h1, h2⟩ := h
  have ht := div_mul_cancel₀ (1 * x + 0) hx
  generalize (1 * x + 0) / ((-1) * x + 1) = t at *
  have hxt : x * (1 + t) = t := by linear_combination (-1 : ℝ) * ht
  by_contra hpos
  push Not at hpos
  nlinarith [mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ 1 + t)]

/-- A point whose image `x / (1 + x)` is nonpositive lies in `[-1, 0]`, and `x ≠ -1`. -/
private theorem mem_Icc_of_div_nonpos {x : ℝ} (hx : 1 * x + 1 ≠ 0)
    (h : (1 * x + 0) / (1 * x + 1) ∈ Iic (0 : ℝ)) : x ∈ Icc (-1 : ℝ) 0 := by
  have ht := div_mul_cancel₀ (1 * x + 0) hx
  generalize (1 * x + 0) / (1 * x + 1) = t at *
  have h0 : t ≤ 0 := h
  have hxt : x * (1 - t) = t := by linear_combination (-1 : ℝ) * ht
  have hx1 : (x + 1) * (1 - t) = 1 := by linear_combination hxt
  constructor
  · by_contra hlt
    push Not at hlt
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(x + 1)) (by linarith : (0 : ℝ) ≤ 1 - t)]
  · by_contra hpos
    push Not at hpos
    nlinarith [mul_nonneg hpos.le (by linarith : (0 : ℝ) ≤ 1 - t)]

/-- A polynomial of degree exactly `D` rooted in `[-1, 0]` has Cayley transform
`(1 - X)^D p (X / (1 - X))` rooted in `(-∞, 0]`. -/
theorem IsRealRootedIn.cayleyTransform_Iic {p : ℝ[X]} {D : ℕ} (hp : p.natDegree = D)
    (h : IsRealRootedIn (Icc (-1) 0) p) : IsRealRootedIn (Iic 0) (cayleyTransform D p) := by
  rw [cayleyTransform_eq_mobiusTransform]
  exact (h.mobiusTransform_of_natDegree_eq (by simp) hp).mono fun x hx =>
    nonpos_of_div_mem_Icc hx.1 hx.2

/-- The transform `(1 + X)^D q (X / (1 + X))` of a polynomial `q` of degree at most `D` which is
rooted in `(-∞, 0]` is rooted in `[-1, 0]` and has degree exactly `D`. -/
theorem IsRealRootedIn.mobiusTransform_one_zero_one_one {q : ℝ[X]} {D : ℕ}
    (hq : q.natDegree ≤ D) (h : IsRealRootedIn (Iic 0) q) :
    IsRealRootedIn (Icc (-1) 0) (Polynomial.mobiusTransform D 1 0 1 1 q) ∧
      (Polynomial.mobiusTransform D 1 0 1 1 q).natDegree = D := by
  refine ⟨(h.mobiusTransform (by simp) hq).mono (union_subset (fun x hx => ?_) fun x hx => ?_),
    le_antisymm (natDegree_mobiusTransform_le D 1 0 1 1 hq) ?_⟩
  · exact mem_Icc_of_div_nonpos hx.1 hx.2
  · exact ⟨by linarith [hx.1], by linarith [hx.1]⟩
  · refine le_natDegree_of_ne_zero ?_
    rw [coeff_mobiusTransform_one_zero_one_one D hq]
    intro h0
    exact absurd (h.mem_of_isRoot h0) (by norm_num)

/-- For `p` of degree exactly `D`: `p` is rooted in `[-1, 0]` iff its Cayley transform
`(1 - X)^D p (X / (1 - X))` is rooted in `(-∞, 0]`.  The implication from right to left only needs
`natDegree p ≤ D`. -/
theorem isRealRootedIn_Icc_iff_cayleyTransform {p : ℝ[X]} {D : ℕ} (hp : p.natDegree = D) :
    IsRealRootedIn (Icc (-1) 0) p ↔ IsRealRootedIn (Iic 0) (cayleyTransform D p) := by
  refine ⟨IsRealRootedIn.cayleyTransform_Iic hp, fun h => ?_⟩
  have hdeg : (cayleyTransform D p).natDegree ≤ D := by
    rw [cayleyTransform_eq_mobiusTransform]
    exact natDegree_mobiusTransform_le D 1 0 (-1) 1 hp.le
  have := (IsRealRootedIn.mobiusTransform_one_zero_one_one hdeg h).1
  rwa [mobiusTransform_one_zero_one_one_cayleyTransform D hp.le] at this

/-- For `p` of degree exactly `D`, the degree of the Cayley transform drops by the multiplicity of
the root `-1` (which is sent to infinity). -/
theorem natDegree_cayleyTransform_of_isRealRootedIn {p : ℝ[X]} {D : ℕ} (hp : p.natDegree = D)
    (h : IsRealRootedIn (Icc (-1) 0) p) :
    (cayleyTransform D p).natDegree = D - p.rootMultiplicity (-1) :=
  natDegree_cayleyTransform_eq D h.splits h.ne_zero hp

/-- For `p` of degree exactly `D`: `p` is rooted in `(-1, 0]` iff its Cayley transform
`(1 - X)^D p (X / (1 - X))` is rooted in `(-∞, 0]` and still has degree `D` (no root of `p` was
sent to infinity). -/
theorem isRealRootedIn_Ioc_iff_cayleyTransform {p : ℝ[X]} {D : ℕ} (hp : p.natDegree = D) :
    IsRealRootedIn (Ioc (-1) 0) p ↔
      IsRealRootedIn (Iic 0) (cayleyTransform D p) ∧ (cayleyTransform D p).natDegree = D := by
  constructor
  · intro h
    have hI := h.mono Ioc_subset_Icc_self
    refine ⟨(isRealRootedIn_Icc_iff_cayleyTransform hp).1 hI, ?_⟩
    have h0 : p.rootMultiplicity (-1) = 0 :=
      rootMultiplicity_eq_zero fun hr => by simpa using h.mem_of_isRoot hr
    rw [natDegree_cayleyTransform_of_isRealRootedIn hp hI, h0, Nat.sub_zero]
  · rintro ⟨hJ, hd⟩
    have hI := (isRealRootedIn_Icc_iff_cayleyTransform hp).2 hJ
    rw [natDegree_cayleyTransform_of_isRealRootedIn hp hI] at hd
    refine ⟨hI.ne_zero, hI.splits, fun r hr => ?_⟩
    have hrI := hI.mem_of_mem_roots hr
    refine ⟨lt_of_le_of_ne hrI.1 ?_, hrI.2⟩
    rintro rfl
    have hpos : 0 < p.rootMultiplicity (-1) := (rootMultiplicity_pos hI.ne_zero).2
      ((mem_roots hI.ne_zero).1 hr)
    have hle : p.rootMultiplicity (-1) ≤ D := by
      rw [← count_roots, ← hp]
      exact (Multiset.count_le_card _ _).trans (card_roots' p)
    lia

/-- Conjugation of a linear map `T` on polynomials by the Bernstein/Cayley change of variable in
degree `D`: `p ↦ (1 + X)^D (T ((1 - X)^D p (X / (1 - X)))) (X / (1 + X))`. -/
def cayleyConj (D : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  mobiusTransformLinearMap D 1 0 1 1 ∘ₗ T ∘ₗ mobiusTransformLinearMap D 1 0 (-1) 1

/-- Unfolding `cayleyConj`. -/
theorem cayleyConj_apply (D : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (p : ℝ[X]) :
    cayleyConj D T p = mobiusTransform D 1 0 1 1 (T (cayleyTransform D p)) := by
  simp [cayleyConj, cayleyTransform_eq_mobiusTransform]

/-- Conjugating the identity by the change of variable is the identity in degree at most `D`. -/
theorem cayleyConj_id {D : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ D) :
    cayleyConj D LinearMap.id p = p := by
  rw [cayleyConj_apply, LinearMap.id_apply, mobiusTransform_one_zero_one_one_cayleyTransform D hp]

/-- Transport of a preserver from `(-∞, 0]` to `[-1, 0]`.  If `T` sends polynomials of degree at
most `D` rooted in `(-∞, 0]` to `0` or to polynomials rooted in `(-∞, 0]`, and does not raise the
degree above `D`, then the conjugate `cayleyConj D T` sends a degree-`D` polynomial rooted in
`[-1, 0]` to `0` or to a degree-`D` polynomial rooted in `[-1, 0]`.

Degree-`D` inputs are necessary: a root of `p` at infinity (`natDegree p < D`) becomes the root `1`
of the Cayley transform, which lies outside `(-∞, 0]`. -/
theorem cayleyConj_isRealRootedIn {D : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hT : MapsRealRootedIn T D (Iic 0) (Iic 0))
    (hdeg : ∀ q : ℝ[X], q.natDegree ≤ D → (T q).natDegree ≤ D)
    {p : ℝ[X]} (hp : p.natDegree = D) (h : IsRealRootedIn (Icc (-1) 0) p) :
    cayleyConj D T p = 0 ∨
      (IsRealRootedIn (Icc (-1) 0) (cayleyConj D T p) ∧ (cayleyConj D T p).natDegree = D) := by
  have hJ := h.cayleyTransform_Iic hp
  have hJdeg : (cayleyTransform D p).natDegree ≤ D := by
    rw [cayleyTransform_eq_mobiusTransform]
    exact natDegree_mobiusTransform_le D 1 0 (-1) 1 hp.le
  rw [cayleyConj_apply]
  rcases hT _ hJdeg hJ with h0 | hr
  · left
    rw [h0, mobiusTransform_zero]
  · right
    exact IsRealRootedIn.mobiusTransform_one_zero_one_one (hdeg _ hJdeg) hr

end Bernstein

end RealRooted
