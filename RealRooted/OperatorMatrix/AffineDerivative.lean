module

public import RealRooted.PFPolynomial
import RealRooted.FiniteFreeAdditive.FiniteDegreeCompanions
import RealRooted.OperatorMatrix.Directed
import RealRooted.QuadraticRoot
import RealRooted.Wronskian.WeakForward

/-!
# Affine-derivative rows and columns

Nonnegative affine-derivative rows preserve directed PF inputs exactly when
`a B ≤ A b`; their output precedes the derivative-weighted input sum.
Same-input columns have the opposite cross inequality `A c ≤ a C`.
Degree-two and degree-one witnesses give the same criteria at finite caps.

Source: *General affine-derivative matrices*
([source](https://github.com/PerAlexandersson/real-zero-preservers/tree/3255043)),
`weyl-operators/notes/general-affine-derivative-matrices.md`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- An affine combination of the derivative and the identity. -/
def affineD (a A : ℝ) (p : ℝ[X]) : ℝ[X] := C a * p.derivative + C A * p

/-- A row with two affine-derivative entries. -/
def affineDRow (a b A B : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  affineD a A p + affineD b B q

private theorem pf_combo {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsPFPolynomial (C a * p + C b * q) := by
  exact ((IsPFPolynomial.of_C_nonneg ha).mul hp).add_of_interl
    ((IsPFPolynomial.of_C_nonneg hb).mul hq)
    ((hpq.C_mul_left_of_nonneg ha).C_mul_right_of_nonneg hb)

/-- Nonnegative affine-derivative operators preserve PF polynomials. -/
theorem IsPFPolynomial.affineD {p : ℝ[X]} (hp : IsPFPolynomial p)
    {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) : IsPFPolynomial (RealRooted.affineD a A p) := by
  exact pf_combo hp.derivative hp hp.derivative_interl_self ha hA

private theorem affineDRow_pf_anchor {a b A B : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ A ∧ 0 ≤ B) (hc : a * B ≤ A * b)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    IsPFPolynomial (affineDRow a b A B p q) ∧
      Interl (affineDRow a b A B p q) (C a * p + C b * q) := by
  let H := C a * p + C b * q
  let K := C A * p + C B * q
  have hH : IsPFPolynomial H := pf_combo hp hq hpq h.1 h.2.1
  have hK : IsPFPolynomial K := pf_combo hp hq hpq h.2.2.1 h.2.2.2
  have hKH : Interl K H := interl_nonneg_combos_of_cross hp hq hpq
    h.1 h.2.2.1 h.2.1 h.2.2.2 hc
  have heq : affineDRow a b A B p q = H.derivative + K := by
    simp only [affineDRow, affineD, H, K, derivative_add, derivative_mul, derivative_C,
      zero_mul, zero_add]
    ring
  have hedge := interl_add_left_of_common_right_of_nonneg
    hH.derivative_interl_self hKH hH.derivative.hasNonnegCoeffs hK.hasNonnegCoeffs
  rw [heq]
  refine ⟨?_, hedge⟩
  by_cases hH0 : H = 0
  · simpa [hH0] using hK
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hH.derivative.hasNonnegCoeffs.add hK.hasNonnegCoeffs)
  by_cases hout : H.derivative + K = 0
  · exact Or.inl hout
  · exact Or.inr (hedge.toStrictInterl_of_ne hout hH0).1.2

/-- A safe affine-derivative row precedes its derivative-weighted input sum. -/
theorem affineDRow_anchor {a b A B : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ A ∧ 0 ≤ B) (hc : a * B ≤ A * b)
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q) (hpq : Interl p q) :
    Interl (affineDRow a b A B p q) (C a * p + C b * q) := by
  exact (affineDRow_pf_anchor h hc hp hq hpq).2

private theorem affineD_natDegree_le (a A : ℝ) (p : ℝ[X]) :
    (affineD a A p).natDegree ≤ p.natDegree := by
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_C_mul_le _ _).trans ((natDegree_derivative_le p).trans (Nat.sub_le _ _)))
    (natDegree_C_mul_le _ _))

/-- An affine-derivative row does not raise the common degree cap. -/
theorem affineDRow_natDegree_le (a b A B : ℝ) (p q : ℝ[X]) :
    (affineDRow a b A B p q).natDegree ≤ max p.natDegree q.natDegree := by
  exact (natDegree_add_le _ _).trans
    (max_le_max (affineD_natDegree_le a A p) (affineD_natDegree_le b B q))

private theorem row_cross_of_cap_two {a b A B : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ A ∧ 0 ≤ B)
    (hall : ∀ p q : ℝ[X], IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      p.natDegree ≤ 2 → q.natDegree ≤ 2 → IsPFPolynomial (affineDRow a b A B p q)) :
    a * B ≤ A * b := by
  by_contra hn
  have hh : 0 < a * B - A * b := sub_pos.mpr (lt_of_not_ge hn)
  have hB : 0 < B := by
    by_contra hB
    nlinarith [mul_nonneg h.2.2.1 h.2.1,
      mul_nonpos_of_nonneg_of_nonpos h.1 (le_of_not_gt hB)]
  let l : ℝ := (b ^ 2 + 1) / (a * B - A * b)
  let r : ℝ := A * l / B
  have hl : 0 < l := div_pos (by positivity) hh
  have hr : 0 ≤ r := div_nonneg (mul_nonneg h.2.2.1 hl.le) hB.le
  have hleq : (a * B - A * b) * l = b ^ 2 + 1 := by
    dsimp [l]
    field_simp
  have hreq : B * r = A * l := by
    dsimp [r]
    field_simp
  have hf := isPFPolynomial_X_add_C hr
  have hfx : Interl (X + C r) (X * (X + C r)) :=
    interl_mul_X_of_interl hf.interl_self hf.hasNonnegCoeffs hf.hasNonnegCoeffs
  have hout := hall (C l * (X + C r)) (X * (X + C r))
    (hf.const_mul hl) hf.X_mul (hfx.C_mul_left_of_nonneg hl.le)
    (by rw [natDegree_C_mul hl.ne', natDegree_X_add_C]; norm_num)
    (by rw [natDegree_X_mul (monic_X_add_C r).ne_zero, natDegree_X_add_C])
  have heq : affineDRow a b A B (C l * (X + C r)) (X * (X + C r)) =
      C B * X ^ 2 + C (A * l + 2 * b + B * r) * X + C (a * l + b * r + A * l * r) := by
    simp only [affineDRow, affineD, derivative_mul, derivative_X,
      derivative_C, mul_one, zero_mul, zero_add, add_zero, map_add, map_mul, map_ofNat]
    ring
  have hd : discrim B (A * l + 2 * b + B * r) (a * l + b * r + A * l * r) = -4 := by
    calc
      _ = (A * l - B * r) ^ 2 - 4 * (a * B - A * b) * l + 4 * b ^ 2 := by
        unfold discrim
        ring
      _ = -4 := by rw [hreq, sub_self, zero_pow (by decide), mul_assoc, hleq]; ring
  exact quadraticPoly_not_splits_of_discrim_neg hB.ne' (by rw [hd]; norm_num)
    (heq ▸ hout.splits)

/-- At every common cap at least two, row safety is the cross inequality. -/
theorem affineDRow_isPFPolynomial_upTo_iff {a b A B : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (h : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ A ∧ 0 ≤ B) :
    (∀ p q : ℝ[X], IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      p.natDegree ≤ N → q.natDegree ≤ N →
      IsPFPolynomial (affineDRow a b A B p q)) ↔ a * B ≤ A * b := by
  constructor
  · intro hall
    exact row_cross_of_cap_two h (fun p q hp hq hi hd he ↦
      hall p q hp hq hi (hd.trans hN) (he.trans hN))
  · intro hc p q hp hq hi _ _
    exact (affineDRow_pf_anchor h hc hp hq hi).1

/-- The unrestricted affine-derivative row criterion. -/
theorem affineDRow_isPFPolynomial_iff {a b A B : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ A ∧ 0 ≤ B) :
    (∀ p q : ℝ[X], IsPFPolynomial p → IsPFPolynomial q → Interl p q →
      IsPFPolynomial (affineDRow a b A B p q)) ↔ a * B ≤ A * b := by
  constructor
  · intro hall
    exact row_cross_of_cap_two h (fun p q hp hq hi _ _ ↦ hall p q hp hq hi)
  · intro hc p q hp hq hi
    exact (affineDRow_pf_anchor h hc hp hq hi).1

private theorem column_cross_of_linear {a c A C₀ : ℝ}
    (hcol : IsPFPolynomial (affineD a A (X + 1)) ∧
      IsPFPolynomial (affineD c C₀ (X + 1)) ∧
      Interl (affineD a A (X + 1)) (affineD c C₀ (X + 1))) : A * c ≤ a * C₀ := by
  have hw : 0 ≤ (Polynomial.wronskian (affineD a A (X + 1))
      (affineD c C₀ (X + 1))).eval 0 := by
    rcases hcol.2.2 with hz | hz | hi
    · simp [hz, Polynomial.wronskian]
    · simp [hz, Polynomial.wronskian]
    · exact wronskian_eval_nonneg_of_strictInterl
        (hcol.2.1.hasNonnegCoeffs.pos_leadingCoeff hi.2.1.1)
        (hcol.1.hasNonnegCoeffs.pos_leadingCoeff hi.1.1) hi 0
  simp [affineD, Polynomial.wronskian, derivative_mul] at hw
  nlinarith

private theorem affineD_column {a c A C₀ : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ c ∧ 0 ≤ A ∧ 0 ≤ C₀) (hc : A * c ≤ a * C₀)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (affineD a A p) ∧ IsPFPolynomial (affineD c C₀ p) ∧
      Interl (affineD a A p) (affineD c C₀ p) := by
  exact ⟨hp.affineD h.1 h.2.2.1, hp.affineD h.2.1 h.2.2.2,
    interl_nonneg_combos_of_cross hp.derivative hp hp.derivative_interl_self
      h.2.1 h.1 h.2.2.2 h.2.2.1 (by nlinarith)⟩

/-- The affine-derivative column criterion at every positive degree cap. -/
theorem affineD_column_through_iff {a c A C₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (h : 0 ≤ a ∧ 0 ≤ c ∧ 0 ≤ A ∧ 0 ≤ C₀) :
    (∀ p : ℝ[X], IsPFPolynomial p → p.natDegree ≤ N →
      IsPFPolynomial (affineD a A p) ∧ IsPFPolynomial (affineD c C₀ p) ∧
        Interl (affineD a A p) (affineD c C₀ p)) ↔ A * c ≤ a * C₀ := by
  constructor
  · intro hall
    exact column_cross_of_linear (hall (X + 1) isPFPolynomial_X_add_one (by simpa using hN))
  · intro hc p hp _
    exact affineD_column h hc hp

/-- The unrestricted same-input affine-derivative column criterion, including PF images. -/
theorem affineD_column_iff {a c A C₀ : ℝ}
    (h : 0 ≤ a ∧ 0 ≤ c ∧ 0 ≤ A ∧ 0 ≤ C₀) :
    (∀ p : ℝ[X], IsPFPolynomial p →
      IsPFPolynomial (affineD a A p) ∧ IsPFPolynomial (affineD c C₀ p) ∧
        Interl (affineD a A p) (affineD c C₀ p)) ↔ A * c ≤ a * C₀ := by
  constructor
  · intro hall
    exact column_cross_of_linear (hall (X + 1) isPFPolynomial_X_add_one)
  · intro hc p hp
    exact affineD_column h hc hp

example : ∀ p q : ℝ[X], IsPFPolynomial p → IsPFPolynomial q → Interl p q →
    IsPFPolynomial (affineDRow 0 1 1 0 p q) := by
  exact (affineDRow_isPFPolynomial_iff (by norm_num)).mpr (by norm_num)

example : ¬ (∀ p q : ℝ[X], IsPFPolynomial p → IsPFPolynomial q → Interl p q →
    IsPFPolynomial (affineDRow 1 0 0 1 p q)) := by
  rw [affineDRow_isPFPolynomial_iff (by norm_num)]
  norm_num

example {p : ℝ[X]} (hp : IsPFPolynomial p) :
    Interl (affineD 1 0 p) (affineD 0 1 p) := by
  exact ((affineD_column_iff (by norm_num)).mpr (by norm_num) p hp).2.2

end RealRooted
