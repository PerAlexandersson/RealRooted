module

public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
public import RealRooted.PFPolynomial
public import RealRooted.Interlacing.QuadraticPFPreservers
public import RealRooted.SimpleRoots
import RealRooted.Interlacing.Closure
import RealRooted.Interlacing.Residue
import RealRooted.Interlacing.RootDeletionExpansion
import RealRooted.GarloffWagner.KreinExpansion
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Operations
import RealRooted.QuadraticInterlacingClosure
import RealRooted.LaguerreSamuelson
import RealRooted.Linear
import RealRooted.QuadraticRoot

/-!
# Second-order operators on the Pólya-frequency cone

Reusable algebraic and order-theoretic parts of the classification of
`(a + bX) + (c + dX)D + fXD²` on polynomials with nonpositive real roots.
-/

public section

open Polynomial BigOperators Filter Topology

noncomputable section

namespace RealRooted

/-- The affine-coefficient second-order differential operator on the ray. -/
def secondOrderRayOperator (a b c d f : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (C a + C b * X) * p + (C c + C d * X) * p.derivative +
    C f * X * p.derivative.derivative

/-- The factored PF operator is the zero constant-derivative slice of the ray
operator, with its parameters reordered. -/
theorem secondOrderPFOperator_eq_secondOrderRayOperator
    (A B C₀ E : ℝ) (p : ℝ[X]) :
    secondOrderPFOperator A B C₀ E p =
      secondOrderRayOperator E C₀ 0 B A p := by
  simp [secondOrderPFOperator, secondOrderRayOperator]
  ring

/-- The second-order ray operator, packaged as a real-linear map. -/
def secondOrderRayOperatorₗ (a b c d f : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  LinearMap.mul ℝ ℝ[X] (C a + C b * X) +
    (LinearMap.mul ℝ ℝ[X] (C c + C d * X)).comp derivative +
      (LinearMap.mul ℝ ℝ[X] (C f * X)).comp (derivative.comp derivative)

/-- The linear-map package agrees with the displayed differential operator. -/
@[simp] theorem secondOrderRayOperatorₗ_apply (a b c d f : ℝ) (p : ℝ[X]) :
    secondOrderRayOperatorₗ a b c d f p = secondOrderRayOperator a b c d f p := by
  simp [secondOrderRayOperatorₗ, secondOrderRayOperator]
  ring

/-- The operator sends the constant polynomial `1` to `a + bX`. -/
theorem secondOrderRayOperator_one (a b c d f : ℝ) :
    secondOrderRayOperator a b c d f 1 = C a + C b * X := by
  simp [secondOrderRayOperator]

/-- Explicit image of a positive-degree monomial. -/
theorem secondOrderRayOperator_X_pow_succ (a b c d f : ℝ) (n : ℕ) :
    secondOrderRayOperator a b c d f (X ^ (n + 1)) =
      C b * X ^ (n + 2) + C (a + d * (n + 1)) * X ^ (n + 1) +
        C ((n + 1) * (c + f * n)) * X ^ n := by
  cases n with
  | zero =>
      simp [secondOrderRayOperator]
      ring
  | succ n =>
      simp [secondOrderRayOperator, derivative_pow]
      ring

/-- The monomial image is a power of `X` times its residual quadratic. -/
theorem secondOrderRayOperator_X_pow_succ_factor (a b c d f : ℝ) (n : ℕ) :
    secondOrderRayOperator a b c d f (X ^ (n + 1)) =
      X ^ n *
        (C b * X ^ 2 + C (a + d * (n + 1)) * X +
          C ((n + 1) * (c + f * n))) := by
  rw [secondOrderRayOperator_X_pow_succ]
  ring

/-- Removing the repeated factor from a shifted-power image leaves the cubic
used by the lower-branch obstruction. -/
theorem secondOrderRayOperator_shifted_pow_factor
    (a b c d f r : ℝ) (n : ℕ) :
    secondOrderRayOperator a b c d f ((X + C r) ^ (n + 2)) =
      (X + C r) ^ n *
        ((C a + C b * X) * (X + C r) ^ 2 +
          C (n + 2 : ℝ) * (C c + C d * X) * (X + C r) +
          C ((n + 2 : ℝ) * (n + 1) * f) * X) := by
  simp [secondOrderRayOperator, derivative_pow]
  ring

/-- The discriminant of the residual quadratic in a monomial image. -/
def secondOrderMonomialDiscrim (a b c d f : ℝ) (m : ℕ) : ℝ :=
  (a + d * m) ^ 2 - 4 * b * m * (c + f * (m - 1))

/-- Universal preservation of the PF cone by the second-order ray operator. -/
def SecondOrderRayPreserving (a b c d f : ℝ) : Prop :=
  ∀ p : ℝ[X], IsPFPolynomial p →
    IsPFPolynomial (secondOrderRayOperator a b c d f p)

/-- A negative residual discriminant obstructs splitting of the monomial image. -/
theorem not_splits_secondOrderRayOperator_X_pow_of_discrim_neg
    {a b c d f : ℝ} {m : ℕ} (hm : 0 < m) (hb : b ≠ 0)
    (hdisc : secondOrderMonomialDiscrim a b c d f m < 0) :
    ¬(secondOrderRayOperator a b c d f (X ^ m)).Splits := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
  rw [secondOrderRayOperator_X_pow_succ_factor]
  intro hout
  let q : ℝ[X] :=
    C b * X ^ 2 + C (a + d * (n + 1)) * X + C ((n + 1) * (c + f * n))
  have hq0 : q ≠ 0 := by
    intro hzero
    have hdegree : q.natDegree = 2 := by
      dsimp [q]
      exact natDegree_quadratic hb
    rw [hzero] at hdegree
    simp at hdegree
  have hq_dvd : q ∣ X ^ n * q := dvd_mul_left q (X ^ n)
  have hq_splits : q.Splits :=
    (isRealRooted_of_dvd (mul_ne_zero (pow_ne_zero n X_ne_zero) hq0) hout hq0 hq_dvd).2
  have hnot : ¬q.Splits := by
    apply quadraticPoly_not_splits_of_discrim_neg hb
    rw [discrim]
    simp [secondOrderMonomialDiscrim] at hdisc
    nlinarith
  exact hnot hq_splits

/-- A negative operator discriminant eventually gives a negative monomial
discriminant. -/
theorem exists_secondOrderMonomialDiscrim_neg_of_discrim_neg
    (a b c d f : ℝ) (hdelta : d ^ 2 - 4 * b * f < 0) :
    ∃ m : ℕ, 0 < m ∧ secondOrderMonomialDiscrim a b c d f m < 0 := by
  let delta := d ^ 2 - 4 * b * f
  let linear := 2 * a * d - 4 * b * c + 4 * b * f
  let bound := max 1 ((|linear| + a ^ 2) / (-delta))
  obtain ⟨m, hm⟩ := exists_nat_gt bound
  have hdelta_neg : delta < 0 := by simpa [delta] using hdelta
  have hdenom : 0 < -delta := neg_pos.mpr hdelta_neg
  have hm_one : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm_pos : 0 < m := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hm_one)
  have hratio : (|linear| + a ^ 2) / (-delta) < (m : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hm
  have hmain : |linear| + a ^ 2 < (-delta) * m :=
    by simpa [mul_comm] using (div_lt_iff₀ hdenom).mp hratio
  have hm_real : (1 : ℝ) ≤ m := hm_one.le
  have hmul : (|linear| + a ^ 2) * m ≤ (-delta) * m ^ 2 := by
    nlinarith
  have ha_sq : 0 ≤ a ^ 2 := sq_nonneg a
  have habs : linear ≤ |linear| := le_abs_self linear
  have hstrict : delta * (m : ℝ) ^ 2 + linear * m + a ^ 2 < 0 := by
    nlinarith
  refine ⟨m, hm_pos, ?_⟩
  rw [secondOrderMonomialDiscrim]
  change (a + d * (m : ℝ)) ^ 2 -
      4 * b * (m : ℝ) * (c + f * ((m : ℝ) - 1)) < 0
  dsimp [delta, linear] at hstrict
  nlinarith

/-- Negative operator discriminant is a genuine universal PF obstruction. -/
theorem not_secondOrderRayPreserving_of_discrim_neg
    {a b c d f : ℝ} (hb : 0 < b) (hdelta : d ^ 2 - 4 * b * f < 0) :
    ¬SecondOrderRayPreserving a b c d f := by
  obtain ⟨m, hm, hdisc⟩ :=
    exists_secondOrderMonomialDiscrim_neg_of_discrim_neg a b c d f hdelta
  intro hpres
  have hout := hpres (X ^ m) (isPFPolynomial_X.pow m)
  have hnot := not_splits_secondOrderRayOperator_X_pow_of_discrim_neg
    hm hb.ne' hdisc
  rcases hout.eq_zero_or_splits with hzero | hsplits
  · exact hnot (hzero.symm ▸ Splits.zero)
  · exact hnot hsplits

/-- The existing factored quadratic-operator theorem gives the `c = 0`
sufficiency slice of the ray family. -/
theorem IsPFPolynomial.secondOrderRayOperator_of_constDerivative_eq_zero
    {p : ℝ[X]} (hp : IsPFPolynomial p) {a b d f : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d) (hf : 0 < f)
    (hdelta : 4 * b * f ≤ d ^ 2) :
    IsPFPolynomial (secondOrderRayOperator a b 0 d f p) := by
  have hpres := hp.secondOrderPFOperator_of_discrim_nonneg
    (A := f) (B := d) (C₀ := b) (E := a) hf hb hd ha (by nlinarith)
  rw [secondOrderPFOperator_eq_secondOrderRayOperator] at hpres
  exact hpres

/-- The sharp root-sum estimate used at a point in a fixed input-root gap.

The first list consists of the `j` positive terms (each at least one), and
the second list consists of the nonpositive terms. -/
theorem sum_sq_ge_card_and_sum_sq
    (positive negative : List ℝ)
    (hpositive : ∀ x ∈ positive, 1 ≤ x)
    (hnegative : ∀ x ∈ negative, x ≤ 0)
    (hsum : 0 < positive.sum + negative.sum) :
    (positive.length : ℝ) ≤
        (positive.map (fun x ↦ x ^ 2)).sum +
          (negative.map (fun x ↦ x ^ 2)).sum ∧
      (positive.sum + negative.sum) ^ 2 ≤
        (positive.length : ℝ) *
          ((positive.map (fun x ↦ x ^ 2)).sum +
            (negative.map (fun x ↦ x ^ 2)).sum) := by
  have hneg_sum : negative.sum ≤ 0 := by
    have aux : ∀ l : List ℝ, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
          simp only [List.sum_cons]
          linarith [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
    exact aux negative hnegative
  have hneg_sq : 0 ≤ (negative.map (fun x ↦ x ^ 2)).sum := by
    exact List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      positivity
  have hpos_card : (positive.length : ℝ) ≤
      (positive.map (fun x ↦ x ^ 2)).sum := by
    have aux : ∀ l : List ℝ, (∀ x ∈ l, 1 ≤ x) →
        (l.length : ℝ) ≤ (l.map (fun x ↦ x ^ 2)).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
            List.sum_cons]
          have hx := hl x (by simp)
          have hxs : ∀ y ∈ xs, 1 ≤ y := fun y hy => hl y (by simp [hy])
          nlinarith [ih hxs]
    exact aux positive hpositive
  have hcs := RealRooted.Samuelson.sq_sum_le_card_mul_sum_sq
    (Multiset.ofList positive)
  have htotal_le : positive.sum + negative.sum ≤ positive.sum := by linarith
  have hpos_sum : 0 < positive.sum := lt_of_lt_of_le hsum htotal_le
  have hsquares : (positive.sum + negative.sum) ^ 2 ≤ positive.sum ^ 2 := by
    nlinarith
  constructor
  · linarith
  · simpa using
      hsquares.trans (hcs.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right hneg_sq) (Nat.cast_nonneg positive.length)))

/-- If every root-sum term is nonpositive or at least one, a positive total
has sum of squares at least both the total and one. -/
theorem sum_sq_ge_max_sum_one
    (positive negative : List ℝ)
    (hpositive : ∀ x ∈ positive, 1 ≤ x)
    (hnegative : ∀ x ∈ negative, x ≤ 0)
    (hsum : 0 < positive.sum + negative.sum) :
    max (positive.sum + negative.sum) 1 ≤
      (positive.map (fun x ↦ x ^ 2)).sum +
        (negative.map (fun x ↦ x ^ 2)).sum := by
  obtain ⟨hcard, hsquare⟩ :=
    sum_sq_ge_card_and_sum_sq positive negative hpositive hnegative hsum
  have hneg_sum : negative.sum ≤ 0 := by
    have aux : ∀ l : List ℝ, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
          simp only [List.sum_cons]
          linarith [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
    exact aux negative hnegative
  have hpos_sum : 0 < positive.sum := by linarith
  have hnonempty : positive ≠ [] := by
    intro hnil
    simp [hnil] at hpos_sum
  have hcard_one : (1 : ℝ) ≤ positive.length := by
    have : 0 < positive.length := by
      apply Nat.pos_of_ne_zero
      intro hzero
      apply hnonempty
      simpa using hzero
    exact_mod_cast this
  have hq_nonneg : 0 ≤
      (positive.map (fun x ↦ x ^ 2)).sum +
        (negative.map (fun x ↦ x ^ 2)).sum := by linarith
  have hproduct := mul_le_mul_of_nonneg_right hcard hq_nonneg
  apply max_le
  · nlinarith
  · linarith

/-- The root-sum estimate gives both scalar lower bounds used in the
per-gap test. -/
theorem secondOrder_perGap_lower_bounds
    (positive negative : List ℝ)
    (hpositive : ∀ x ∈ positive, 1 ≤ x)
    (hnegative : ∀ x ∈ negative, x ≤ 0)
    (hsum : 0 < positive.sum + negative.sum)
    (A H f v : ℝ) (hf : 0 ≤ f) (hv : 0 < v) :
    let s := positive.sum + negative.sum
    let q := (positive.map (fun x ↦ x ^ 2)).sum +
      (negative.map (fun x ↦ x ^ 2)).sum
    A + H * s / v + f * v / s * (positive.length : ℝ) ≤
        A + H * s / v + f * v / s * q ∧
      A + H * s / v + f * v / s * (s ^ 2 / positive.length) ≤
        A + H * s / v + f * v / s * q := by
  dsimp only
  obtain ⟨hcard, hsquare⟩ :=
    sum_sq_ge_card_and_sum_sq positive negative hpositive hnegative hsum
  have hneg_sum : negative.sum ≤ 0 := by
    have aux : ∀ l : List ℝ, (∀ x ∈ l, x ≤ 0) → l.sum ≤ 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons x xs ih =>
          simp only [List.sum_cons]
          linarith [hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
    exact aux negative hnegative
  have hpos_sum : 0 < positive.sum := by linarith
  have hnonempty : positive ≠ [] := by
    intro hnil
    simp [hnil] at hpos_sum
  have hcard_pos : (0 : ℝ) < positive.length := by
    have hlen : positive.length ≠ 0 := by
      intro hzero
      apply hnonempty
      simpa using hzero
    have : 0 < positive.length := Nat.pos_of_ne_zero hlen
    exact_mod_cast this
  have hcoef : 0 ≤ f * v / (positive.sum + negative.sum) := by positivity
  have hdiv : (positive.sum + negative.sum) ^ 2 / positive.length ≤
      (positive.map (fun x ↦ x ^ 2)).sum +
        (negative.map (fun x ↦ x ^ 2)).sum := by
    rw [div_le_iff₀ hcard_pos]
    simpa [mul_comm] using hsquare
  constructor <;>
    gcongr

/-- Algebraic logarithmic-derivative identity used in every gap. -/
theorem secondOrder_perGap_identity
    (a b c d f v s squareSum : ℝ) (hv : v ≠ 0) (hs : s ≠ 0) :
    a - c * v + (d * v - b - f * v ^ 2) * s / v +
        f * v / s * squareSum =
      a - c * v + (d - b / v - f * v) * s +
        f * v / s * squareSum := by
  field_simp

/-- The limiting-quadratic discriminant identity for the upper obstruction. -/
theorem secondOrder_upper_obstruction_identity (a b c d f : ℝ) :
    ((a - d) * c + 2 * f * (a + d)) ^ 2 -
        (c ^ 2 + 4 * f ^ 2) * ((a + d) ^ 2 - 4 * b * c) =
      4 * c * (b * c ^ 2 - a * d * c - f * (d ^ 2 - 4 * b * f - a ^ 2)) := by
  ring

/-- The indexed limiting-quadratic discriminant identity used by the
upper-branch converse. -/
theorem secondOrder_upper_obstruction_identity_at_index
    (a b c d f : ℝ) (m : ℕ) :
    let k : ℝ := m
    ((a + d * k) * (c + 2 * f * k) -
          2 * d * k * (c + f * (k - 1))) ^ 2 -
        (c ^ 2 + 4 * f ^ 2 * k) *
          ((a + d * k) ^ 2 - 4 * b * k * (c + f * (k - 1))) =
      4 * k * (c + f * (k - 1)) *
        (b * c ^ 2 - a * d * c + f * (a ^ 2 - k * (d ^ 2 - 4 * b * f))) := by
  dsimp
  ring

/-- A positive-leading quadratic in a nonnegative parameter is negative at
its vertex when its linear coefficient is negative and its discriminant is
positive. -/
theorem exists_pos_quadratic_lt_zero {B C L : ℝ}
    (hL : 0 < L) (hB : B < 0) (hdisc : L * C < B ^ 2) :
    ∃ t : ℝ, 0 < t ∧ C + 2 * B * t + L * t ^ 2 < 0 := by
  refine ⟨-B / L, div_pos (neg_pos.mpr hB) hL, ?_⟩
  have hcalc : C + 2 * B * (-B / L) + L * (-B / L) ^ 2 =
      C - B ^ 2 / L := by
    field_simp [hL.ne']
    ring
  rw [hcalc, sub_lt_zero]
  exact (lt_div_iff₀ hL).2 (by simpa [mul_comm] using hdisc)

/-- Subtracting a scalar multiple of the identity changes only the constant
parameter of the second-order operator. -/
theorem secondOrderRayOperator_sub_const
    (a b c d f rho : ℝ) (p : ℝ[X]) :
    secondOrderRayOperator a b c d f p - C rho * p =
      secondOrderRayOperator (a - rho) b c d f p := by
  simp [secondOrderRayOperator]
  ring

/-- Abstract tail-transfer theorem for a linear operator whose scalar shifts
preserve PF polynomials. -/
theorem isPFPolynomial_basisTransform_iterate_of_shift_preservers
    (L : ℝ[X] →ₗ[ℝ] ℝ[X]) (g : ℝ[X]) (k : ℕ) (eta : ℝ)
    (hbase : IsPFPolynomial ((L : ℝ[X] → ℝ[X])^[k] g))
    (hshift : ∀ rho ≤ eta, ∀ {p : ℝ[X]}, IsPFPolynomial p →
      IsPFPolynomial (L p - C rho * p))
    {q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq_splits : q.Splits)
    (hq_roots : ∀ rho ∈ q.roots, rho ≤ eta) :
    IsPFPolynomial
      (basisTransform (fun n ↦ ((L : ℝ[X] → ℝ[X])^[n])
        (((L : ℝ[X] → ℝ[X])^[k]) g)) q) := by
  let seed : ℝ[X] := ((L : ℝ[X] → ℝ[X])^[k]) g
  let B : ℕ → ℝ[X] := fun n ↦ ((L : ℝ[X] → ℝ[X])^[n]) seed
  have hsucc : ∀ n, B (n + 1) = L (B n) := by
    intro n
    simp [B, Function.iterate_succ_apply']
  have hfactor_step (rho : ℝ) (p : ℝ[X]) :
      basisTransform B ((X - C rho) * p) =
        L (basisTransform B p) - C rho * basisTransform B p := by
    calc
      basisTransform B ((X - C rho) * p) =
          basisTransformₗ B ((X - C rho) * p) := rfl
      _ = basisTransformₗ B (X * p - C rho * p) := by
        congr 1
        ring
      _ = basisTransformₗ B (X * p) - basisTransformₗ B (C rho * p) :=
        LinearMap.map_sub _ _ _
      _ = L (basisTransform B p) - C rho * basisTransform B p := by
        rw [basisTransformₗ_apply, basisTransform_X_mul_of_succ B L hsucc,
          basisTransformₗ_apply]
        have hscalar := basisTransform_smul B rho p
        rw [Polynomial.smul_eq_C_mul] at hscalar
        rw [hscalar]
  have hproducts : ∀ roots : Multiset ℝ,
      (∀ rho ∈ roots, rho ≤ eta) →
      IsPFPolynomial
        (basisTransform B ((roots.map fun rho ↦ X - C rho).prod)) := by
    intro roots hroots
    induction roots using Multiset.induction_on with
    | empty =>
        rw [Multiset.map_zero, Multiset.prod_zero,
          show (1 : ℝ[X]) = C 1 by simp, basisTransform_C]
        simpa [B, seed] using hbase
    | @cons rho roots ih =>
        have hrho : rho ≤ eta := hroots rho (by simp)
        have htail : ∀ r ∈ roots, r ≤ eta :=
          fun r hr ↦ hroots r (by simp [hr])
        rw [Multiset.map_cons, Multiset.prod_cons, hfactor_step]
        exact hshift rho hrho (ih htail)
  rw [hq_splits.eq_prod_roots]
  change IsPFPolynomial
    (basisTransform B (C q.leadingCoeff *
      (q.roots.map fun rho ↦ X - C rho).prod))
  rw [show C q.leadingCoeff * (q.roots.map fun rho ↦ X - C rho).prod =
      q.leadingCoeff • (q.roots.map fun rho ↦ X - C rho).prod by
        rw [Polynomial.smul_eq_C_mul],
    basisTransform_smul]
  exact (hproducts q.roots hq_roots).const_mul hq_pos

/-- Every tail of a second-order orbit gives a PF-preserving basis map once
all scalar shifts through the source endpoint preserve the PF cone. -/
theorem secondOrderRay_tail_basisTransform_isPFPolynomial
    (a b c d f eta : ℝ) (g : ℝ[X]) (k : ℕ)
    (heta : 0 ≤ eta) (hg : IsPFPolynomial g)
    (hshift : ∀ rho ≤ eta,
      SecondOrderRayPreserving (a - rho) b c d f)
    {q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq_splits : q.Splits)
    (hq_roots : ∀ rho ∈ q.roots, rho ≤ eta) :
    IsPFPolynomial
      (basisTransform
        (fun n ↦ ((secondOrderRayOperatorₗ a b c d f : ℝ[X] → ℝ[X])^[n])
          (((secondOrderRayOperatorₗ a b c d f : ℝ[X] → ℝ[X])^[k]) g)) q) := by
  let L := secondOrderRayOperatorₗ a b c d f
  have horbit : ∀ n : ℕ, IsPFPolynomial (((L : ℝ[X] → ℝ[X])^[n]) g) := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hpres := hshift 0 heta
        simpa [L, secondOrderRayOperator_sub_const] using hpres _ ih
  apply isPFPolynomial_basisTransform_iterate_of_shift_preservers
    L g k (eta := eta) (horbit k) ?_ hq_pos hq_splits hq_roots
  intro rho hrho p hp
  simpa [L, secondOrderRayOperator_sub_const] using hshift rho hrho p hp

/-- The residues of a successor-degree Lagrange expansion sum to the ratio of
leading coefficients. -/
theorem leadingCoeffRatio_eq_sum_residues {p g : ℝ[X]}
    (hgs : g.Splits) (hgnd : g.roots.Nodup)
    (hdeg : g.natDegree = p.natDegree + 1) :
    ∑ r ∈ g.roots.toFinset, p.eval r / g.derivative.eval r =
      p.leadingCoeff / g.leadingCoeff := by
  have hgpos : 1 ≤ g.natDegree := by lia
  have hpdeg : p.degree < g.natDegree := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [degree_eq_natDegree hp0]
      exact_mod_cast (by lia : p.natDegree < g.natDegree)
  have hlag := lagInterp_eq_g hgs hgnd hgpos hpdeg
  have hcoeff0 := congrArg (fun q : ℝ[X] ↦ q.coeff p.natDegree) hlag
  have hcoeff :
      ∑ r ∈ g.roots.toFinset,
          (p.eval r / g.derivative.eval r) *
            (g /ₘ (X - C r)).coeff p.natDegree = p.coeff p.natDegree := by
    simpa [lagInterp] using hcoeff0
  have hterm : ∀ r ∈ g.roots.toFinset,
      (p.eval r / g.derivative.eval r) *
          (g /ₘ (X - C r)).coeff p.natDegree =
        (p.eval r / g.derivative.eval r) * g.leadingCoeff := by
    intro r hr
    have hrroot : g.IsRoot r :=
      isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    congr 1
    have hqdeg : (g /ₘ (X - C r)).natDegree = p.natDegree := by
      rw [Polynomial.natDegree_divByMonic_X_sub_C, hdeg]
      lia
    rw [← hqdeg]
    exact leadingCoeff_divByMonic_X_sub_C hrroot
  have hcoeff' :
      ∑ r ∈ g.roots.toFinset,
          (p.eval r / g.derivative.eval r) * g.leadingCoeff =
        p.coeff p.natDegree := by
    calc
      _ = ∑ r ∈ g.roots.toFinset,
          (p.eval r / g.derivative.eval r) *
            (g /ₘ (X - C r)).coeff p.natDegree := by
              apply Finset.sum_congr rfl
              intro r hr
              exact (hterm r hr).symm
      _ = p.coeff p.natDegree := hcoeff
  rw [← Finset.sum_mul] at hcoeff'
  have hglc : g.leadingCoeff ≠ 0 := by
    exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hgpos)
  apply (eq_div_iff hglc).2
  simpa using hcoeff'

/-! ## Derivative-minus-interlacer decomposition -/

/-- The residue weights in the derivative-minus-interlacer expansion are
nonnegative. -/
private theorem derivative_sub_ratio_root_weight_nonneg {p g : ℝ[X]}
    (hpg : StrictInterl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    (hg_simple : HasSimpleRoots g) :
    ∀ r ∈ g.roots.toFinset,
      0 ≤ 1 - (g.leadingCoeff / p.leadingCoeff) *
        (p.eval r / g.derivative.eval r) := by
  let beta : ℝ := g.leadingCoeff / p.leadingCoeff
  have hbeta_pos : 0 < beta := by
    dsimp [beta]
    exact div_pos hg_pos hp_pos
  have hres_nonneg : ∀ r ∈ g.roots,
      0 ≤ p.eval r / g.derivative.eval r := by
    intro r hr
    exact residue_nonneg_of_right_nodup hpg hg_pos hp_pos
      hg_simple.roots_nodup r hr
  have hsum :
      ∑ r ∈ g.roots.toFinset, p.eval r / g.derivative.eval r = 1 / beta := by
    rw [leadingCoeffRatio_eq_sum_residues hpg.2.1.2 hg_simple.roots_nodup hdeg]
    dsimp [beta]
    field_simp [hp_pos.ne', hg_pos.ne']
  intro r hr
  have hrm : r ∈ g.roots := Multiset.mem_toFinset.mp hr
  have hle : p.eval r / g.derivative.eval r ≤
      ∑ s ∈ g.roots.toFinset, p.eval s / g.derivative.eval s := by
    apply Finset.single_le_sum
      (f := fun s ↦ p.eval s / g.derivative.eval s)
      (s := g.roots.toFinset)
    · intro s hs
      exact hres_nonneg s (Multiset.mem_toFinset.mp hs)
    · exact hr
  have hone : beta *
      (∑ s ∈ g.roots.toFinset,
        p.eval s / g.derivative.eval s) = 1 := by
    rw [hsum]
    field_simp [hbeta_pos.ne']
  dsimp [beta] at hone ⊢
  nlinarith

/-- Lagrange expansion of the derivative-minus-interlacer polynomial in the
root-deletion cofactor basis. -/
private theorem derivative_sub_ratio_eq_weighted_rootDeletionSum {p g : ℝ[X]}
    (hpg : StrictInterl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hg_simple : HasSimpleRoots g) :
    weightedSum
        (g.roots.toFinset.toList.map fun r ↦
          (1 - (g.leadingCoeff / p.leadingCoeff) *
            (p.eval r / g.derivative.eval r), g /ₘ (X - C r))) =
      g.derivative - C (g.leadingCoeff / p.leadingCoeff) * p := by
  let beta : ℝ := g.leadingCoeff / p.leadingCoeff
  let weight : ℝ → ℝ := fun r ↦
    1 - beta * (p.eval r / g.derivative.eval r)
  let cofactor : ℝ → ℝ[X] := fun r ↦ g /ₘ (X - C r)
  let l : List (ℝ × ℝ[X]) :=
    g.roots.toFinset.toList.map fun r ↦ (weight r, cofactor r)
  have hgdeg : 1 ≤ g.natDegree := by lia
  have hlag_p : lagInterp g p = p := by
    apply lagInterp_eq_g hpg.2.1.2 hg_simple.roots_nodup hgdeg
    rw [degree_eq_natDegree hpg.1.1]
    exact_mod_cast (by lia : p.natDegree < g.natDegree)
  have hlag_der : lagInterp g g.derivative = g.derivative := by
    apply lagInterp_eq_g hpg.2.1.2 hg_simple.roots_nodup hgdeg
    rw [degree_eq_natDegree (Polynomial.derivative_ne_zero.mpr (by lia)),
      g.natDegree_derivative]
    exact_mod_cast (by lia : g.natDegree - 1 < g.natDegree)
  have hder_eval : ∀ r ∈ g.roots.toFinset,
      g.derivative.eval r / g.derivative.eval r = 1 := by
    intro r hr
    have hrroot : g.IsRoot r :=
      isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
    exact div_self (hg_simple.eval_derivative_ne_zero hrroot)
  have hl_sum : weightedSum l =
      ∑ r ∈ g.roots.toFinset,
        C (weight r) * cofactor r := by
    simp [l, weightedSum_eq_sum_map]
  have hl_eq : weightedSum l =
      g.derivative - C beta * p := by
    rw [hl_sum, ← hlag_der, ← hlag_p]
    simp only [lagInterp]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hder_eval r hr]
    simp only [cofactor, weight, C_1]
    rw [C_sub, C_1, C_mul]
    ring
  simpa [l, weight, cofactor, beta] using hl_eq

/-- A nonzero nonnegative sum of root-deletion cofactors strictly interlaces
the original split polynomial. -/
private theorem weighted_rootDeletionSum_strictInterl {g : ℝ[X]}
    (hg0 : g ≠ 0) (hgs : g.Splits) (hg_pos : HasPosLeadingCoeff g)
    (weight : ℝ → ℝ)
    (hweight : ∀ r ∈ g.roots.toFinset, 0 ≤ weight r)
    (hex : ∃ ap ∈ g.roots.toFinset.toList.map
      (fun r ↦ (weight r, g /ₘ (X - C r))), 0 < ap.1) :
    StrictInterl
      (weightedSum (g.roots.toFinset.toList.map
        (fun r ↦ (weight r, g /ₘ (X - C r))))) g := by
  apply StrictInterl.weightedSum_right_of_nonneg _ g
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨r, hr, rfl⟩
    exact hweight r (Finset.mem_toList.mp hr)
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨r, hr, rfl⟩
    have hrroot : g.IsRoot r := isRoot_of_mem_roots
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hr))
    have hfactor := mul_divByMonic_eq_iff_isRoot.mpr hrroot
    have hq0 : g /ₘ (X - C r) ≠ 0 := by
      intro hq0
      rw [hq0, mul_zero] at hfactor
      exact hg0 hfactor.symm
    have hqs : (g /ₘ (X - C r)).Splits :=
      (IsKreinSummand.ne_zero_and_splits
        (Or.inr ⟨r, hfactor.symm⟩) hg0 hgs).2
    have hs := strictInterl_self_X_sub_C_mul hq0 hqs r
    rw [hfactor] at hs
    exact hs
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨r, hr, rfl⟩
    exact hg_pos.divByMonic_X_sub_C
      (isRoot_of_mem_roots
        (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hr)))
  · exact hex

/-- The derivative-minus-interlacer lemma when the right polynomial has
simple roots. -/
theorem derivative_sub_leadingCoeffRatio_interl_of_simple {p g : ℝ[X]}
    (hpg : StrictInterl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    (hg_simple : HasSimpleRoots g) :
    Interl
      (g.derivative - C (g.leadingCoeff / p.leadingCoeff) * p) g := by
  let beta : ℝ := g.leadingCoeff / p.leadingCoeff
  let weight : ℝ → ℝ := fun r ↦
    1 - beta * (p.eval r / g.derivative.eval r)
  let l : List (ℝ × ℝ[X]) :=
    g.roots.toFinset.toList.map fun r ↦ (weight r, g /ₘ (X - C r))
  have hweight : ∀ r ∈ g.roots.toFinset, 0 ≤ weight r := by
    simpa [weight, beta] using
      derivative_sub_ratio_root_weight_nonneg hpg hdeg hp_pos hg_pos hg_simple
  have hl_eq : weightedSum l = g.derivative - C beta * p := by
    simpa [l, weight, beta] using
      derivative_sub_ratio_eq_weighted_rootDeletionSum hpg hdeg hg_simple
  by_cases hh0 : g.derivative - C beta * p = 0
  · rw [hh0]
    exact interl_zero_left _
  · have hex : ∃ ap ∈ l, 0 < ap.1 := by
      by_contra hnot
      have hzero : ∀ ap ∈ l, ap.1 = 0 := by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨r, hr, rfl⟩
        exact le_antisymm (not_lt.mp fun hpos ↦ hnot ⟨_, hap, hpos⟩)
          (hweight r (Finset.mem_toList.mp hr))
      have : weightedSum l = 0 :=
        weightedSum_eq_zero_of_forall_coeff_zero l hzero
      exact hh0 (hl_eq.symm.trans this)
    have hstrict : StrictInterl (weightedSum l) g :=
      weighted_rootDeletionSum_strictInterl
        hpg.2.1.1 hpg.2.1.2 hg_pos weight hweight hex
    rw [hl_eq] at hstrict
    exact hstrict.toInterl

/-- The derivative-minus-interlacer polynomial has the expected degree and
leading coefficient above the constant-left boundary. -/
theorem derivative_sub_leadingCoeffRatio_degree_leadingCoeff {p g : ℝ[X]}
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    (hpdeg : 1 ≤ p.natDegree) :
    let h := g.derivative - C (g.leadingCoeff / p.leadingCoeff) * p
    h.natDegree = p.natDegree ∧
      h.leadingCoeff = (p.natDegree : ℝ) * g.leadingCoeff := by
  dsimp
  let beta := g.leadingCoeff / p.leadingCoeff
  let h := g.derivative - C beta * p
  have hcoeff : h.coeff p.natDegree =
      (p.natDegree : ℝ) * g.leadingCoeff := by
    dsimp [h]
    rw [coeff_sub, coeff_derivative, coeff_C_mul]
    have hgcoeff : g.coeff (p.natDegree + 1) = g.leadingCoeff := by
      rw [← hdeg]
      rfl
    rw [hgcoeff]
    rw [show p.coeff p.natDegree = p.leadingCoeff by rfl]
    change (g.leadingCoeff * ((p.natDegree : ℝ) + 1) -
      beta * p.leadingCoeff) = (p.natDegree : ℝ) * g.leadingCoeff
    dsimp [beta]
    field_simp [hp_pos.ne']
    ring
  have hcoeff_ne : h.coeff p.natDegree ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by lia)) hg_pos.ne'
  have hlower : p.natDegree ≤ h.natDegree :=
    le_natDegree_of_ne_zero hcoeff_ne
  have hderdeg : g.derivative.natDegree ≤ p.natDegree := by
    rw [g.natDegree_derivative, hdeg]
    lia
  have hscaleddeg : (C beta * p).natDegree ≤ p.natDegree :=
    natDegree_C_mul_le beta p
  have hupper : h.natDegree ≤ p.natDegree := by
    simpa [h] using natDegree_sub_le_of_le hderdeg hscaleddeg
  have hnat : h.natDegree = p.natDegree := le_antisymm hupper hlower
  refine ⟨hnat, ?_⟩
  rw [leadingCoeff, hnat]
  exact hcoeff

/-! ## Repeated-root closure -/

/-- A coefficientwise limit of fixed-degree interlacing pairs with fixed
positive leading coefficients still interlaces. -/
private theorem interlaces_of_fixed_leadingCoeff_of_coeff_tendsto
    {P G : ℕ → ℝ[X]} {p g : ℝ[X]} {n : ℕ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hPlc : ∀ M, (P M).leadingCoeff = a)
    (hGlc : ∀ M, (G M).leadingCoeff = b)
    (hplc : p.leadingCoeff = a) (hglc : g.leadingCoeff = b)
    (hPdeg : ∀ M, (P M).natDegree = n)
    (hGdeg : ∀ M, (G M).natDegree = n + 1)
    (hpdeg : p.natDegree = n) (hgdeg : g.natDegree = n + 1)
    (hinter : ∀ M, Interlaces (P M) (G M))
    (hPcoeff : ∀ i, Tendsto (fun M ↦ (P M).coeff i) atTop (nhds (p.coeff i)))
    (hGcoeff : ∀ i, Tendsto (fun M ↦ (G M).coeff i) atTop (nhds (g.coeff i))) :
    Interlaces p g := by
  let PM : ℕ → ℝ[X] := fun M ↦ C a⁻¹ * P M
  let GM : ℕ → ℝ[X] := fun M ↦ C b⁻¹ * G M
  let p₀ : ℝ[X] := C a⁻¹ * p
  let g₀ : ℝ[X] := C b⁻¹ * g
  have hPMMonic (M : ℕ) : (PM M).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hPlc M]
    exact inv_mul_cancel₀ ha.ne'
  have hGMMonic (M : ℕ) : (GM M).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hGlc M]
    exact inv_mul_cancel₀ hb.ne'
  have hp₀Monic : p₀.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hplc]
    exact inv_mul_cancel₀ ha.ne'
  have hg₀Monic : g₀.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hglc]
    exact inv_mul_cancel₀ hb.ne'
  have hPMDegree (M : ℕ) : (PM M).natDegree = n := by
    rw [natDegree_C_mul (inv_ne_zero ha.ne'), hPdeg]
  have hGMDegree (M : ℕ) : (GM M).natDegree = n + 1 := by
    rw [natDegree_C_mul (inv_ne_zero hb.ne'), hGdeg]
  have hp₀Degree : p₀.natDegree = n := by
    rw [natDegree_C_mul (inv_ne_zero ha.ne'), hpdeg]
  have hg₀Degree : g₀.natDegree = n + 1 := by
    rw [natDegree_C_mul (inv_ne_zero hb.ne'), hgdeg]
  have hscaled (M : ℕ) : Interlaces (PM M) (GM M) := by
    apply (StrictInterl.C_mul_right
      (StrictInterl.C_mul_left (hinter M).toStrictInterl
        (inv_ne_zero ha.ne')) (inv_ne_zero hb.ne')).toInterlaces
    rw [hPMDegree, hGMDegree]
  have hPMCoeff (i : ℕ) : Tendsto (fun M ↦ (PM M).coeff i) atTop
      (nhds (p₀.coeff i)) := by
    simpa [PM, p₀, coeff_C_mul] using tendsto_const_nhds.mul (hPcoeff i)
  have hGMCoeff (i : ℕ) : Tendsto (fun M ↦ (GM M).coeff i) atTop
      (nhds (g₀.coeff i)) := by
    simpa [GM, g₀, coeff_C_mul] using tendsto_const_nhds.mul (hGcoeff i)
  have hlimit : Interlaces p₀ g₀ :=
    interlaces_of_monic_of_coeff_tendsto hPMMonic hGMMonic hp₀Monic
      hg₀Monic hPMDegree hGMDegree hp₀Degree hg₀Degree
      hscaled hPMCoeff hGMCoeff
  have hunscaled := StrictInterl.C_mul_right
    (StrictInterl.C_mul_left hlimit.toStrictInterl ha.ne') hb.ne'
  have hp_norm : C a * p₀ = p := by
    rw [show p₀ = C a⁻¹ * p by rfl, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ ha.ne', C_1, one_mul]
  have hg_norm : C b * g₀ = g := by
    rw [show g₀ = C b⁻¹ * g by rfl, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hb.ne', C_1, one_mul]
  rw [hp_norm, hg_norm] at hunscaled
  exact hunscaled.toInterlaces (by rw [hpdeg, hgdeg])

/-- The regularized derivative-minus-interlacer pair has simple right roots
and hence interlaces before taking the limit. -/
private theorem iterateTDeriv_derivative_sub_ratio_interlaces {p g : ℝ[X]}
    (hpg : StrictInterl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    (hpdeg : 1 ≤ p.natDegree) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    let P := iterateTDeriv (-epsilon) g.natDegree p
    let G := iterateTDeriv (-epsilon) g.natDegree g
    Interlaces
      (G.derivative - C (g.leadingCoeff / p.leadingCoeff) * P) G := by
  dsimp only
  let P := iterateTDeriv (-epsilon) g.natDegree p
  let G := iterateTDeriv (-epsilon) g.natDegree g
  have hPdeg : P.natDegree = p.natDegree := by simp [P]
  have hGdeg : G.natDegree = g.natDegree := by simp [G]
  have hPlc : P.leadingCoeff = p.leadingCoeff := by simp [P]
  have hGlc : G.leadingCoeff = g.leadingCoeff := by simp [G]
  have hPpos : HasPosLeadingCoeff P := by
    simpa [HasPosLeadingCoeff, hPlc] using hp_pos
  have hGpos : HasPosLeadingCoeff G := by
    simpa [HasPosLeadingCoeff, hGlc] using hg_pos
  have hPGdeg : G.natDegree = P.natDegree + 1 := by rw [hPdeg, hGdeg, hdeg]
  have hpair : StrictInterl P G :=
    hpg.iterateTDeriv_common (-epsilon) g.natDegree
  have hsimple : HasSimpleRoots G :=
    hasSimpleRoots_iterateTDeriv_neg_of_natDegree_le
      hepsilon hpg.2.1.1 hpg.2.1.2 (by rfl)
  have hinter : Interl
      (G.derivative - C (g.leadingCoeff / p.leadingCoeff) * P) G := by
    simpa [hGlc, hPlc] using
      derivative_sub_leadingCoeffRatio_interl_of_simple
        hpair hPGdeg hPpos hGpos hsimple
  have hdata :
      (G.derivative - C (g.leadingCoeff / p.leadingCoeff) * P).natDegree =
          P.natDegree ∧
        (G.derivative - C (g.leadingCoeff / p.leadingCoeff) * P).leadingCoeff =
          (P.natDegree : ℝ) * G.leadingCoeff := by
    simpa [hGlc, hPlc] using
      derivative_sub_leadingCoeffRatio_degree_leadingCoeff
        hPGdeg hPpos hGpos (by simpa [hPdeg] using hpdeg)
  have hleft0 : G.derivative - C (g.leadingCoeff / p.leadingCoeff) * P ≠ 0 := by
    apply leadingCoeff_ne_zero.mp
    rw [hdata.2]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by lia)) hGpos.ne'
  exact (hinter.toStrictInterl_of_ne hleft0 hGpos.ne_zero).toInterlaces
    (by rw [hdata.1, hGdeg, hdeg, hPdeg])

/-- In the constant-left case the derivative-minus-interlacer polynomial
vanishes identically. -/
private theorem derivative_sub_leadingCoeffRatio_eq_zero_of_natDegree_eq_zero
    {p g : ℝ[X]} (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hpdeg : p.natDegree = 0) :
    g.derivative - C (g.leadingCoeff / p.leadingCoeff) * p = 0 := by
  have hgdeg : g.natDegree = 1 := by lia
  have hpC : p = C p.leadingCoeff := by
    have hpC' := eq_C_of_natDegree_eq_zero hpdeg
    simpa [leadingCoeff, hpdeg] using hpC'
  have hgder : g.derivative = C g.leadingCoeff := by
    ext n
    cases n with
    | zero =>
        simp only [coeff_derivative, coeff_C_zero]
        rw [show g.coeff 1 = g.leadingCoeff by rw [leadingCoeff, hgdeg]]
        norm_num
    | succ n =>
        rw [coeff_derivative, coeff_C]
        have hzero : g.coeff (n + 1 + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hgdeg]; lia)
        rw [hzero]
        simp
  have hscaled : C (g.leadingCoeff / p.leadingCoeff) * p =
      C g.leadingCoeff := by
    calc
      C (g.leadingCoeff / p.leadingCoeff) * p =
          C (g.leadingCoeff / p.leadingCoeff) * C p.leadingCoeff := by
            exact congrArg
              (fun q : ℝ[X] ↦ C (g.leadingCoeff / p.leadingCoeff) * q) hpC
      _ = C ((g.leadingCoeff / p.leadingCoeff) * p.leadingCoeff) := by rw [C_mul]
      _ = C g.leadingCoeff := by
        congr 1
        field_simp [hp_pos.ne']
  rw [hgder, hscaled, sub_self]

/-- The derivative-minus-interlacer conclusion for a nonconstant left
polynomial, obtained by common regularization and coefficientwise closure. -/
private theorem derivative_sub_leadingCoeffRatio_interl_of_natDegree_ne_zero
    {p g : ℝ[X]} (hpg : StrictInterl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    (hpdeg0 : p.natDegree ≠ 0) :
    Interl (g.derivative - C (g.leadingCoeff / p.leadingCoeff) * p) g := by
  have hpdeg : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hpdeg0
  let beta : ℝ := g.leadingCoeff / p.leadingCoeff
  let lead : ℝ := (p.natDegree : ℝ) * g.leadingCoeff
  let delta : ℕ → ℝ := fun M ↦ ((M : ℝ) + 1)⁻¹
  let P : ℕ → ℝ[X] := fun M ↦ iterateTDeriv (-(delta M)) g.natDegree p
  let G : ℕ → ℝ[X] := fun M ↦ iterateTDeriv (-(delta M)) g.natDegree g
  let H : ℕ → ℝ[X] := fun M ↦ (G M).derivative - C beta * P M
  let H₀ : ℝ[X] := g.derivative - C beta * p
  have hlead_pos : 0 < lead := by
    exact mul_pos (Nat.cast_pos.mpr hpdeg) hg_pos
  have hdelta_pos (M : ℕ) : 0 < delta M := by positivity
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simpa [delta, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hneg_delta : Tendsto (fun M ↦ -(delta M)) atTop (nhds 0) := by
    simpa using hdelta.neg
  have hPdeg (M : ℕ) : (P M).natDegree = p.natDegree := by simp [P]
  have hGdeg (M : ℕ) : (G M).natDegree = p.natDegree + 1 := by
    simp [G, hdeg]
  have hPlc (M : ℕ) : (P M).leadingCoeff = p.leadingCoeff := by simp [P]
  have hGlc (M : ℕ) : (G M).leadingCoeff = g.leadingCoeff := by simp [G]
  have hHdata (M : ℕ) :
      (H M).natDegree = p.natDegree ∧ (H M).leadingCoeff = lead := by
    simpa [H, P, G, beta, lead] using
      derivative_sub_leadingCoeffRatio_degree_leadingCoeff
        (show (G M).natDegree = (P M).natDegree + 1 by rw [hPdeg, hGdeg])
        (show HasPosLeadingCoeff (P M) by simpa [HasPosLeadingCoeff, hPlc M])
        (show HasPosLeadingCoeff (G M) by simpa [HasPosLeadingCoeff, hGlc M])
        (by simpa [hPdeg M] using hpdeg)
  have hH₀data : H₀.natDegree = p.natDegree ∧ H₀.leadingCoeff = lead := by
    simpa [H₀, beta, lead] using
      derivative_sub_leadingCoeffRatio_degree_leadingCoeff hdeg hp_pos hg_pos hpdeg
  have hinter (M : ℕ) : Interlaces (H M) (G M) := by
    simpa [H, P, G, beta] using
      iterateTDeriv_derivative_sub_ratio_interlaces
        hpg hdeg hp_pos hg_pos hpdeg (hdelta_pos M)
  have hPcoeff (i : ℕ) : Tendsto (fun M ↦ (P M).coeff i) atTop
      (nhds (p.coeff i)) := by
    simpa [P, Function.comp_def] using
      (continuousAt_coeff_iterateTDeriv_zero g.natDegree p i).tendsto.comp hneg_delta
  have hGcoeff (i : ℕ) : Tendsto (fun M ↦ (G M).coeff i) atTop
      (nhds (g.coeff i)) := by
    simpa [G, Function.comp_def] using
      (continuousAt_coeff_iterateTDeriv_zero g.natDegree g i).tendsto.comp hneg_delta
  have hHcoeff (i : ℕ) : Tendsto (fun M ↦ (H M).coeff i) atTop
      (nhds (H₀.coeff i)) := by
    simp only [H, H₀, coeff_sub, coeff_derivative, coeff_C_mul]
    exact (((hGcoeff (i + 1)).mul tendsto_const_nhds).sub
      (tendsto_const_nhds.mul (hPcoeff i)))
  exact (interlaces_of_fixed_leadingCoeff_of_coeff_tendsto
    hlead_pos hg_pos (fun M ↦ (hHdata M).2) hGlc hH₀data.2 rfl
    (fun M ↦ (hHdata M).1) hGdeg hH₀data.1 hdeg hinter hHcoeff hGcoeff).toStrictInterl.toInterl

/-- The derivative-minus-interlacer lemma, including repeated roots and the
zero output in degree one. -/
theorem derivative_sub_leadingCoeffRatio_interl_of_strictInterl {p g : ℝ[X]}
    (hpg : StrictInterl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g) :
    Interl (g.derivative - C (g.leadingCoeff / p.leadingCoeff) * p) g := by
  by_cases hpdeg0 : p.natDegree = 0
  · rw [derivative_sub_leadingCoeffRatio_eq_zero_of_natDegree_eq_zero
      hdeg hp_pos hpdeg0]
    exact interl_zero_left g
  · exact derivative_sub_leadingCoeffRatio_interl_of_natDegree_ne_zero
      hpg hdeg hp_pos hg_pos hpdeg0


/-- If a positive-leading polynomial is in weak proper position below a
successor-degree positive-leading polynomial, subtracting the leading-
coefficient-ratio multiple from the derivative preserves weak proper position.
Repeated roots are allowed, and the left result may be zero. -/
theorem derivative_sub_leadingCoeffRatio_smul_interl {p g : ℝ[X]}
    (hpg : Interl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g) :
    Interl
      (g.derivative - (g.leadingCoeff / p.leadingCoeff) • p) g := by
  have hstrict : StrictInterl p g :=
    hpg.toStrictInterl_of_ne hp_pos.ne_zero hg_pos.ne_zero
  simpa [Polynomial.smul_eq_C_mul] using
    derivative_sub_leadingCoeffRatio_interl_of_strictInterl
      hstrict hdeg hp_pos hg_pos

/-- A derivative-plus-lag combination remains below the same right
interlacer once its lag coefficient is at least the sharp negative endpoint.
This is the nonconstant-left common-interlacer wrapper. -/
private theorem derivative_add_lag_interl_of_leadingCoeffRatio_of_natDegree_ne_zero
    {p g : ℝ[X]}
    (hpg : Interl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    (hpdeg0 : p.natDegree ≠ 0) {q lambda : ℝ}
    (hq : 0 ≤ q)
    (hlambda : -(g.leadingCoeff / p.leadingCoeff) * q ≤ lambda) :
    Interl (q • g.derivative + lambda • p) g := by
  have hpdeg : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hpdeg0
  let beta : ℝ := g.leadingCoeff / p.leadingCoeff
  let h : ℝ[X] := g.derivative - C beta * p
  let mu : ℝ := lambda + beta * q
  have hmu : 0 ≤ mu := by
    dsimp [mu, beta]
    linarith
  by_cases hq0 : q = 0
  · subst q
    have hlambda_nonneg : 0 ≤ lambda := by simpa using hlambda
    simpa [Polynomial.smul_eq_C_mul] using
      Interl.C_mul_left_of_nonneg hpg hlambda_nonneg
  · have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hh : Interl h g := by
      simpa [h, beta, Polynomial.smul_eq_C_mul] using
        derivative_sub_leadingCoeffRatio_smul_interl
          hpg hdeg hp_pos hg_pos
    have hhdata : h.natDegree = p.natDegree ∧
        h.leadingCoeff = (p.natDegree : ℝ) * g.leadingCoeff := by
      simpa [h, beta] using
        derivative_sub_leadingCoeffRatio_degree_leadingCoeff
          hdeg hp_pos hg_pos hpdeg
    have hh_pos : HasPosLeadingCoeff h := by
      rw [HasPosLeadingCoeff, hhdata.2]
      exact mul_pos (Nat.cast_pos.mpr hpdeg) hg_pos
    have hh_strict : StrictInterl h g :=
      hh.toStrictInterl_of_ne hh_pos.ne_zero hg_pos.ne_zero
    have hp_strict : StrictInterl p g :=
      hpg.toStrictInterl_of_ne hp_pos.ne_zero hg_pos.ne_zero
    have hsum : StrictInterl (weightedSum [(q, h), (mu, p)]) g := by
      apply StrictInterl.weightedSum_right_of_nonneg
      · simp [hq, hmu]
      · simp [hh_strict, hp_strict]
      · simp [hh_pos, hp_pos]
      · exact ⟨(q, h), by simp, hq_pos⟩
    have hid : weightedSum [(q, h), (mu, p)] =
        C q * g.derivative + C lambda * p := by
      simp only [weightedSum_cons, weightedSum_nil, add_zero]
      dsimp [h, mu, beta]
      simp only [map_add, map_mul]
      ring
    rw [hid] at hsum
    simpa [Polynomial.smul_eq_C_mul] using hsum.toInterl

/-- A derivative-plus-lag combination remains below the same right
interlacer once its lag coefficient is at least the sharp negative endpoint.
This includes a constant left polynomial and a possibly zero result. -/
theorem derivative_add_lag_interl_of_leadingCoeffRatio {p g : ℝ[X]}
    (hpg : Interl p g)
    (hdeg : g.natDegree = p.natDegree + 1)
    (hp_pos : HasPosLeadingCoeff p) (hg_pos : HasPosLeadingCoeff g)
    {q lambda : ℝ} (hq : 0 ≤ q)
    (hlambda : -(g.leadingCoeff / p.leadingCoeff) * q ≤ lambda) :
    Interl (q • g.derivative + lambda • p) g := by
  by_cases hpdeg0 : p.natDegree = 0
  · have hgdeg : g.natDegree = 1 := by lia
    have hpC : p = C p.leadingCoeff := by
      have hpC' := eq_C_of_natDegree_eq_zero hpdeg0
      simpa [leadingCoeff, hpdeg0] using hpC'
    have hgder : g.derivative = C g.leadingCoeff := by
      ext n
      cases n with
      | zero =>
          simp only [coeff_derivative, coeff_C_zero]
          rw [show g.coeff 1 = g.leadingCoeff by rw [leadingCoeff, hgdeg]]
          norm_num
      | succ n =>
          rw [coeff_derivative, coeff_C]
          have hzero : g.coeff (n + 1 + 1) = 0 :=
            coeff_eq_zero_of_natDegree_lt (by rw [hgdeg]; lia)
          rw [hzero]
          simp
    have hqder : q • g.derivative = C (q * g.leadingCoeff) := by
      calc
        q • g.derivative = q • C g.leadingCoeff := congrArg (q • ·) hgder
        _ = C (q * g.leadingCoeff) := by
          rw [Polynomial.smul_eq_C_mul, ← C_mul]
    have hlp : lambda • p = C (lambda * p.leadingCoeff) := by
      calc
        lambda • p = lambda • C p.leadingCoeff := congrArg (lambda • ·) hpC
        _ = C (lambda * p.leadingCoeff) := by
          rw [Polynomial.smul_eq_C_mul, ← C_mul]
    have hform : q • g.derivative + lambda • p =
        C (q * g.leadingCoeff + lambda * p.leadingCoeff) := by
      rw [hqder, hlp, ← C_add]
    rw [hform]
    by_cases hcoeff : q * g.leadingCoeff + lambda * p.leadingCoeff = 0
    · left
      simp [hcoeff]
    · exact (interlaces_C_linear hcoeff hgdeg).toStrictInterl.toInterl
  · exact derivative_add_lag_interl_of_leadingCoeffRatio_of_natDegree_ne_zero
      hpg hdeg hp_pos hg_pos hpdeg0 hq hlambda


end RealRooted
