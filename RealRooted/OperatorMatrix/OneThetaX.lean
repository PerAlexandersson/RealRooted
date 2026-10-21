import RealRooted.OperatorMatrix.MixedLemma
import RealRooted.OperatorMatrix.LocalToGlobal
import RealRooted.QuadraticRoot

/-!
# Two-by-two operator matrices over `{1, θ, X}`

A two-by-two block of operators from the alphabet `{1, θ, X}` (with `θ = X d/dX`) preserves
ordered PF pairs if and only if it is one of thirteen blocks
(`preservesOrderedPFPair_iff_isAllowedBlock`).  With the local-to-global theorem this
classifies rectangular matrices (`preservesOrderedPF_letters_iff`).  Necessity uses explicit
counterexamples; the block `(θ, 1) / (θ, θ)` uses the mixed differential lemma
`p' + q' ≤ q + X p'`.
-/

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- The three entries in the `{1, θ, X}` alphabet. -/
inductive Letter where
  | one
  | theta
  | x
  deriving DecidableEq, Repr

/-- The real-linear polynomial operator represented by a letter. -/
def Letter.linearMap : Letter → ℝ[X] →ₗ[ℝ] ℝ[X]
  | .one => LinearMap.id
  | .theta => (LinearMap.mulLeft ℝ X).comp Polynomial.derivative
  | .x => LinearMap.mulLeft ℝ X

/-- The letter `1` acts as the identity. -/
@[simp]
theorem Letter.linearMap_one (p : ℝ[X]) : Letter.one.linearMap p = p := rfl

/-- The letter `θ` acts by the Euler derivative. -/
@[simp]
theorem Letter.linearMap_theta (p : ℝ[X]) :
    Letter.theta.linearMap p = RealRooted.theta p := rfl

/-- The letter `X` acts by multiplication by `X`. -/
@[simp]
theorem Letter.linearMap_x (p : ℝ[X]) : Letter.x.linearMap p = X * p := rfl

/-- The allowed blocks are `(1,1)/(1,1)`, `(1,1)/(θ,θ)`, `(1,1)/(X,1)`,
`(1,1)/(X,X)`, `(θ,1)/(θ,1)`, `(θ,1)/(θ,θ)`, `(θ,1)/(X,θ)`,
`(θ,θ)/(θ,θ)`, `(θ,θ)/(X,X)`, `(X,1)/(X,1)`, `(X,1)/(X,X)`,
`(X,θ)/(X,θ)`, and `(X,X)/(X,X)`. -/
def Letter.IsAllowedBlock : Letter → Letter → Letter → Letter → Prop
  | .one, .one, .one, .one => True
  | .one, .one, .theta, .theta => True
  | .one, .one, .x, .one => True
  | .one, .one, .x, .x => True
  | .theta, .one, .theta, .one => True
  | .theta, .one, .theta, .theta => True
  | .theta, .one, .x, .theta => True
  | .theta, .theta, .theta, .theta => True
  | .theta, .theta, .x, .x => True
  | .x, .one, .x, .one => True
  | .x, .one, .x, .x => True
  | .x, .theta, .x, .theta => True
  | .x, .x, .x, .x => True
  | _, _, _, _ => False

/-- Membership in the thirteen allowed blocks is decidable. -/
instance Letter.instDecidableIsAllowedBlock (a b c d : Letter) :
    Decidable (a.IsAllowedBlock b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [Letter.IsAllowedBlock] <;> infer_instance

private theorem ne_zero_of_eval_one_ne {p : ℝ[X]} (h : p.eval 1 ≠ 0) : p ≠ 0 := by
  rintro rfl
  exact h (by simp)

private theorem interl_P_Q :
    Interl (X + 1 : ℝ[X]) (X * (X + 1)) := by
  simpa using (interl_iff_interl_X_mul isPFPolynomial_X_add_one
    isPFPolynomial_X_add_one).mp isPFPolynomial_X_add_one.interl_self

private theorem not_interl_of_sorted_roots {f g : ℝ[X]} {leftRoots rightRoots : List ℝ}
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hleftSort : leftRoots.Pairwise (· ≤ ·))
    (hrightSort : rightRoots.Pairwise (· ≤ ·))
    (hleftRoots : f.roots = ↑leftRoots)
    (hrightRoots : g.roots = ↑rightRoots)
    (hshape : ¬ (leftRoots.length + 1 = rightRoots.length ∧
      ListInterlaces leftRoots rightRoots ∨
        leftRoots.length = rightRoots.length ∧ ListAlternates leftRoots rightRoots)) :
    ¬ Interl f g := by
  rintro (hleft | hright | hstrict)
  · exact hf hleft
  · exact hg hright
  rcases hstrict with ⟨_, _, left, right, hleftSort', hrightSort', hleftEq, hrightEq, hshape'⟩
  have hleftList : left = leftRoots := by
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
      hleftSort' hleftSort (Multiset.coe_eq_coe.mp (hleftEq.trans hleftRoots))
  have hrightList : right = rightRoots := by
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
      hrightSort' hrightSort (Multiset.coe_eq_coe.mp (hrightEq.trans hrightRoots))
  exact hshape (hleftList ▸ hrightList ▸ hshape')

private theorem roots_square_P :
    ((X + 1 : ℝ[X]) ^ 2).roots = ↑([-1, -1] : List ℝ) := by
  rw [Polynomial.roots_pow]
  change 2 • (X + C 1 : ℝ[X]).roots = _
  rw [Polynomial.roots_X_add_C]
  rfl

private theorem roots_X_mul_X_add_two :
    (X * (X + 2) : ℝ[X]).roots = ↑([-2, 0] : List ℝ) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero Polynomial.X_ne_zero (ne_zero_of_eval_one_ne (by norm_num))),
    Polynomial.roots_X]
  change {0} + (X + C 2 : ℝ[X]).roots = _
  rw [Polynomial.roots_X_add_C, Multiset.add_comm]
  norm_num
  rfl

private theorem not_interl_square_P_X_mul_X_add_two :
    ¬ Interl ((X + 1 : ℝ[X]) ^ 2) (X * (X + 2)) := by
  exact not_interl_of_sorted_roots (leftRoots := [-1, -1]) (rightRoots := [-2, 0])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_square_P roots_X_mul_X_add_two
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_isPFPolynomial_of_not_splits {p : ℝ[X]}
    (hp0 : p ≠ 0) (hnot : ¬ p.Splits) :
    ¬ IsPFPolynomial p := by
  intro hp
  rcases hp.eq_zero_or_splits with hzero | hsplits
  · exact hp0 hzero
  · exact hnot hsplits

private theorem not_isPFPolynomial_one_add_X_sq :
    ¬ IsPFPolynomial (1 + X ^ 2 : ℝ[X]) := by
  apply not_isPFPolynomial_of_not_splits (ne_zero_of_eval_one_ne (by norm_num))
  convert (quadraticPoly_not_splits_of_discrim_neg one_ne_zero
    (by norm_num [discrim]) :
      ¬ ((C 1 * X ^ 2 + C 0 * X + C 1) : ℝ[X]).Splits) using 1
  norm_num [map_ofNat]
  ring

private theorem not_isPFPolynomial_one_add_two_X_add_two_X_sq :
    ¬ IsPFPolynomial (1 + 2 * X + 2 * X ^ 2 : ℝ[X]) := by
  apply not_isPFPolynomial_of_not_splits (ne_zero_of_eval_one_ne (by norm_num))
  convert (quadraticPoly_not_splits_of_discrim_neg (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num [discrim]) :
      ¬ ((C 2 * X ^ 2 + C 2 * X + C 1) : ℝ[X]).Splits) using 1
  norm_num [map_ofNat]
  ring

private theorem not_isPFPolynomial_X_add_X_sq_add_X_cu :
    ¬ IsPFPolynomial (X + X ^ 2 + X ^ 3 : ℝ[X]) := by
  apply not_isPFPolynomial_of_not_splits (ne_zero_of_eval_one_ne (by norm_num))
  intro hsplits
  have hquadratic : ¬ (X ^ 2 + X + 1 : ℝ[X]).Splits := by
    simpa only [map_one, one_mul] using
      (quadraticPoly_not_splits_of_discrim_neg one_ne_zero (by norm_num [discrim]) :
        ¬ ((C 1 * X ^ 2 + C 1 * X + C 1) : ℝ[X]).Splits)
  apply hquadratic
  have hfactor : X * (X ^ 2 + X + 1 : ℝ[X]) = X + X ^ 2 + X ^ 3 := by ring
  rw [← hfactor] at hsplits
  exact (Polynomial.splits_mul_iff_right Polynomial.X_ne_zero Polynomial.Splits.X).mp hsplits

private theorem interl_one_X : Interl (1 : ℝ[X]) X := by
  simpa only [mul_one] using
    (interl_iff_interl_X_mul IsPFPolynomial.one IsPFPolynomial.one).mp
      IsPFPolynomial.one.interl_self

private theorem not_preservesOrderedPFPair_of_top_row_one_x (c d : Letter) :
    ¬ PreservesOrderedPFPair Letter.one.linearMap Letter.x.linearMap c.linearMap d.linearMap := by
  intro hpreserves
  apply not_isPFPolynomial_one_add_X_sq
  simpa only [Letter.linearMap_one, Letter.linearMap_x, pow_two] using
    (hpreserves 1 X IsPFPolynomial.one isPFPolynomial_X interl_one_X).1

private theorem not_preservesOrderedPFPair_of_top_row_one_theta (c d : Letter) :
    ¬ PreservesOrderedPFPair Letter.one.linearMap Letter.theta.linearMap
      c.linearMap d.linearMap := by
  intro hpreserves
  obtain ⟨hpf, _, _⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_isPFPolynomial_one_add_two_X_add_two_X_sq
  change IsPFPolynomial ((X + 1) + X * (X * (X + 1)).derivative) at hpf
  convert hpf using 1
  simp only [derivative_mul, derivative_X, derivative_add, mul_one, one_mul, mul_add]
  ring

private theorem not_preservesOrderedPFPair_of_top_row_theta_x (c d : Letter) :
    ¬ PreservesOrderedPFPair Letter.theta.linearMap Letter.x.linearMap
      c.linearMap d.linearMap := by
  intro hpreserves
  obtain ⟨hpf, _, _⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_isPFPolynomial_X_add_X_sq_add_X_cu
  change IsPFPolynomial (X * (X + 1).derivative + X * (X * (X + 1))) at hpf
  convert hpf using 1
  simp only [derivative_add, derivative_X, derivative_one, mul_one, add_zero]
  ring

private theorem not_preservesOrderedPFPair_of_bottom_row_one_x (a b : Letter) :
    ¬ PreservesOrderedPFPair a.linearMap b.linearMap Letter.one.linearMap Letter.x.linearMap := by
  intro hpreserves
  apply not_isPFPolynomial_one_add_X_sq
  simpa only [Letter.linearMap_one, Letter.linearMap_x, pow_two] using
    (hpreserves 1 X IsPFPolynomial.one isPFPolynomial_X interl_one_X).2.1

private theorem not_preservesOrderedPFPair_of_bottom_row_one_theta (a b : Letter) :
    ¬ PreservesOrderedPFPair a.linearMap b.linearMap
      Letter.one.linearMap Letter.theta.linearMap := by
  intro hpreserves
  obtain ⟨_, hpf, _⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_isPFPolynomial_one_add_two_X_add_two_X_sq
  change IsPFPolynomial ((X + 1) + X * (X * (X + 1)).derivative) at hpf
  convert hpf using 1
  simp only [derivative_mul, derivative_X, derivative_add, mul_one, one_mul, mul_add]
  ring

private theorem not_preservesOrderedPFPair_of_bottom_row_theta_x (a b : Letter) :
    ¬ PreservesOrderedPFPair a.linearMap b.linearMap
      Letter.theta.linearMap Letter.x.linearMap := by
  intro hpreserves
  obtain ⟨_, hpf, _⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_isPFPolynomial_X_add_X_sq_add_X_cu
  change IsPFPolynomial (X * (X + 1).derivative + X * (X * (X + 1))) at hpf
  convert hpf using 1
  simp only [derivative_add, derivative_X, derivative_one, mul_one, add_zero]
  ring

private theorem roots_P : (X + 1 : ℝ[X]).roots = ↑([-1] : List ℝ) := by
  change (X + C 1 : ℝ[X]).roots = _
  rw [Polynomial.roots_X_add_C]
  norm_num

private theorem roots_X_mul_P : (X * (X + 1) : ℝ[X]).roots = ↑([-1, 0] : List ℝ) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero Polynomial.X_ne_zero (ne_zero_of_eval_one_ne (by norm_num))),
    Polynomial.roots_X]
  change {0} + (X + C 1 : ℝ[X]).roots = _
  rw [Polynomial.roots_X_add_C, Multiset.add_comm]
  norm_num
  rfl

private theorem roots_X : (X : ℝ[X]).roots = ↑([0] : List ℝ) := by
  rw [Polynomial.roots_X]
  rfl

private theorem not_interl_X_X_add_one : ¬ Interl (X : ℝ[X]) (X + 1) := by
  intro hinterl
  have hiff : Interl (X + C 0 : ℝ[X]) (X + C 1) ↔ (1 : ℝ) ≤ 0 :=
    Interl.X_add_C_iff
  apply (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1))
  apply hiff.mp
  simpa only [map_zero, map_one, add_zero] using hinterl

private theorem not_interl_X_mul_P_P : ¬ Interl (X * (X + 1)) (X + 1) := by
  exact not_interl_of_sorted_roots (leftRoots := [-1, 0]) (rightRoots := [-1])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_X_mul_P roots_P
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_interl_X_mul_P_X : ¬ Interl (X * (X + 1)) X := by
  exact not_interl_of_sorted_roots (leftRoots := [-1, 0]) (rightRoots := [0])
    (ne_zero_of_eval_one_ne (by norm_num)) Polynomial.X_ne_zero
    (by norm_num) (by norm_num) roots_X_mul_P roots_X
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_preservesOrderedPFPair_of_left_column_theta_one (b d : Letter) :
    ¬ PreservesOrderedPFPair Letter.theta.linearMap b.linearMap
      Letter.one.linearMap d.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) 0
    isPFPolynomial_X_add_one IsPFPolynomial.zero (interl_zero_right (X + 1))
  apply not_interl_X_X_add_one
  simpa only [Letter.linearMap_theta, Letter.linearMap_one, LinearMap.map_zero,
    add_zero, RealRooted.theta, derivative_add, derivative_X, derivative_one, mul_one]
    using hinterl

private theorem not_preservesOrderedPFPair_of_left_column_x_one (b d : Letter) :
    ¬ PreservesOrderedPFPair Letter.x.linearMap b.linearMap Letter.one.linearMap d.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) 0
    isPFPolynomial_X_add_one IsPFPolynomial.zero (interl_zero_right (X + 1))
  apply not_interl_X_mul_P_P
  simpa only [Letter.linearMap_x, Letter.linearMap_one, LinearMap.map_zero, add_zero]
    using hinterl

private theorem not_preservesOrderedPFPair_of_left_column_x_theta (b d : Letter) :
    ¬ PreservesOrderedPFPair Letter.x.linearMap b.linearMap
      Letter.theta.linearMap d.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) 0
    isPFPolynomial_X_add_one IsPFPolynomial.zero (interl_zero_right (X + 1))
  apply not_interl_X_mul_P_X
  simpa only [Letter.linearMap_x, Letter.linearMap_theta, LinearMap.map_zero,
    add_zero, RealRooted.theta, derivative_add, derivative_X, derivative_one, mul_one]
    using hinterl

private theorem not_preservesOrderedPFPair_of_right_column_theta_one (a c : Letter) :
    ¬ PreservesOrderedPFPair a.linearMap Letter.theta.linearMap
      c.linearMap Letter.one.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves 0 (X + 1)
    IsPFPolynomial.zero isPFPolynomial_X_add_one (interl_zero_left (X + 1))
  apply not_interl_X_X_add_one
  simpa only [Letter.linearMap_theta, Letter.linearMap_one, LinearMap.map_zero,
    zero_add, RealRooted.theta, derivative_add, derivative_X, derivative_one, mul_one, add_zero]
    using hinterl

private theorem not_preservesOrderedPFPair_of_right_column_x_one (a c : Letter) :
    ¬ PreservesOrderedPFPair a.linearMap Letter.x.linearMap c.linearMap Letter.one.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves 0 (X + 1)
    IsPFPolynomial.zero isPFPolynomial_X_add_one (interl_zero_left (X + 1))
  apply not_interl_X_mul_P_P
  simpa only [Letter.linearMap_x, Letter.linearMap_one, LinearMap.map_zero, zero_add]
    using hinterl

private theorem not_preservesOrderedPFPair_of_right_column_x_theta (a c : Letter) :
    ¬ PreservesOrderedPFPair a.linearMap Letter.x.linearMap
      c.linearMap Letter.theta.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves 0 (X + 1)
    IsPFPolynomial.zero isPFPolynomial_X_add_one (interl_zero_left (X + 1))
  apply not_interl_X_mul_P_X
  simpa only [Letter.linearMap_x, Letter.linearMap_theta, LinearMap.map_zero,
    zero_add, RealRooted.theta, derivative_add, derivative_X, derivative_one, mul_one, add_zero]
    using hinterl

/-- The first exceptional Ferrers block in the table does not preserve ordered
PF pairs. -/
private theorem not_preservesOrderedPFPair_one_one_theta_one :
    ¬ PreservesOrderedPFPair Letter.one.linearMap Letter.one.linearMap
      Letter.theta.linearMap Letter.one.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_interl_square_P_X_mul_X_add_two
  change Interl ((X + 1) + X * (X + 1))
    (X * (X + 1).derivative + X * (X + 1)) at hinterl
  convert hinterl using 1
  · ring
  · simp only [derivative_add, derivative_X, derivative_one, mul_one, add_zero]
    ring

private theorem interl_P_P : Interl (X + 1 : ℝ[X]) (X + 1) :=
  Interl.refl fun hne => isPFPolynomial_X_add_one.eq_zero_or_splits.resolve_left hne

private theorem interl_X_add_ten_X_add_eleven_mul_X_add_one :
    Interl (X + 10 : ℝ[X]) ((X + 11) * (X + 1)) := by
  have hp := isPFPolynomial_X_add_C (a := 10) (by norm_num)
  have hq := (isPFPolynomial_X_add_C (a := 11) (by norm_num)).mul
    isPFPolynomial_X_add_one
  have hp0 : (X + 10 : ℝ[X]) ≠ 0 := ne_zero_of_eval_one_ne (by norm_num)
  have hq0 : ((X + 11) * (X + 1) : ℝ[X]) ≠ 0 :=
    ne_zero_of_eval_one_ne (by norm_num)
  have hpRoots : (X + 10 : ℝ[X]).roots = ↑([-10] : List ℝ) := by
    change (X + C 10 : ℝ[X]).roots = _
    rw [Polynomial.roots_X_add_C]
    norm_num
  have hqRoots : ((X + 11) * (X + 1) : ℝ[X]).roots =
      ↑([-11, -1] : List ℝ) := by
    rw [Polynomial.roots_mul hq0]
    change (X + C 11 : ℝ[X]).roots + (X + C 1 : ℝ[X]).roots = _
    rw [Polynomial.roots_X_add_C, Polynomial.roots_X_add_C]
    norm_num
    rfl
  apply StrictInterl.toInterl
  refine ⟨⟨hp0, (hp.ne_zero_and_splits hp0).2⟩,
    ⟨hq0, (hq.ne_zero_and_splits hq0).2⟩, ?_⟩
  refine ⟨[-10], [-11, -1], by norm_num, by norm_num, hpRoots.symm, hqRoots.symm, ?_⟩
  left
  constructor
  · norm_num
  · norm_num [ListInterlaces]

private theorem roots_X_mul_three_X_add_two :
    (X * (3 * X + 2) : ℝ[X]).roots = ↑([-(2 / 3), 0] : List ℝ) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero Polynomial.X_ne_zero (ne_zero_of_eval_one_ne (by norm_num))),
    Polynomial.roots_X]
  change {0} + (C 3 * X + C 2 : ℝ[X]).roots = _
  rw [Polynomial.roots_C_mul_X_add_C 2 (by norm_num), Multiset.add_comm]
  norm_num
  rfl

private theorem roots_two_X_add_one :
    (2 * X + 1 : ℝ[X]).roots = ↑([-(1 / 2)] : List ℝ) := by
  change (C 2 * X + C 1 : ℝ[X]).roots = _
  rw [Polynomial.roots_C_mul_X_add_C 1 (by norm_num)]
  norm_num

private theorem roots_X_mul_square_P :
    (X * (X + 1) ^ 2 : ℝ[X]).roots = ↑([-1, -1, 0] : List ℝ) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero Polynomial.X_ne_zero (pow_ne_zero 2 (ne_zero_of_eval_one_ne (by norm_num)))),
    Polynomial.roots_X, roots_square_P, Multiset.add_comm]
  rfl

private theorem roots_X_mul_two_X_add_thirteen :
    (X * (2 * X + 13) : ℝ[X]).roots = ↑([-(13 / 2), 0] : List ℝ) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero Polynomial.X_ne_zero (ne_zero_of_eval_one_ne (by norm_num))),
    Polynomial.roots_X]
  change {0} + (C 2 * X + C 13 : ℝ[X]).roots = _
  rw [Polynomial.roots_C_mul_X_add_C 13 (by norm_num), Multiset.add_comm]
  norm_num
  rfl

private theorem roots_X_mul_three_X_add_twenty_two :
    (X * (3 * X + 22) : ℝ[X]).roots = ↑([-(22 / 3), 0] : List ℝ) := by
  rw [Polynomial.roots_mul
      (mul_ne_zero Polynomial.X_ne_zero (ne_zero_of_eval_one_ne (by norm_num))),
    Polynomial.roots_X]
  change {0} + (C 3 * X + C 22 : ℝ[X]).roots = _
  rw [Polynomial.roots_C_mul_X_add_C 22 (by norm_num), Multiset.add_comm]
  norm_num
  rfl

private theorem not_interl_square_P_X_mul_three_X_add_two :
    ¬ Interl ((X + 1 : ℝ[X]) ^ 2) (X * (3 * X + 2)) := by
  exact not_interl_of_sorted_roots (leftRoots := [-1, -1])
    (rightRoots := [-(2 / 3), 0])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_square_P roots_X_mul_three_X_add_two
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_interl_two_X_add_one_square_P :
    ¬ Interl (2 * X + 1 : ℝ[X]) ((X + 1) ^ 2) := by
  exact not_interl_of_sorted_roots (leftRoots := [-(1 / 2)])
    (rightRoots := [-1, -1])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_two_X_add_one roots_square_P
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_interl_X_mul_X_add_two_X_mul_square_P :
    ¬ Interl (X * (X + 2) : ℝ[X]) (X * (X + 1) ^ 2) := by
  exact not_interl_of_sorted_roots (leftRoots := [-2, 0])
    (rightRoots := [-1, -1, 0])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_X_mul_X_add_two roots_X_mul_square_P
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_interl_X_mul_three_X_add_two_X_mul_square_P :
    ¬ Interl (X * (3 * X + 2) : ℝ[X]) (X * (X + 1) ^ 2) := by
  exact not_interl_of_sorted_roots (leftRoots := [-(2 / 3), 0])
    (rightRoots := [-1, -1, 0])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_X_mul_three_X_add_two roots_X_mul_square_P
    (by norm_num [ListInterlaces, ListAlternates])

private theorem not_interl_special_outputs :
    ¬ Interl (X * (2 * X + 13) : ℝ[X]) (X * (3 * X + 22)) := by
  exact not_interl_of_sorted_roots (leftRoots := [-(13 / 2), 0])
    (rightRoots := [-(22 / 3), 0])
    (ne_zero_of_eval_one_ne (by norm_num)) (ne_zero_of_eval_one_ne (by norm_num))
    (by norm_num) (by norm_num) roots_X_mul_two_X_add_thirteen
    roots_X_mul_three_X_add_twenty_two (by norm_num [ListInterlaces, ListAlternates])

/-- The exceptional block `(1, 1) / (X, θ)` does not preserve ordered PF pairs. -/
private theorem not_preservesOrderedPFPair_one_one_x_theta :
    ¬ PreservesOrderedPFPair Letter.one.linearMap Letter.one.linearMap
      Letter.x.linearMap Letter.theta.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_interl_square_P_X_mul_three_X_add_two
  change Interl ((X + 1) + X * (X + 1))
    (X * (X + 1) + X * (X * (X + 1)).derivative) at hinterl
  convert hinterl using 1
  · ring
  · simp only [derivative_mul, derivative_X, derivative_add, mul_one, one_mul, mul_add]
    ring

/-- The exceptional block `(θ, 1) / (X, 1)` does not preserve ordered PF pairs. -/
private theorem not_preservesOrderedPFPair_theta_one_x_one :
    ¬ PreservesOrderedPFPair Letter.theta.linearMap Letter.one.linearMap
      Letter.x.linearMap Letter.one.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) (X + 1)
    isPFPolynomial_X_add_one isPFPolynomial_X_add_one interl_P_P
  apply not_interl_two_X_add_one_square_P
  change Interl (X * (X + 1).derivative + (X + 1))
    (X * (X + 1) + (X + 1)) at hinterl
  convert hinterl using 1
  · simp only [derivative_add, derivative_X, derivative_one, mul_one, add_zero]
    ring
  · ring

/-- The exceptional block `(θ, 1) / (X, X)` does not preserve ordered PF pairs. -/
private theorem not_preservesOrderedPFPair_theta_one_x_x :
    ¬ PreservesOrderedPFPair Letter.theta.linearMap Letter.one.linearMap
      Letter.x.linearMap Letter.x.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_interl_X_mul_X_add_two_X_mul_square_P
  change Interl (X * (X + 1).derivative + X * (X + 1))
    (X * (X + 1) + X * (X * (X + 1))) at hinterl
  convert hinterl using 1
  · simp only [derivative_add, derivative_X, derivative_one, mul_one, add_zero]
    ring
  · ring

/-- The exceptional block `(X, 1) / (X, θ)` does not preserve ordered PF pairs. -/
private theorem not_preservesOrderedPFPair_x_one_x_theta :
    ¬ PreservesOrderedPFPair Letter.x.linearMap Letter.one.linearMap
      Letter.x.linearMap Letter.theta.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) (X + 1)
    isPFPolynomial_X_add_one isPFPolynomial_X_add_one interl_P_P
  apply not_interl_square_P_X_mul_X_add_two
  change Interl (X * (X + 1) + (X + 1))
    (X * (X + 1) + X * (X + 1).derivative) at hinterl
  convert hinterl using 1
  · ring
  · simp only [derivative_add, derivative_X, derivative_one, mul_one, add_zero]
    ring

/-- The exceptional block `(X, θ) / (X, X)` does not preserve ordered PF pairs. -/
private theorem not_preservesOrderedPFPair_x_theta_x_x :
    ¬ PreservesOrderedPFPair Letter.x.linearMap Letter.theta.linearMap
      Letter.x.linearMap Letter.x.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 1) (X * (X + 1))
    isPFPolynomial_X_add_one
    (IsPFPolynomial.X_mul isPFPolynomial_X_add_one)
    interl_P_Q
  apply not_interl_X_mul_three_X_add_two_X_mul_square_P
  change Interl (X * (X + 1) + X * (X * (X + 1)).derivative)
    (X * (X + 1) + X * (X * (X + 1))) at hinterl
  convert hinterl using 1
  · simp only [derivative_mul, derivative_X, derivative_add, mul_one, one_mul, mul_add]
    ring
  · ring

/-- The exceptional block `(θ, θ) / (X, θ)` does not preserve ordered PF pairs. -/
private theorem not_preservesOrderedPFPair_theta_theta_x_theta :
    ¬ PreservesOrderedPFPair Letter.theta.linearMap Letter.theta.linearMap
      Letter.x.linearMap Letter.theta.linearMap := by
  intro hpreserves
  obtain ⟨_, _, hinterl⟩ := hpreserves (X + 10) ((X + 11) * (X + 1))
    (isPFPolynomial_X_add_C (by norm_num))
    ((isPFPolynomial_X_add_C (by norm_num)).mul isPFPolynomial_X_add_one)
    interl_X_add_ten_X_add_eleven_mul_X_add_one
  apply not_interl_special_outputs
  change Interl (X * (X + 10).derivative + X * ((X + 11) * (X + 1)).derivative)
    (X * (X + 10) + X * ((X + 11) * (X + 1)).derivative) at hinterl
  convert hinterl using 1
  · simp only [derivative_mul, derivative_X, derivative_add, derivative_ofNat,
      mul_one, one_mul, add_zero, mul_add]
    ring
  · simp only [derivative_mul, derivative_X, derivative_add, derivative_ofNat,
      mul_one, one_mul, add_zero, mul_add]
    ring

/-- Every letter block outside the thirteen classified blocks fails to preserve
ordered PF pairs. -/
theorem not_preservesOrderedPFPair_of_not_isAllowedBlock (a b c d : Letter)
    (h : ¬ Letter.IsAllowedBlock a b c d) :
    ¬ PreservesOrderedPFPair a.linearMap b.linearMap c.linearMap d.linearMap := by
  cases a <;> cases b
  · cases c <;> cases d
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_of_bottom_row_one_theta _ _
    · exact not_preservesOrderedPFPair_of_bottom_row_one_x _ _
    · exact not_preservesOrderedPFPair_one_one_theta_one
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_of_bottom_row_theta_x _ _
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_one_one_x_theta
    · exact (h trivial).elim
  · exact not_preservesOrderedPFPair_of_top_row_one_theta c d
  · exact not_preservesOrderedPFPair_of_top_row_one_x c d
  · cases c <;> cases d
    · exact not_preservesOrderedPFPair_of_left_column_theta_one _ _
    · exact not_preservesOrderedPFPair_of_bottom_row_one_theta _ _
    · exact not_preservesOrderedPFPair_of_bottom_row_one_x _ _
    · exact (h trivial).elim
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_of_bottom_row_theta_x _ _
    · exact not_preservesOrderedPFPair_theta_one_x_one
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_theta_one_x_x
  · cases c <;> cases d
    · exact not_preservesOrderedPFPair_of_left_column_theta_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_theta_one _ _
    · exact not_preservesOrderedPFPair_of_bottom_row_one_x _ _
    · exact not_preservesOrderedPFPair_of_right_column_theta_one _ _
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_of_bottom_row_theta_x _ _
    · exact not_preservesOrderedPFPair_of_right_column_theta_one _ _
    · exact not_preservesOrderedPFPair_theta_theta_x_theta
    · exact (h trivial).elim
  · exact not_preservesOrderedPFPair_of_top_row_theta_x c d
  · cases c <;> cases d
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_x_one_x_theta
    · exact (h trivial).elim
  · cases c <;> cases d
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_right_column_theta_one _ _
    · exact (h trivial).elim
    · exact not_preservesOrderedPFPair_x_theta_x_x
  · cases c <;> cases d
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_left_column_x_theta _ _
    · exact not_preservesOrderedPFPair_of_right_column_x_one _ _
    · exact not_preservesOrderedPFPair_of_right_column_x_theta _ _
    · exact (h trivial).elim

private theorem isPFPolynomial_theta_add_right
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    IsPFPolynomial (RealRooted.theta p + q) := by
  by_cases hp0 : p = 0
  · simpa [hp0, RealRooted.theta] using hq
  have htheta := theta_preserves_pf hp
  have hnonneg : HasNonnegCoeffs (RealRooted.theta p + q) :=
    htheta.hasNonnegCoeffs.add hq.hasNonnegCoeffs
  have hinterl : Interl p (RealRooted.theta p + q) :=
    interl_add_right_of_common_left_of_nonneg hp.interl_theta hpq
      htheta.hasNonnegCoeffs hq.hasNonnegCoeffs
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnonneg
  by_cases hzero : RealRooted.theta p + q = 0
  · exact Or.inl hzero
  · exact Or.inr (hinterl.toStrictInterl_of_ne hp0 hzero).2.1.2

private theorem isPFPolynomial_add_derivative_of_interl
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    IsPFPolynomial (p + q.derivative) := by
  by_cases hq0 : q = 0
  · simpa [hq0] using hp
  have hqder := hq.derivative
  have hnonneg : HasNonnegCoeffs (p + q.derivative) :=
    hp.hasNonnegCoeffs.add hqder.hasNonnegCoeffs
  have hinterl : Interl (p + q.derivative) q :=
    interl_add_left_of_common_right_of_nonneg hpq hq.interl_derivative_self
      hp.hasNonnegCoeffs hqder.hasNonnegCoeffs
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hnonneg
  by_cases hzero : p + q.derivative = 0
  · exact Or.inl hzero
  · exact Or.inr (hinterl.toStrictInterl_of_ne hzero hq0).1.2

private theorem isPFPolynomial_X_mul_add_right
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    IsPFPolynomial (X * p + q) := by
  have hqp : Interl q (X * p) := (interl_iff_interl_X_mul hp hq).mp hpq
  simpa only [add_comm] using hq.add_of_interl hp.X_mul hqp

private theorem interl_add_add_X_mul_add
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    Interl (p + q) (X * p + q) := by
  have hpXp : Interl p (X * p) :=
    (interl_iff_interl_X_mul hp hp).mp hp.interl_self
  have hqXp : Interl q (X * p) := (interl_iff_interl_X_mul hp hq).mp hpq
  have hpout : Interl p (X * p + q) :=
    interl_add_right_of_common_left_of_nonneg hpXp hpq hp.X_mul.hasNonnegCoeffs
      hq.hasNonnegCoeffs
  have hqout : Interl q (X * p + q) :=
    interl_add_right_of_common_left_of_nonneg hqXp hq.interl_self
      hp.X_mul.hasNonnegCoeffs hq.hasNonnegCoeffs
  exact interl_add_left_of_common_right_of_nonneg hpout hqout
    hp.hasNonnegCoeffs hq.hasNonnegCoeffs

private theorem interl_X_mul_add_X_mul_add_X_mul
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    Interl (X * p + q) (X * p + X * q) := by
  have hXpXq : Interl (X * p) (X * q) := hpq.mul_X_both
  have hqXp : Interl q (X * p) := (interl_iff_interl_X_mul hp hq).mp hpq
  have hqXq : Interl q (X * q) :=
    (interl_iff_interl_X_mul hq hq).mp hq.interl_self
  have hXpout : Interl (X * p) (X * p + X * q) :=
    interl_add_right_of_common_left_of_nonneg hp.X_mul.interl_self hXpXq
      hp.X_mul.hasNonnegCoeffs hq.X_mul.hasNonnegCoeffs
  have hqout : Interl q (X * p + X * q) :=
    interl_add_right_of_common_left_of_nonneg hqXp hqXq
      hp.X_mul.hasNonnegCoeffs hq.X_mul.hasNonnegCoeffs
  exact interl_add_left_of_common_right_of_nonneg hXpout hqout
    hp.X_mul.hasNonnegCoeffs hq.hasNonnegCoeffs

private theorem interl_theta_add_X_mul_add_theta
    {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) :
    Interl (RealRooted.theta p + q) (X * p + RealRooted.theta q) := by
  have hthetaP_Xp : Interl (RealRooted.theta p) (X * p) := hp.interl_theta_X_mul
  have hthetaP_thetaQ : Interl (RealRooted.theta p) (RealRooted.theta q) :=
    hpq.theta
  have hqXp : Interl q (X * p) := (interl_iff_interl_X_mul hp hq).mp hpq
  have hqthetaQ : Interl q (RealRooted.theta q) := hq.interl_theta
  have hthetaP_out : Interl (RealRooted.theta p) (X * p + RealRooted.theta q) :=
    interl_add_right_of_common_left_of_nonneg hthetaP_Xp hthetaP_thetaQ
      hp.X_mul.hasNonnegCoeffs (theta_preserves_pf hq).hasNonnegCoeffs
  have hqout : Interl q (X * p + RealRooted.theta q) :=
    interl_add_right_of_common_left_of_nonneg hqXp hqthetaQ
      hp.X_mul.hasNonnegCoeffs (theta_preserves_pf hq).hasNonnegCoeffs
  exact interl_add_left_of_common_right_of_nonneg hthetaP_out hqout
    (theta_preserves_pf hp).hasNonnegCoeffs hq.hasNonnegCoeffs

/-- The constant block `(1,1)/(1,1)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_one_one_one_one :
    PreservesOrderedPFPair
      Letter.one.linearMap Letter.one.linearMap Letter.one.linearMap Letter.one.linearMap := by
  intro p q hp hq hpq
  have hsum := hp.add_of_interl hq hpq
  simpa only [Letter.linearMap_one] using
    And.intro hsum (And.intro hsum hsum.interl_self)

/-- The staircase block `(1,1)/(X,1)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_one_one_x_one :
    PreservesOrderedPFPair
      Letter.one.linearMap Letter.one.linearMap Letter.x.linearMap Letter.one.linearMap := by
  intro p q hp hq hpq
  exact ⟨by simpa only [Letter.linearMap_one] using hp.add_of_interl hq hpq,
    by simpa only [Letter.linearMap_x, Letter.linearMap_one] using
      isPFPolynomial_X_mul_add_right hp hq hpq,
    by simpa only [Letter.linearMap_x, Letter.linearMap_one] using
      interl_add_add_X_mul_add hp hq hpq⟩

/-- The staircase block `(1,1)/(X,X)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_one_one_x_x :
    PreservesOrderedPFPair
      Letter.one.linearMap Letter.one.linearMap Letter.x.linearMap Letter.x.linearMap := by
  intro p q hp hq hpq
  have hsum := hp.add_of_interl hq hpq
  have hXsum := hsum.X_mul
  have hinterl : Interl (p + q) (X * (p + q)) :=
    (interl_iff_interl_X_mul hsum hsum).mp hsum.interl_self
  refine ⟨by simpa only [Letter.linearMap_one] using hsum, ?_, ?_⟩
  · simpa only [Letter.linearMap_x, mul_add] using hXsum
  · simpa only [Letter.linearMap_x, Letter.linearMap_one, mul_add] using hinterl

/-- The staircase block `(X,1)/(X,1)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_x_one_x_one :
    PreservesOrderedPFPair
      Letter.x.linearMap Letter.one.linearMap Letter.x.linearMap Letter.one.linearMap := by
  intro p q hp hq hpq
  have hsum := isPFPolynomial_X_mul_add_right hp hq hpq
  simpa only [Letter.linearMap_x, Letter.linearMap_one] using
    And.intro hsum (And.intro hsum hsum.interl_self)

/-- The staircase block `(X,1)/(X,X)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_x_one_x_x :
    PreservesOrderedPFPair
      Letter.x.linearMap Letter.one.linearMap Letter.x.linearMap Letter.x.linearMap := by
  intro p q hp hq hpq
  have hsum := hp.add_of_interl hq hpq
  refine ⟨by simpa only [Letter.linearMap_x, Letter.linearMap_one] using
      isPFPolynomial_X_mul_add_right hp hq hpq,
    by simpa only [Letter.linearMap_x, mul_add] using hsum.X_mul, ?_⟩
  simpa only [Letter.linearMap_x, Letter.linearMap_one, mul_add] using
    interl_X_mul_add_X_mul_add_X_mul hp hq hpq

/-- The staircase block `(X,X)/(X,X)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_x_x_x_x :
    PreservesOrderedPFPair
      Letter.x.linearMap Letter.x.linearMap Letter.x.linearMap Letter.x.linearMap := by
  intro p q hp hq hpq
  have hsum := (hp.add_of_interl hq hpq).X_mul
  simpa only [Letter.linearMap_x, ← mul_add] using
    And.intro hsum (And.intro hsum hsum.interl_self)

/-- The block `(1,1)/(θ,θ)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_one_one_theta_theta :
    PreservesOrderedPFPair
      Letter.one.linearMap Letter.one.linearMap Letter.theta.linearMap Letter.theta.linearMap := by
  intro p q hp hq hpq
  have hsum := hp.add_of_interl hq hpq
  have htheta := theta_preserves_pf hsum
  have hinterl := hsum.interl_theta
  refine ⟨by simpa only [Letter.linearMap_one] using hsum, ?_, ?_⟩
  · simpa only [Letter.linearMap_theta, derivative_add,
      mul_add, RealRooted.theta] using htheta
  · simpa only [Letter.linearMap_theta, Letter.linearMap_one,
      derivative_add, mul_add, RealRooted.theta] using hinterl

/-- The block `(θ,θ)/(θ,θ)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_theta_theta_theta_theta :
    PreservesOrderedPFPair
      Letter.theta.linearMap Letter.theta.linearMap
      Letter.theta.linearMap Letter.theta.linearMap := by
  intro p q hp hq hpq
  have hsum := theta_preserves_pf (hp.add_of_interl hq hpq)
  simpa only [Letter.linearMap_theta, derivative_add,
    mul_add, RealRooted.theta] using And.intro hsum (And.intro hsum hsum.interl_self)

/-- The block `(θ,θ)/(X,X)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_theta_theta_x_x :
    PreservesOrderedPFPair
      Letter.theta.linearMap Letter.theta.linearMap Letter.x.linearMap Letter.x.linearMap := by
  intro p q hp hq hpq
  have hsum := hp.add_of_interl hq hpq
  refine ⟨?_, by simpa only [Letter.linearMap_x, ← mul_add] using hsum.X_mul, ?_⟩
  · simpa only [Letter.linearMap_theta, derivative_add,
      mul_add, RealRooted.theta] using theta_preserves_pf hsum
  · simpa only [Letter.linearMap_theta, Letter.linearMap_x, derivative_add,
      mul_add, RealRooted.theta] using hsum.interl_theta_X_mul

/-- The block `(θ,1)/(θ,1)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_theta_one_theta_one :
    PreservesOrderedPFPair
      Letter.theta.linearMap Letter.one.linearMap Letter.theta.linearMap Letter.one.linearMap := by
  intro p q hp hq hpq
  have hsum := isPFPolynomial_theta_add_right hp hq hpq
  simpa only [Letter.linearMap_theta, Letter.linearMap_one,
    RealRooted.theta] using And.intro hsum (And.intro hsum hsum.interl_self)

/-- The block `(X,θ)/(X,θ)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_x_theta_x_theta :
    PreservesOrderedPFPair
      Letter.x.linearMap Letter.theta.linearMap Letter.x.linearMap Letter.theta.linearMap := by
  intro p q hp hq hpq
  have hsum := (isPFPolynomial_add_derivative_of_interl hp hq hpq).X_mul
  simpa only [Letter.linearMap_x, Letter.linearMap_theta, mul_add, RealRooted.theta] using
    And.intro hsum (And.intro hsum hsum.interl_self)

/-- The block `(θ,1)/(X,θ)` preserves ordered PF pairs. -/
theorem preservesOrderedPFPair_theta_one_x_theta :
    PreservesOrderedPFPair
      Letter.theta.linearMap Letter.one.linearMap Letter.x.linearMap Letter.theta.linearMap := by
  intro p q hp hq hpq
  have htop := isPFPolynomial_theta_add_right hp hq hpq
  have hbottom := (isPFPolynomial_add_derivative_of_interl hp hq hpq).X_mul
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Letter.linearMap_theta, Letter.linearMap_one,
      RealRooted.theta] using htop
  · simpa only [Letter.linearMap_theta, Letter.linearMap_x, mul_add, RealRooted.theta] using
      hbottom
  · simpa only [Letter.linearMap_theta, Letter.linearMap_x, Letter.linearMap_one,
      RealRooted.theta] using interl_theta_add_X_mul_add_theta hp hq hpq

/-- The block `(θ,1)/(θ,θ)` preserves ordered PF pairs; this is the mixed differential lemma
followed by `X`-duality. -/
theorem preservesOrderedPFPair_theta_one_theta_theta :
    PreservesOrderedPFPair
      Letter.theta.linearMap Letter.one.linearMap Letter.theta.linearMap
      Letter.theta.linearMap := by
  intro p q hp hq hpq
  have htop := isPFPolynomial_add_X_mul_derivative_of_interl hp hq hpq
  have hsum := isPFPolynomial_derivative_add_derivative_of_interl hp hq hpq
  have hdual := (interl_iff_interl_X_mul hsum htop).mp
    (interl_derivative_add_derivative_add_X_mul_derivative hp hq hpq)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Letter.linearMap_theta, Letter.linearMap_one, RealRooted.theta,
      add_comm (X * p.derivative)] using htop
  · simpa only [Letter.linearMap_theta, RealRooted.theta, mul_add] using hsum.X_mul
  · simpa only [Letter.linearMap_theta, Letter.linearMap_one, RealRooted.theta, mul_add,
      add_comm (X * p.derivative) q] using hdual

/-- **Classification.** A two-by-two block over `{1, θ, X}` preserves ordered PF pairs if and only
if it is one of the thirteen blocks of `Letter.IsAllowedBlock`. -/
theorem preservesOrderedPFPair_iff_isAllowedBlock (a b c d : Letter) :
    PreservesOrderedPFPair a.linearMap b.linearMap c.linearMap d.linearMap ↔
      a.IsAllowedBlock b c d := by
  refine ⟨fun h => by_contra fun hn => not_preservesOrderedPFPair_of_not_isAllowedBlock
    a b c d hn h, fun h => ?_⟩
  match a, b, c, d, h with
  | .one, .one, .one, .one, _ => exact preservesOrderedPFPair_one_one_one_one
  | .one, .one, .theta, .theta, _ => exact preservesOrderedPFPair_one_one_theta_theta
  | .one, .one, .x, .one, _ => exact preservesOrderedPFPair_one_one_x_one
  | .one, .one, .x, .x, _ => exact preservesOrderedPFPair_one_one_x_x
  | .theta, .one, .theta, .one, _ => exact preservesOrderedPFPair_theta_one_theta_one
  | .theta, .one, .theta, .theta, _ => exact preservesOrderedPFPair_theta_one_theta_theta
  | .theta, .one, .x, .theta, _ => exact preservesOrderedPFPair_theta_one_x_theta
  | .theta, .theta, .theta, .theta, _ => exact preservesOrderedPFPair_theta_theta_theta_theta
  | .theta, .theta, .x, .x, _ => exact preservesOrderedPFPair_theta_theta_x_x
  | .x, .one, .x, .one, _ => exact preservesOrderedPFPair_x_one_x_one
  | .x, .one, .x, .x, _ => exact preservesOrderedPFPair_x_one_x_x
  | .x, .theta, .x, .theta, _ => exact preservesOrderedPFPair_x_theta_x_theta
  | .x, .x, .x, .x, _ => exact preservesOrderedPFPair_x_x_x_x

/-- **Rectangular classification.** A matrix with at least two rows and columns over
`{1, θ, X}` preserves ordered PF vectors if and only if every ordered two-by-two submatrix, on
rows `i < k` and columns `j < l`, is one of the thirteen allowed blocks. -/
theorem preservesOrderedPF_letters_iff {m n : ℕ} (L : Fin m → Fin n → Letter)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    PreservesOrderedPF (fun i j => (L i j).linearMap) ↔
      ∀ i k j l, i < k → j < l → (L i j).IsAllowedBlock (L i l) (L k j) (L k l) := by
  rw [preservesOrderedPF_iff_preservesBlock_of_two_le _ hm hn]
  simp only [PreservesBlock, preservesOrderedPFPair_iff_isAllowedBlock]

end RealRooted.OperatorMatrix

