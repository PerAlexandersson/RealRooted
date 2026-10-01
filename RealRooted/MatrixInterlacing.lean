import RealRooted.MatrixInterlacing.Action
import RealRooted.MatrixInterlacing.SparseTests
import RealRooted.MatrixInterlacing.Converse
import RealRooted.MatrixInterlacing.AffinePair
import RealRooted.MatrixInterlacing.Preservation
import RealRooted.MatrixInterlacing.TotallyNonnegative
import RealRooted.QuadraticRoot

/-!
# Matrix preservation of interlacing sequences

Sparse pair machinery, `matPolyAction` definition, forward and backward
matrix-preservation theorems (Brändén, Theorem 7.8.5).
The totally-nonnegative leaf specializes the generic polynomial-matrix theorem
to constant rectangular matrices and proves Fisk's positive-leading wrapper.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Atomic two-by-two polynomial matrices -/

/-- The three polynomial entries used by the atomic matrix classification. -/
inductive AtomicMatrixEntry where
  | zero
  | one
  | x
  deriving DecidableEq, Repr

instance : Fintype AtomicMatrixEntry where
  elems := {.zero, .one, .x}
  complete e := by cases e <;> simp

namespace AtomicMatrixEntry

/-- Interpret an atomic entry as `0`, `1`, or `X` in `ℝ[X]`. -/
@[simp] def eval : AtomicMatrixEntry → ℝ[X]
  | zero => 0
  | one => 1
  | x => X

theorem hasNonnegCoeffs (e : AtomicMatrixEntry) : HasNonnegCoeffs e.eval := by
  cases e
  · exact hasNonnegCoeffs_zero
  · exact hasNonnegCoeffs_one
  · exact hasNonnegCoeffs_X

end AtomicMatrixEntry

/-- A row-major `2 × 2` matrix code with entries in `{0, 1, X}`. -/
structure Atomic2x2Matrix where
  a : AtomicMatrixEntry
  b : AtomicMatrixEntry
  c : AtomicMatrixEntry
  d : AtomicMatrixEntry
  deriving DecidableEq, Repr

private def atomic2x2MatrixEquiv :
    Atomic2x2Matrix ≃
      AtomicMatrixEntry × AtomicMatrixEntry × AtomicMatrixEntry × AtomicMatrixEntry where
  toFun M := (M.a, M.b, M.c, M.d)
  invFun M := ⟨M.1, M.2.1, M.2.2.1, M.2.2.2⟩
  left_inv M := by cases M; rfl
  right_inv M := by rcases M with ⟨a, b, c, d⟩; rfl

instance : Fintype Atomic2x2Matrix :=
  Fintype.ofEquiv
    (AtomicMatrixEntry × AtomicMatrixEntry × AtomicMatrixEntry × AtomicMatrixEntry)
    atomic2x2MatrixEquiv.symm

namespace Atomic2x2Matrix

/-- Interpret an atomic code as a row-major list matrix over `ℝ[X]`. -/
@[simp] def eval (M : Atomic2x2Matrix) : List (List ℝ[X]) :=
  [[M.a.eval, M.b.eval], [M.c.eval, M.d.eval]]

/-- The off-diagonal affine pencil condition for an atomic matrix. -/
def HasAffineProperty (M : Atomic2x2Matrix) : Prop :=
  Has2x2InterlacingProperty0 M.a.eval M.b.eval M.c.eval M.d.eval

/-- All nine weak affine tests obtained by allowing repeated ordered row and
column indices. This is the exact hypothesis consumed by the zero-aware matrix
preservation theorem for a `2 × 2` matrix. -/
def HasFullAffineProperty (M : Atomic2x2Matrix) : Prop :=
  Has2x2InterlacingProperty0 M.a.eval M.a.eval M.a.eval M.a.eval ∧
  Has2x2InterlacingProperty0 M.a.eval M.b.eval M.a.eval M.b.eval ∧
  Has2x2InterlacingProperty0 M.b.eval M.b.eval M.b.eval M.b.eval ∧
  Has2x2InterlacingProperty0 M.a.eval M.a.eval M.c.eval M.c.eval ∧
  M.HasAffineProperty ∧
  Has2x2InterlacingProperty0 M.b.eval M.b.eval M.d.eval M.d.eval ∧
  Has2x2InterlacingProperty0 M.c.eval M.c.eval M.c.eval M.c.eval ∧
  Has2x2InterlacingProperty0 M.c.eval M.d.eval M.c.eval M.d.eval ∧
  Has2x2InterlacingProperty0 M.d.eval M.d.eval M.d.eval M.d.eval

/-- The 42 atomic codes whose off-diagonal affine pencil is valid. The two
codes admitted here but rejected by `isPreserving` are the degenerate pencils
`[[0, X], [0, 1]]` and `[[X, 0], [1, 0]]`; their zero pencil side hides a bad
single-column test. -/
def isAffineAdmissible : Atomic2x2Matrix → Bool
  | ⟨.zero, .zero, .zero, .zero⟩
  | ⟨.zero, .zero, .zero, .one⟩
  | ⟨.zero, .zero, .zero, .x⟩
  | ⟨.zero, .zero, .one, .zero⟩
  | ⟨.zero, .zero, .one, .one⟩
  | ⟨.zero, .zero, .x, .zero⟩
  | ⟨.zero, .zero, .x, .one⟩
  | ⟨.zero, .zero, .x, .x⟩
  | ⟨.zero, .one, .zero, .zero⟩
  | ⟨.zero, .one, .zero, .one⟩
  | ⟨.zero, .one, .zero, .x⟩
  | ⟨.zero, .one, .x, .zero⟩
  | ⟨.zero, .one, .x, .one⟩
  | ⟨.zero, .one, .x, .x⟩
  | ⟨.zero, .x, .zero, .zero⟩
  | ⟨.zero, .x, .zero, .one⟩
  | ⟨.zero, .x, .zero, .x⟩
  | ⟨.one, .zero, .zero, .zero⟩
  | ⟨.one, .zero, .zero, .one⟩
  | ⟨.one, .zero, .one, .zero⟩
  | ⟨.one, .zero, .one, .one⟩
  | ⟨.one, .zero, .x, .zero⟩
  | ⟨.one, .zero, .x, .one⟩
  | ⟨.one, .one, .zero, .zero⟩
  | ⟨.one, .one, .zero, .one⟩
  | ⟨.one, .one, .one, .one⟩
  | ⟨.one, .one, .x, .zero⟩
  | ⟨.one, .one, .x, .one⟩
  | ⟨.one, .one, .x, .x⟩
  | ⟨.x, .zero, .zero, .zero⟩
  | ⟨.x, .zero, .zero, .x⟩
  | ⟨.x, .zero, .one, .zero⟩
  | ⟨.x, .zero, .x, .zero⟩
  | ⟨.x, .zero, .x, .x⟩
  | ⟨.x, .one, .zero, .zero⟩
  | ⟨.x, .one, .zero, .x⟩
  | ⟨.x, .one, .x, .zero⟩
  | ⟨.x, .one, .x, .one⟩
  | ⟨.x, .one, .x, .x⟩
  | ⟨.x, .x, .zero, .zero⟩
  | ⟨.x, .x, .zero, .x⟩
  | ⟨.x, .x, .x, .x⟩ => true
  | _ => false

/-- Boolean form of the full repeated-index affine criterion. -/
def isPreserving (M : Atomic2x2Matrix) : Bool :=
  M.isAffineAdmissible &&
    !(M.a == .one && M.b == .x) &&
    !(M.c == .one && M.d == .x) &&
    !(M.a == .x && M.c == .one) &&
    !(M.b == .x && M.d == .one)

/-- Reflection across the anti-diagonal. This is the square reflection that
preserves the directed atomic classification. -/
def antiTranspose (M : Atomic2x2Matrix) : Atomic2x2Matrix :=
  ⟨M.d, M.b, M.c, M.a⟩

@[simp] theorem antiTranspose_antiTranspose (M : Atomic2x2Matrix) :
    M.antiTranspose.antiTranspose = M := by
  cases M
  rfl

theorem isPreserving_antiTranspose (M : Atomic2x2Matrix) :
    M.antiTranspose.isPreserving = M.isPreserving := by
  rcases M with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- The explicit enumeration of all `3^4 = 81` atomic matrices. -/
def all : Finset Atomic2x2Matrix := Finset.univ

/-- The checked finite collection of atomic matrices satisfying the full
affine criterion. -/
def preserving : Finset Atomic2x2Matrix :=
  all.filter fun M => M.isPreserving

theorem card_all : all.card = 81 := by decide

theorem card_preserving : preserving.card = 40 := by decide

/-- Boolean form of the 18-matrix table's nondegeneracy convention: neither
row is zero and the two rows are distinct. -/
def isNondegenerate (M : Atomic2x2Matrix) : Bool :=
  !(M.a == .zero && M.b == .zero) &&
  !(M.c == .zero && M.d == .zero) &&
  !(M.a == M.c && M.b == M.d)

/-- Proposition form of `isNondegenerate`. -/
def IsNondegenerate (M : Atomic2x2Matrix) : Prop :=
  M.isNondegenerate = true

/-- The 56 atomic codes remaining after deleting zero-row and repeated-row
matrices. -/
def nondegenerate : Finset Atomic2x2Matrix :=
  all.filter fun M => M.isNondegenerate = true

/-- The nondegenerate members of the full 40-code preserving table. -/
def nondegeneratePreserving : Finset Atomic2x2Matrix :=
  preserving.filter fun M => M.isNondegenerate = true

theorem card_nondegenerate : nondegenerate.card = 56 := by decide

theorem card_nondegeneratePreserving : nondegeneratePreserving.card = 18 := by
  decide

/-- The 18 nondegenerate preservers displayed at
<https://www.symmetricfunctions.com/realRootedInterlacing.htm#smallInterlacingMatrices>. -/
def symCatPreservingList : List Atomic2x2Matrix :=
  [⟨.zero, .one, .zero, .x⟩,
    ⟨.zero, .one, .x, .zero⟩,
    ⟨.one, .zero, .zero, .one⟩,
    ⟨.one, .zero, .x, .zero⟩,
    ⟨.x, .zero, .zero, .x⟩,
    ⟨.zero, .one, .x, .one⟩,
    ⟨.zero, .one, .x, .x⟩,
    ⟨.one, .zero, .one, .one⟩,
    ⟨.one, .zero, .x, .one⟩,
    ⟨.one, .one, .zero, .one⟩,
    ⟨.one, .one, .x, .zero⟩,
    ⟨.x, .zero, .x, .x⟩,
    ⟨.x, .one, .zero, .x⟩,
    ⟨.x, .one, .x, .zero⟩,
    ⟨.x, .x, .zero, .x⟩,
    ⟨.one, .one, .x, .one⟩,
    ⟨.one, .one, .x, .x⟩,
    ⟨.x, .one, .x, .x⟩]

def symCatPreserving : Finset Atomic2x2Matrix :=
  symCatPreservingList.toFinset

theorem nondegeneratePreserving_eq_symCatPreserving :
    nondegeneratePreserving = symCatPreserving := by decide

/-! ### Affine certificates for the accepted codes -/

theorem hasAffineProperty_of_isAffineAdmissible
    {M : Atomic2x2Matrix} (hM : M.isAffineAdmissible) :
    M.HasAffineProperty := by
  rcases M with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals simp [isAffineAdmissible] at hM
  all_goals simp only [HasAffineProperty, AtomicMatrixEntry.eval]
  all_goals intro s t hs ht
  all_goals try simp only [mul_zero, mul_one, add_zero, zero_add]
  all_goals first
    | with_reducible exact interl_zero_left _
    | with_reducible exact interl_zero_right _
    | with_reducible exact interl_one_one
    | with_reducible exact interl_one_X
    | with_reducible exact interl_one_affine hs
    | with_reducible exact interl_one_affine_add_one hs
    | with_reducible exact interl_one_affine_add_X hs
    | with_reducible exact interl_X_X
    | with_reducible exact interl_affine_X hs ht
    | with_reducible exact interl_affine_add_one_X hs ht
    | with_reducible exact interl_affine_add_X_X hs ht
    | with_reducible exact interl_affine_self hs
    | with_reducible exact interl_affine_add_one_affine hs
    | with_reducible exact interl_affine_add_one_self hs
    | with_reducible exact interl_affine_affine_add_X hs ht
    | with_reducible exact interl_affine_add_one_affine_add_X hs ht
    | with_reducible exact interl_affine_add_X_self hs
    | with_reducible exact interl_X_affine_mul_X hs ht
    | with_reducible exact interl_X_affine_mul_X_add_X hs ht
    | with_reducible exact interl_affine_affine_mul_X hs ht
    | with_reducible exact interl_affine_add_X_affine_mul_X hs ht
    | with_reducible exact interl_affine_affine_mul_X_add_X hs ht
    | with_reducible exact interl_affine_add_one_affine_mul_X_add_X hs ht
    | with_reducible exact interl_affine_add_X_affine_mul_X_add_X hs ht
    | with_reducible exact interl_affine_mul_X_self hs
    | with_reducible exact interl_affine_mul_X_add_X_affine_mul_X hs ht
    | with_reducible exact interl_affine_mul_X_add_X_self hs

/-! ### Exact obstructions for the excluded codes -/

private lemma affine_cross_of_interl
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (h : Interl (C u * X + C v) (C U * X + C V)) :
    u * V ≤ U * v := by
  have hstrict := h.toStrictInterl_of_ne
    (isRealRooted_affine_factor hu).1 (isRealRooted_affine_factor hU).1
  have hp : (C u * X + C v : ℝ[X]) = C u * (X + C (v / u)) := by
    rw [mul_add, ← C_mul, mul_div_cancel₀ v hu.ne']
  have hq : (C U * X + C V : ℝ[X]) = C U * (X + C (V / U)) := by
    rw [mul_add, ← C_mul, mul_div_cancel₀ V hU.ne']
  have hpdeg : (C u * X + C v : ℝ[X]).natDegree = 1 := by grind
  have hqdeg : (C U * X + C V : ℝ[X]).natDegree = 1 := by grind
  have hsum := hstrict.roots_sum_le_of_sameDegree (hpdeg.trans hqdeg.symm)
  rw [hp, hq, roots_C_mul _ hu.ne', roots_C_mul _ hU.ne',
    roots_X_add_C, roots_X_add_C] at hsum
  have hdiv : V / U ≤ v / u := by simpa using hsum
  rw [div_le_div_iff₀ hU hu] at hdiv
  nlinarith

private lemma not_interl_affine_of_cross_lt
    {u v U V : ℝ} (hu : 0 < u) (hU : 0 < U)
    (hcross : U * v < u * V) :
    ¬ Interl (C u * X + C v) (C U * X + C V) := by
  intro h
  nlinarith [affine_cross_of_interl hu hU h]

private lemma not_interl_X_two_mul_X_add_one :
    ¬ Interl (X : ℝ[X]) (2 * X + 1) := by
  simpa only [C_0, C_1, C_ofNat, one_mul, add_zero] using
    (not_interl_affine_of_cross_lt
      (u := 1) (v := 0) (U := 2) (V := 1)
      (by norm_num) (by norm_num) (by norm_num))

private lemma not_interl_X_X_add_one :
    ¬ Interl (X : ℝ[X]) (X + 1) := by
  simpa only [C_0, C_1, C_ofNat, one_mul, add_zero] using
    (not_interl_affine_of_cross_lt
      (u := 1) (v := 0) (U := 1) (V := 1)
      (by norm_num) (by norm_num) (by norm_num))

private lemma not_interl_X_X_add_two :
    ¬ Interl (X : ℝ[X]) (X + 2) := by
  simpa only [C_0, C_1, C_ofNat, one_mul, add_zero] using
    (not_interl_affine_of_cross_lt
      (u := 1) (v := 0) (U := 1) (V := 2)
      (by norm_num) (by norm_num) (by norm_num))

private lemma not_interl_two_mul_X_add_one_X_add_one :
    ¬ Interl (2 * X + 1 : ℝ[X]) (X + 1) := by
  simpa only [C_1, C_ofNat, one_mul] using
    (not_interl_affine_of_cross_lt
      (u := 2) (v := 1) (U := 1) (V := 1)
      (by norm_num) (by norm_num) (by norm_num))

private lemma not_interl_two_mul_X_add_one_X_add_two :
    ¬ Interl (2 * X + 1 : ℝ[X]) (X + 2) := by
  simpa only [C_1, C_ofNat, one_mul] using
    (not_interl_affine_of_cross_lt
      (u := 2) (v := 1) (U := 1) (V := 2)
      (by norm_num) (by norm_num) (by norm_num))

private lemma not_interl_X_add_one_X_add_two :
    ¬ Interl (X + 1 : ℝ[X]) (X + 2) := by
  simpa only [C_1, C_ofNat, one_mul] using
    (not_interl_affine_of_cross_lt
      (u := 1) (v := 1) (U := 1) (V := 2)
      (by norm_num) (by norm_num) (by norm_num))

private lemma not_interl_X_X_add_one_add_X :
    ¬ Interl (X : ℝ[X]) (X + 1 + X) := by
  convert not_interl_X_two_mul_X_add_one using 1; ring_nf

private lemma not_interl_X_X_add_one_add_one :
    ¬ Interl (X : ℝ[X]) (X + 1 + 1) := by
  convert not_interl_X_X_add_two using 1; ring_nf

private lemma not_interl_X_add_one_add_X_X_add_one :
    ¬ Interl (X + 1 + X : ℝ[X]) (X + 1) := by
  convert not_interl_two_mul_X_add_one_X_add_one using 1; ring_nf

private lemma not_interl_X_add_one_add_X_X_add_one_add_one :
    ¬ Interl (X + 1 + X : ℝ[X]) (X + 1 + 1) := by
  convert not_interl_two_mul_X_add_one_X_add_two using 1; ring_nf

private lemma not_interl_X_add_one_X_add_one_add_one :
    ¬ Interl (X + 1 : ℝ[X]) (X + 1 + 1) := by
  convert not_interl_X_add_one_X_add_two using 1; ring_nf

private lemma natDegree_X_add_one_add_one :
    (X + 1 + 1 : ℝ[X]).natDegree = 1 := by compute_degree!

private lemma natDegree_X_add_one_add_X :
    (X + 1 + X : ℝ[X]).natDegree = 1 := by compute_degree!

private lemma natDegree_X_add_one_mul_X :
    ((X + 1) * X : ℝ[X]).natDegree = 2 := by compute_degree!

private lemma natDegree_X_add_one_mul_X_add_X :
    ((X + 1) * X + X : ℝ[X]).natDegree = 2 := by compute_degree!

private lemma atomicBadQuadratic_ne_zero :
    ((X + 1) * X + 1 : ℝ[X]) ≠ 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 0) h
  norm_num at heval

private lemma atomicBadQuadratic_not_splits :
    ¬ ((X + 1) * X + 1 : ℝ[X]).Splits := by
  rw [show ((X + 1) * X + 1 : ℝ[X]) = X ^ 2 + C 1 * X + C 1 by
    norm_num
    ring]
  rw [monicQuadraticPoly_not_splits_iff_discrim_neg]
  norm_num

private lemma not_interl_atomicBadQuadratic_left {p : ℝ[X]} (hp : p ≠ 0) :
    ¬ Interl ((X + 1) * X + 1 : ℝ[X]) p := by
  intro h
  exact atomicBadQuadratic_not_splits
    (h.toStrictInterl_of_ne atomicBadQuadratic_ne_zero hp).1.2

private lemma not_interl_atomicBadQuadratic_right {p : ℝ[X]} (hp : p ≠ 0) :
    ¬ Interl p ((X + 1) * X + 1 : ℝ[X]) := by
  intro h
  exact atomicBadQuadratic_not_splits
    (h.toStrictInterl_of_ne hp atomicBadQuadratic_ne_zero).2.1.2

private lemma ne_zero_of_natDegree_eq_succ {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n + 1) : p ≠ 0 := by
  intro hp
  simp [hp] at hdeg

private lemma not_interl_bad_linear_quadratic :
    ¬ Interl (X + 2 : ℝ[X]) ((X + 1) * X) := by
  intro h
  have hstrict := h.toStrictInterl_of_ne
    (X_add_C_ne_zero 2) (mul_ne_zero (X_add_C_ne_zero 1) X_ne_zero)
  have hreduced : StrictInterl (X + 1 : ℝ[X]) (X + 2) := by
    apply strictInterl_of_strictInterl_X_mul_of_nonneg
    · convert hstrict using 1; ring
    · convert hasNonnegCoeffs_affine_linear
        (a := 1) (b := 1) (by norm_num) (by norm_num) using 1
      all_goals try simp only [C_1, one_mul]
    · convert hasNonnegCoeffs_affine_linear
        (a := 1) (b := 2) (by norm_num) (by norm_num) using 1
      all_goals try simp only [Polynomial.C_ofNat, C_1, one_mul]
  have hcross := affine_cross_of_interl
    (u := 1) (v := 1) (U := 1) (V := 2)
    zero_lt_one zero_lt_one (by
      convert hreduced.toInterl using 1
      all_goals try simp only [Polynomial.C_ofNat, C_1, one_mul])
  norm_num at hcross

private lemma not_interl_bad_linear_quadratic_raw :
    ¬ Interl (X + 1 + 1 : ℝ[X]) ((X + 1) * X) := by
  convert not_interl_bad_linear_quadratic using 1; ring_nf

private lemma not_interl_bad_quadratic_pair :
    ¬ Interl ((X + 1) * X : ℝ[X]) ((X + 1) * X + X) := by
  intro h
  have hfactor : Interl (X * (X + 1) : ℝ[X]) (X * (X + 2)) := by
    convert h using 1 <;> ring
  have hreduced : Interl (X + 1 : ℝ[X]) (X + 2) := by
    apply Interl.of_mul_X_both_of_nonneg
    · exact hfactor
    · convert hasNonnegCoeffs_affine_linear
        (a := 1) (b := 1) (by norm_num) (by norm_num) using 1
      all_goals try simp only [C_1, one_mul]
    · convert hasNonnegCoeffs_affine_linear
        (a := 1) (b := 2) (by norm_num) (by norm_num) using 1
      all_goals try simp only [Polynomial.C_ofNat, C_1, one_mul]
  have hcross := affine_cross_of_interl
    (u := 1) (v := 1) (U := 1) (V := 2)
    zero_lt_one zero_lt_one (by
      convert hreduced using 1
      all_goals try simp only [Polynomial.C_ofNat, C_1, one_mul])
  norm_num at hcross

theorem isAffineAdmissible_of_hasAffineProperty
    {M : Atomic2x2Matrix} (hM : M.HasAffineProperty) :
    M.isAffineAdmissible = true := by
  rcases M with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals simp only [isAffineAdmissible]
  all_goals exfalso
  all_goals have h := hM 1 1 zero_lt_one zero_lt_one
  all_goals norm_num at h
  all_goals first
    | ((with_reducible_and_instances refine absurd h (not_interl_atomicBadQuadratic_left ?_))
       first
        | exact one_ne_zero
        | exact X_ne_zero
        | exact ne_zero_of_natDegree_eq_succ (by compute_degree!))
    | ((with_reducible_and_instances refine absurd h (not_interl_atomicBadQuadratic_right ?_))
       first
        | exact one_ne_zero
        | exact X_ne_zero
        | exact ne_zero_of_natDegree_eq_succ (by compute_degree!))
    | with_reducible_and_instances exact absurd h not_interl_X_two_mul_X_add_one
    | with_reducible_and_instances exact absurd h not_interl_X_X_add_one
    | with_reducible_and_instances exact absurd h not_interl_X_X_add_two
    | with_reducible_and_instances exact absurd h not_interl_two_mul_X_add_one_X_add_one
    | with_reducible_and_instances exact absurd h not_interl_two_mul_X_add_one_X_add_two
    | with_reducible_and_instances exact absurd h not_interl_X_add_one_X_add_two
    | with_reducible_and_instances exact absurd h not_interl_X_X_add_one_add_X
    | with_reducible_and_instances exact absurd h not_interl_X_X_add_one_add_one
    | with_reducible_and_instances exact absurd h not_interl_X_add_one_add_X_X_add_one
    | with_reducible_and_instances exact absurd h not_interl_X_add_one_add_X_X_add_one_add_one
    | with_reducible_and_instances exact absurd h not_interl_X_add_one_X_add_one_add_one
    | with_reducible_and_instances exact absurd h not_interl_bad_linear_quadratic
    | with_reducible_and_instances exact absurd h not_interl_bad_linear_quadratic_raw
    | with_reducible_and_instances exact absurd h not_interl_bad_quadratic_pair
    | (have hs := h.toStrictInterl_of_ne
          (by first
            | exact one_ne_zero
            | exact X_ne_zero
            | exact ne_zero_of_natDegree_eq_succ (by compute_degree!))
          (by first
            | exact one_ne_zero
            | exact X_ne_zero
            | exact ne_zero_of_natDegree_eq_succ (by compute_degree!));
       have hbounds := hs.natDegree_bounds;
       norm_num [natDegree_X_add_one_add_one, natDegree_X_add_one_add_X,
         natDegree_X_add_one_mul_X, natDegree_X_add_one_mul_X_add_X] at hbounds)

/-- Exact classification of all 81 off-diagonal atomic affine pencils. -/
theorem hasAffineProperty_iff_isAffineAdmissible (M : Atomic2x2Matrix) :
    M.HasAffineProperty ↔ M.isAffineAdmissible = true :=
  ⟨isAffineAdmissible_of_hasAffineProperty,
    hasAffineProperty_of_isAffineAdmissible⟩

/-- The compact Boolean recognizes exactly the full repeated-index affine
criterion, not merely the off-diagonal test. -/
theorem hasFullAffineProperty_iff_isPreserving (M : Atomic2x2Matrix) :
    M.HasFullAffineProperty ↔ M.isPreserving = true := by
  rcases M with ⟨a, b, c, d⟩
  change
    HasAffineProperty ⟨a, a, a, a⟩ ∧
      HasAffineProperty ⟨a, b, a, b⟩ ∧
      HasAffineProperty ⟨b, b, b, b⟩ ∧
      HasAffineProperty ⟨a, a, c, c⟩ ∧
      HasAffineProperty ⟨a, b, c, d⟩ ∧
      HasAffineProperty ⟨b, b, d, d⟩ ∧
      HasAffineProperty ⟨c, c, c, c⟩ ∧
      HasAffineProperty ⟨c, d, c, d⟩ ∧
      HasAffineProperty ⟨d, d, d, d⟩ ↔
        isPreserving ⟨a, b, c, d⟩ = true
  simp_rw [hasAffineProperty_iff_isAffineAdmissible]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- Membership form of the exact 40-code affine classification. -/
theorem mem_preserving_iff_hasFullAffineProperty (M : Atomic2x2Matrix) :
    M ∈ preserving ↔ M.HasFullAffineProperty := by
  rw [hasFullAffineProperty_iff_isPreserving]
  simp [preserving, all]

theorem mem_preserving_antiTranspose_iff (M : Atomic2x2Matrix) :
    M.antiTranspose ∈ preserving ↔ M ∈ preserving := by
  simp [preserving, all, isPreserving_antiTranspose]

/-- An atomic matrix preserves the iterative zero-aware nonnegative
real-rooted interlacing package under the polynomial matrix action. -/
def PreservesInterlacing (M : Atomic2x2Matrix) : Prop :=
  ∀ (fs : List ℝ[X]), fs.length = 2 →
    IsInterlacingSeq0NonnegRealRooted fs →
    IsInterlacingSeq0NonnegRealRooted (matPolyAction M.eval fs)

private theorem eval_rect (M : Atomic2x2Matrix) :
    ∀ row ∈ M.eval, row.length = 2 := by
  intro row hrow
  simp only [eval, AtomicMatrixEntry.eval, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl <;> simp

private theorem eval_nonneg (M : Atomic2x2Matrix) :
    ∀ row ∈ M.eval, ∀ p ∈ row, HasNonnegCoeffs p := by
  rcases M with ⟨a, b, c, d⟩
  intro row hrow p hp
  simp only [eval, AtomicMatrixEntry.eval, List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> apply AtomicMatrixEntry.hasNonnegCoeffs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> apply AtomicMatrixEntry.hasNonnegCoeffs

private theorem affine_submatrix_of_hasFullAffineProperty
    {M : Atomic2x2Matrix} (hM : M.HasFullAffineProperty)
    (i₁ i₂ : Fin M.eval.length) (j₁ j₂ : Fin 2)
    (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    Has2x2InterlacingProperty0
      ((M.eval.get i₁).get ⟨j₁, by
        rw [eval_rect M _ (List.get_mem M.eval i₁)]
        exact j₁.isLt⟩)
      ((M.eval.get i₁).get ⟨j₂, by
        rw [eval_rect M _ (List.get_mem M.eval i₁)]
        exact j₂.isLt⟩)
      ((M.eval.get i₂).get ⟨j₁, by
        rw [eval_rect M _ (List.get_mem M.eval i₂)]
        exact j₁.isLt⟩)
      ((M.eval.get i₂).get ⟨j₂, by
        rw [eval_rect M _ (List.get_mem M.eval i₂)]
        exact j₂.isLt⟩) := by
  rcases M with ⟨a, b, c, d⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp_all [eval, HasFullAffineProperty, HasAffineProperty]

/-- Every code in the 40-element table preserves weak zero-aware
interlacing, nonnegative coefficients, and real-rootedness of nonzero output
entries. -/
theorem preservesInterlacing_of_mem_preserving
    {M : Atomic2x2Matrix} (hM : M ∈ preserving) :
    M.PreservesInterlacing := by
  rw [mem_preserving_iff_hasFullAffineProperty] at hM
  intro fs hfs_len hfs
  exact matrix_preserves_interlacing_seq0_of_2x2_weak
    M.eval (eval_rect M) (eval_nonneg M)
    (affine_submatrix_of_hasFullAffineProperty hM)
    fs hfs_len hfs.1 hfs.2

private theorem interl_action_pair
    {M : Atomic2x2Matrix} (hM : M.PreservesInterlacing)
    {f g : ℝ[X]} (hfg : IsInterlacingSeq0NonnegRealRooted [f, g]) :
    Interl (M.a.eval * f + M.b.eval * g)
      (M.c.eval * f + M.d.eval * g) := by
  have hout := hM [f, g] (by simp) hfg
  have hp := isInterlacingSeq0_iff_pairwise.mp hout.1.1
  simpa [matPolyAction, eval] using hp

private theorem action_mem_splits
    {M : Atomic2x2Matrix} (hM : M.PreservesInterlacing)
    {f g p : ℝ[X]} (hfg : IsInterlacingSeq0NonnegRealRooted [f, g])
    (hp : p ∈ matPolyAction M.eval [f, g]) (hp0 : p ≠ 0) :
    p.Splits :=
  (hM [f, g] (by simp) hfg).2 p hp hp0 |>.2

private theorem interlacingPair
    {f g : ℝ[X]} (hfg : Interl f g)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfrr : f ≠ 0 → f.Splits) (hgrr : g ≠ 0 → g.Splits) :
    IsInterlacingSeq0NonnegRealRooted [f, g] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    simpa using hfg
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hfnn
    · exact hgnn
  · intro p hp hp0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨hp0, hfrr hp0⟩
    · exact ⟨hp0, hgrr hp0⟩

private theorem splits_X_sq : (X ^ 2 : ℝ[X]).Splits :=
  isRealRooted_X.2.pow 2

private theorem nonneg_X_sq : HasNonnegCoeffs (X ^ 2 : ℝ[X]) :=
  hasNonnegCoeffs_X.pow 2

private theorem input_zero_X_sq :
    IsInterlacingSeq0NonnegRealRooted [0, X ^ 2] :=
  interlacingPair (interl_zero_left _) hasNonnegCoeffs_zero nonneg_X_sq
    (fun h => (h rfl).elim) (fun _ => splits_X_sq)

private theorem input_X_sq_zero :
    IsInterlacingSeq0NonnegRealRooted [X ^ 2, 0] :=
  interlacingPair (interl_zero_right _) nonneg_X_sq hasNonnegCoeffs_zero
    (fun _ => splits_X_sq) (fun h => (h rfl).elim)

private theorem input_X_sq_X_sq :
    IsInterlacingSeq0NonnegRealRooted [X ^ 2, X ^ 2] :=
  interlacingPair (Interl.refl fun _ => splits_X_sq) nonneg_X_sq nonneg_X_sq
    (fun _ => splits_X_sq) (fun _ => splits_X_sq)

private theorem input_X_X_sq :
    IsInterlacingSeq0NonnegRealRooted [X, X ^ 2] := by
  apply interlacingPair
  · convert (strictInterl_self_X_mul_of_nonneg
      X_ne_zero isRealRooted_X.2 hasNonnegCoeffs_X).toInterl using 1; ring
  · exact hasNonnegCoeffs_X
  · exact nonneg_X_sq
  · exact fun _ => isRealRooted_X.2
  · exact fun _ => splits_X_sq

private theorem input_one_X_add_one :
    IsInterlacingSeq0NonnegRealRooted [1, X + 1] := by
  apply interlacingPair
  · simpa only [C_1, one_mul] using interl_one_affine_linear (b := 1) zero_lt_one
  · exact hasNonnegCoeffs_one
  · exact hasNonnegCoeffs_X_add_one
  · exact fun _ => Polynomial.Splits.one
  · intro
    simpa only [C_1, one_mul] using
      (isRealRooted_affine_factor (s := 1) (t := 1) zero_lt_one).2

private theorem not_interl_of_bad_natDegrees
    {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hbad : ¬(p.natDegree ≤ q.natDegree ∧ q.natDegree ≤ p.natDegree + 1)) :
    ¬ Interl p q := by
  intro h
  exact hbad (h.toStrictInterl_of_ne hp hq).natDegree_bounds

private theorem not_interl_of_natDegree_gap
    {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (hgap : q.natDegree < p.natDegree ∨ p.natDegree + 1 < q.natDegree) :
    ¬ Interl p q := by
  apply not_interl_of_bad_natDegrees hp hq
  lia

private theorem not_interl_X_sq_X :
    ¬ Interl (X ^ 2 : ℝ[X]) X := by
  apply not_interl_of_natDegree_gap
  · exact pow_ne_zero 2 X_ne_zero
  · exact X_ne_zero
  · left
    compute_degree!

private theorem not_interl_X_cube_X_sq :
    ¬ Interl (X ^ 3 : ℝ[X]) (X ^ 2) := by
  apply not_interl_of_natDegree_gap
  · exact pow_ne_zero 3 X_ne_zero
  · exact pow_ne_zero 2 X_ne_zero
  · left
    compute_degree!

private theorem not_interl_X_X_cube :
    ¬ Interl (X : ℝ[X]) (X ^ 3) := by
  apply not_interl_of_natDegree_gap X_ne_zero (pow_ne_zero 3 X_ne_zero)
  right
  have hdeg : (X ^ 3 : ℝ[X]).natDegree = 3 := by
    norm_num [Polynomial.natDegree_pow]
  rw [hdeg, Polynomial.natDegree_X]
  norm_num

private theorem not_interl_X_X_sq_add_X_cube :
    ¬ Interl (X : ℝ[X]) (X ^ 2 + X ^ 3) := by
  apply not_interl_of_natDegree_gap X_ne_zero
    (ne_zero_of_natDegree_eq_succ (by compute_degree!))
  right
  have hdeg : (X ^ 2 + X ^ 3 : ℝ[X]).natDegree = 3 := by compute_degree!
  rw [hdeg, Polynomial.natDegree_X]
  norm_num

private theorem not_interl_X_add_X_sq_X :
    ¬ Interl (X + X ^ 2 : ℝ[X]) X := by
  apply not_interl_of_natDegree_gap
    (ne_zero_of_natDegree_eq_succ (by compute_degree!)) X_ne_zero
  left
  have hdeg : (X + X ^ 2 : ℝ[X]).natDegree = 2 := by compute_degree!
  rw [hdeg, Polynomial.natDegree_X]
  norm_num

private theorem not_interl_X_sq_add_X_cube_X_sq :
    ¬ Interl (X ^ 2 + X ^ 3 : ℝ[X]) (X ^ 2) := by
  apply not_interl_of_natDegree_gap
    (ne_zero_of_natDegree_eq_succ (by compute_degree!))
    (pow_ne_zero 2 X_ne_zero)
  left
  have hdeg : (X ^ 2 + X ^ 3 : ℝ[X]).natDegree = 3 := by compute_degree!
  rw [hdeg, Polynomial.natDegree_pow, Polynomial.natDegree_X]
  norm_num

private theorem not_interl_X_sq_X_add_X_sq :
    ¬ Interl (X ^ 2 : ℝ[X]) (X + X ^ 2) := by
  intro h
  have hreduced : Interl X (1 + X) := by
    apply Interl.of_mul_X_both_of_nonneg
    · convert h using 1 <;> ring
    · exact hasNonnegCoeffs_X
    · exact hasNonnegCoeffs_one.add hasNonnegCoeffs_X
  exact not_interl_X_X_add_one (by simpa [add_comm] using hreduced)

private theorem not_interl_X_cube_X_sq_add_X_cube :
    ¬ Interl (X ^ 3 : ℝ[X]) (X ^ 2 + X ^ 3) := by
  intro h
  have hreduced : Interl (X ^ 2 : ℝ[X]) (X + X ^ 2) := by
    apply Interl.of_mul_X_both_of_nonneg
    · convert h using 1 <;> ring
    · exact nonneg_X_sq
    · exact hasNonnegCoeffs_X.add nonneg_X_sq
  exact not_interl_X_sq_X_add_X_sq hreduced

private theorem not_interl_X_add_X_sq_X_cube :
    ¬ Interl (X + X ^ 2 : ℝ[X]) (X ^ 3) := by
  intro h
  have hreduced : Interl (1 + X : ℝ[X]) (X ^ 2) := by
    apply Interl.of_mul_X_both_of_nonneg
    · convert h using 1 <;> ring
    · exact hasNonnegCoeffs_one.add hasNonnegCoeffs_X
    · exact nonneg_X_sq
  have hstrict := hreduced.toStrictInterl_of_ne
    (ne_zero_of_natDegree_eq_succ (by compute_degree!))
    (pow_ne_zero 2 X_ne_zero)
  have hbad := strictInterl_of_strictInterl_X_mul_of_nonneg
    (f := X) (g := 1 + X)
    (by convert hstrict using 1; ring)
    hasNonnegCoeffs_X (hasNonnegCoeffs_one.add hasNonnegCoeffs_X)
  exact not_interl_X_X_add_one (by simpa [add_comm] using hbad.toInterl)

private theorem X_sq_add_one_not_splits :
    ¬ (X ^ 2 + 1 : ℝ[X]).Splits := by
  rw [show (X ^ 2 + 1 : ℝ[X]) = X ^ 2 + C 0 * X + C 1 by
    simp only [C_0, C_1, zero_mul, add_zero]]
  rw [monicQuadraticPoly_not_splits_iff_discrim_neg]
  norm_num

private theorem X_add_X_cube_not_splits :
    ¬ (X + X ^ 3 : ℝ[X]).Splits := by
  intro h
  apply X_sq_add_one_not_splits
  exact h.of_dvd
    (ne_zero_of_natDegree_eq_succ (by compute_degree!))
    ⟨X, by ring⟩

private theorem not_preserves_top_row_one_x (c d : AtomicMatrixEntry) :
    ¬ PreservesInterlacing ⟨.one, .x, c, d⟩ := by
  intro hM
  apply X_add_X_cube_not_splits
  apply action_mem_splits hM input_X_X_sq
  · simp only [matPolyAction, eval, AtomicMatrixEntry.eval, List.map_cons, List.zipWith_cons_cons,
        one_mul, List.zipWith_self, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        List.mem_cons, add_right_inj, List.not_mem_nil, or_false]
    left
    ring
  · exact ne_zero_of_natDegree_eq_succ (by compute_degree!)

private theorem not_preserves_bottom_row_one_x (a b : AtomicMatrixEntry) :
    ¬ PreservesInterlacing ⟨a, b, .one, .x⟩ := by
  intro hM
  apply X_add_X_cube_not_splits
  apply action_mem_splits hM input_X_X_sq
  · simp only [matPolyAction, eval, AtomicMatrixEntry.eval, List.map_cons, List.zipWith_cons_cons,
        List.zipWith_self, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
        List.mem_cons, add_right_inj, List.not_mem_nil, or_false]
    right
    ring
  · exact ne_zero_of_natDegree_eq_succ (by compute_degree!)

/-- Semantic completeness of the finite atomic classification: every atomic
matrix preserving the iterative zero-aware interlacing package belongs to the
checked table. -/
theorem mem_preserving_of_preservesInterlacing
    {M : Atomic2x2Matrix} (hM : M.PreservesInterlacing) :
    M ∈ preserving := by
  rw [mem_preserving_iff_hasFullAffineProperty,
    hasFullAffineProperty_iff_isPreserving]
  rcases M with ⟨a, b, c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals simp only [isPreserving, isAffineAdmissible, Bool.not_and, Bool.true_and, Bool.and_self,
                Bool.and_self_right, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
                Bool.not_true, beq_eq_false_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, or_self,
                and_self, BEq.rfl, Bool.and_true, Bool.false_and, Bool.false_eq_true,
                Bool.and_false]
  all_goals try exact not_preserves_top_row_one_x _ _ hM
  all_goals try exact not_preserves_bottom_row_one_x _ _ hM
  all_goals
    have hzeroX := interl_action_pair hM input_zero_X_sq
    have hXzero := interl_action_pair hM input_X_sq_zero
    have hXX := interl_action_pair hM input_X_sq_X_sq
    have hxX := interl_action_pair hM input_X_X_sq
    have hone := interl_action_pair hM input_one_X_add_one
    have hbadAffine₁ := not_interl_X_two_mul_X_add_one
    have hbadAffine₂ := not_interl_two_mul_X_add_one_X_add_one
    simp [AtomicMatrixEntry.eval] at hzeroX hXzero hXX hxX hone
    ring_nf at hzeroX hXzero hXX hxX hone hbadAffine₁ hbadAffine₂
    first
    | with_reducible_and_instances exact absurd hzeroX not_interl_X_sq_X
    | with_reducible_and_instances exact absurd hXzero not_interl_X_sq_X
    | with_reducible_and_instances exact absurd hXX not_interl_X_sq_X
    | with_reducible_and_instances exact absurd hxX not_interl_X_sq_X
    | with_reducible_and_instances exact absurd hzeroX not_interl_X_cube_X_sq
    | with_reducible_and_instances exact absurd hXzero not_interl_X_cube_X_sq
    | with_reducible_and_instances exact absurd hXX not_interl_X_cube_X_sq
    | with_reducible_and_instances exact absurd hxX not_interl_X_cube_X_sq
    | with_reducible_and_instances exact absurd hzeroX not_interl_X_X_cube
    | with_reducible_and_instances exact absurd hXzero not_interl_X_X_cube
    | with_reducible_and_instances exact absurd hXX not_interl_X_X_cube
    | with_reducible_and_instances exact absurd hxX not_interl_X_X_cube
    | with_reducible_and_instances exact absurd hxX not_interl_X_X_sq_add_X_cube
    | with_reducible_and_instances exact absurd hxX not_interl_X_add_X_sq_X
    | with_reducible_and_instances exact absurd hxX not_interl_X_sq_add_X_cube_X_sq
    | with_reducible_and_instances exact absurd hxX not_interl_X_sq_X_add_X_sq
    | with_reducible_and_instances exact absurd hxX not_interl_X_cube_X_sq_add_X_cube
    | with_reducible_and_instances exact absurd hxX not_interl_X_add_X_sq_X_cube
    | with_reducible_and_instances exact absurd hone hbadAffine₁
    | with_reducible_and_instances exact absurd hone not_interl_X_X_add_one
    | with_reducible_and_instances exact absurd hone not_interl_X_X_add_two
    | with_reducible_and_instances exact absurd hone hbadAffine₂

/-- Exact semantic classification of all 81 atomic matrices. -/
theorem preservesInterlacing_iff_mem_preserving (M : Atomic2x2Matrix) :
    M.PreservesInterlacing ↔ M ∈ preserving :=
  ⟨mem_preserving_of_preservesInterlacing,
    preservesInterlacing_of_mem_preserving⟩

/-- Anti-diagonal reflection preserves the semantic matrix property. -/
theorem preservesInterlacing_antiTranspose_iff (M : Atomic2x2Matrix) :
    M.antiTranspose.PreservesInterlacing ↔ M.PreservesInterlacing := by
  rw [preservesInterlacing_iff_mem_preserving,
    mem_preserving_antiTranspose_iff,
    ← preservesInterlacing_iff_mem_preserving]

/-- Membership in the displayed 18-matrix table is exactly nondegeneracy plus
semantic preservation of the zero-aware interlacing package. -/
theorem mem_symCatPreserving_iff (M : Atomic2x2Matrix) :
    M ∈ symCatPreserving ↔ M.IsNondegenerate ∧ M.PreservesInterlacing := by
  rw [← nondegeneratePreserving_eq_symCatPreserving]
  simp [nondegeneratePreserving, IsNondegenerate,
    preservesInterlacing_iff_mem_preserving, and_comm]

end Atomic2x2Matrix

end RealRooted
