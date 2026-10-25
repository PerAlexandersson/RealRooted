module

public import RealRooted.Basic.AffineInterlacing
public import RealRooted.EulerOperator
public import RealRooted.PosCombo
public import RealRooted.WagnerX.NonnegativeRoots

/-!
# Finite interlacing-window induction

Target module: `RealRooted.Interlacing.WindowInduction`.

This file packages the data carried by a finite window of polynomial rows.
An edge records its own relation, so a window may mix differ-by-one
`Interlaces` edges with general directed `StrictInterl` edges.  The degree
law is an explicit parameter; it is not reconstructed from interlacing.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The two directed edge relations supported by a finite window. -/
inductive WindowEdgeKind where
  | interlaces
  | strictInterl
  deriving DecidableEq

/-- A directed edge between two offsets in a finite polynomial window. -/
structure WindowEdge where
  /-- Offset of the source row. -/
  source : ℕ
  /-- Offset of the target row. -/
  target : ℕ
  /-- The interlacing relation required on this edge. -/
  kind : WindowEdgeKind
  deriving DecidableEq

namespace WindowEdge

/-- The proposition represented by a directed window edge at starting rank `n`. -/
def Holds (P : ℕ → ℝ[X]) (n : ℕ) (e : WindowEdge) : Prop :=
  match e.kind with
  | .interlaces => Interlaces (P (n + e.source)) (P (n + e.target))
  | .strictInterl => StrictInterl (P (n + e.source)) (P (n + e.target))

end WindowEdge

/-- The complete local certificate on `P n, ..., P (n + w - 1)`.

The function `degreeLaw` is deliberately external to the structure, so two
successive windows certify the same global degree formula.  Every listed edge
must have both endpoints in the window. -/
structure WindowInvariant (P : ℕ → ℝ[X]) (degreeLaw : ℕ → ℕ)
    (E : Finset WindowEdge) (n w : ℕ) : Prop where
  /-- Every row in the window is nonzero. -/
  ne_zero : ∀ i, i < w → P (n + i) ≠ 0
  /-- Every row in the window splits over the reals. -/
  splits : ∀ i, i < w → (P (n + i)).Splits
  /-- Every row in the window satisfies the prescribed degree law. -/
  natDegree_eq : ∀ i, i < w → (P (n + i)).natDegree = degreeLaw (n + i)
  /-- Every row in the window has positive leading coefficient. -/
  posLeadingCoeff : ∀ i, i < w → HasPosLeadingCoeff (P (n + i))
  /-- Every edge source is a valid offset. -/
  source_lt : ∀ e ∈ E, e.source < w
  /-- Every edge target is a valid offset. -/
  target_lt : ∀ e ∈ E, e.target < w
  /-- Every prescribed directed edge holds. -/
  edge : ∀ e ∈ E, e.Holds P n

namespace WindowInvariant

/-- Induction on a finite interlacing-window certificate. -/
theorem induction {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {w : ℕ}
    (hbase : WindowInvariant P degreeLaw E 0 w)
    (hstep : ∀ n, WindowInvariant P degreeLaw E n w →
      WindowInvariant P degreeLaw E (n + 1) w) :
    ∀ n, WindowInvariant P degreeLaw E n w := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n => simpa only [Nat.succ_eq_add_one] using hstep n (by assumption)

/-- Extract real-rootedness of any row occurring in a certified window. -/
theorem isRealRooted {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w i : ℕ}
    (h : WindowInvariant P degreeLaw E n w) (hi : i < w) :
    P (n + i) ≠ 0 ∧ (P (n + i)).Splits :=
  ⟨h.ne_zero i hi, h.splits i hi⟩

/-- A certified differ-by-one edge can be used as a `StrictInterl` edge. -/
theorem strictInterl_of_interlaces_edge
    {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w : ℕ} (h : WindowInvariant P degreeLaw E n w)
    {i j : ℕ} (hedge : ⟨i, j, .interlaces⟩ ∈ E) :
    StrictInterl (P (n + i)) (P (n + j)) :=
  (h.edge ⟨i, j, .interlaces⟩ hedge).toStrictInterl

/-- Extract a general directed `StrictInterl` edge from a certified window. -/
theorem strictInterl_of_strictInterl_edge
    {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w : ℕ} (h : WindowInvariant P degreeLaw E n w)
    {i j : ℕ} (hedge : ⟨i, j, .strictInterl⟩ ∈ E) :
    StrictInterl (P (n + i)) (P (n + j)) :=
  h.edge ⟨i, j, .strictInterl⟩ hedge

/-- Translating every polynomial variable preserves a complete window certificate. -/
theorem comp_X_add_C {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w : ℕ}
    (h : WindowInvariant P degreeLaw E n w) (r : ℝ) :
    WindowInvariant (fun k ↦ (P k).comp (X + C r)) degreeLaw E n w := by
  refine ⟨?_, ?_, ?_, ?_, h.source_lt, h.target_lt, ?_⟩
  · intro i hi
    exact (Polynomial.comp_X_add_C_ne_zero_iff).2 (h.ne_zero i hi)
  · intro i hi
    exact (isRealRooted_comp_X_add_C (h.ne_zero i hi) (h.splits i hi) r).2
  · intro i hi
    rw [Polynomial.natDegree_comp, h.natDegree_eq i hi]
    simp
  · intro i hi
    exact (h.posLeadingCoeff i hi).comp_X_add_C r
  · intro e he
    have hedge := h.edge e he
    cases hk : e.kind with
    | interlaces =>
        rw [WindowEdge.Holds, hk] at hedge ⊢
        exact interlaces_comp_X_add_C hedge r
    | strictInterl =>
        rw [WindowEdge.Holds, hk] at hedge ⊢
        exact hedge.comp_X_add_C r

/-- Positive rescaling of the variable preserves a complete window certificate. -/
theorem comp_C_mul_X {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w : ℕ}
    (h : WindowInvariant P degreeLaw E n w) {a : ℝ} (ha : 0 < a) :
    WindowInvariant (fun k ↦ (P k).comp (C a * X)) degreeLaw E n w := by
  refine ⟨?_, ?_, ?_, ?_, h.source_lt, h.target_lt, ?_⟩
  · intro i hi
    exact (isRealRooted_comp_C_mul_X (h.ne_zero i hi) (h.splits i hi) ha.ne').1
  · intro i hi
    exact (isRealRooted_comp_C_mul_X (h.ne_zero i hi) (h.splits i hi) ha.ne').2
  · intro i hi
    rw [Polynomial.natDegree_comp, h.natDegree_eq i hi]
    simp [ha.ne']
  · intro i hi
    unfold HasPosLeadingCoeff
    rw [Polynomial.leadingCoeff_comp (by simp [ha.ne'])]
    simp only [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
    exact mul_pos (h.posLeadingCoeff i hi) (pow_pos ha _)
  · intro e he
    have hedge := h.edge e he
    cases hk : e.kind with
    | interlaces =>
        rw [WindowEdge.Holds, hk] at hedge ⊢
        apply (hedge.toStrictInterl.comp_C_mul_X ha).toInterlaces
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_comp]
        simpa only [Polynomial.natDegree_C_mul_X a ha.ne', mul_one] using hedge.2.2.1
    | strictInterl =>
        rw [WindowEdge.Holds, hk] at hedge ⊢
        exact hedge.comp_C_mul_X ha

/-- A positive-slope affine change of variable preserves a complete window certificate. -/
theorem comp_C_mul_X_add_C {P : ℕ → ℝ[X]} {degreeLaw : ℕ → ℕ}
    {E : Finset WindowEdge} {n w : ℕ}
    (h : WindowInvariant P degreeLaw E n w) {a b : ℝ} (ha : 0 < a) :
    WindowInvariant (fun k ↦ (P k).comp (C a * X + C b)) degreeLaw E n w := by
  simpa only [Polynomial.comp_assoc, add_comp, X_comp, C_comp] using
    (h.comp_X_add_C b).comp_C_mul_X ha

end WindowInvariant

/-- `thetaPlusOne` preserves the degree of a nonzero polynomial. -/
theorem natDegree_thetaPlusOne_of_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    (thetaPlusOne p).natDegree = p.natDegree := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_thetaPlusOne, coeff_eq_zero_of_natDegree_lt hk, mul_zero]
  · rw [coeff_thetaPlusOne]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hp)

/-- The Euler operator `thetaPlusOne` is nonzero on nonzero polynomials. -/
theorem thetaPlusOne_ne_zero_of_ne_zero {p : ℝ[X]} (hp : p ≠ 0) :
    thetaPlusOne p ≠ 0 := by
  intro hzero
  have hcoeff : (thetaPlusOne p).coeff p.natDegree ≠ 0 := by
    rw [coeff_thetaPlusOne]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hp)
  rw [hzero, coeff_zero] at hcoeff
  exact hcoeff rfl

/-- `thetaPlusOne` preserves a directed nonzero interlacing edge. -/
theorem StrictInterl.thetaPlusOne {p q : ℝ[X]} (h : StrictInterl p q) :
    StrictInterl (thetaPlusOne p) (thetaPlusOne q) := by
  have hinterl := h.toInterl.thetaPlusOne
  rcases hinterl with hp0 | hq0 | hstrict
  · exact absurd hp0 (thetaPlusOne_ne_zero_of_ne_zero h.1.1)
  · exact absurd hq0 (thetaPlusOne_ne_zero_of_ne_zero h.2.1.1)
  · exact hstrict

/-- Applying `theta + 1` to a polar comparison preserves strict interlacing. -/
theorem StrictInterl.polarTheta_thetaPlusOne {N : ℕ} {p q : ℝ[X]}
    (h : StrictInterl (polarTheta N p) q) :
    StrictInterl (polarTheta N (RealRooted.thetaPlusOne p)) (RealRooted.thetaPlusOne q) := by
  rw [polarTheta_thetaPlusOne_comm]
  exact h.thetaPlusOne

/-- `thetaPlusOne` preserves a differ-by-one interlacing edge. -/
theorem Interlaces.thetaPlusOne {p q : ℝ[X]} (h : Interlaces p q) :
    Interlaces (RealRooted.thetaPlusOne p) (RealRooted.thetaPlusOne q) := by
  apply h.toStrictInterl.thetaPlusOne.toInterlaces
  rw [natDegree_thetaPlusOne_of_ne_zero h.2.1.1,
    natDegree_thetaPlusOne_of_ne_zero h.1.1]
  exact h.2.2.1

/-- A positive two-term sum remains above a common strict left interleaver. -/
theorem StrictInterl.add_mul_X_of_common_left {h u v : ℝ[X]} {c : ℝ}
    (hc : 0 < c) (hu : StrictInterl h u) (hv : StrictInterl h (X * v))
    (hupos : HasPosLeadingCoeff u) (hvpos : HasPosLeadingCoeff (X * v)) :
    StrictInterl h (u + C c * X * v) := by
  have hscaled : StrictInterl h (C c * (X * v)) :=
    StrictInterl.C_mul_right hv hc.ne'
  have hscaledPos : HasPosLeadingCoeff (C c * (X * v)) :=
    hasPosLeadingCoeff_C_mul hc hvpos
  have hsum : StrictInterl h ([u, C c * (X * v)] : List ℝ[X]).sum := by
    apply StrictInterl.sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hu
      · exact hscaled
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hupos
      · exact hscaledPos
    · simp
  simpa only [List.sum_cons, List.sum_nil, add_zero, mul_assoc] using hsum

end RealRooted
