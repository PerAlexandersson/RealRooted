module

public import RealRooted.Linear
public import RealRooted.Tactic.Finish

/-!
# Linear-polynomial tactic frontends

Thin wrappers for the degree-one real-rootedness and interlacing endpoints.
-/

public section

open Lean.Elab.Tactic
open Polynomial

namespace RealRooted

lemma strictInterl_C_mul_left_sequence {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hstrictInterl : ∀ i : Nat, StrictInterl (F i) (G i))
    (ha : ∀ i : Nat, a i ≠ 0) :
    ∀ i : Nat, StrictInterl (C (a i) * F i) (G i) := fun i =>
  StrictInterl.C_mul_left (hstrictInterl i) (ha i)

lemma strictInterl_C_mul_right_sequence {F G : Nat → ℝ[X]} {a : Nat → ℝ}
    (hstrictInterl : ∀ i : Nat, StrictInterl (F i) (G i))
    (ha : ∀ i : Nat, a i ≠ 0) :
    ∀ i : Nat, StrictInterl (F i) (C (a i) * G i) := fun i =>
  StrictInterl.C_mul_right (hstrictInterl i) (ha i)

lemma strictInterl_C_mul_both_sequence {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hstrictInterl : ∀ i : Nat, StrictInterl (F i) (G i))
    (ha : ∀ i : Nat, a i ≠ 0)
    (hb : ∀ i : Nat, b i ≠ 0) :
    ∀ i : Nat, StrictInterl (C (a i) * F i) (C (b i) * G i) := fun i =>
  StrictInterl.C_mul_right (StrictInterl.C_mul_left (hstrictInterl i) (ha i)) (hb i)

lemma C_mul_realrooted_sequence {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (ha : ∀ i : Nat, a i ≠ 0) :
    ∀ i : Nat, C (a i) * P i ≠ 0 ∧ (C (a i) * P i).Splits := fun i =>
  isRealRooted_C_mul_of_isRealRooted (hrr i) (ha i)

lemma X_mul_realrooted_sequence {P : Nat → ℝ[X]}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits) :
    ∀ i : Nat, X * P i ≠ 0 ∧ (X * P i).Splits := fun i =>
  isRealRooted_X_mul_of_isRealRooted (hrr i)

namespace Tactic

/-- Closes `X - C r ≠ 0 ∧ (X - C r).Splits` for the root `root := r`. -/
syntax (name := rr_X_sub_C_realrooted_named)
  "rr_X_sub_C_realrooted" " using "
    "root" ":=" term :
  tactic

/-- Closes `p ≠ 0 ∧ p.Splits` from `degree : p.natDegree = 1`. -/
syntax (name := rr_degree_one_realrooted_named)
  "rr_degree_one_realrooted" " using "
    "degree" ":=" term :
  tactic

/-- Bare form of `rr_degree_one_realrooted`: proves `p.natDegree = 1` by `rr_lookup [rr_degree]` or
`compute_degree!`. -/
syntax (name := rr_degree_one_realrooted_auto)
  "rr_degree_one_realrooted" : tactic

/-- Closes `p ≠ 0 ∧ p.Splits` from `nonzero : p ≠ 0` and `degree : p.natDegree ≤ 1`. -/
syntax (name := rr_natDegree_le_one_realrooted_named)
  "rr_natDegree_le_one_realrooted" " using "
    "nonzero" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Closes `Interlaces 1 p` for a linear polynomial `p`, from `degree : p.natDegree = 1`. -/
syntax (name := rr_interlaces_one_linear_named)
  "rr_interlaces_one_linear" " using "
    "degree" ":=" term :
  tactic

/-- Bare form of `rr_interlaces_one_linear`: proves `p.natDegree = 1` by `rr_lookup [rr_degree]` or
`compute_degree!`. -/
syntax (name := rr_interlaces_one_linear_auto)
  "rr_interlaces_one_linear" : tactic

/-- Closes `Interlaces (C c) p` for a linear polynomial `p`, from `scalar_ne : c ≠ 0` and
`degree : p.natDegree = 1`. -/
syntax (name := rr_interlaces_C_linear_named)
  "rr_interlaces_C_linear" " using "
    "scalar_ne" ":=" term ","
    "degree" ":=" term :
  tactic

/-- Form of `rr_interlaces_C_linear` without `degree`: `p.natDegree = 1` is proved by
`rr_lookup [rr_degree]` or `compute_degree!`. -/
syntax (name := rr_interlaces_C_linear_auto)
  "rr_interlaces_C_linear" " using "
    "scalar_ne" ":=" term :
  tactic

/-- Closes `StrictInterl (C a * f) g` from `strictInterl : StrictInterl f g` and
`scalar_ne : a ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_left_named)
  "rr_strict_interl_C_mul_left" " using "
    "strictInterl" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

/-- Form of `rr_strict_interl_C_mul_left` without `scalar_ne`: the side condition `a ≠ 0` is proved
by `rr_side_ne`. -/
syntax (name := rr_strict_interl_C_mul_left_auto)
  "rr_strict_interl_C_mul_left" " using "
    "strictInterl" ":=" term :
  tactic

/-- Sequence form of `rr_strict_interl_C_mul_left`: the same certificate for every index `i`. -/
syntax (name := rr_strict_interl_C_mul_left_sequence_named)
  "rr_strict_interl_C_mul_left_sequence" " using "
    "strictInterl" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

/-- Sequence form of `rr_strict_interl_C_mul_left` without `scalar_ne`: the side condition `a i ≠ 0`
is proved by `rr_side_ne` for every `i`. -/
syntax (name := rr_strict_interl_C_mul_left_sequence_auto)
  "rr_strict_interl_C_mul_left_sequence" " using "
    "strictInterl" ":=" term :
  tactic

/-- Closes `StrictInterl f (C a * g)` from `strictInterl : StrictInterl f g` and
`scalar_ne : a ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_right_named)
  "rr_strict_interl_C_mul_right" " using "
    "strictInterl" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

/-- Form of `rr_strict_interl_C_mul_right` without `scalar_ne`: the side condition `a ≠ 0` is proved
by `rr_side_ne`. -/
syntax (name := rr_strict_interl_C_mul_right_auto)
  "rr_strict_interl_C_mul_right" " using "
    "strictInterl" ":=" term :
  tactic

/-- Sequence form of `rr_strict_interl_C_mul_right`: the same certificate for every index `i`. -/
syntax (name := rr_strict_interl_C_mul_right_sequence_named)
  "rr_strict_interl_C_mul_right_sequence" " using "
    "strictInterl" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

/-- Sequence form of `rr_strict_interl_C_mul_right` without `scalar_ne`: the side condition
`a i ≠ 0` is proved by `rr_side_ne` for every `i`. -/
syntax (name := rr_strict_interl_C_mul_right_sequence_auto)
  "rr_strict_interl_C_mul_right_sequence" " using "
    "strictInterl" ":=" term :
  tactic

/-- Closes `StrictInterl (C a * f) (C b * g)` from `strictInterl : StrictInterl f g`,
`left_ne : a ≠ 0` and `right_ne : b ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_both_named)
  "rr_strict_interl_C_mul_both" " using "
    "strictInterl" ":=" term ","
    "left_ne" ":=" term ","
    "right_ne" ":=" term :
  tactic

/-- Form of `rr_strict_interl_C_mul_both` without `left_ne` and `right_ne`: both side conditions are
proved by `rr_side_ne`. -/
syntax (name := rr_strict_interl_C_mul_both_auto)
  "rr_strict_interl_C_mul_both" " using "
    "strictInterl" ":=" term :
  tactic

/-- Sequence form of `rr_strict_interl_C_mul_both`: the same certificate for every index `i`. -/
syntax (name := rr_strict_interl_C_mul_both_sequence_named)
  "rr_strict_interl_C_mul_both_sequence" " using "
    "strictInterl" ":=" term ","
    "left_ne" ":=" term ","
    "right_ne" ":=" term :
  tactic

/-- Sequence form of `rr_strict_interl_C_mul_both` without `left_ne` and `right_ne`: both side
conditions are proved by `rr_side_ne` for every `i`. -/
syntax (name := rr_strict_interl_C_mul_both_sequence_auto)
  "rr_strict_interl_C_mul_both_sequence" " using "
    "strictInterl" ":=" term :
  tactic

/-- Closes `C a * p ≠ 0 ∧ (C a * p).Splits` from `realrooted : p ≠ 0 ∧ p.Splits` and
`scalar_ne : a ≠ 0`; a projection of this conclusion is also accepted. -/
syntax (name := rr_C_mul_realrooted_named)
  "rr_C_mul_realrooted" " using "
    "realrooted" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

/-- Sequence form of `rr_C_mul_realrooted`: the same certificate for every index `i`. -/
syntax (name := rr_C_mul_realrooted_sequence_named)
  "rr_C_mul_realrooted_sequence" " using "
    "realrooted" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

/-- Sequence form of `rr_C_mul_realrooted` without `scalar_ne`: the side condition `a i ≠ 0` is
proved by `rr_side_ne` for every `i`. -/
syntax (name := rr_C_mul_realrooted_sequence_auto)
  "rr_C_mul_realrooted_sequence" " using "
    "realrooted" ":=" term :
  tactic

/-- Closes `X * p ≠ 0 ∧ (X * p).Splits` from `realrooted : p ≠ 0 ∧ p.Splits`; a projection of this
conclusion is also accepted. -/
syntax (name := rr_X_mul_realrooted_named)
  "rr_X_mul_realrooted" " using "
    "realrooted" ":=" term :
  tactic

/-- Sequence form of `rr_X_mul_realrooted`: the same certificate for every index `i`. -/
syntax (name := rr_X_mul_realrooted_sequence_named)
  "rr_X_mul_realrooted_sequence" " using "
    "realrooted" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_X_sub_C_realrooted using
        root := $r:term) =>
      `(tactic| exact RealRooted.isRealRooted_X_sub_C $r)
  | `(tactic|
      rr_degree_one_realrooted using
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.isRealRooted_of_degree_one $hdeg)
  | `(tactic| rr_degree_one_realrooted) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_degree_one (by
          first
            | rr_lookup [rr_degree]
            | compute_degree!))
  | `(tactic|
      rr_natDegree_le_one_realrooted using
        nonzero := $hne:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.isRealRooted_of_natDegree_le_one $hne $hdeg)
  | `(tactic|
      rr_interlaces_one_linear using
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.interlaces_one_linear $hdeg)
  | `(tactic| rr_interlaces_one_linear) =>
      `(tactic|
        exact RealRooted.interlaces_one_linear (by
          first
            | rr_lookup [rr_degree]
            | compute_degree!))
  | `(tactic|
      rr_interlaces_C_linear using
        scalar_ne := $hc:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.interlaces_C_linear $hc $hdeg)
  | `(tactic|
      rr_interlaces_C_linear using
        scalar_ne := $hc:term) =>
      `(tactic|
        exact RealRooted.interlaces_C_linear $hc (by
          first
            | rr_lookup [rr_degree]
            | compute_degree!))
  | `(tactic|
      rr_strict_interl_C_mul_left using
        strictInterl := $hstrictInterl:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.StrictInterl.C_mul_left $hstrictInterl $ha)
  | `(tactic|
      rr_strict_interl_C_mul_left using
        strictInterl := $hstrictInterl:term) =>
      `(tactic| exact RealRooted.StrictInterl.C_mul_left $hstrictInterl (by rr_side_ne))
  | `(tactic|
      rr_strict_interl_C_mul_left_sequence using
        strictInterl := $hstrictInterl:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.strictInterl_C_mul_left_sequence $hstrictInterl $ha)
  | `(tactic|
      rr_strict_interl_C_mul_left_sequence using
        strictInterl := $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.strictInterl_C_mul_left_sequence $hstrictInterl (fun i => by rr_side_ne))
  | `(tactic|
      rr_strict_interl_C_mul_right using
        strictInterl := $hstrictInterl:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.StrictInterl.C_mul_right $hstrictInterl $ha)
  | `(tactic|
      rr_strict_interl_C_mul_right using
        strictInterl := $hstrictInterl:term) =>
      `(tactic| exact RealRooted.StrictInterl.C_mul_right $hstrictInterl (by rr_side_ne))
  | `(tactic|
      rr_strict_interl_C_mul_right_sequence using
        strictInterl := $hstrictInterl:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.strictInterl_C_mul_right_sequence $hstrictInterl $ha)
  | `(tactic|
      rr_strict_interl_C_mul_right_sequence using
        strictInterl := $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.strictInterl_C_mul_right_sequence $hstrictInterl (fun i => by rr_side_ne))
  | `(tactic|
      rr_strict_interl_C_mul_both using
        strictInterl := $hstrictInterl:term,
        left_ne := $hleft:term,
        right_ne := $hright:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.C_mul_right
          (RealRooted.StrictInterl.C_mul_left $hstrictInterl $hleft) $hright)
  | `(tactic|
      rr_strict_interl_C_mul_both using
        strictInterl := $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.StrictInterl.C_mul_right
          (RealRooted.StrictInterl.C_mul_left $hstrictInterl (by rr_side_ne)) (by rr_side_ne))
  | `(tactic|
      rr_strict_interl_C_mul_both_sequence using
        strictInterl := $hstrictInterl:term,
        left_ne := $hleft:term,
        right_ne := $hright:term) =>
      `(tactic|
        exact RealRooted.strictInterl_C_mul_both_sequence $hstrictInterl $hleft $hright)
  | `(tactic|
      rr_strict_interl_C_mul_both_sequence using
        strictInterl := $hstrictInterl:term) =>
      `(tactic|
        exact RealRooted.strictInterl_C_mul_both_sequence $hstrictInterl
          (fun i => by rr_side_ne) (fun i => by rr_side_ne))
  | `(tactic|
      rr_C_mul_realrooted using
        realrooted := $hp:term,
        scalar_ne := $ha:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_C_mul_of_isRealRooted $hp $ha))
  | `(tactic|
      rr_C_mul_realrooted_sequence using
        realrooted := $hp:term,
        scalar_ne := $ha:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.C_mul_realrooted_sequence $hp $ha))
  | `(tactic|
      rr_C_mul_realrooted_sequence using
        realrooted := $hp:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.C_mul_realrooted_sequence $hp (fun i => by rr_side_ne)))
  | `(tactic|
      rr_X_mul_realrooted using
        realrooted := $hp:term) =>
      `(tactic|
        rr_first_realrooted_or_projection
          (RealRooted.isRealRooted_X_mul_of_isRealRooted $hp))
  | `(tactic|
      rr_X_mul_realrooted_sequence using
        realrooted := $hp:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.X_mul_realrooted_sequence $hp))

end Tactic
end RealRooted
namespace RealRooted

end RealRooted
