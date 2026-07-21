import RealRooted.MagnitudeDominated

/-!
# Magnitude-dominated lag tactic frontends

Thin wrappers for magnitude-dominated Ma-Wang / generalized Liu-Wang
interlacing certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem magnitude_dominated_sequence_succ
    {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hinter : ∀ i : Nat, Interlaces (G1 i) (F i))
    (hinterpos : ∀ i : Nat, HasPosLeadingCoeff (G1 i))
    (htargetpos : ∀ i : Nat,
      HasPosLeadingCoeff (A i * F i + B1 i * G1 i + B2 i * G2 i))
    (hdeg : ∀ i : Nat,
      (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree =
        (F i).natDegree + 1)
    (hcert : ∀ i : Nat, ∀ r, (F i).IsRoot r →
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0) :
    ∀ i : Nat, Prec (F i) (A i * F i + B1 i * G1 i + B2 i * G2 i) := fun i =>
  RealRooted.prec_of_magnitude_dominated_succ
    (hinter i) (hinterpos i) (htargetpos i) (hdeg i) (hcert i)

theorem magnitude_dominated_sequence_same
    {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hinter : ∀ i : Nat, Interlaces (G1 i) (F i))
    (hinterpos : ∀ i : Nat, HasPosLeadingCoeff (G1 i))
    (htargetpos : ∀ i : Nat,
      HasPosLeadingCoeff (A i * F i + B1 i * G1 i + B2 i * G2 i))
    (hdeg : ∀ i : Nat,
      (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree =
        (F i).natDegree)
    (hcert : ∀ i : Nat, ∀ r, (F i).IsRoot r →
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0) :
    ∀ i : Nat, Prec (F i) (A i * F i + B1 i * G1 i + B2 i * G2 i) := fun i =>
  RealRooted.prec_of_magnitude_dominated_same
    (hinter i) (hinterpos i) (htargetpos i) (hdeg i) (hcert i)

theorem magnitude_dominated_sequence
    {F G1 G2 A B1 B2 : Nat → ℝ[X]}
    (hinter : ∀ i : Nat, Interlaces (G1 i) (F i))
    (hinterpos : ∀ i : Nat, HasPosLeadingCoeff (G1 i))
    (htargetpos : ∀ i : Nat,
      HasPosLeadingCoeff (A i * F i + B1 i * G1 i + B2 i * G2 i))
    (hdeglo : ∀ i : Nat,
      (F i).natDegree ≤ (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree)
    (hdeghi : ∀ i : Nat,
      (A i * F i + B1 i * G1 i + B2 i * G2 i).natDegree ≤
        (F i).natDegree + 1)
    (hcert : ∀ i : Nat, ∀ r, (F i).IsRoot r →
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0) :
    ∀ i : Nat, Prec (F i) (A i * F i + B1 i * G1 i + B2 i * G2 i) := fun i =>
  RealRooted.prec_of_magnitude_dominated
    (hinter i) (hinterpos i) (htargetpos i) (hdeglo i) (hdeghi i) (hcert i)

theorem magnitude_sequence_cert_of_abs_dominated
    {B1 G1 B2 G2 : Nat → ℝ[X]}
    (hhead : ∀ i : Nat, ∀ r,
      (B1 i).eval r * ((G1 i).eval r) ^ 2 < 0)
    (hdom : ∀ i : Nat, ∀ r,
      |(B2 i).eval r * ((G2 i).eval r * (G1 i).eval r)| <
        |(B1 i).eval r * ((G1 i).eval r) ^ 2|) :
    ∀ i : Nat, ∀ r,
      (B1 i).eval r * ((G1 i).eval r) ^ 2 +
        (B2 i).eval r * ((G2 i).eval r * (G1 i).eval r) < 0 := fun i r =>
  RealRooted.magnitude_cert_of_abs_dominated (hhead i r) (hdom i r)

syntax (name := rr_magnitude_dominated_succ_named)
  "rr_magnitude_dominated_succ" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_sequence_succ_named)
  "rr_magnitude_dominated_sequence_succ" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_same_named)
  "rr_magnitude_dominated_same" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_sequence_same_named)
  "rr_magnitude_dominated_sequence_same" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_named)
  "rr_magnitude_dominated" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_sequence_named)
  "rr_magnitude_dominated_sequence" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_cert_abs_dominated_named)
  "rr_magnitude_cert_abs_dominated" " using "
    "head_negative" ":=" term ","
    "domination" ":=" term :
  tactic

syntax (name := rr_magnitude_sequence_cert_abs_dominated_named)
  "rr_magnitude_sequence_cert_abs_dominated" " using "
    "head_negative" ":=" term ","
    "domination" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_magnitude_dominated_succ using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree := $hdeg:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.prec_of_magnitude_dominated_succ
          $hinter $hinterpos $htargetpos $hdeg $hcert)
  | `(tactic|
      rr_magnitude_dominated_sequence_succ using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree := $hdeg:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.Tactic.magnitude_dominated_sequence_succ
          $hinter $hinterpos $htargetpos $hdeg $hcert)
  | `(tactic|
      rr_magnitude_dominated_same using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree := $hdeg:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.prec_of_magnitude_dominated_same
          $hinter $hinterpos $htargetpos $hdeg $hcert)
  | `(tactic|
      rr_magnitude_dominated_sequence_same using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree := $hdeg:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.Tactic.magnitude_dominated_sequence_same
          $hinter $hinterpos $htargetpos $hdeg $hcert)
  | `(tactic|
      rr_magnitude_dominated using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree_lower := $hlo:term,
        degree_upper := $hhi:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.prec_of_magnitude_dominated
          $hinter $hinterpos $htargetpos $hlo $hhi $hcert)
  | `(tactic|
      rr_magnitude_dominated_sequence using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree_lower := $hlo:term,
        degree_upper := $hhi:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.Tactic.magnitude_dominated_sequence
          $hinter $hinterpos $htargetpos $hlo $hhi $hcert)
  | `(tactic|
      rr_magnitude_cert_abs_dominated using
        head_negative := $hhead:term,
        domination := $hdom:term) =>
      `(tactic| exact RealRooted.magnitude_cert_of_abs_dominated $hhead $hdom)
  | `(tactic|
      rr_magnitude_sequence_cert_abs_dominated using
        head_negative := $hhead:term,
        domination := $hdom:term) =>
      `(tactic|
        exact RealRooted.Tactic.magnitude_sequence_cert_of_abs_dominated
          $hhead $hdom)

end Tactic
end RealRooted
