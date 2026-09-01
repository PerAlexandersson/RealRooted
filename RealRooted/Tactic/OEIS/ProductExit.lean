import RealRooted.Tactic.Product

/-!
# OEIS product-exit certificate frontend

Parser declarations and dispatch rules for product recurrences that terminate
at an identity, a zero root, or a period-two endpoint.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_product_exit_sequence_identity)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "identity" :
  tactic

syntax (name := rr_product_exit_sequence_root_zero)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "rootZero" :
  tactic

syntax (name := rr_product_exit_sequence_auto)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    ("cutoff" ":=" term ",")?
    "recurrence" ":=" term ","
    "certificate" ":=" "auto" :
  tactic

syntax (name := rr_product_exit_sequence_period_two)
  "rr_product_exit_sequence" " using "
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "periodTwo" :
  tactic

syntax (name := rr_product_exit_sequence_period_two_cutoff)
  "rr_product_exit_sequence" " using "
    "base" ":=" term ","
    "cutoff" ":=" term ","
    "recurrence" ":=" term ","
    "certificate" ":=" "periodTwo" :
  tactic

macro_rules
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := identity) =>
      `(tactic|
        rr_product_identity_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := identity) =>
      `(tactic|
        rr_product_identity_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_root_zero_sequence using
          base := $hbase,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := rootZero) =>
      `(tactic|
        rr_product_root_zero_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_identity_sequence using
              base := $hbase,
              recurrence := $hrec
          | rr_product_root_zero_sequence using
              base := $hbase,
              recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := auto) =>
      `(tactic|
        first
          | rr_product_identity_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec
          | rr_product_root_zero_sequence using
              base := $hbase,
              cutoff := $N,
              recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        recurrence := $hrec:term,
        certificate := periodTwo) =>
      `(tactic|
        rr_product_period_two_sequence using
          base_zero := $hbase_zero,
          base_one := $hbase_one,
          recurrence := $hrec)
  | `(tactic|
      rr_product_exit_sequence using
        base := $hbase:term,
        cutoff := $N:term,
        recurrence := $hrec:term,
        certificate := periodTwo) =>
      `(tactic|
        rr_product_period_two_sequence using
          base := $hbase,
          cutoff := $N,
          recurrence := $hrec)
end Tactic
end RealRooted
