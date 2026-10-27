module

public import RealRooted.Tactic.Finish

/-!
# Product-family tactic syntax

Syntax for Product side tactics and the retained lift dispatcher.
-/

@[expose] public section

namespace RealRooted

namespace Tactic

open Lean
open Lean.Elab.Tactic
open Lean.Meta

/-- Closes a nonvanishing side goal such as `a ≠ 0` by `rr_side_ne`. -/
syntax (name := rr_product_nonzero) "rr_product_nonzero" : tactic

/-- Closes the goal from the certificate `h` by `exact`, or else after normalizing numerals and ring
expressions with `norm_num` and `ring`. -/
syntax (name := rr_product_normalize)
  "rr_product_normalize" " using " term :
  tactic

/-- Term elaborating to `fun n => by rr_product_nonzero`, a pointwise nonvanishing proof for a
sequence. -/
syntax (name := rr_product_nonzero_seq) "rr_product_nonzero_seq" : term

/-- Term elaborating to `fun n _ => by rr_product_nonzero`, a pointwise nonvanishing proof for a
sequence from a cutoff on. -/
syntax (name := rr_product_nonzero_seq_from) "rr_product_nonzero_seq_from" : term

/-- Closes the goal by one of two sequence certificates, written with the factor on the left and on
the right: the orientation of the first one is read off its type, and the matching certificate is
passed to `rr_first_realrooted_sequence_or_projection`. -/
syntax (name := rr_product_two_sequence_variants)
  "rr_product_two_sequence_variants" term ", " term :
  tactic

end Tactic
end RealRooted
