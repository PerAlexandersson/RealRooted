import RealRooted.Favard.Affine
import RealRooted.Tactic.Finish
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.SideGoals

/-!
# Favard tactic shared syntax

Shared parser declarations and macro helpers for the focused Favard tactic frontends.
-/

namespace RealRooted
namespace Tactic

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- `rr_target_head_in c₁ … cₖ` fails unless the goal, under its `∀` binders and without
unfolding, is an application of one of the `cᵢ` (or is still a metavariable).  It lets a
certificate be tried only on goals of its shape: a failing `exact` elaborates the
certificate's `by` blocks before it compares types. -/
elab "rr_target_head_in" cs:(ppSpace ident)+ : tactic => withMainContext do
  let heads ← cs.mapM fun c => realizeGlobalConstNoOverloadWithInfo c
  let body ← forallTelescope (← instantiateMVars (← getMainTarget)) fun _ b =>
    instantiateMVars b
  let f := body.getAppFn
  unless f.isMVar || heads.any f.isConstOf do
    throwError "rr_target_head_in: the goal is not an application of {cs}"

/-- The function `fun n => by simpa using hstep n`: a recurrence-step certificate for every
`n` from `hstep`. -/
syntax (name := rr_favard_step_seq) "rr_favard_step_seq " term : term

/-- Variant of `rr_favard_step_seq` that unfolds with `dsimp` first and, if
`simpa` fails, converts the goal to `hstep n` by `simp` and `ring_nf`. -/
syntax (name := rr_favard_step_dsimp_seq) "rr_favard_step_dsimp_seq " term : term

/-- The term `by simpa using hP1`: the base certificate for the second row from the hypothesis
`hP1`. -/
syntax (name := rr_favard_base_one) "rr_favard_base_one " term : term

/-- Variant of `rr_favard_base_one` that unfolds with `dsimp` first and, if
`simpa` fails, converts the goal to `hP1` by `simp` and `ring_nf`. -/
syntax (name := rr_favard_base_one_dsimp) "rr_favard_base_one_dsimp " term : term

/-- A term proving a base-case certificate by `rr_lookup`, after `dsimp` and `simp` if needed. -/
syntax (name := rr_favard_base_lookup_term) "rr_favard_base_lookup_term" : term

/-- A term proving a positivity certificate by `rr_lookup` or `rr_positivity_seq`. -/
syntax (name := rr_favard_positive_lookup_term) "rr_favard_positive_lookup_term" : term

macro_rules
  | `(rr_favard_step_seq $hstep:term) =>
      `(fun n => by simpa using $hstep n)
  | `(rr_favard_step_dsimp_seq $hstep:term) =>
      `(by
        intro n
        first | dsimp | skip
        first
        | simpa using $hstep n
        | (convert ($hstep n) <;>
            first
              | (dsimp; simp; ring_nf)
              | (dsimp; simp)
              | (simp; ring_nf)
              | simp))
  | `(rr_favard_base_one $hP1:term) =>
      `(by simpa using $hP1)
  | `(rr_favard_base_one_dsimp $hP1:term) =>
      `(by
        first | dsimp | skip
        first
        | simpa using $hP1
        | (convert ($hP1) <;>
            first
              | (dsimp; simp; ring_nf)
              | (dsimp; simp)
              | (simp; ring_nf)
              | simp))
  | `(rr_favard_base_lookup_term) =>
      `(by
        first
          | rr_lookup
          | ((first | dsimp | skip); (first | simp | skip); rr_lookup))
  | `(rr_favard_positive_lookup_term) =>
      `(by
        first
          | rr_lookup
          | rr_positivity_seq)

/-- Closes `∀ n, ...` by introducing `n` and deriving the normalized recurrence from `hraw
n` by `simpa` with ring-normalization lemmas. -/
syntax (name := rr_favard_den_raw) "rr_favard_den_raw" " using " term : tactic

/-- Term form of `rr_favard_den_raw`: elaborates to `by rr_favard_den_raw using hraw`. -/
syntax (name := rr_favard_den_raw_term) "rr_favard_den_raw_term " term : term

/-- Alias of `rr_scalar_active_den_all`: closes the scalar denominator side goal at every row. -/
macro "rr_favard_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

/-- Alias of `rr_scalar_coeff_at n`: closes a scalar coefficient identity at row `n`. -/
macro "rr_favard_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

/-- Alias of `rr_scalar_coeff_all`: closes a scalar coefficient identity at every row. -/
macro "rr_favard_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

/-- Term form of `rr_favard_active_den_all`: elaborates to `by rr_favard_active_den_all`. -/
syntax (name := rr_favard_active_den_all_term)
  "rr_favard_active_den_all_term" : term

/-- Term form of `rr_favard_coeff_at n`: elaborates to `by rr_favard_coeff_at n`. -/
syntax (name := rr_favard_coeff_at_term)
  "rr_favard_coeff_at_term " term : term

/-- Term form of `rr_favard_coeff_all`: elaborates to `by rr_favard_coeff_all`. -/
syntax (name := rr_favard_coeff_all_term)
  "rr_favard_coeff_all_term" : term

/-- Closes the goal by the first matching certificate among `hinterlace`, `hrealrooted` and
`hnonzero` (for interlacing, real-rootedness and nonvanishing goals), followed by their
projected forms; the six terms are in this order. -/
syntax (name := rr_favard_goal_variants)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term :
  tactic

/-- Variant of `rr_favard_goal_variants` that distinguishes `Interlaces` and
`StrictInterl` goals; the eight terms are `hinterlaces`, `hstrictInterl`, `hrealrooted`,
`hnonzero` and their projected forms. -/
syntax (name := rr_favard_goal_variants_interlaces)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

/-- Three-term form of `rr_favard_goal_variants`: the projected forms are the same certificates
applied to `_`. -/
syntax (name := rr_favard_goal_variants_seq)
  "rr_favard_goal_variants" term ", " term ", " term :
  tactic

/-- Closes the goal by trying three alternative certificate triples, separated by `;`, each
given as interlacing, real-rootedness and nonvanishing certificates, with and without an
argument `_`. -/
syntax (name := rr_favard_goal_variant_alternatives3)
  "rr_favard_goal_variant_alternatives3"
    term ", " term ", " term "; "
    term ", " term ", " term "; "
    term ", " term ", " term :
  tactic

/-- Refines the goal with the term
`h` and closes the remaining row-wise side goals by `rr_positivity_seq`. -/
syntax (name := rr_favard_refine_positivity_seq)
  "rr_favard_refine_positivity_seq " term :
  tactic

/-- Variant of `rr_favard_refine_positivity_seq` for real-rootedness goals, using
`rr_exact_realrooted_refine_then`. -/
syntax (name := rr_favard_exact_realrooted_positivity_seq)
  "rr_favard_exact_realrooted_positivity_seq " term :
  tactic

macro_rules
  | `(tactic| rr_favard_refine_positivity_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_positivity_seq)
  | `(tactic| rr_favard_exact_realrooted_positivity_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_positivity_seq)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlace:term, $hrealrooted:term, $hnonzero:term,
        $hinterlace_proj:term, $hrealrooted_proj:term, $hnonzero_proj:term) =>
      `(tactic|
        first
          | (rr_target_head_in StrictInterl Interlaces Interl; exact $hinterlace)
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | (rr_target_head_in Ne; exact $hnonzero)
          | (rr_target_head_in StrictInterl Interlaces Interl; exact $hinterlace_proj)
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | (rr_target_head_in Ne; exact $hnonzero_proj))
  | `(tactic|
      rr_favard_goal_variants
        $hinterlaces:term, $hstrictInterl:term, $hrealrooted:term, $hnonzero:term,
        $hinterlaces_proj:term, $hstrictInterl_proj:term, $hrealrooted_proj:term,
        $hnonzero_proj:term) =>
      `(tactic|
        first
          | (rr_target_head_in Interlaces; exact $hinterlaces)
          | (rr_target_head_in StrictInterl; exact $hstrictInterl)
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | (rr_target_head_in Ne; exact $hnonzero)
          | (rr_target_head_in Interlaces; exact $hinterlaces_proj)
          | (rr_target_head_in StrictInterl; exact $hstrictInterl_proj)
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | (rr_target_head_in Ne; exact $hnonzero_proj))
  | `(tactic|
      rr_favard_goal_variants
        $hinterlace:term, $hrealrooted:term, $hnonzero:term) =>
      `(tactic|
        rr_favard_goal_variants
          $hinterlace, $hrealrooted, $hnonzero,
          ($hinterlace _), ($hrealrooted _), ($hnonzero _))
  | `(tactic|
      rr_favard_goal_variant_alternatives3
        $hinterlace1:term, $hrealrooted1:term, $hnonzero1:term;
        $hinterlace2:term, $hrealrooted2:term, $hnonzero2:term;
        $hinterlace3:term, $hrealrooted3:term, $hnonzero3:term) =>
      `(tactic|
        first
          | rr_first_exact $hinterlace1, $hinterlace2, $hinterlace3
          | rr_first_exact $hrealrooted1, $hrealrooted2, $hrealrooted3
          | rr_first_exact $hnonzero1, $hnonzero2, $hnonzero3
          | rr_first_exact ($hinterlace1 _), ($hinterlace2 _), ($hinterlace3 _)
          | rr_first_exact ($hrealrooted1 _), ($hrealrooted2 _), ($hrealrooted3 _)
          | rr_first_exact ($hnonzero1 _), ($hnonzero2 _), ($hnonzero3 _))
  | `(tactic| rr_favard_den_raw using $hraw:term) =>
      `(tactic|
        first
          | intro n
            simpa [Nat.succ_eq_add_one] using $hraw n
          | intro n
            simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc, C_mul, mul_assoc]
              using $hraw n
          | intro n
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, C_mul,
              mul_assoc] using $hraw n)
  | `(rr_favard_den_raw_term $hraw:term) =>
      `(by rr_favard_den_raw using $hraw)
  | `(rr_favard_active_den_all_term) =>
      `(by rr_favard_active_den_all)
  | `(rr_favard_coeff_at_term $n:term) =>
      `(by rr_favard_coeff_at $n)
  | `(rr_favard_coeff_all_term) =>
      `(by rr_favard_coeff_all)

end Tactic
end RealRooted
