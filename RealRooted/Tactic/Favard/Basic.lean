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

syntax (name := rr_favard_step_seq) "rr_favard_step_seq " term : term

syntax (name := rr_favard_step_dsimp_seq) "rr_favard_step_dsimp_seq " term : term

syntax (name := rr_favard_base_one) "rr_favard_base_one " term : term

syntax (name := rr_favard_base_one_dsimp) "rr_favard_base_one_dsimp " term : term

syntax (name := rr_favard_base_lookup_term) "rr_favard_base_lookup_term" : term

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

syntax (name := rr_favard_den_raw) "rr_favard_den_raw" " using " term : tactic

syntax (name := rr_favard_den_raw_term) "rr_favard_den_raw_term " term : term

macro "rr_favard_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

macro "rr_favard_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

macro "rr_favard_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

syntax (name := rr_favard_active_den_all_term)
  "rr_favard_active_den_all_term" : term

syntax (name := rr_favard_coeff_at_term)
  "rr_favard_coeff_at_term " term : term

syntax (name := rr_favard_coeff_all_term)
  "rr_favard_coeff_all_term" : term

syntax (name := rr_favard_goal_variants)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variants_interlaces)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variants_seq)
  "rr_favard_goal_variants" term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variant_alternatives3)
  "rr_favard_goal_variant_alternatives3"
    term ", " term ", " term "; "
    term ", " term ", " term "; "
    term ", " term ", " term :
  tactic

syntax (name := rr_favard_refine_positivity_seq)
  "rr_favard_refine_positivity_seq " term :
  tactic

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
          | exact $hinterlace
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | exact $hnonzero
          | exact $hinterlace_proj
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | exact $hnonzero_proj)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlaces:term, $hprec:term, $hrealrooted:term, $hnonzero:term,
        $hinterlaces_proj:term, $hprec_proj:term, $hrealrooted_proj:term,
        $hnonzero_proj:term) =>
      `(tactic|
        first
          | exact $hinterlaces
          | exact $hprec
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | exact $hnonzero
          | exact $hinterlaces_proj
          | exact $hprec_proj
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | exact $hnonzero_proj)
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
