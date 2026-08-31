import RealRooted.Bezoutian

/-!
# Strict proper-position bridge

The Bezoutian/Wronskian criterion produces `StrictPrecSameDegree`; this module
converts it to the project's legacy non-strict `Prec` predicate.
-/

open Polynomial

namespace RealRooted

/-- Strict same-degree proper position implies the legacy non-strict proper
position predicate. -/
theorem strictPrecSameDegree_toPrec {p q : ℝ[X]}
    (h : StrictPrecSameDegree p q) : Prec p q := by
  obtain ⟨hp, hq, hdeg, hint⟩ := h
  set ss := p.roots.sort (· ≤ ·) with hss_def
  set rs := q.roots.sort (· ≤ ·) with hrs_def
  have hss_eq : (↑ss : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hrs_eq : (↑rs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
  have hss_pw : ss.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_pw : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_len : ss.length = p.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hp.2]
  have hrs_len : rs.length = q.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
  have hlen : ss.length = rs.length := by
    simp_all
  have hswap : List.Interleaves (· < ·) rs ss := by
    have hrev := (List.interleaves_reverse_reverse_of_length_eq_length
      (r := (· > ·)) hlen).1 hint
    exact hrev
  have hweak : List.Interleaves (· ≤ ·) rs ss :=
    List.Interleaves.mono (fun _ _ hab ↦ le_of_lt hab) _ _ hswap
  have halt : ListAlternates ss rs :=
    listAlternates_of_interleaves_of_length hlen hweak
  exact ⟨hp, hq, ss, rs, hss_pw, hrs_pw, hss_eq, hrs_eq, Or.inr ⟨hlen, halt⟩⟩

end RealRooted
